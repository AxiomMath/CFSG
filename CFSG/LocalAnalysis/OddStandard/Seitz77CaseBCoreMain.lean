module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBCoreGen
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBCoreO
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Main

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section Diagonal

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G}

structure CaseB.DiagData (c : CaseB A R t) (M₁ M₂ : Subgroup G) (a a' : G) : Prop where
  mem₁ : a ∈ M₁
  mem₂ : a' ∈ M₂
  sq : a * a = 1
  comm : a * a' = a' * a
  swap : t * a * t⁻¹ = a'
  mem_A : a * a' ∈ A
  not_mem_K : a ∉ centralizer (c.W : Set G)

namespace CaseB.DiagData

variable {c : CaseB A R t} {M₁ M₂ : Subgroup G} {a a' : G} (D : CaseB.DiagData c M₁ M₂ a a')

include D

theorem sq' : a' * a' = 1 := by
  have h : a' * a' = t * (a * a) * t⁻¹ := by rw [← D.swap]; group
  rw [h, D.sq]
  group

theorem z_sq : (a * a') * (a * a') = 1 := by
  calc a * a' * (a * a') = a * (a' * a) * a' := by group
    _ = a * (a * a') * a' := by rw [D.comm]
    _ = (a * a) * (a' * a') := by group
    _ = 1 := by rw [D.sq, D.sq', one_mul]

theorem a_comm_z : a * (a * a') = (a * a') * a := by
  calc a * (a * a') = a * (a' * a) := by rw [D.comm]
    _ = (a * a') * a := by group

theorem t_comm_z (ht2 : t * t = 1) : t * (a * a') = (a * a') * t := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 : t * a = a' * t := by rw [← D.swap]; group
  have h2 : t * a' = a * t := by
    rw [← D.swap]
    calc t * (t * a * t⁻¹) = (t * t) * a * t⁻¹ := by group
      _ = a * t := by rw [ht2, one_mul, ht1]
  calc t * (a * a') = (t * a) * a' := by group
    _ = (a' * t) * a' := by rw [h1]
    _ = a' * (t * a') := by group
    _ = a' * (a * t) := by rw [h2]
    _ = (a' * a) * t := by group
    _ = (a * a') * t := by rw [D.comm]

theorem t_mul_z (ht2 : t * t = 1) : t * (a * a') = a * t * a⁻¹ := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right D.sq
  have h2 : t * a' = a * t := by
    rw [← D.swap]
    calc t * (t * a * t⁻¹) = (t * t) * a * t⁻¹ := by group
      _ = a * t := by rw [ht2, one_mul, ht1]
  calc t * (a * a') = t * (a' * a) := by rw [D.comm]
    _ = (t * a') * a := by group
    _ = a * t * a⁻¹ := by rw [h2, ha1]

end CaseB.DiagData

end Diagonal

section Heart

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G}
  {c : CaseB A R t} {M₁ M₂ : Subgroup G} {a a' : G}

theorem CaseB.DiagData.Q_le_centralizer_z (D : CaseB.DiagData c M₁ M₂ a a') (F : c.Factors M₁ M₂)
    {O₁ : Subgroup G} (hO : CaseB.OddCoreData c O₁) :
    O₁ ⊓ c.Ninf ≤ centralizer ({a * a'} : Set G) := by
  have ht2 : t * t = 1 := c.t_mul_self
  have hM₁ : M₁ ≤ c.Ninf := by rw [F.ninf_eq]; exact le_sup_left
  have hM₂ : M₂ ≤ c.Ninf := by rw [F.ninf_eq]; exact le_sup_right
  have hNinfN : c.Ninf ≤ c.N := prOf_le c.N
  have haN : a ∈ c.N := hNinfN (hM₁ D.mem₁)
  have hzN : a * a' ∈ c.N := hNinfN (c.Ninf.mul_mem (hM₁ D.mem₁) (hM₂ D.mem₂))
  have hQn : ∀ x ∈ c.N, ∀ q ∈ O₁ ⊓ c.Ninf, x * q * x⁻¹ ∈ O₁ ⊓ c.Ninf :=
    fun x hx q hq => hO.conj_mem hx hq
  refine le_of_forall_commute_mem_four hO.odd_card_inf ht2 D.z_sq (D.t_comm_z ht2) ?_ ?_ ?_
  · exact mem_normalizer_fintype fun n hn => hQn t c.t_mem_N n hn
  · exact mem_normalizer_fintype fun n hn => hQn _ hzN n hn
  · intro w hw n hn hwn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h | h
    ·
      subst h
      have hnA := hO.mem_centralizer_A_of_comm_t hn.1 hwn.symm
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hnA _ D.mem_A).symm
    ·
      subst h
      exact mem_centralizer_singleton_iff.mpr hwn.symm
    ·
      subst h
      rw [D.t_mul_z ht2] at hwn
      have hn' : a⁻¹ * n * a ∈ O₁ ⊓ c.Ninf := by
        have := hQn a⁻¹ (c.N.inv_mem haN) n hn
        simpa using this
      have hcomm : t * (a⁻¹ * n * a) = (a⁻¹ * n * a) * t := by
        calc t * (a⁻¹ * n * a) = a⁻¹ * ((a * t * a⁻¹) * n) * a := by group
          _ = a⁻¹ * (n * (a * t * a⁻¹)) * a := by rw [hwn]
          _ = (a⁻¹ * n * a) * t := by group
      have hn'A := hO.mem_centralizer_A_of_comm_t hn'.1 hcomm.symm
      have hz' : (a * a') * (a⁻¹ * n * a) = (a⁻¹ * n * a) * (a * a') :=
        mem_centralizer_iff.mp hn'A _ D.mem_A
      have hz_conj : a * (a * a') * a⁻¹ = a * a' := by
        rw [D.a_comm_z]
        group
      rw [mem_centralizer_singleton_iff]
      calc n * (a * a') = n * (a * (a * a') * a⁻¹) := by rw [hz_conj]
        _ = a * ((a⁻¹ * n * a) * (a * a')) * a⁻¹ := by group
        _ = a * ((a * a') * (a⁻¹ * n * a)) * a⁻¹ := by rw [hz']
        _ = (a * (a * a') * a⁻¹) * n := by group
        _ = (a * a') * n := by rw [hz_conj]

theorem CaseB.Factors.centralOddCore_of_diagonal (F : c.Factors M₁ M₂)
    (D : CaseB.DiagData c M₁ M₂ a a') : CentralOddCore c.Ninf := by
  obtain ⟨O₁, hO⟩ := F.exists_oddCoreData
  have hW : c.W ≤ c.Ninf := F.W_le
  have hM₁ : M₁ ≤ c.Ninf := by rw [F.ninf_eq]; exact le_sup_left
  have hM₂ : M₂ ≤ c.Ninf := by rw [F.ninf_eq]; exact le_sup_right
  have hNinfN : c.Ninf ≤ c.N := prOf_le c.N
  have haN : a ∈ c.N := hNinfN (hM₁ D.mem₁)
  have ha'N : a' ∈ c.N := hNinfN (hM₂ D.mem₂)
  have hQn : ∀ x ∈ c.N, ∀ q ∈ O₁ ⊓ c.Ninf, x * q * x⁻¹ ∈ O₁ ⊓ c.Ninf :=
    fun x hx q hq => hO.conj_mem hx hq
  have hQz := D.Q_le_centralizer_z F hO
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G,
      C = c.Ninf ⊓ centralizer ((O₁ ⊓ c.Ninf : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hCmem : ∀ y, y ∈ C ↔ y ∈ c.Ninf ∧ ∀ q ∈ O₁ ⊓ c.Ninf, q * y = y * q := fun y => by
    rw [hC, mem_inf, mem_centralizer_iff]
    exact Iff.rfl
  have hCn : ∀ x ∈ c.N, ∀ y ∈ C, x * y * x⁻¹ ∈ C := by
    intro x hx y hy
    obtain ⟨hyN, hyq⟩ := (hCmem y).mp hy
    refine (hCmem _).mpr ⟨prOf_conj_mem c.N hx hyN, fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x⁻¹⁻¹ ∈ O₁ ⊓ c.Ninf := hQn x⁻¹ (c.N.inv_mem hx) q hq
    have hyq' := hyq _ hq'
    calc q * (x * y * x⁻¹) = x * ((x⁻¹ * q * x⁻¹⁻¹) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * q * x⁻¹⁻¹)) * x⁻¹ := by rw [hyq']
      _ = (x * y * x⁻¹) * q := by group
  have hWC : c.W ≤ C := fun w hw => (hCmem w).mpr ⟨hW hw, fun q hq =>
    (mem_centralizer_iff.mp (hO.le_centralizer hq.1) w hw).symm⟩
  have hzC : a * a' ∈ C := (hCmem _).mpr ⟨c.Ninf.mul_mem (hM₁ D.mem₁) (hM₂ D.mem₂), fun q hq =>
    mem_centralizer_singleton_iff.mp (hQz hq)⟩
  have hQnorm : (O₁ ⊓ c.Ninf : Subgroup G) ≤ normalizer (C : Set G) := fun q hq =>
    mem_normalizer_fintype fun y hy => hCn q (hNinfN hq.2) y hy
  have hDmem : ∀ d ∈ C ⊔ (O₁ ⊓ c.Ninf), ∃ y ∈ C, ∃ q ∈ O₁ ⊓ c.Ninf, d = y * q := by
    intro d hd
    have hd' : d ∈ ((C ⊔ (O₁ ⊓ c.Ninf) : Subgroup G) : Set G) := hd
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C (O₁ ⊓ c.Ninf) hQnorm] at hd'
    obtain ⟨y, hy, q, hq, rfl⟩ := hd'
    exact ⟨y, hy, q, hq, rfl⟩
  have hDn : ∀ x ∈ c.N, ∀ d ∈ C ⊔ (O₁ ⊓ c.Ninf), x * d * x⁻¹ ∈ C ⊔ (O₁ ⊓ c.Ninf) := by
    intro x hx d hd
    obtain ⟨y, hy, q, hq, rfl⟩ := hDmem d hd
    have : x * (y * q) * x⁻¹ = (x * y * x⁻¹) * (x * q * x⁻¹) := by group
    rw [this]
    exact mul_mem (mem_sup_left (hCn x hx y hy)) (mem_sup_right (hQn x hx q hq))
  have hKD : ∀ k ∈ centralizer (c.W : Set G), k ∈ c.Ninf → k ∈ C ⊔ (O₁ ⊓ c.Ninf) := by
    intro k hk hkN
    obtain ⟨w, hw, o, ho, rfl⟩ := hO.decomp k hk
    have hoN : o ∈ c.Ninf := by
      have := c.Ninf.mul_mem (c.Ninf.inv_mem (hW hw)) hkN
      simpa using this
    exact mul_mem (mem_sup_left (hWC hw)) (mem_sup_right (mem_inf.mpr ⟨ho, hoN⟩))
  have hinfQ : M₁ ⊓ M₂ ≤ O₁ ⊓ c.Ninf := by
    refine hO.le_inf_of_odd_normal hW (inf_le_left.trans hM₁) ?_ F.odd_inf
    intro n hn q hq
    exact ⟨F.norm₁ n hn q hq.1, F.norm₂ n hn q hq.2⟩
  have hc₁ : ∀ m ∈ M₁, m * a' * m⁻¹ * a'⁻¹ ∈ O₁ ⊓ c.Ninf := by
    intro m hm
    refine hinfQ ⟨?_, ?_⟩
    · have h1 := F.norm₁ a' (hM₂ D.mem₂) m⁻¹ (M₁.inv_mem hm)
      have e : m * a' * m⁻¹ * a'⁻¹ = m * (a' * m⁻¹ * a'⁻¹) := by group
      rw [e]
      exact M₁.mul_mem hm h1
    · exact M₂.mul_mem (F.norm₂ m (hM₁ hm) a' D.mem₂) (M₂.inv_mem D.mem₂)
  have hc₂ : ∀ m ∈ M₂, m * a * m⁻¹ * a⁻¹ ∈ O₁ ⊓ c.Ninf := by
    intro m hm
    refine hinfQ ⟨?_, ?_⟩
    · exact M₁.mul_mem (F.norm₁ m (hM₂ hm) a D.mem₁) (M₁.inv_mem D.mem₁)
    · have h1 := F.norm₂ a (hM₁ D.mem₁) m⁻¹ (M₂.inv_mem hm)
      have e : m * a * m⁻¹ * a⁻¹ = m * (a * m⁻¹ * a⁻¹) := by group
      rw [e]
      exact M₂.mul_mem hm h1
  have hcomm₁ : ∀ m ∈ M₁, m * a * m⁻¹ * a⁻¹ ∈ C ⊔ (O₁ ⊓ c.Ninf) := by
    intro m hm
    have hX : m * (a * a') * m⁻¹ * (a * a')⁻¹ ∈ C :=
      C.mul_mem (hCn m (hNinfN (hM₁ hm)) _ hzC) (C.inv_mem hzC)
    have hY : a * (m * a' * m⁻¹ * a'⁻¹) * a⁻¹ ∈ O₁ ⊓ c.Ninf := hQn a haN _ (hc₁ m hm)
    have e : m * a * m⁻¹ * a⁻¹ = (m * (a * a') * m⁻¹ * (a * a')⁻¹) *
        (a * (m * a' * m⁻¹ * a'⁻¹) * a⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem (mem_sup_left hX) (inv_mem (mem_sup_right hY))
  have hcomm₂ : ∀ m ∈ M₂, m * a' * m⁻¹ * a'⁻¹ ∈ C ⊔ (O₁ ⊓ c.Ninf) := by
    intro m hm
    have hX : m * (a * a') * m⁻¹ * (a * a')⁻¹ ∈ C :=
      C.mul_mem (hCn m (hNinfN (hM₂ hm)) _ hzC) (C.inv_mem hzC)
    have hY : a' * (m * a * m⁻¹ * a⁻¹) * a'⁻¹ ∈ O₁ ⊓ c.Ninf := hQn a' ha'N _ (hc₂ m hm)
    have e : m * a' * m⁻¹ * a'⁻¹ = (m * (a * a') * m⁻¹ * (a * a')⁻¹) *
        (a' * (m * a * m⁻¹ * a⁻¹) * a'⁻¹)⁻¹ := by
      rw [D.comm]
      group
    rw [e]
    exact mul_mem (mem_sup_left hX) (inv_mem (mem_sup_right hY))
  have ha'K : a' ∉ centralizer (c.W : Set G) := by
    intro h
    apply D.not_mem_K
    have htN : t⁻¹ ∈ c.N := c.N.inv_mem c.t_mem_N
    have h1 := (mem_set_normalizer_iff.mp (normalizer_le_normalizer_centralizer_W c.W htN) a').mp h
    have e : t⁻¹ * a' * t⁻¹⁻¹ = a := by rw [← D.swap]; group
    rwa [e] at h1
  obtain ⟨π₁, hπ₁, hker₁⟩ := F.a5₁
  obtain ⟨π₂, hπ₂, hker₂⟩ := F.a5₂
  have hM₁D : M₁ ≤ C ⊔ (O₁ ⊓ c.Ninf) :=
    le_of_commutators_mem_of_a5 π₁ hπ₁ hker₁ (fun m hm d hd => hDn m (hNinfN (hM₁ hm)) d hd)
      (fun k hk hkM => hKD k hk (hM₁ hkM)) D.mem₁ D.not_mem_K hcomm₁
  have hM₂D : M₂ ≤ C ⊔ (O₁ ⊓ c.Ninf) :=
    le_of_commutators_mem_of_a5 π₂ hπ₂ hker₂ (fun m hm d hd => hDn m (hNinfN (hM₂ hm)) d hd)
      (fun k hk hkM => hKD k hk (hM₂ hkM)) D.mem₂ ha'K hcomm₂
  have hle : c.Ninf ≤ C ⊔ (O₁ ⊓ c.Ninf) := F.ninf_eq.le.trans (sup_le hM₁D hM₂D)
  have hCNinf : C ≤ c.Ninf := fun y hy => ((hCmem y).mp hy).1
  have hNinfC : c.Ninf ≤ C :=
    le_of_perfect_of_odd c.Ninf_perfect hCNinf inf_le_right
      (fun h hh y hy => hCn h (hNinfN hh) y hy) hO.odd_card_inf (fun x hx => hDmem x (hle hx))
  intro Q' hQ'N hQ'n hQ'odd q hq n hn
  have hQ'Q : Q' ≤ O₁ ⊓ c.Ninf := hO.le_inf_of_odd_normal hW hQ'N hQ'n hQ'odd
  exact ((hCmem n).mp (hNinfC hn)).2 q (hQ'Q hq)

end Heart

section Final

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G}

theorem CaseB.oddCoreCentral
    (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {R : Subgroup G}
    (hRW : R = V₁ ∨ R = V₂) (c : CaseB A R d.t) : c.OddCoreCentral := by
  obtain ⟨R', hR'⟩ : ∃ R' : Subgroup G, Radicals d.V R R' := by
    rcases hRW with rfl | rfl
    · exact ⟨V₂, hR⟩
    · exact ⟨V₁, hR.symm_B42⟩
  obtain ⟨M₁, M₂, S₀, A₁, B₁, k, hkF, e, F, S⟩ := c.exists_sylowB h d hR'
  have : CharP k 2 := charP_two_of_card_four_B42 S.card_k
  obtain ⟨a, haA, hea⟩ : ∃ a : G, ∃ ha : a ∈ A₁, e ⟨a, ha⟩ = uelt 0 1 0 :=
    ⟨(e.symm (uelt 0 1 0) : G), (e.symm (uelt 0 1 0)).2, e.apply_symm_apply _⟩
  have haW : a ∉ c.W := fun hW => by
    have h1 := (S.W_coord ⟨a, haA⟩).mp hW
    rw [hea, mem_radOne] at h1
    simp at h1
  have ha2 : a * a = 1 := by
    have h1 : e (⟨a, haA⟩ * ⟨a, haA⟩) = 1 := by
      rw [map_mul, hea, uelt_mul_self]
      simp
    have h2 : (⟨a, haA⟩ * ⟨a, haA⟩ : ↥A₁) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have haM₁ : a ∈ M₁ := by
    have : a ∈ S₀ ⊓ M₁ := by rw [← S.A₁_eq]; exact haA
    exact this.2
  have hB : d.t * a * d.t⁻¹ ∈ B₁ := S.swap₁ a haA
  have ha'M₂ : d.t * a * d.t⁻¹ ∈ M₂ := by
    have : d.t * a * d.t⁻¹ ∈ S₀ ⊓ M₂ := by rw [← S.B₁_eq]; exact hB
    exact this.2
  have hzA : a * (d.t * a * d.t⁻¹) ∈ A :=
    (Subgroup.mem_inf.mp ((S.V_diag _).mpr ⟨a, haA, rfl⟩)).2
  have haK : a ∉ centralizer (c.W : Set G) := fun hK => haW (F.two_elem a hK (by
    have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact ⟨0, by rw [h1]; norm_num⟩
    · exact ⟨1, by rw [h1]; norm_num⟩))
  exact F.centralOddCore_of_diagonal
    { mem₁ := haM₁, mem₂ := ha'M₂, sq := ha2, comm := S.comm a haA _ hB, swap := rfl,
      mem_A := hzA, not_mem_K := haK }

theorem SylowB.exists_torus_centralizes {R : Subgroup G} {d : Datum A} {c : CaseB A R d.t}
    {R' M₁ M₂ S₀ A₁ B₁ : Subgroup G} {k : Type} [Field k] {e : ↥A₁ ≃* ↥(unipAll k)}
    (S : SylowB c R' M₁ M₂ S₀ A₁ B₁ e) (hZ : c.OddCoreCentral) :
    ∃ x : G, x ∈ M₁ ∧ Odd (orderOf x) ∧ x ∉ centralizer (c.W : Set G) ∧
      x ^ 3 ∈ centralizer (c.W : Set G) ∧ (∀ a ∈ A₁, x * a * x⁻¹ ∈ A₁) ∧
      (∀ m ∈ M₂, x * m = m * x) ∧
      ∃ μ : k, μ ≠ 0 ∧ μ ≠ 1 ∧ ∀ a a' : ↥A₁, (a' : G) = x * a * x⁻¹ →
        coordA (e a') = μ * coordA (e a) ∧ coordB (e a') = μ * coordB (e a) := by
  obtain ⟨x, h1, h2, h3, h4, h5, h6, μ, h7, h8, h9⟩ := S.torus
  exact ⟨x, h1, h2, h3, h4, h5, h6 hZ, μ, h7, h8, h9⟩

end Final

end CFSG.OddStandard.Seitz77
