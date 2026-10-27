module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRed
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenSympl

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def nabZ (P : Subgroup G) : Subgroup G :=
  P ⊓ Subgroup.centralizer (P : Set G)

theorem mem_nabZ {P : Subgroup G} {z : G} : z ∈ nabZ P ↔ z ∈ P ∧ ∀ a ∈ P, a * z = z * a := by
  simp only [nabZ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

structure NabHyp (Y P : Subgroup G) (p : ℕ) : Prop where
  prime : p.Prime
  perfect : ⁅Y, Y⁆ = Y
  pgroup : IsPGroup p P
  normalizes : Y ≤ Subgroup.normalizer (P : Set G)
  noncentral : ¬ P ≤ Subgroup.centralizer (Y : Set G)
  minimal : ∀ Q : Subgroup G, Q < P → Y ≤ Subgroup.normalizer (Q : Set G) →
    Q ≤ Subgroup.centralizer (Y : Set G)
  nonabelian : ¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a

end Defs

section Basic

variable {G : Type} [Group G] {Y P : Subgroup G} {p : ℕ}

theorem NabHyp.conj_mem (h : NabHyp Y P p) {y : G} (hy : y ∈ Y) {a : G} (ha : a ∈ P) :
    y * a * y⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp (h.normalizes hy) a).mp ha

theorem NabHyp.conj_mem' (h : NabHyp Y P p) {y : G} (hy : y ∈ Y) {a : G} (ha : a ∈ P) :
    y⁻¹ * a * y ∈ P := by
  simpa using h.conj_mem (inv_mem hy) ha

theorem le_normalizer_of_forall {A S : Subgroup G} (h : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S) :
    A ≤ Subgroup.normalizer (S : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => h a ha s hs, fun hs => ?_⟩
  have := h a⁻¹ (inv_mem ha) _ hs
  simpa [mul_assoc] using this

theorem conj_mem_commutator {A B : Subgroup G} {g : G}
    (h1 : ∀ a ∈ A, ∀ b ∈ B, g * ⁅a, b⁆ * g⁻¹ ∈ ⁅A, B⁆) :
    ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  intro x hx
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact h1 a ha b hb
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem P_le_normalizer_commutator {P : Subgroup G} (B : Subgroup G) :
    P ≤ Subgroup.normalizer ((⁅P, B⁆ : Subgroup G) : Set G) :=
  le_normalizer_of_forall fun g hg => conj_mem_commutator fun a ha b hb => by
    have : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅g, b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hg ha) hb)
      (inv_mem (Subgroup.commutator_mem_commutator hg hb))

theorem NabHyp.Y_le_normalizer_commutator (h : NabHyp Y P p) {B : Subgroup G}
    (hB : ∀ y ∈ Y, ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    Y ≤ Subgroup.normalizer ((⁅P, B⁆ : Subgroup G) : Set G) :=
  le_normalizer_of_forall fun y hy => conj_mem_commutator fun a ha b hb => by
    have : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.commutator_mem_commutator (h.conj_mem hy ha) (hB y hy b hb)

theorem NabHyp.commutator_le (h : NabHyp Y P p) : ⁅P, Y⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro a ha y hy
  have : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact mul_mem ha (h.conj_mem hy (inv_mem ha))

theorem NabHyp.comm_eq (h : NabHyp Y P p) : ⁅P, Y⁆ = P := by
  by_contra hne
  have hlt : ⁅P, Y⁆ < P := lt_of_le_of_ne h.commutator_le hne
  have hY : Y ≤ Subgroup.normalizer ((⁅P, Y⁆ : Subgroup G) : Set G) :=
    h.Y_le_normalizer_commutator fun y hy b hb => mul_mem (mul_mem hy hb) (inv_mem hy)
  refine h.noncentral (le_centralizer_of_stable h.perfect (P_le_normalizer_commutator Y)
    (h.minimal _ hlt hY) fun x hx y hy => ?_)
  have : x⁻¹ * (y * x * y⁻¹) = ⁅x⁻¹, y⁆ := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact Subgroup.commutator_mem_commutator (inv_mem hx) hy

theorem NabHyp.nabZ_lt (h : NabHyp Y P p) : nabZ P < P := by
  refine lt_of_le_of_ne (fun z hz => (mem_nabZ.mp hz).1) fun heq =>
    h.nonabelian fun a ha b hb => ?_
  have : a ∈ nabZ P := by
    rw [heq]
    exact ha
  exact ((mem_nabZ.mp this).2 b hb).symm

theorem NabHyp.Y_le_normalizer_nabZ (h : NabHyp Y P p) :
    Y ≤ Subgroup.normalizer (nabZ P : Set G) :=
  le_normalizer_of_forall fun y hy z hz => by
    obtain ⟨hzP, hzc⟩ := mem_nabZ.mp hz
    refine mem_nabZ.mpr ⟨h.conj_mem hy hzP, fun a ha => ?_⟩
    have h1 := hzc (y⁻¹ * a * y) (h.conj_mem' hy ha)
    calc a * (y * z * y⁻¹) = y * ((y⁻¹ * a * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * a * y)) * y⁻¹ := by rw [h1]
      _ = (y * z * y⁻¹) * a := by group

theorem NabHyp.nabZ_le_centralizer (h : NabHyp Y P p) :
    nabZ P ≤ Subgroup.centralizer (Y : Set G) :=
  h.minimal _ h.nabZ_lt h.Y_le_normalizer_nabZ

theorem mem_center_iff_mem_nabZ {z : ↥P} : z ∈ Subgroup.center ↥P ↔ (z : G) ∈ nabZ P := by
  rw [Subgroup.mem_center_iff, mem_nabZ]
  constructor
  · intro hz
    exact ⟨z.2, fun a ha => congrArg Subtype.val (hz ⟨a, ha⟩)⟩
  · rintro ⟨-, hz⟩ g
    exact Subtype.ext (hz g g.2)

theorem NabHyp.normConj_center (h : NabHyp Y P p) {y : G} (hy : y ∈ Y) {z : ↥P}
    (hz : z ∈ Subgroup.center ↥P) : normConj P y (h.normalizes hy) z = z := by
  have h1 : y * (z : G) = (z : G) * y :=
    Subgroup.mem_centralizer_iff.mp
      (h.nabZ_le_centralizer (mem_center_iff_mem_nabZ.mp hz)) y hy
  apply Subtype.ext
  rw [coe_normConj, mul_inv_eq_iff_eq_mul]
  exact h1

end Basic

section Radical

variable {Γ : Type*} [Group Γ] {M : Type*} [Group M]

@[expose] def radical (hc : ∀ g k : Γ, ⁅g, k⁆ ∈ Subgroup.center Γ)
    (lam : ↥(Subgroup.center Γ) →* M) : Subgroup Γ where
  carrier := {g | ∀ (k : Γ) (hk : ⁅g, k⁆ ∈ Subgroup.center Γ), lam ⟨⁅g, k⁆, hk⟩ = 1}
  one_mem' := fun k hk => by
    have : (⟨⁅(1 : Γ), k⁆, hk⟩ : ↥(Subgroup.center Γ)) = 1 :=
      Subtype.ext (commutatorElement_one_left k)
    rw [this, map_one]
  mul_mem' := fun {a b} ha hb k hk => by
    have e : (⟨⁅a * b, k⁆, hk⟩ : ↥(Subgroup.center Γ)) =
        ⟨⁅a, k⁆, hc a k⟩ * ⟨⁅b, k⁆, hc b k⟩ :=
      Subtype.ext (comm_mul_left_of_central hc a b k)
    rw [e, map_mul, ha k (hc a k), hb k (hc b k), one_mul]
  inv_mem' := fun {a} ha k hk => by
    have e : (⟨⁅a⁻¹, k⁆, hk⟩ : ↥(Subgroup.center Γ)) = (⟨⁅a, k⁆, hc a k⟩)⁻¹ := by
      apply Subtype.ext
      have := comm_mul_left_of_central hc a⁻¹ a k
      rw [inv_mul_cancel, commutatorElement_one_left] at this
      exact eq_inv_of_mul_eq_one_left this.symm
    rw [e, map_inv, ha k (hc a k), inv_one]

end Radical

section Structure

variable {G : Type} [Group G] [Finite G] {Y P : Subgroup G} {p : ℕ}

theorem NabHyp.derived_lt (h : NabHyp Y P p) : ⁅P, P⁆ < P := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Group.IsNilpotent ↥P := h.pgroup.isNilpotent
  have hnt : Nontrivial ↥P := by
    by_contra hno
    rw [not_nontrivial_iff_subsingleton] at hno
    refine h.nonabelian fun a ha b hb => ?_
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨a, ha⟩ * ⟨b, hb⟩ : ↥P) (⟨b, hb⟩ * ⟨a, ha⟩))
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥P
  rw [← Subgroup.map_subtype_commutator]
  calc Subgroup.map P.subtype (commutator ↥P) < Subgroup.map P.subtype ⊤ :=
        Subgroup.map_subtype_lt_map_subtype.mpr h1
    _ = P := by rw [Subgroup.map_top, Subgroup.range_subtype]

theorem NabHyp.derived_le_centralizer (h : NabHyp Y P p) :
    ⁅P, P⁆ ≤ Subgroup.centralizer (Y : Set G) :=
  h.minimal _ h.derived_lt (h.Y_le_normalizer_commutator fun _ hy _ hb => h.conj_mem hy hb)

theorem NabHyp.derived_le_Z (h : NabHyp Y P p) : ⁅P, P⁆ ≤ nabZ P := by
  have hD := h.derived_le_centralizer
  have hYD : ⁅Y, ⁅P, P⁆⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Y ⁅P, P⁆]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hD
  have h1 : ⁅⁅Y, ⁅P, P⁆⁆, P⁆ = ⊥ := by rw [hYD, Subgroup.commutator_bot_left]
  have hnorm : ∀ a ∈ P, ∀ d ∈ ⁅P, P⁆, a * d * a⁻¹ ∈ ⁅P, P⁆ := fun a ha d hd =>
    (Subgroup.mem_normalizer_iff.mp (P_le_normalizer_commutator P ha) d).mp hd
  have hDP : ⁅⁅P, P⁆, P⁆ ≤ ⁅P, P⁆ := by
    rw [Subgroup.commutator_le]
    intro d hd a ha
    have : ⁅d, a⁆ = d * (a * d⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem hd (hnorm a ha d⁻¹ (inv_mem hd))
  have h2 : ⁅⁅⁅P, P⁆, P⁆, Y⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono_left hDP).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hD).le)
  have h3 : ⁅⁅P, Y⁆, ⁅P, P⁆⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [h.comm_eq, Subgroup.commutator_comm P ⁅P, P⁆] at h3
  exact le_inf (Subgroup.commutator_le_self P)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

theorem NabHyp.mem_nabZ_of_centralizes (h : NabHyp Y P p) {z : G} (hz : z ∈ P)
    (hY : z ∈ Subgroup.centralizer (Y : Set G)) : z ∈ nabZ P := by
  refine mem_nabZ.mpr ⟨hz, ?_⟩
  have hle : ⁅P, Y⁆ ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z' hz'
    rw [Set.mem_singleton_iff.mp hz']
    have hw : a⁻¹ * z * a ∈ Subgroup.centralizer (Y : Set G) := by
      have : a⁻¹ * z * a = ⁅a⁻¹, z⁆ * z := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact mul_mem (h.derived_le_centralizer
        (Subgroup.commutator_mem_commutator (inv_mem ha) hz)) hY
    have hw2 : y * (a⁻¹ * z * a) = (a⁻¹ * z * a) * y :=
      Subgroup.mem_centralizer_iff.mp hw y hy
    have hyz : y * z = z * y := Subgroup.mem_centralizer_iff.mp hY y hy
    have hzy : z * y⁻¹ = y⁻¹ * z := by
      calc z * y⁻¹ = y⁻¹ * (y * z) * y⁻¹ := by group
        _ = y⁻¹ * (z * y) * y⁻¹ := by rw [hyz]
        _ = y⁻¹ * z := by group
    calc z * ⁅a, y⁆ = a * ((a⁻¹ * z * a) * y) * a⁻¹ * y⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = a * (y * (a⁻¹ * z * a)) * a⁻¹ * y⁻¹ := by rw [hw2]
      _ = a * y * a⁻¹ * (z * y⁻¹) := by group
      _ = a * y * a⁻¹ * (y⁻¹ * z) := by rw [hzy]
      _ = ⁅a, y⁆ * z := by
          simp only [commutatorElement_def]
          group
  rw [h.comm_eq] at hle
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) z (Set.mem_singleton z)).symm

theorem NabHyp.le_nabZ_of_lt (h : NabHyp Y P p) {Q : Subgroup G} (hQ : Q < P)
    (hY : Y ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ nabZ P :=
  fun _ hq => h.mem_nabZ_of_centralizes (hQ.le hq) (h.minimal Q hQ hY hq)

theorem NabHyp.commutator_mem_center (h : NabHyp Y P p) (g k : ↥P) :
    ⁅g, k⁆ ∈ Subgroup.center ↥P :=
  mem_center_iff_mem_nabZ.mpr (h.derived_le_Z (Subgroup.commutator_mem_commutator g.2 k.2))

theorem NabHyp.le_center_of_invariant (h : NabHyp Y P p) (Q : Subgroup ↥P)
    (hQ : ∀ (y : G) (hy : y ∈ Y) (q : ↥P), q ∈ Q → normConj P y (h.normalizes hy) q ∈ Q)
    (hne : Q ≠ ⊤) : Q ≤ Subgroup.center ↥P := by
  have hlt : Q.map P.subtype < P := by
    refine lt_of_le_of_ne (Subgroup.map_subtype_le Q) fun heq => hne ?_
    rw [eq_top_iff]
    intro g _
    have hg : (g : G) ∈ Q.map P.subtype := by
      rw [heq]
      exact g.2
    obtain ⟨q, hq, hqg⟩ := hg
    have : q = g := Subtype.ext hqg
    rwa [← this]
  have hY : Y ≤ Subgroup.normalizer ((Q.map P.subtype : Subgroup G) : Set G) :=
    le_normalizer_of_forall fun y hy s hs => by
      obtain ⟨q, hq, rfl⟩ := hs
      exact ⟨normConj P y (h.normalizes hy) q, hQ y hy q hq, coe_normConj P y (h.normalizes hy) q⟩
  intro q hq
  exact mem_center_iff_mem_nabZ.mpr (h.le_nabZ_of_lt hlt hY ⟨q, hq, rfl⟩)

theorem pow_mem_center_mul {Γ : Type*} [Group Γ] (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    {p : ℕ} {g k : Γ} (hg : g ^ p ∈ Subgroup.center Γ) (hk : k ^ p ∈ Subgroup.center Γ) :
    (g * k) ^ p ∈ Subgroup.center Γ := by
  rw [← QuotientGroup.eq_one_iff] at hg hk ⊢
  rw [QuotientGroup.mk_pow] at hg hk ⊢
  rw [QuotientGroup.mk_mul]
  have hcomm : Commute (QuotientGroup.mk g : Γ ⧸ Subgroup.center Γ) (QuotientGroup.mk k) :=
    centerQuot_comm hc _ _
  rw [hcomm.mul_pow, hg, hk, one_mul]

theorem NabHyp.pow_mem_center (h : NabHyp Y P p) (g : ↥P) : g ^ p ∈ Subgroup.center ↥P := by
  have hc := h.commutator_mem_center
  have : Fact p.Prime := ⟨h.prime⟩
  let Ω : Subgroup ↥P :=
    { carrier := {a | a ^ p ∈ Subgroup.center ↥P}
      one_mem' := by
        show (1 : ↥P) ^ p ∈ Subgroup.center ↥P
        rw [one_pow]
        exact one_mem _
      mul_mem' := fun {a b} ha hb => pow_mem_center_mul hc ha hb
      inv_mem' := fun {a} ha => by
        show a⁻¹ ^ p ∈ Subgroup.center ↥P
        rw [inv_pow]
        exact inv_mem ha }
  have hmem : ∀ a : ↥P, a ∈ Ω ↔ a ^ p ∈ Subgroup.center ↥P := fun a => Iff.rfl
  by_cases hΩ : Ω = ⊤
  · exact (hmem g).mp (by rw [hΩ]; exact Subgroup.mem_top g)
  · exfalso
    have hle : Ω ≤ Subgroup.center ↥P := by
      refine h.le_center_of_invariant Ω (fun y hy q hq => ?_) hΩ
      rw [hmem, ← map_pow (normConj P y (h.normalizes hy)) q p,
        h.normConj_center hy ((hmem q).mp hq)]
      exact (hmem q).mp hq
    have hA : IsPGroup p (↥P ⧸ Subgroup.center ↥P) := h.pgroup.to_quotient _
    obtain ⟨a₀, b₀, ha₀, hb₀, hab⟩ : ∃ a b : G, a ∈ P ∧ b ∈ P ∧ a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact h.nonabelian fun a ha b hb => hcon a b ha hb
    have hnt : ∃ x : ↥P ⧸ Subgroup.center ↥P, x ≠ 1 := by
      refine ⟨QuotientGroup.mk ⟨a₀, ha₀⟩, fun h1 => hab ?_⟩
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp h2 ⟨b₀, hb₀⟩).symm)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
    have hn0 : n ≠ 0 := by
      rintro rfl
      obtain ⟨x, hx⟩ := hnt
      have h1 : Nat.card (↥P ⧸ Subgroup.center ↥P) = 1 := by simpa using hn
      have : Subsingleton (↥P ⧸ Subgroup.center ↥P) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hx (Subsingleton.elim x 1)
    have hdvd : p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) := by
      rw [hn]
      exact dvd_pow_self p hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hg₀ : g₀ ^ p ∈ Subgroup.center ↥P := by
      have h1 := pow_orderOf_eq_one (QuotientGroup.mk g₀ : ↥P ⧸ Subgroup.center ↥P)
      rw [hx, ← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hg₁ : g₀ ∈ Subgroup.center ↥P := hle ((hmem g₀).mpr hg₀)
    have h1 : (QuotientGroup.mk g₀ : ↥P ⧸ Subgroup.center ↥P) = 1 :=
      (QuotientGroup.eq_one_iff g₀).mpr hg₁
    rw [h1, orderOf_one] at hx
    exact h.prime.one_lt.ne hx

theorem NabHyp.radical_le_center (h : NabHyp Y P p) {M : Type*} [Group M]
    (lam : ↥(Subgroup.center ↥P) →* M)
    (hnt : ∃ (g k : ↥P) (hc : ⁅g, k⁆ ∈ Subgroup.center ↥P), lam ⟨⁅g, k⁆, hc⟩ ≠ 1) :
    radical h.commutator_mem_center lam ≤ Subgroup.center ↥P := by
  refine h.le_center_of_invariant _ (fun y hy q hq k hk => ?_) ?_
  · have e : ⁅normConj P y (h.normalizes hy) q, k⁆ =
        ⁅q, (normConj P y (h.normalizes hy)).symm k⁆ := by
      have h1 : normConj P y (h.normalizes hy) ⁅q, (normConj P y (h.normalizes hy)).symm k⁆ =
          ⁅q, (normConj P y (h.normalizes hy)).symm k⁆ :=
        h.normConj_center hy (h.commutator_mem_center _ _)
      rw [map_commutatorElement, MulEquiv.apply_symm_apply] at h1
      exact h1
    have e2 : (⟨⁅normConj P y (h.normalizes hy) q, k⁆, hk⟩ : ↥(Subgroup.center ↥P)) =
        ⟨⁅q, (normConj P y (h.normalizes hy)).symm k⁆, h.commutator_mem_center _ _⟩ :=
      Subtype.ext e
    rw [e2]
    exact hq _ _
  · intro htop
    obtain ⟨g, k, hc, hne⟩ := hnt
    have hg : g ∈ radical h.commutator_mem_center lam := by
      rw [htop]
      exact Subgroup.mem_top g
    exact hne (hg k hc)

omit [Finite G] in
theorem NabHyp.exists_gen_act (h : NabHyp Y P p) {S : Set G} (hgen : Subgroup.closure S = Y) :
    ∃ x ∈ S, ∃ g ∈ P, g⁻¹ * (x * g * x⁻¹) ∉ nabZ P := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ y ∈ Subgroup.closure S, ∀ g ∈ P, g⁻¹ * (y * g * y⁻¹) ∈ nabZ P := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hcon x hx
    | one =>
      intro g _
      simp
    | mul x y hx hy ihx ihy =>
      intro g hg
      have hx' : x ∈ Y := hgen ▸ hx
      have hy' : y ∈ Y := hgen ▸ hy
      have h1 := ihy g hg
      have h2 := ihx (y * g * y⁻¹) (h.conj_mem hy' hg)
      have : g⁻¹ * (x * y * g * (x * y)⁻¹) =
          (g⁻¹ * (y * g * y⁻¹)) * ((y * g * y⁻¹)⁻¹ * (x * (y * g * y⁻¹) * x⁻¹)) := by group
      rw [this]
      exact mul_mem h1 h2
    | inv x hx ihx =>
      intro g hg
      have hx' : x ∈ Y := hgen ▸ hx
      have h1 := ihx (x⁻¹ * g * x⁻¹⁻¹) (h.conj_mem (inv_mem hx') hg)
      have : g⁻¹ * (x⁻¹ * g * x⁻¹⁻¹) = ((x⁻¹ * g * x⁻¹⁻¹)⁻¹ * (x * (x⁻¹ * g * x⁻¹⁻¹) * x⁻¹))⁻¹ := by
        group
      rw [this]
      exact inv_mem h1
  have hPN : P ≤ Subgroup.normalizer (nabZ P : Set G) :=
    le_normalizer_of_forall fun g hg z hz => by
      have : g * z * g⁻¹ = z := by
        rw [(mem_nabZ.mp hz).2 g hg, mul_inv_cancel_right]
      rw [this]
      exact hz
  exact h.noncentral (le_centralizer_of_stable h.perfect hPN h.nabZ_le_centralizer
    fun g hg y hy => hall y (hgen ▸ hy) g hg)

end Structure

end CFSG.CGT.PushingUpLit.CGT6
