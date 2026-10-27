module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44A5
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Basic
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44FT

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section Gen

variable {G : Type} [Group G]

theorem commutator_mul_of_comm {u v a b : G} (hau : Commute a u) (hav : Commute a v)
    (hbu : Commute b u) (hbv : Commute b v) : ⁅u * a, v * b⁆ = ⁅u, v⁆ * ⁅a, b⁆ := by
  have h1 : Commute (a * b * a⁻¹) u⁻¹ :=
    Commute.mul_left (Commute.mul_left (Commute.inv_right hau) (Commute.inv_right hbu))
      (Commute.inv_inv hau)
  have h2 : Commute (a * b * a⁻¹ * b⁻¹) v⁻¹ :=
    Commute.mul_left (Commute.mul_left (Commute.mul_left (Commute.inv_right hav)
      (Commute.inv_right hbv)) (Commute.inv_inv hav)) (Commute.inv_inv hbv)
  have e1 : ⁅u * a, v * b⁆ = u * (a * v) * (b * a⁻¹) * u⁻¹ * (b⁻¹ * v⁻¹) := by
    simp only [commutatorElement_def, mul_inv_rev]; group
  rw [e1, hav.eq]
  calc u * (v * a) * (b * a⁻¹) * u⁻¹ * (b⁻¹ * v⁻¹)
      = u * v * ((a * b * a⁻¹) * u⁻¹) * (b⁻¹ * v⁻¹) := by group
    _ = u * v * (u⁻¹ * (a * b * a⁻¹)) * (b⁻¹ * v⁻¹) := by rw [h1.eq]
    _ = u * v * u⁻¹ * ((a * b * a⁻¹ * b⁻¹) * v⁻¹) := by group
    _ = u * v * u⁻¹ * (v⁻¹ * (a * b * a⁻¹ * b⁻¹)) := by rw [h2.eq]
    _ = ⁅u, v⁆ * ⁅a, b⁆ := by simp only [commutatorElement_def]; group

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] def projSub (M₁ M₂ Q : Subgroup G) (hc : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x) :
    Subgroup G where
  carrier := {m | m ∈ M₁ ∧ ∃ m' ∈ M₂, m * m' ∈ Q}
  mul_mem' := by
    rintro a b ⟨ha, a', ha', haQ⟩ ⟨hb, b', hb', hbQ⟩
    refine ⟨M₁.mul_mem ha hb, a' * b', M₂.mul_mem ha' hb', ?_⟩
    have : a * b * (a' * b') = (a * a') * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [hc b hb a' ha']
        _ = (a * a') * (b * b') := by group
    rw [this]
    exact Q.mul_mem haQ hbQ
  one_mem' := ⟨M₁.one_mem, 1, M₂.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, a', ha', haQ⟩
    refine ⟨M₁.inv_mem ha, a'⁻¹, M₂.inv_mem ha', ?_⟩
    have : a⁻¹ * a'⁻¹ = (a * a')⁻¹ := by
      calc a⁻¹ * a'⁻¹ = (a' * a)⁻¹ := by group
        _ = (a * a')⁻¹ := by rw [← hc a ha a' ha']
    rw [this]
    exact Q.inv_mem haQ

theorem mem_projSub {M₁ M₂ Q : Subgroup G} {hc : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x} {m : G} :
    m ∈ projSub M₁ M₂ Q hc ↔ m ∈ M₁ ∧ ∃ m' ∈ M₂, m * m' ∈ Q := Iff.rfl

theorem mem_of_pow_odd_mem {H : Subgroup G} {a : G} (ha : ∃ n, orderOf a = 2 ^ n) {m : ℕ}
    (hm : Odd m) (h : a ^ m ∈ H) : a ∈ H := by
  obtain ⟨n, hn⟩ := ha
  have hcop : m.Coprime (orderOf a) := by
    rw [hn]
    exact hm.coprime_two_right.pow_right n
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact H.pow_mem h j

end Gen

section Qmax

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M₁ M₂ : Subgroup G}

theorem CaseB.Factors.qmax_le (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral) {S Q : Subgroup G}
    (hS : IsSylowOf 2 S c.Ninf) (hWS : c.W ≤ S) (hQN : Q ≤ c.Ninf) (hQ : ⁅Q, Q⁆ = Q)
    (hSQ : S ≤ Q) : M₁ ≤ Q := by
  have hc : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x := fun x hx y hy => F.comm_elem hZ hx hy
  have hc' : ∀ x ∈ M₂, ∀ y ∈ M₁, x * y = y * x := fun x hx y hy => (hc y hy x hx).symm
  have hO : Odd2 M₁ M₂ :=
    ⟨fun x hx m hm => F.norm₁ x (F.ninf_eq ▸ hx) m hm,
      fun x hx m hm => F.norm₂ x (F.ninf_eq ▸ hx) m hm, F.odd_inf⟩
  have hSn : IsSylowOf 2 S (M₁ ⊔ M₂) := F.ninf_eq ▸ hS
  have hT₁ : IsSylowOf 2 (S ⊓ M₁) M₁ := (hO.sylow_inf hSn).1
  have hM₁N : M₁ ≤ c.Ninf := F.M₁_le
  have hZc : ∀ z ∈ M₁ ⊓ M₂, ∀ n ∈ c.Ninf, z * n = n * z := fun z hz n hn => F.inf_central hZ hz hn
  set Q₁ : Subgroup G := projSub M₁ M₂ Q hc with hQ₁
  set Q₂ : Subgroup G := projSub M₂ M₁ Q hc' with hQ₂
  have hQ₁M : Q₁ ≤ M₁ := fun m hm => hm.1
  have hQ₂M : Q₂ ≤ M₂ := fun m hm => hm.1
  have hQQ : Q ≤ Q₁ ⊔ Q₂ := by
    intro q hq
    have hqN : q ∈ M₁ ⊔ M₂ := F.ninf_eq ▸ hQN hq
    obtain ⟨m, hm, m', hm', rfl⟩ := mem_sup_of_forall_comm (O := M₁) (E := M₂) hc hqN
    exact mul_mem (mem_sup_left (mem_projSub.mpr ⟨hm, m', hm', hq⟩))
      (mem_sup_right (mem_projSub.mpr ⟨hm', m, hm, by rw [hc' m' hm' m hm]; exact hq⟩))
  have hQ₁₂ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy => hc x hx.1 y hy.1
  have hD : Q ≤ ⁅Q₁, Q₁⁆ ⊔ ⁅Q₂, Q₂⁆ := by
    calc Q = ⁅Q, Q⁆ := hQ.symm
      _ ≤ ⁅Q₁, Q₁⁆ ⊔ ⁅Q₂, Q₂⁆ := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup_of_forall_comm (O := Q₁) (E := Q₂) hQ₁₂ (hQQ hx)
        obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup_of_forall_comm (O := Q₁) (E := Q₂) hQ₁₂ (hQQ hy)
        rw [commutator_mul_of_comm (hQ₁₂ x₁ hx₁ x₂ hx₂).symm (hQ₁₂ y₁ hy₁ x₂ hx₂).symm
          (hQ₁₂ x₁ hx₁ y₂ hy₂).symm (hQ₁₂ y₁ hy₁ y₂ hy₂).symm]
        exact mul_mem (mem_sup_left (commutator_mem_commutator hx₁ hy₁))
          (mem_sup_right (commutator_mem_commutator hx₂ hy₂))
  have hD₁M : ⁅Q₁, Q₁⁆ ≤ M₁ := (commutator_self_le Q₁).trans hQ₁M
  have hD₂M : ⁅Q₂, Q₂⁆ ≤ M₂ := (commutator_self_le Q₂).trans hQ₂M
  have hsplit : ∀ m ∈ Q₁, ∃ d ∈ ⁅Q₁, Q₁⁆, ∃ z ∈ M₁ ⊓ M₂, m = d * z := by
    intro m hm
    obtain ⟨hmM, m', hm', hmQ⟩ := hm
    have h1 : m * m' ∈ ⁅Q₁, Q₁⁆ ⊔ ⁅Q₂, Q₂⁆ := hD hmQ
    obtain ⟨d₁, hd₁, d₂, hd₂, hdd⟩ := mem_sup_of_forall_comm (O := ⁅Q₁, Q₁⁆) (E := ⁅Q₂, Q₂⁆)
      (fun x hx y hy => hc x (hD₁M hx) y (hD₂M hy)) h1
    have h2 : d₁⁻¹ * m = d₂ * m'⁻¹ := by
      calc d₁⁻¹ * m = d₁⁻¹ * (m * m') * m'⁻¹ := by group
        _ = d₁⁻¹ * (d₁ * d₂) * m'⁻¹ := by rw [← hdd]
        _ = d₂ * m'⁻¹ := by group
    refine ⟨d₁, hd₁, d₁⁻¹ * m, ⟨M₁.mul_mem (M₁.inv_mem (hD₁M hd₁)) hmM, ?_⟩, by group⟩
    rw [h2]
    exact M₂.mul_mem (hD₂M hd₂) (M₂.inv_mem hm')
  have hD₁perf : ⁅⁅Q₁, Q₁⁆, ⁅Q₁, Q₁⁆⁆ = ⁅Q₁, Q₁⁆ := by
    refine le_antisymm (commutator_self_le _) ?_
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    obtain ⟨d, hd, z, hz, rfl⟩ := hsplit m hm
    obtain ⟨d', hd', z', hz', rfl⟩ := hsplit m' hm'
    have hdN : d ∈ c.Ninf := hM₁N (hD₁M hd)
    have hd'N : d' ∈ c.Ninf := hM₁N (hD₁M hd')
    have hzN : z ∈ c.Ninf := hM₁N hz.1
    have hz'N : z' ∈ c.Ninf := hM₁N hz'.1
    rw [commutator_mul_of_comm (hZc z hz d hdN) (hZc z hz d' hd'N)
      (hZc z' hz' d hdN) (hZc z' hz' d' hd'N)]
    have : ⁅z, z'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZc z hz z' hz'N)
    rw [this, mul_one]
    exact commutator_mem_commutator hd hd'
  have hT₁Q : S ⊓ M₁ ≤ Q₁ := fun a ha =>
    mem_projSub.mpr ⟨ha.2, 1, M₂.one_mem, by simpa using hSQ ha.1⟩
  have hT₁D : S ⊓ M₁ ≤ ⁅Q₁, Q₁⁆ := by
    intro a ha
    obtain ⟨d, hd, z, hz, hadz⟩ := hsplit a (hT₁Q ha)
    have ha2 : ∃ n, orderOf a = 2 ^ n := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hS.isPGroup ⟨a, ha.1⟩
      exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
    have hzc : Commute d z := (hZc z hz d (hM₁N (hD₁M hd))).symm
    have hzm : z ^ Nat.card ↥(M₁ ⊓ M₂) = 1 := by
      have := pow_card_eq_one' (G := ↥(M₁ ⊓ M₂)) (x := ⟨z, hz⟩)
      exact congrArg Subtype.val this
    refine mem_of_pow_odd_mem ha2 F.odd_inf ?_
    rw [hadz, hzc.mul_pow, hzm, mul_one]
    exact pow_mem hd _
  obtain ⟨π, hπs, hπk⟩ := F.a5₁
  set D : Subgroup G := ⁅Q₁, Q₁⁆ with hDdef
  set D' : Subgroup ↥M₁ := D.subgroupOf M₁ with hD'
  have hD'perf : ⁅D', D'⁆ = D' := by
    apply Subgroup.map_injective M₁.subtype_injective
    rw [Subgroup.map_commutator, hD', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hD₁M,
      hD₁perf]
  have hπperf : ⁅D'.map π, D'.map π⁆ = D'.map π := by
    rw [← Subgroup.map_commutator, hD'perf]
  have hπne : D'.map π ≠ ⊥ := by
    intro hbot
    have hker : ∀ a ∈ S ⊓ M₁, a ∈ centralizer (c.W : Set G) := by
      intro a ha
      have hmem : (⟨a, ha.2⟩ : ↥M₁) ∈ D' := mem_subgroupOf.mpr (hT₁D ha)
      have : π ⟨a, ha.2⟩ ∈ D'.map π := ⟨_, hmem, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (hπk _).mp this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTK : S ⊓ M₁ ≤ M₁ ⊓ centralizer (c.W : Set G) := fun a ha => ⟨ha.2, hker a ha⟩
    have h1 := (hT₁.of_le hTK inf_le_left).card_eq
    have h2 := F.sylow_W₁.card_eq
    rw [F.card₁] at h2
    have h3 := F.sylow_card₁ _ hT₁
    have h4 : (16 : ℕ) = 64 := h2.trans (h1.symm.trans h3)
    omega
  have hπtop : D'.map π = ⊤ := a5_perfect_eq_top _ hπperf hπne
  have hDK : ∀ m ∈ M₁, ∃ d ∈ D, d⁻¹ * m ∈ centralizer (c.W : Set G) := by
    intro m hm
    have : π ⟨m, hm⟩ ∈ D'.map π := by rw [hπtop]; trivial
    obtain ⟨d', hd', hd'π⟩ := this
    have h1 : π (d'⁻¹ * ⟨m, hm⟩) = 1 := by rw [map_mul, map_inv, hd'π, inv_mul_cancel]
    have h2 := (hπk _).mp h1
    exact ⟨(d' : G), mem_subgroupOf.mp hd', by simpa using h2⟩
  have hKT : ∀ k ∈ M₁, k ∈ centralizer (c.W : Set G) → ∀ s ∈ S ⊓ M₁, k * s * k⁻¹ ∈ S ⊓ M₁ := by
    intro k hkM hkC s hs
    obtain ⟨O₁, hO₁C, hO₁odd, -, hO₁dec, hO₁norm, -⟩ := F.exists_O₁
    obtain ⟨w, hw, o, ho, hk⟩ := hO₁dec k hkC
    have hoN : o ∈ c.Ninf := by
      have : o = w⁻¹ * k := by rw [hk]; group
      rw [this]
      exact c.Ninf.mul_mem (c.Ninf.inv_mem (F.W_le hw)) (hM₁N hkM)
    have hodd : Odd (Nat.card ↥(O₁ ⊓ c.Ninf)) :=
      hO₁odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hocent : ∀ n ∈ c.Ninf, o * n = n * o := fun n hn =>
      hZ (O₁ ⊓ c.Ninf) inf_le_right (fun x hx q hq =>
        ⟨hO₁norm x hx q hq.1, c.Ninf.mul_mem (c.Ninf.mul_mem hx hq.2) (c.Ninf.inv_mem hx)⟩)
        hodd o ⟨ho, hoN⟩ n hn
    have hwF : w ∈ (c.W ⊓ M₁) ⊔ (c.W ⊓ M₂) := by rw [F.W_eq]; exact hw
    obtain ⟨f₁, hf₁, f₂, hf₂, hw12⟩ := mem_sup_of_forall_comm (O := c.W ⊓ M₁) (E := c.W ⊓ M₂)
      (fun x hx y hy => comm_of_isElemAbelian_two c.W_elem hx.1 hy.1) hwF
    have hsN : s ∈ c.Ninf := hM₁N hs.2
    have hos : o * s * o⁻¹ = s := by rw [hocent s hsN]; group
    have hf₂s : f₂ * s = s * f₂ := (mem_centralizer_iff.mp (F.W₂_cent hf₂) s hs.2).symm
    have hf₂s' : f₂ * s * f₂⁻¹ = s := by rw [hf₂s]; group
    have e : k * s * k⁻¹ = f₁ * s * f₁⁻¹ := by
      calc k * s * k⁻¹ = w * (o * s * o⁻¹) * w⁻¹ := by rw [hk]; group
        _ = w * s * w⁻¹ := by rw [hos]
        _ = f₁ * (f₂ * s * f₂⁻¹) * f₁⁻¹ := by rw [hw12]; group
        _ = f₁ * s * f₁⁻¹ := by rw [hf₂s']
    rw [e]
    have hf₁T : f₁ ∈ S ⊓ M₁ := ⟨hWS hf₁.1, hf₁.2⟩
    exact (S ⊓ M₁).mul_mem ((S ⊓ M₁).mul_mem hf₁T hs) ((S ⊓ M₁).inv_mem hf₁T)
  have hgen := perfect_le_closure_conj_sylow F.perfect₁ hT₁
  have hMD : M₁ ≤ D := by
    refine hgen.trans ((Subgroup.closure_le D).mpr ?_)
    rintro y ⟨m, hm, s, hs, rfl⟩
    obtain ⟨d, hd, hdk⟩ := hDK m hm
    have hkM : d⁻¹ * m ∈ M₁ := M₁.mul_mem (M₁.inv_mem (hD₁M hd)) hm
    have hks := hKT (d⁻¹ * m) hkM hdk s hs
    have e : m * s * m⁻¹ = d * ((d⁻¹ * m) * s * (d⁻¹ * m)⁻¹) * d⁻¹ := by group
    rw [e]
    exact D.mul_mem (D.mul_mem hd (hT₁D hks)) (D.inv_mem hd)
  have hMQ₁ : M₁ ≤ Q₁ := hMD.trans (commutator_self_le Q₁)
  refine hgen.trans ((Subgroup.closure_le Q).mpr ?_)
  rintro y ⟨m, hm, s, hs, rfl⟩
  obtain ⟨-, m', hm', hmm'⟩ := hMQ₁ hm
  have hcs : m' * s = s * m' := hc' m' hm' s hs.2
  have e : m * s * m⁻¹ = (m * m') * s * (m * m')⁻¹ := by
    calc m * s * m⁻¹ = m * (s * m') * m'⁻¹ * m⁻¹ := by group
      _ = m * (m' * s) * m'⁻¹ * m⁻¹ := by rw [hcs]
      _ = (m * m') * s * (m * m')⁻¹ := by group
  rw [e]
  exact Q.mul_mem (Q.mul_mem hmm' (hSQ hs.1)) (Q.inv_mem hmm')

end Qmax

section CS

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.qmax₁ (hZ₁ : c₁.OddCoreCentral) :
    ∀ Q : Subgroup G, Q ≤ perfectResidualOf (normalizer (c₁.W : Set G)) → ⁅Q, Q⁆ = Q → S ≤ Q →
      Q = perfectResidualOf (normalizer (c₁.W : Set G)) := by
  intro Q hQN hQ hSQ
  refine le_antisymm hQN ?_
  show c₁.Ninf ≤ Q
  rw [CS.F₁.ninf_eq]
  exact sup_le (CS.F₁.qmax_le hZ₁ CS.syl.S₀_sylow CS.W₁_le_S hQN hQ hSQ)
    (CS.F₁.symm.qmax_le hZ₁ CS.syl.S₀_sylow CS.W₁_le_S hQN hQ hSQ)

theorem CommonSylow.qmax₂ (hZ₂ : c₂.OddCoreCentral) :
    ∀ Q : Subgroup G, Q ≤ perfectResidualOf (normalizer (c₂.W : Set G)) → ⁅Q, Q⁆ = Q → S ≤ Q →
      Q = perfectResidualOf (normalizer (c₂.W : Set G)) := by
  intro Q hQN hQ hSQ
  refine le_antisymm hQN ?_
  show c₂.Ninf ≤ Q
  rw [CS.F₂.ninf_eq]
  exact sup_le (CS.F₂.qmax_le hZ₂ CS.S_sylow₂ CS.W₂_le_S hQN hQ hSQ)
    (CS.F₂.symm.qmax_le hZ₂ CS.S_sylow₂ CS.W₂_le_S hQN hQ hSQ)

end CS

end CFSG.OddStandard.Seitz77
