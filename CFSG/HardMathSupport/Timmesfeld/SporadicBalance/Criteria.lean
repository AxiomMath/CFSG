module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving

variable {p : ℕ} {S : Type*} [Group S]

theorem noOuterFixesCentralizer_of_fixed_dvd {K : Type*} [Group K] [Finite K] (N : ℕ)
    (hfix : ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∀ H : Subgroup K,
      (∀ x ∈ H, σ x = x) → Nat.card H ∣ N)
    (hcent : ∀ s : K, orderOf s = p → ¬ Nat.card ↥(Subgroup.centralizer ({s} : Set K)) ∣ N) :
    NoOuterFixesCentralizer p K := by
  intro σ hσ2 hσ s hs
  by_contra hno
  push Not at hno
  exact hcent s hs (hfix σ hσ2 hσ _ fun t ht =>
    hno t (Subgroup.mem_centralizer_singleton_iff.1 ht).symm)

section Commutator

variable {G : Type*} [Group G]

open scoped commutatorElement

theorem conj_mem_commutator_self {C : Subgroup G} {g : G} (hg : g ∈ C) {x : G}
    (hx : x ∈ ⁅C, C⁆) : g * x * g⁻¹ ∈ ⁅C, C⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨g * a * g⁻¹, C.mul_mem (C.mul_mem hg ha) (C.inv_mem hg), g * b * g⁻¹,
      C.mul_mem (C.mul_mem hg hb) (C.inv_mem hg), ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul y z _ _ hy hz =>
    have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hy

theorem commutator_zpowers_sup {z : G} {L : Subgroup G} (hz : ∀ x ∈ L, x * z = z * x) :
    ⁅Subgroup.zpowers z ⊔ L, Subgroup.zpowers z ⊔ L⁆ = ⁅L, L⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have hcomm : ∀ u ∈ Subgroup.zpowers z, ∀ l ∈ L, u * l = l * u := by
      intro u hu l hl
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      exact ((Commute.zpow_left (show Commute z l from (hz l hl).symm) k)).eq
    obtain ⟨u1, hu1, l1, hl1, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm ha
    obtain ⟨u2, hu2, l2, hl2, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hb
    rw [CFSG.GroupTheory.commutatorElement_mul_of_commute hcomm hu1 hu2 hl1 hl2]
    have : ⁅u1, u2⁆ = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu1
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu2
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Commute.zpow_zpow_self z i j).eq
    rw [this, one_mul]
    exact Subgroup.commutator_mem_commutator hl1 hl2
  · exact Subgroup.commutator_mono le_sup_right le_sup_right

end Commutator

theorem gLAPPrimeCoreOf_eq_bot_of_zpowers_sup_simple {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) {C L : Subgroup G} {z : G} (hz : orderOf z = p)
    (hsup : C = Subgroup.zpowers z ⊔ L) (hcomm : ∀ x ∈ L, x * z = z * x)
    (hder : ⁅C, C⁆ = L) (hsimple : IsSimpleGroup ↥L) (hdvd : p ∣ Nat.card L) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have hLC : L ≤ C := hsup ▸ le_sup_right
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl => by
    rw [← hder] at hl ⊢
    exact conj_mem_commutator_self hg hl
  have hperf : ⁅L, L⁆ = L := by
    have h := commutator_zpowers_sup hcomm
    rw [← hsup, hder] at h
    exact h.symm
  have hcommu : ∀ u ∈ Subgroup.zpowers z, ∀ l ∈ L, u * l = l * u := by
    intro u hu l hl
    have hs : z ∈ Subgroup.centralizer ({l} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hcomm l hl).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.zpowers_le.2 hs hu)
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hno
    push Not at hno
    have h1 : ⁅L, L⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have h2 : a * b = b * a := congrArg Subtype.val (hno ⟨a, ha⟩ ⟨b, hb⟩)
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 h2)
    rw [h1] at hperf
    have h3 : Nat.card ↥L = 1 := by rw [← hperf]; exact Subgroup.card_bot
    rw [h3] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
  have hcenter : ∀ l ∈ L, (∀ y ∈ L, y * l = l * y) → l = 1 := by
    intro l hl hy
    have hcen : Subgroup.center ↥L = ⊥ :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
    have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hy g g.2)
    rw [hcen] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hle : C ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers z := by
    intro x hx
    obtain ⟨hxC, hxcent⟩ := Subgroup.mem_inf.1 hx
    rw [hsup] at hxC
    obtain ⟨u, hu, l, hl, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommu hxC
    have hl1 : l = 1 := hcenter l hl fun y hy => by
      have h1 := Subgroup.mem_centralizer_iff.1 hxcent y hy
      have h2 : y * u = u * y := (hcommu u hu y hy).symm
      have h3 : u * (y * l) = u * (l * y) := by
        calc u * (y * l) = (u * y) * l := by rw [mul_assoc]
          _ = (y * u) * l := by rw [h2]
          _ = y * (u * l) := by rw [mul_assoc]
          _ = (u * l) * y := h1
          _ = u * (l * y) := by rw [mul_assoc]
      exact mul_left_cancel h3
    rw [hl1, mul_one]
    exact hu
  have hzp : IsPGroup p ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  refine gLAPPrimeCoreOf_eq_bot_of_perfect hp hLC hLn hperf ?_ (hzp.to_le hle)
  intro M hML hMn hcop m hm l hl
  have hnorm : (M.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff hML).2 fun h k hh hk => hMn k hk h hh
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf L) with h | h
  · have hm1 : m = 1 := by
      have hm' : (⟨m, hML hm⟩ : ↥L) ∈ M.subgroupOf L := hm
      rw [h] at hm'
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hm')
    rw [hm1]
    simp
  · exfalso
    have hMeq : M = L := le_antisymm hML fun x hx => by
      have : (⟨x, hx⟩ : ↥L) ∈ M.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
    rw [hMeq] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hdvd

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
