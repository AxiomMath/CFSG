module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

theorem index_range_conj_congr {L M : Type*} [Group L] [Group M] (e : L ≃* M) :
    (MulAut.conj : M →* MulAut M).range.index = (MulAut.conj : L →* MulAut L).range.index := by
  have hrange : (MulAut.conj : M →* MulAut M).range =
      (MulAut.conj : L →* MulAut L).range.map (MulAut.congr e).toMonoidHom := by
    ext φ
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨MulAut.conj (e.symm m), ⟨e.symm m, rfl⟩, ?_⟩
      ext x
      simp [MulAut.congr_apply]
    · rintro ⟨f, ⟨l, rfl⟩, rfl⟩
      refine ⟨e l, ?_⟩
      ext x
      simp [MulAut.congr_apply]
  rw [hrange]
  exact Subgroup.index_map_equiv _ (MulAut.congr e)

theorem index_le_two_of_centralizer_le {N : Type*} [Group N] [Finite N] (H : Subgroup N)
    [H.Normal] (hC : ∀ σ : N, (∀ h ∈ H, σ * h = h * σ) → σ ∈ H)
    (hOut : (MulAut.conj : H →* MulAut H).range.index ≤ 2) : H.index ≤ 2 := by
  haveI : Finite H := inferInstance
  haveI : Finite (MulAut H) :=
    Finite.of_injective (fun f : MulAut H => (f : H → H)) DFunLike.coe_injective
  let I : Subgroup (MulAut H) := (MulAut.conj : H →* MulAut H).range
  have hcomap : I.comap (MulAut.conjNormal : N →* MulAut H) = H := by
    ext σ
    constructor
    · rintro ⟨h, hh⟩
      have hcomm : ∀ k ∈ H, ((h : N)⁻¹ * σ) * k = k * ((h : N)⁻¹ * σ) := by
        intro k hk
        have hk' := congrArg (fun f : MulAut H => (f ⟨k, hk⟩ : N)) hh
        simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at hk'
        push_cast at hk'
        calc ((h : N)⁻¹ * σ) * k = ((h : N)⁻¹ * (σ * k * σ⁻¹)) * σ := by group
          _ = ((h : N)⁻¹ * ((h : N) * k * (h : N)⁻¹)) * σ := by rw [← hk']
          _ = k * ((h : N)⁻¹ * σ) := by group
      have hσ' : (h : N)⁻¹ * σ ∈ H := hC _ hcomm
      have hσ : σ = (h : N) * ((h : N)⁻¹ * σ) := by group
      rw [hσ]
      exact H.mul_mem h.2 hσ'
    · intro hσ
      exact ⟨⟨σ, hσ⟩, MulAut.conjNormal_val.symm⟩
  have hI : I.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc H.index = (I.comap (MulAut.conjNormal : N →* MulAut H)).index := by rw [hcomap]
    _ = I.relIndex (MulAut.conjNormal : N →* MulAut H).range := Subgroup.index_comap I _
    _ ≤ I.relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top (by rwa [Subgroup.relIndex_top_right])
    _ = I.index := Subgroup.relIndex_top_right I
    _ ≤ 2 := hOut

theorem index_eq_relIndex_of_sup_eq_top {K : Type*} [Group K] (A B : Subgroup K) [A.Normal]
    (h : A ⊔ B = ⊤) : A.index = A.relIndex B := by
  have h1 := Subgroup.relIndex_sup_right B A
  rwa [sup_comm, h, Subgroup.relIndex_top_right] at h1

theorem index_le_two_of_sup_eq_top {K : Type*} [Group K] [Finite K] (A B : Subgroup K) [A.Normal]
    (hAB : A ⊔ B = ⊤) (hC : ∀ σ ∈ B, (∀ h ∈ A ⊓ B, σ * h = h * σ) → σ ∈ A) {L : Type*}
    [Group L] (e : L ≃* ↥(A.subgroupOf B))
    (hOut : (MulAut.conj : L →* MulAut L).range.index ≤ 2) : A.index ≤ 2 := by
  haveI : Finite B := inferInstance
  have hC' : ∀ σ : B, (∀ h ∈ A.subgroupOf B, σ * h = h * σ) → σ ∈ A.subgroupOf B := by
    intro σ hσ
    refine hC σ σ.2 fun h hh => ?_
    have := hσ ⟨h, hh.2⟩ hh.1
    exact congrArg Subtype.val this
  have h1 := index_le_two_of_centralizer_le (A.subgroupOf B) hC'
    (by rw [index_range_conj_congr e]; exact hOut)
  rw [index_eq_relIndex_of_sup_eq_top A B hAB]
  exact h1

theorem commutator_le_of_index_le_two {K : Type*} [Group K] [Finite K] (A : Subgroup K)
    [A.Normal] (h : A.index ≤ 2) : _root_.commutator K ≤ A := by
  have h0 : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : A.index = 1 ∨ A.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact le_top
  · have hcard : Nat.card (K ⧸ A) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact h2
    haveI : IsCyclic (K ⧸ A) := isCyclic_of_prime_card (p := 2) hcard
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
