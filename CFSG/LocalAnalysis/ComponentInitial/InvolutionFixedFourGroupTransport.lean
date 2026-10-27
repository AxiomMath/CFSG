module

public import CFSG.LocalAnalysis.ComponentInitial.InvolutionCentralizerRank
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_four_group_le_fixedSubgroup_conj {L : Type*} [Group L] [Finite L]
    [IsSimpleGroup L] (hL : ∃ a b : L, a * b ≠ b * a) (g : L) (hα : MulAut.conj g ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup (MulAut.conj g) ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := center_eq_bot_of_isSimpleGroup hL
  have hg2 : g ^ 2 = 1 := by
    have hmem : g ^ 2 ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut L => φ y) hα
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g ^ 2 = g ^ 2 * y * (g ^ 2)⁻¹ * g ^ 2 := by rw [h1]
        _ = g ^ 2 * y := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hrank : 2 ≤ CFSG.pRank 2 L := two_le_pRank_of_isQuasisimple_of_odd_center
    (isQuasisimple_of_isSimpleGroup hL) (by rw [hZ, Subgroup.card_bot]; exact odd_one)
  have hC := involution_centralizer_contains_four_group hrank hg2
  obtain ⟨A, hA, hAcard⟩ := exists_four_group_of_two_le_pRank hC
  have hA' : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 x x.2) }
  refine ⟨A.map (Subgroup.centralizer ({g} : Set L)).subtype, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    change MulAut.conj g (x : L) = x
    rw [MulAut.conj_apply, (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm,
      mul_inv_cancel_right]
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hAcard

theorem congr_apply_eq {L C : Type*} [Group L] [Group C] (e : L ≃* C) (α : MulAut L) (y : C) :
    MulAut.congr e α y = e (α (e.symm y)) :=
  rfl

theorem exists_four_group_le_fixedSubgroup_of_congr {L C : Type*} [Group L] [Group C]
    (e : L ≃* C) (α : MulAut L) {V : Subgroup C} (hV : V ≤ fixedSubgroup (MulAut.congr e α))
    (hVab : IsElementaryAbelian 2 V) (hVc : Nat.card V = 4) :
    ∃ W : Subgroup L, W ≤ fixedSubgroup α ∧ IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨V.map e.symm.toMonoidHom, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : MulAut.congr e α y = y := hV hy
    rw [congr_apply_eq] at h1
    change α (e.symm y) = e.symm y
    have h2 := congrArg e.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hVc

theorem congr_mem_inner_iff {L C : Type*} [Group L] [Group C] (e : L ≃* C) (α : MulAut L) :
    MulAut.congr e α ∈ inner C ↔ α ∈ inner L := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun φ : MulAut C => φ (e x)) hy
    simp only [MulAut.conj_apply, congr_apply_eq, MulEquiv.symm_apply_apply] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    refine ⟨e y, MulEquiv.ext fun x => ?_⟩
    rw [congr_apply_eq, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

theorem congr_eq_conj {C : Type*} [Group C] (ψ β : MulAut C) :
    MulAut.congr ψ β = ψ * β * ψ⁻¹ :=
  MulEquiv.ext fun _ => rfl

end CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
