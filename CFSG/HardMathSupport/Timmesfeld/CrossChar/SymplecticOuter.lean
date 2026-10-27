module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm
open CFSG.Open (IsElemAbelian)

theorem exists_inner_plane_psp {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut (StatedProj (StatedSp r K)))) (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup (MulAut (StatedProj (StatedSp r K))), E ≤ D ∧
      E ≤ innerAut (StatedProj (StatedSp r K)) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have O := spOuter (K := K) hℓ hf hr hK
  have : CFSG.IsElementaryAbelian p D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hD.2 x x.2) }
  have hDE : D ≤ spSemilinearAutGroup r K := fun a ha => mem_E_of_mem O hp hp2 ha
  have := O.normal
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  set Es := spSemilinearAutGroup r K with hEs
  set Dl := spLinearAutGroup r K with hDl
  have hcycQ : IsCyclic (↥Es ⧸ Dl.subgroupOf Es) := by
    have hFE : (fieldAut r K).range ≤ Es := by
      rw [hEs, ← O.sup_eq]
      exact le_sup_right
    let ψ : ↥(fieldAut r K).range →* ↥Es ⧸ Dl.subgroupOf Es :=
      (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hFE)
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨⟨e, he⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have he' := he
      rw [hEs, ← O.sup_eq] at he'
      obtain ⟨d, hd, φ, hφ, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he'
      refine ⟨⟨φ, hφ⟩, ?_⟩
      show (QuotientGroup.mk (⟨φ, hFE hφ⟩ : ↥Es) : ↥Es ⧸ Dl.subgroupOf Es) = _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (φ⁻¹ * (d * φ) : MulAut (StatedProj (StatedSp r K))) ∈ Dl
      have : φ⁻¹ * (d * φ) = (φ⁻¹) * d * (φ⁻¹)⁻¹ := by group
      rw [this]
      exact (inferInstance : Dl.Normal).conj_mem d hd φ⁻¹
    have : IsCyclic ↥(fieldAut r K).range :=
      isCyclic_of_surjective (fieldAut r K).rangeRestrict (fieldAut r K).rangeRestrict_surjective
    exact isCyclic_of_surjective ψ hψ
  let α : D →* ↥Es ⧸ Dl.subgroupOf Es := (QuotientGroup.mk' _).comp (Subgroup.inclusion hDE)
  refine exists_plane_of_hom_cyclic hp (innerAut _) hD hcard α fun x hx => ?_
  have hxDl : (x : MulAut (StatedProj (StatedSp r K))) ∈ Dl := by
    change QuotientGroup.mk (Subgroup.inclusion hDE x) = (1 : ↥Es ⧸ Dl.subgroupOf Es) at hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    exact hx
  exact mem_inner_of_mem_D O hp hp2 x.2 hxDl

end CFSG.HardMathSupport.Timmesfeld.CrossChar
