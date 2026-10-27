module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCommutantKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {F : Type*} [Group F] [Finite F]

theorem cyclic_overgroup_normalizer_le (A B : Subgroup F) [IsCyclic A]
    (hBA : B ≤ A) :
    Subgroup.normalizer (A : Set F) ≤ Subgroup.normalizer (B : Set F) := by
  intro n hn
  let C := B.map (MulAut.conj n).toMonoidHom
  have hCA : C ≤ A := by
    rintro y ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn x).mp (hBA hx)
  have hcard : Nat.card C = Nat.card B :=
    Nat.card_congr ((MulAut.conj n).subgroupMap B).toEquiv.symm
  have hCB : C = B := by
    have hsub : C.subgroupOf A = B.subgroupOf A :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, hcard])
    calc
      C = (C.subgroupOf A).map A.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hCA).symm
      _ = (B.subgroupOf A).map A.subtype := by rw [hsub]
      _ = B := Subgroup.map_subgroupOf_eq_of_le hBA
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hCB

theorem full_cyclic_centralizer_normalizer_index_dvd_four
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    (rho : F →* LinearMap.GeneralLinearGroup K V) (hrho : Function.Injective rho)
    (A : Subgroup F) [IsCyclic A] (z : F) (hzA : z ∈ A)
    (hCz : Subgroup.centralizer ({z} : Set F) = A)
    (hirr : ∀ U : Submodule K V,
      (∀ v ∈ U, (rho z : Module.End K V) v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdim : Module.finrank K V = 4) :
    A.relIndex (Subgroup.normalizer (A : Set F)) ∣ 4 := by
  have hN := cyclic_overgroup_normalizer_le A (Subgroup.zpowers z)
    (Subgroup.zpowers_le.mpr hzA)
  have hdiv : A.relIndex (Subgroup.normalizer (Subgroup.zpowers z : Set F)) ∣ 4 := by
    rw [← hCz]
    exact cyclic_normalizer_centralizer_index_dvd_four rho hrho z hirr hdim
  have htower := Subgroup.relIndex_mul_relIndex A
    (Subgroup.normalizer (A : Set F))
    (Subgroup.normalizer (Subgroup.zpowers z : Set F)) Subgroup.le_normalizer hN
  exact (dvd_mul_right (A.relIndex (Subgroup.normalizer (A : Set F)))
    ((Subgroup.normalizer (A : Set F)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers z : Set F)))).trans
        (htower.symm ▸ hdiv)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
