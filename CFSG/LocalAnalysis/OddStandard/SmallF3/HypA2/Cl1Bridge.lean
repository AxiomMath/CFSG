module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ProperFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.GH74.Orders.LieType
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem cl1_of_gls3 (h : CatLeaf.GLS3OddLieAutComponentsInput) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] {σ : MulAut S} {P : Subgroup S} (hP : ProperFixedComp σ P) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hS : HarrisLit.IsSimpleChevalleyOver r S) :
    HarrisLit.IsSimpleChevalleyOver r (P ⧸ center P) ∨
      LieModel (P ⧸ center P) .PSL 2 2 3 := by
  obtain ⟨τ, n, f, hm⟩ := hS
  have hadm : CFSG.Open.StatedLieAdmissible τ n r f := hm.admissible
  have hpow : σ ^ 2 = 1 := by
    ext x
    simpa [pow_two] using hP.1 x
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hFtop : fixedSubgroup (1 : MulAut S) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rfl
    haveI : IsSimpleGroup (fixedSubgroup (1 : MulAut S)) :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have hcomp : IsComponent (P.subgroupOf (fixedSubgroup (1 : MulAut S))) := hP.2.2.2
    have htop : P.subgroupOf (fixedSubgroup (1 : MulAut S)) = ⊤ := by
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hcomp.2 with h' | h'
      · exfalso
        have hnt : Nontrivial (P.subgroupOf (fixedSubgroup (1 : MulAut S))) :=
          CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
        rw [h'] at hnt
        exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
      · exact h'
    apply hP.2.2.1
    rw [eq_top_iff]
    intro x _
    have hmem : (⟨x, hFtop ▸ mem_top x⟩ : fixedSubgroup (1 : MulAut S)) ∈
        P.subgroupOf (fixedSubgroup (1 : MulAut S)) := htop ▸ mem_top _
    exact hmem
  have hσ2 : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hpow hσ1
  rcases h S τ n r f hr hr2 hadm hm σ hσ2
      (P.subgroupOf (fixedSubgroup σ)) hP.2.2.2 with
    ⟨τ', n', f', -, hLie⟩ | ⟨-, -, -, hKlie⟩
  · refine Or.inl ⟨τ', n', f', ?_⟩
    exact LieModel.of_mulEquiv
      (CFSG.ComponentClassification.Sol78.centerQuotCongr
        (Subgroup.subgroupOfEquivOfLe hP.2.1)) hLie
  ·
    have hPLie : LieModel ↥P .PSL 2 2 3 :=
      LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.2.1) hKlie
    haveI : IsSimpleGroup ↥P :=
      (CFSG.LieType.Simplicity.fam_classical_converse ↥P
        ⟨.PSL, 2, 2, 3, GH74.statedClassicalModel_of_lieModel (by norm_num) hPLie⟩).2.2
    have hnab' : ∃ x y : ↥(P.subgroupOf (fixedSubgroup σ)), x * y ≠ y * x := by
      obtain ⟨a, b, hab⟩ := hP.2.2.2.1.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨x, y, fun hxy => hab (by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy])⟩
    have hnab : ∃ x y : ↥P, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hnab'
      let e := Subgroup.subgroupOfEquivOfLe hP.2.1
      exact ⟨e x, e y, fun h => hxy (e.injective (by simpa [map_mul] using h))⟩
    have hcenter : center ↥P = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
    exact Or.inr (LieModel.quotient_center hcenter hPLie)

end CFSG.OddStandard.SmallF3.HypA2
