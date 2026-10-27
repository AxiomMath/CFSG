module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcCommon
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof

theorem hasBigLieSub_toralCentralizer_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] {p : ℕ} (hK2 : ringChar K ≠ 2)
    {reps : List (List Bool)} {entries : List (List Bool × ℕ × List ℕ)}
    (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      HasBigLieSub p ↥(toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))))
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    HasBigLieSub p ↥(toralCentralizer τ K b) := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  by_cases h0 : listMask (τ := τ) (reps.getD ρ []) = fun _ => false
  · refine absurd (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_) hb1
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  · let e : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
        toralCentralizer τ K b :=
      ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact (hreps ρ hρ h0).of_mulEquiv e

end CFSG.ComponentClassification.CatFC
