module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem toralCentralizer_component_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] {p : ℕ} (hK2 : ringChar K ≠ 2)
    {reps : List (List Bool)} {entries : List (List Bool × ℕ × List ℕ)}
    (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      ∀ N : Subgroup (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))),
        IsComponent N → OddLieCentralQuotient p N)
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1)
    {M : Subgroup (toralCentralizer τ K b)} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
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
    exact oddLieCentralQuotient_of_mulEquiv (M.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (hreps ρ hρ h0 _ (LocalCores.isComponent_map_mulEquiv e.symm hM))

end CFSG.ComponentClassification.CatLeafProof
