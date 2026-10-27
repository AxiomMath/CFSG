module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151ExcDefs
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Orders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Blueprint.Chevalley


theorem d4ExitAt_adjoint_G2_two (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : F151.D4ExitAt ↥(adjointGroup .G2 K) 3 := by
  intro x w _ _ _ _ Kc _ hcat _ _
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨d', hv⟩ | _
  · exact absurd hi (by simp [onLie])
  · exact absurd hi (by simp [onLie])
  · obtain ⟨q, rfl, hq2⟩ := hi
    let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
    haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.D 4 q, hv⟩
    have hL : Nat.card F = q.card := by
      show Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = q.card
      rw [TauCeti.ValidLieTypeIndex.card_fixedField]
      simp [TauCeti.ValidLieTypeIndex.fieldOrder]
    have hFcard : Nat.card F = 2 ^ q.exponent := by
      rw [hL, TauCeti.PrimePower.card_def, hq2]
    let θ : ↥Kc ⧸ Subgroup.center ↥Kc ≃* adjointGroup Tag.D4 F :=
      e.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid
          4 q hv).trans
        (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
          F).some)
    have h2 : 2 ^ 12 ∣ Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) := by
      rw [Nat.card_congr θ.toEquiv,
        CFSG.LieType.SeitzGeneration.ExcWideThree.card_adjointGroup_D4_eq (K := F)]
      have hdvd : 2 ^ 12 ∣ Nat.card F ^ 12 := by
        rw [hFcard, ← pow_mul]
        exact Nat.pow_dvd_pow 2 (by have := q.exponent_pos; omega)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdvd _) _
    have hdvd : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ∣ Nat.card (adjointGroup .G2 K) :=
      (Subgroup.card_quotient_dvd_card (Subgroup.center ↥Kc)).trans
        (Subgroup.card_subgroup_dvd_card Kc)
    rw [CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two (k := K) hK] at hdvd
    exact absurd (h2.trans hdvd) (by norm_num)
  · exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
