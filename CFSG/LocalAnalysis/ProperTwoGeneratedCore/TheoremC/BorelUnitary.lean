module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelUnitaryTorus
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelTransport

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

theorem benderBorelFacts_unitaryCoverRoot {K : Type} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    BenderBorelFacts (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryCoverRoot J hJ) where
  commutator_central := unitaryCoverRoot_commutator_central J hcard hfixed hJ
  sq_central := unitaryCoverRoot_sq_central J hcard hfixed hJ
  torus := ⟨unitaryCoverTorus J hJ, unitaryCoverTorus_card_odd J f hf hcard hfixed hJ,
    unitaryCoverTorus_le_normalizer J hJ,
    unitaryCoverRoot_sup_torus_eq_normalizer J hf hcard hfixed hJ,
    fun _ _ hw hw1 hw' hw'1 =>
      unitaryCoverTorus_transitive_center J hcard hfixed hJ hw hw1 hw' hw'1,
    fun β hβ₁ hβ₂ hβ₃ hβ₄ hβ₅ =>
      unitaryCoverRoot_forms_eq_zero J hf hcard hfixed hJ β hβ₁ hβ₂ hβ₃ hβ₄ hβ₅⟩
  center_card := by
    rw [card_inCenterOf_unitaryCoverRoot J hcard hfixed hJ]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  aut_inner := unitaryCoverRoot_aut_inner J hf hcard hfixed hJ

theorem unitaryBorelFacts : UnitaryBorelFacts := by
  intro n hn
  let k := GaloisField 2 n
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian n (by omega)
  have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hcard hfixed
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  let P : Sylow 2 (PSU3Model n) := (unitaryCoverSylow J n hn hcard hfixed hJ).mapSurjective
    (f := e.toMonoidHom) fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  have hP : (P : Subgroup (PSU3Model n)) = (unitaryCoverRoot J hJ).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  exact ⟨P, hP ▸ benderBorelFacts_map_mulEquiv e
    (benderBorelFacts_unitaryCoverRoot J hn hcard hfixed hJ)⟩

end CFSG.ProperTwoGeneratedCore.TheoremC
