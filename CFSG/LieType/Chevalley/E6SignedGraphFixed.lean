module

public import CFSG.LieType.Chevalley.ExactNormalFormE

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (K : Type) [Field K]

@[expose] def signTuple : Fin TwistTag.E6.tag.rank → Kˣ :=
  ![1, -1, 1, 1, 1, 1]

@[expose] def twistA : ModGL TwistTag.E6.tag K :=
  rootDiagUnit TwistTag.E6.tag (signTuple K) * diagramMap TwistTag.E6 K

@[expose] def fixedGroup : Subgroup (ModGL TwistTag.E6.tag K) :=
  adjointGroup TwistTag.E6.tag K ⊓ Subgroup.centralizer {twistA K}

variable {K}

theorem mem_fixedGroup {g : ModGL TwistTag.E6.tag K} :
    g ∈ fixedGroup K ↔ g ∈ adjointGroup TwistTag.E6.tag K ∧ g * twistA K = twistA K * g := by
  rw [fixedGroup, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem signTuple_of_ne {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ ⟨1, by decide⟩) :
    signTuple K i = 1 := by
  fin_cases i
  · rfl
  · exact absurd rfl hi
  all_goals rfl

theorem conjP_xUnit
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    diagramMap TwistTag.E6 K * xUnit TwistTag.E6.tag K i c * (diagramMap TwistTag.E6 K)⁻¹ =
      xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) c :=
  diagramMap_mul_xUnit_mul_inv TwistTag.E6 K i c

theorem conjP_yUnit
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    diagramMap TwistTag.E6 K * yUnit TwistTag.E6.tag K i c * (diagramMap TwistTag.E6 K)⁻¹ =
      yUnit TwistTag.E6.tag K (TwistTag.E6.perm i) c :=
  diagramMap_mul_yUnit_mul_inv TwistTag.E6 K i c

theorem conj_mul_mul {G : Type*} [Group G] (p a b c : G) :
    p * (a * b * c) * p⁻¹ = (p * a * p⁻¹) * (p * b * p⁻¹) * (p * c * p⁻¹) := by
  group

theorem conjP_weylElt
    (i : Fin TwistTag.E6.tag.rank) :
    diagramMap TwistTag.E6 K * weylElt TwistTag.E6.tag K i 1 * (diagramMap TwistTag.E6 K)⁻¹ =
      weylElt TwistTag.E6.tag K (TwistTag.E6.perm i) 1 := by
  rw [weylElt_eq_xUnit_mul, weylElt_eq_xUnit_mul, conj_mul_mul, conjP_xUnit, conjP_yUnit]

theorem conjD_xUnit
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) * xUnit TwistTag.E6.tag K i c *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ =
      xUnit TwistTag.E6.tag K i ((signTuple K i : K) * c) :=
  (root_diagonal_conjugation TwistTag.E6.tag K (signTuple K)).1 i c

theorem conjD_yUnit
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) * yUnit TwistTag.E6.tag K i c *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ =
      yUnit TwistTag.E6.tag K i (((signTuple K i)⁻¹ : Kˣ) * c) :=
  (root_diagonal_conjugation TwistTag.E6.tag K (signTuple K)).2.1 i c

theorem conjD_xUnit_of_ne
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ ⟨1, by decide⟩) (c : K) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) * xUnit TwistTag.E6.tag K i c *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ = xUnit TwistTag.E6.tag K i c := by
  rw [conjD_xUnit, signTuple_of_ne hi, Units.val_one, one_mul]

theorem conjD_yUnit_of_ne
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ ⟨1, by decide⟩) (c : K) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) * yUnit TwistTag.E6.tag K i c *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ = yUnit TwistTag.E6.tag K i c := by
  rw [conjD_yUnit, signTuple_of_ne hi, inv_one, Units.val_one, one_mul]

theorem conjD_weylElt_of_ne
    {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ ⟨1, by decide⟩) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) * weylElt TwistTag.E6.tag K i 1 *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ = weylElt TwistTag.E6.tag K i 1 := by
  rw [weylElt_eq_xUnit_mul, conj_mul_mul, conjD_xUnit_of_ne hi, conjD_yUnit_of_ne hi]

theorem commute_twistA_of_conj {g : ModGL TwistTag.E6.tag K}
    (hP : diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g)
    (hD : rootDiagUnit TwistTag.E6.tag (signTuple K) * g *
      (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ = g) :
    g * twistA K = twistA K * g := by
  have hP' := mul_inv_eq_iff_eq_mul.1 hP
  have hD' := mul_inv_eq_iff_eq_mul.1 hD
  rw [twistA, ← mul_assoc, ← hD', mul_assoc, ← hP', mul_assoc]

end CFSG.LieType.Chevalley.E6SignedGraph
