module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeGraph
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.CoreStatement
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.GraphCorrespondenceAux.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three


private theorem defCharGoodPlus_graph_one (hcore : TrialityThreeCore) {K : Type} [Field K]
    [Finite K] [CharP K 3] (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) :
    DefCharGoodPlus α := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have hK : Nat.card K = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hf : 1 ≤ (n : ℕ) := n.pos
  obtain ⟨K₃, _, _, _, _, hK₃, Fr, hFr⟩ := GraphCorrespondence.exists_ext (ℓ := 3) hf K hK
  set L := AlgebraicClosure K₃ with hL
  have : CharP L 3 := charP_of_injective_algebraMap (algebraMap K₃ L).injective 3
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  set ιK : K →+* K₃ := algebraMap K K₃ with hιK
  set ιL : K₃ →+* L := algebraMap K₃ L with hιL
  set ιLK : K →+* L := ιL.comp ιK with hιLK
  set x : ModGL Tag.D4 L := baseChangeGL ιLK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)
    with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hFrc : (iterateFrobenius L 3 (n : ℕ)).comp ιLK = ιLK := by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, hιLK, ← map_pow]
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hxF : Units.map (entrywiseHom (iterateFrobenius L 3 (n : ℕ))) x = x := by
    rw [hxdef, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      (x * d4P L ^ 1) * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (x * d4P L ^ 1)⁻¹ := by
    intro u
    have h := GraphCorrespondence.baseChange_normalForm_one ιLK g a 1 u
    rw [← hα] at h
    exact h
  have hαx : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      x * (d4P L * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (d4P L)⁻¹) * x⁻¹ := by
    intro u
    rw [hM u, pow_one]
    group
  have hxP : (x * d4P L) ^ 3 = 1 := by
    have := GraphCorrespondence.cube_eq_one ιLK α hα3 g a 1 hx hM
    rwa [pow_one] at this
  set g₃ : adjointGroup Tag.D4 K₃ := ⟨baseChangeGL ιK (g : ModGL Tag.D4 K),
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2⟩ with hg₃
  set a₃ : Fin Tag.D4.rank → K₃ˣ := fun i => Units.map ιK.toMonoidHom (a i) with ha₃
  have hx3' : (g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃ =
      baseChangeGL ιK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) := by
    rw [map_mul, baseChangeGL_rootDiagUnit]
  have hx3 : baseChangeGL ιL ((g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃) = x := by
    rw [hx3', hxdef, baseChangeGL_baseChangeGL]
  obtain ⟨αhat, hαhat3, hαhatout, ⟨e⟩⟩ := exists_fixSubgroupEquiv_graph_ambient (by decide) hf K hK
    K₃ hK₃ Fr hFr L x hx hxF hxP
    (MulAut.conj g₃ * (exactNormalAut Tag.D4 K₃ a₃ Fr 0 * d4Graph K₃ 1))
    (fun u => by
      have h := GraphCorrespondence.baseChange_normalForm L ιL g₃ a₃ Fr 1 u
      rw [hx3] at h
      exact h)
    α hαx
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite (ModGL Tag.D4 K₃) := finite_modGL
  exact defCharGoodPlus_of_equiv e (hcore (n : ℕ) hf K₃ hK₃ Fr hFr αhat hαhat3 hαhatout)

theorem d4ThreeGraphOuter_of_core (hcore : TrialityThreeCore) : D4ThreeGraphOuter := by
  intro K _ _ _ g a ε hε0 hε3 α hα hα3
  have hrefl : (RingEquiv.refl K) = (1 : K ≃+* K) := rfl
  rw [hrefl] at hα
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  suffices hgood : DefCharGoodPlus α from hgood.good
  interval_cases ε
  · exact defCharGoodPlus_graph_one hcore g a α hα3 hα
  · obtain ⟨g', a', hinv⟩ := GraphCorrespondence.inv_normalForm g a
    rw [← hα] at hinv
    exact defCharGoodPlus_inv α (defCharGoodPlus_graph_one hcore g' a' α⁻¹
      (by rw [inv_pow, hα3, inv_one]) hinv)

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
