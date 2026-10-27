module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2D4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.LocalBalance Module CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamily coordinatePlusWitnessEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (plusCX plusCXstar coordinate_plus_pointFamily_orbit_subset)
open scoped Pointwise

section Semilinear

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem localDeltaIn_eq_bot_orth_two_plane (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : 8 ≤ finrank K V)
    (hsemi : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α)
    {D : Subgroup (MulAut (ProjOrthDerived Q))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hDinn : D ≤ innerAut (ProjOrthDerived Q))
    {H : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨G, hGO, hG⟩ := exists_isometry_of_inducedBySemilinear hK (hsemi g)
  exact orth2_eq_one_of_isometry_two hK hQ hT h8 hD hcard hDinn hH hg hGO fun y => by
    obtain ⟨_, h⟩ := hG y
    exact h

theorem innerPlaneBalance_orth_two (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : 8 ≤ finrank K V)
    (hsemi : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α) :
    InnerPlaneBalance 3 (ProjOrthDerived Q) := by
  intro E hEin hE hEc H hH
  exact localDeltaIn_eq_bot_orth_two_plane hK hQ hT h8 hsemi hE hEc hEin hH

end Semilinear

section D4

variable {K : Type} [Field K] [Finite K]

theorem d4two_plane_eq_one_of_mem_image (hK : Nat.card K = 2)
    {D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hDinn : D ≤ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    {H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hH : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H)
    {g : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hg : g ∈ localDeltaIn 3 H D) (hgE : g ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    g = 1 := by
  have hd : 0 < 2 * 4 := by norm_num
  set φ := KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 K) hd with hφ
  obtain ⟨hQ, hT⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
      (n := 4) (K := K) (by norm_num)
  have h8 : 8 ≤ finrank K (Fin (2 * 4) → K) := by rw [Module.finrank_fin_fun]
  have hg' := map_localDeltaIn_le 3 (MulAut.congr φ).toMonoidHom (MulAut.congr φ).injective H D
    ⟨g, hg, rfl⟩
  have hsemi : KCOrthogonalAut.InducedBySemilinear (coordinateQuadPlus 4 K)
      (MulAut.congr φ g) := by
    have hback : MulAut.congr φ.symm (MulAut.congr φ g) = g := by
      ext y
      simp [MulAut.congr_apply]
    obtain ⟨σ, F, hF, μ, hμ, hQF, hind⟩ :=
      KCOrthogonalAut.exists_semilin_of_mem_matrixProjectiveImage _ hd (MulAut.congr φ g)
        (by rw [hback]; exact hgE)
    exact ⟨σ, F, hF, μ, hμ, hQF, hind⟩
  obtain ⟨G, hGO, hGg⟩ := exists_isometry_of_inducedBySemilinear hK hsemi
  have h1 := orth2_eq_one_of_isometry_two hK hQ hT h8 (isElemAbelian_map_three _ hD)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective]; exact hcard)
    (map_congr_le_innerAut φ hDinn) (innerAut_le_map_congr φ hH) hg' hGO
    (fun y => by obtain ⟨_, h⟩ := hGg y; exact h)
  exact (MulAut.congr φ).injective (h1.trans (map_one _).symm)

theorem d4two_innerPlaneBalance (hK : Nat.card K = 2) :
    InnerPlaneBalance 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have hp : Nat.Prime 3 := Nat.prime_three
  intro D hDinn hD hcard H hH
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  set E := matrixProjectiveImage (coordinateQuadPlus 4 K) with hEdef
  set P := projectivePointFamily (coordinateQuadPlus 4 K) with hPdef
  set X := plusCX 4 K with hXdef
  set X' := plusCXstar 4 K (by norm_num) with hX'def
  set O := MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) P
    with hOdef
  have hmemE : ∀ δ, δ ∈ E ↔ δ • P = P :=
    CFSG.SeitzReduction.OmegaPilot.mem_image_iff_smul_pointFamily le_rfl
  have hsub : O ⊆ {P, X, X'} := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  have hXX' : X ≠ X' := CFSG.SeitzReduction.OmegaPilot.plusCX_ne_plusCXstar 4 K (by norm_num)
  obtain ⟨d₁, hd₁, hd₁1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : D = ⊥ := eq_bot_iff.2 fun d hd => (Subgroup.mem_bot).2 (hall d hd)
    rw [this, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hgk : Nat.Coprime 3 (orderOf g) := coprime_orderOf_of_mem_localDeltaIn hp hg hd₁ hd₁1
  have hO13 : O.ncard = 1 ∨ O.ncard = 3 :=
    CFSG.SeitzReduction.OmegaPilot.orbit_pointFamily_ncard_four (K := K)
  rcases hO13 with h1 | h3
  ·
    have hall : ∀ δ, δ ∈ E := by
      intro δ
      rw [hmemE]
      have hPO : P ∈ O := MulAction.mem_orbit_self P
      have hδO : δ • P ∈ O := MulAction.mem_orbit P δ
      obtain ⟨Y, hY⟩ := Set.ncard_eq_one.1 h1
      rw [hY, Set.mem_singleton_iff] at hPO hδO
      exact hδO.trans hPO.symm
    exact d4two_plane_eq_one_of_mem_image hK hD hcard hDinn hH hg (hall g)
  have hO3 : O = {P, X, X'} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h3]; exact ncard_triple_le P X X')
  have hPX : P ≠ X := fun h => by
    have h4 := h3
    rw [hO3, ← h, Set.insert_eq_of_mem (Set.mem_insert P _)] at h4
    have := Set.ncard_insert_le P ({X'} : Set _)
    rw [Set.ncard_singleton] at this
    omega
  have hPX' : P ≠ X' := fun h => by
    have h4 := h3
    rw [hO3, ← h, Set.insert_comm, Set.insert_eq_of_mem (Set.mem_singleton P)] at h4
    have := Set.ncard_insert_le X ({P} : Set _)
    rw [Set.ncard_singleton] at this
    omega
  have hgO : ∀ Y ∈ O, g • Y ∈ O := fun Y hY => by
    obtain ⟨β, rfl⟩ := hY
    exact ⟨g * β, mul_smul _ _ _⟩
  have hmem3 : ∀ Y ∈ O, Y = P ∨ Y = X ∨ Y = X' := fun Y hY => by
    rw [hO3] at hY
    simpa using hY
  have hPO : P ∈ O := MulAction.mem_orbit_self P
  have hXO : X ∈ O := by rw [hO3]; simp
  have hX'O : X' ∈ O := by rw [hO3]; simp
  obtain ⟨Y, hYO, hgY⟩ : ∃ Y ∈ O, g • Y = Y := by
    rcases exists_fixed_of_three hgk hPX hPX' hXX' (hmem3 _ (hgO _ hPO))
        (hmem3 _ (hgO _ hXO)) (hmem3 _ (hgO _ hX'O)) with h | h | h
    · exact ⟨P, hPO, h⟩
    · exact ⟨X, hXO, h⟩
    · exact ⟨X', hX'O, h⟩
  obtain ⟨β, rfl⟩ := hYO
  have hg'E : β⁻¹ * g * β⁻¹⁻¹ ∈ E := by
    rw [hmemE, inv_inv, mul_smul, mul_smul]
    change β⁻¹ • g • β • P = P
    rw [hgY, inv_smul_smul]
  have hg' := conj_mem_localDeltaIn_map β⁻¹ hg
  have hD' : D.map (MulAut.conj β⁻¹).toMonoidHom ≤
      innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨t, rfl⟩ := hDinn hd
    refine ⟨β⁻¹ t, ?_⟩
    change MulAut.conj (β⁻¹ t) = β⁻¹ * MulAut.conj t * β⁻¹⁻¹
    rw [CFSG.SeitzReduction.OmegaPilot.mul_conj_mul_inv]
  have hH' : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤
      H.map (MulAut.conj β⁻¹).toMonoidHom := by
    rintro _ ⟨t, rfl⟩
    refine ⟨MulAut.conj (β t), hH ⟨_, rfl⟩, ?_⟩
    change β⁻¹ * MulAut.conj (β t) * β⁻¹⁻¹ = MulAut.conj t
    rw [CFSG.SeitzReduction.OmegaPilot.mul_conj_mul_inv, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
  have h1 := d4two_plane_eq_one_of_mem_image hK (isElemAbelian_map_three _ hD)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj β⁻¹).injective]; exact hcard)
    hD' hH' hg' hg'E
  have h2 : g = β⁻¹⁻¹ * (β⁻¹ * g * β⁻¹⁻¹) * β⁻¹ := by group
  rw [h2, h1, mul_one, inv_mul_cancel]

end D4

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
