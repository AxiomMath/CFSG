module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Sign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOField

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.U (barEq map_bar_fmap)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL orthComponentData OrthNF
  signMat)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem iotaF_signGL {d : ℕ} (M : Finset (Fin d)) :
    iotaF h (signGL h.fixedField M) = signGL K M := by
  apply Units.ext
  rw [coe_iotaF, coe_signGL, coe_signGL, signMat, signMat, diagonal_map (map_zero _)]
  congr 1
  funext i
  split_ifs <;> simp

theorem field_false (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {wF : Fin (2 * 4) → h.fixedField}
    (hwF : OrthNF wF)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1))))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1)))))}
    (hs : Sit (oQ (diagGL (wK_ne_zero h hwF.1))) B (oκ _ (barPair h h2 hwF.1)) y) : False := by
  have := h.finite
  have : CharP K p := h.charP
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hF2 := two_ne_zero_fixedField h hp2
  have h2F : (2 : h.fixedField) ≠ 0 := Ring.two_ne_zero hF2
  have hw := wK_ne_zero h hwF.1
  obtain ⟨I, hI3, -, hIw⟩ := hwF.2
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < I.card)
  have hHeq := matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose _)
  have hF₀H := omegaF_le h h2 hwF.1
  set φ := (matrixDerivedConjugation (oQ (diagGL hw)) (barPair h h2 hwF.1)).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ (diagGL hw)),
      (((φ Y : matrixDerived _) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
        ((Y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map h.bar := by
    intro Y
    change ((matrixDerivedConjugation _ (barPair h h2 hwF.1) Y : matrixDerived _) :
      GL (Fin (2 * 4)) K).val = _
    rw [matrixDerivedConjugation_val, barPair_left, barPair_right, inv_one, mul_one, one_mul]
    rfl
  have hcd : CompData (omegaF h hwF.1) :=
    CompData.map (orthComponentData hF2 (by norm_num) (diagGL hwF.1) (diagGL_transpose hwF.1)
      (by omega)) (iotaF_injective h)
  have hfix : ∀ X (hX : X ∈ omegaF h hwF.1), y (projH _ ⟨X, hF₀H hX⟩) = projH _ ⟨X, hF₀H hX⟩ := by
    intro X hX
    refine fix_of_compData hs.inj hs.inn φ (fun Y => kappa_lift _ Y) hF₀H (fun X hX => ?_)
      (fun g hg X hX => ?_) hcd hs.core hX
    · obtain ⟨X', -, rfl⟩ := hX
      apply Subtype.ext
      apply Units.ext
      rw [hφc]
      change ((iotaF h X' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map h.bar =
        ((iotaF h X' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      rw [coe_iotaF, map_bar_fmap]
    · have hc' : ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map h.bar =
          (1 : K) • ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
        rw [one_smul, ← hφc, hg]
      have hgI : (g : GL (Fin (2 * 4)) K) ∈ CatalogueBGraphForm.isometryGroup (2 * 4) K
          (diagGL hw) := Subgroup.commutator_le_self _ (by rw [← hHeq]; exact g.2)
      exact conj_mem_omegaF h hwF.1 hgI hc' hX
  have hmemF : ∀ {i j : Fin (2 * 4)}, i ∈ I → j ∈ I → i ≠ j →
      signGL K {i, j} ∈ omegaF h hwF.1 := by
    intro i j hi hj hij
    refine ⟨signGL h.fixedField {i, j}, ?_, iotaF_signGL h _⟩
    rw [← matrixDerived_oQ h2F (diagGL hwF.1) (diagGL_transpose _)]
    exact signGL_pair_mem_derived h2F hwF.1 hij (hIw i hi j hj)
  exact klein_false hw hK hs hab hbc hac (hF₀H (hmemF ha hb hab)) (hF₀H (hmemF hb hc hbc))
    (hfix _ (hmemF ha hb hab)) (hfix _ (hmemF hb hc hbc))

end CFSG.ComponentClassification.Burgoyne.D4
