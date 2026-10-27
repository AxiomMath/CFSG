module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.OddOrder.ExponentComplementCyclicHallAction
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson

universe u

theorem FNI_nonregular_plane_line_unique_centralizer
    (h₁ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_core_disjoint.{u}) :
    Statements.FNI_nonregular_plane_line_unique_centralizer.{u} := by
  intro G _ _ hG p M A E X hAplane hE hAE hXE hXcard hCSX
  have := hG.isSimpleGroup
  have hp : p.Prime := hAplane.prime
  have hXbot : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hXcard
    exact hp.one_lt.ne hXcard
  have hXp : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hNX : normalizer (X : Set G) < ⊤ :=
    normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hXbot hXp
  have hCXtop : centralizer (X : Set G) ≠ ⊤ := fun h =>
    hNX.ne (top_le_iff.1 (h ▸ centralizer_le_normalizer (X : Set G)))
  obtain ⟨-, hlines, -, -, -⟩ := h₁ G hG p M A E hAplane hE hAE
  have hXA : X ≤ A := hlines X hXE hXcard
  have := hAplane.isElementaryAbelianPlane.isMulCommutative
  have hACX : A ≤ centralizer (X : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun x hx => setLike_mul_comm (hXA hx) ha
  have key : ∀ L : Subgroup G, IsCoatom L → centralizer (X : Set G) ≤ L → L = M := by
    intro L hL hCL
    by_contra hLM
    have hbot : sigmaCore M ⊓ L = ⊥ := h₂ G hG p M A L hAplane hL hLM (hACX.trans hCL)
    exact hCSX (le_bot_iff.1 (hbot ▸ inf_le_inf_left _ hCL))
  obtain ⟨L, hL, hCL⟩ := exists_isCoatom_ge_of_ne_top hCXtop
  have hCXM : centralizer (X : Set G) ≤ M := key L hL hCL ▸ hCL
  refine ⟨⟨hAplane.isCoatom, hCXM, fun N hN hCN => key N hN hCN⟩, fun g hg => ?_⟩
  have hgX : MulAut.conj g • X = X := mem_normalizer_iff_conj_smul_eq.1 hg
  have hconj : MulAut.conj g • centralizer (X : Set G) = centralizer (X : Set G) := by
    rw [← centralizer_conj_smul, hgX]
  have hfix : MulAut.conj g • M = M :=
    key _ (isCoatom_conj_smul hAplane.isCoatom g) (by rw [← hconj]; exact smul_mono_right _ hCXM)
  exact normalizer_coe_eq_of_isCoatom hG.not_isMulCommutative hAplane.isCoatom ▸
    mem_normalizer_iff_conj_smul_eq.2 hfix

end

end CFSG.FeitThompson.Proofs
