module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp2Pair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem SP2.card_mulAut_dvd_j1
    (F : Type) [Group F] (hF : NativeSporadic.IsSporadic F .J1) :
    Nat.card (MulAut F) ∣ 175560 := by
  obtain ⟨e₀⟩ := hF
  let e : F ≃* NativeSporadic.J1 := e₀
  rw [Nat.card_congr (MulAut.congr e).toEquiv, ← CFSG.Sporadic.J1.card_J1]
  refine Subgroup.card_dvd_of_surjective
    (f := (MulAut.conj : NativeSporadic.J1 →* MulAut NativeSporadic.J1)) fun φ => ?_
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Schreier.at_j1_schreier.2.1 φ
  exact ⟨g, hg.symm⟩

set_option linter.unusedSectionVars false


theorem leaf_j1 {n : ℕ} : NoTwinS n fun F _ => NativeSporadic.IsSporadic F .J1 := by
  intro Y _ _ R S t h _ hF
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨f, hf⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.embedsAut_mulAut _ Y
    (genFittingFStar Y) ⟨MulEquiv.refl _⟩ hC
  have hY : Nat.card Y ∣ 175560 :=
    (Subgroup.card_dvd_of_injective f hf).trans (SP2.card_mulAut_dvd_j1 _ hF)
  have h16 := (SP2.sixteen_dvd_card_of_perp h).trans hY
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
