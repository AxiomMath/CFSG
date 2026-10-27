module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZB2
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YC6
public import CFSG.ClassicalInvolution.Asc77.AscT8ZA3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY
open CFSG.ClassicalInvolution.RouteD.Gaps (InvOf)

namespace T8ZZ

variable {p f : ℕ} [Fact p.Prime]


theorem layerCenterFact_proved : LayerCenterFact p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne hnconn F
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := T8.card_layerQuot_lt (Ω := Ω) (T8.zt_not_central hs)
  have hΨ := T8.hypOmegaMod_layerQuot hp hq hΩ hx
  have hinj : Function.Injective
      (fun i : Fin 3 => T8.layerImg Ω (z * t) (F.ρ i.castSucc).K) := by
    intro i j h
    by_contra hij
    exact frame_layerImg_ne hs F (fun h' => hij (Fin.castSucc_injective _ h')) h
  obtain ⟨e, ⟨M⟩⟩ := T8X.exists_spin8_datum_of_triangle hn hlt hp hq hΨ
    (CFSG.ComponentClassification.OddCore.quotient_corefree _) (T8.omegaGen_layerFamQ Ω _)
    (T8.noTwins_layerQuot hp hq hΩ hnt hx)
    (fun i : Fin 3 => T8.layerImg Ω (z * t) (F.ρ i.castSucc).K)
    (fun i => T8.layerImg_mem (frame_xMem hs F _)) hinj
    (fun i j hij => frame_layerImg_nbr hs F (fun h' => hij (Fin.castSucc_injective _ h')))
    hnconn
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = f := M.exp_eq_f hD4
  have hF : PlusModelFacts p e := by
    rw [he]
    exact plusModelFacts hp hq
  have hrep : ∀ i : Fin 4, ∃ Ri ∈ M.cls, T8.layerImg Ω (z * t) (F.ρ i).K = Ri.map M.ψ :=
    fun i => (M.mem_iff _).mp (T8.layerImg_mem (frame_xMem hs F i))
  choose Rs hRs hRsψ using hrep
  have hlift : ∀ i : Fin 4, ∃ ζ, InvOf (Rs i) ζ ∧
      M.ψ ζ = T8V.layerMk (z * t) (F.zz i) (frame_zz_mem_layerJoin hs F i) := by
    intro i
    refine datum_exists_involution_lift M hF (hRs i) ?_
    rw [← hRsψ i]
    exact frame_isUniqueInvolution_layerImg hs F i
  choose ζ hζ hζψ using hlift
  have hcomm : ∀ i j : Fin 4, i ≠ j → Commutes (Rs i) (Rs j) := by
    intro i j hij
    have hadj : (Rs j).map M.ψ ∈
        omegaNbr (T8.layerFamQ Ω (z * t)) ((Rs i).map M.ψ) := by
      rw [← hRsψ i, ← hRsψ j]
      exact frame_layerImg_nbr hs F hij
    exact ((M.muTab_omegaNbr_iff hΨ hp hq hG2 hD4 (hRs i) (hRs j)).mp hadj).2
  have hprod : ∀ i j : Fin 4, i ≠ j →
      T8V.layerMk (z * t) (F.zz i) (frame_zz_mem_layerJoin hs F i) *
        T8V.layerMk (z * t) (F.zz j) (frame_zz_mem_layerJoin hs F j) ∈
          Subgroup.center (T8.LayerQuot Ω (z * t)) := by
    intro i j hij
    have h := datum_mul_mem_center M hF (hRs i) (hRs j) (hcomm i j hij) (hζ i) (hζ j)
    rwa [hζψ i, hζψ j] at h
  exact layerCenter_of_central hs F (hprod 0 1 (by decide)) (hprod 0 2 (by decide))
    (datum_card_center_le M hF)

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
