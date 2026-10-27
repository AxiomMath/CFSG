module

public import CFSG.ClassicalInvolution.Asc77.AscT8YA1
import CFSG.ClassicalInvolution.Asc77.AscT8YAEng
public import CFSG.ClassicalInvolution.Asc77.AscT8YB4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem alphaOf_odd [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    T8T.hyp51Tri_proved p f G Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃ hs.stand hnt hF
      (by simpa using hind)
  have hc01 : z * t = t * z := hF.comm hp hΩ 0 1
  exact alphaOf_oddE F hnt hF hHyp hc01

theorem layerJoin_le_sigmaNorm_of_lift (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K₀ : Subgroup G} (hK : T8.XMem Ω x K₀)
    (hO : oddCoreOf (T8.layerJoin Ω x) ≤ sigmaNorm Ω K₀)
    (hconn : DConnected (T8.layerFamQ Ω x)) : T8.layerJoin Ω x ≤ sigmaNorm Ω K₀ := by
  refine iSup₂_le fun L hL => ?_
  obtain ⟨K', hK', rfl⟩ := hL
  obtain ⟨ν, hν, hνK⟩ := T8.exists_oddCore_conj_mem_dComp hp hq hΩ hx hK hconn hK'
  have hle : conjSub ν K' ≤ sigmaNorm Ω K₀ :=
    Subgroup.le_normalizer.trans (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK.1 hνK)
  have hνN : ν ∈ sigmaNorm Ω K₀ := hO hν
  intro y hy
  have hyK : y ∈ K' := T8.layerRes_le x K' hy
  have h1 : ν * y * ν⁻¹ ∈ sigmaNorm Ω K₀ :=
    hle (mem_conjSub_iff.mpr (by simpa [mul_assoc] using hyK))
  have h2 := (sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).inv_mem hνN) h1)
    hνN
  simpa [mul_assoc] using h2

theorem false_of_caseA_uniform [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hconn : DConnected (T8.layerFamQ Ω (z * t)))
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      DConnected (T8.layerFamQ Ω (z * s))) : False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hN := sigmaNorm_le_normalizer_alpha hs hframe
  have hH : T8.H274 Ω K z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
      centralizer_le_normalizer_alpha_of_nbr hs hμ hne hdisc hframe hN hM hs' (huni M hM s hs'))
  have htop : T8.H274 Ω K z = ⊤ := h274_eq_top hs hdisc hμ hne
  rw [htop, top_le_iff] at hH
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH
  have hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hodd := alphaOf_odd hs hμ hne
      have hz := hs.hz
      have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
      have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hY : oddCoreOf (T8.layerJoin Ω (z * t)) ≤ sigmaNorm Ω K :=
    T8.oddCoreOf_layerJoin_le_of_alpha hs hα
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hY1 : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K :=
    layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hY hconn
  have hC : Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K :=
    T8.centralizer_le_sigmaNorm_of_layerJoin_le hs hY1
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hM := F.mgrp_le_centralizer c 0 1
  rw [F.hz0, F.hz1] at hM
  exact mgrp_not_le_sigmaNorm hs hne (hM.trans hC)

end T8YY

end CFSG.ClassicalInvolution.Asc77
