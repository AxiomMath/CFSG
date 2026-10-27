module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3UniModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form
open CFSG.LieType.BorelTits

theorem concA_of_twistedA {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {r : ℕ} (hr : r = 5 ∨ r = 6) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.twistedA r Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r Q, hv⟩).Group)
    (h3 : 3 ∣ Q.card - 1) : S267ConcA 3 S B := by
  obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv e
  haveI : Fact Q.p.Prime := ⟨hp⟩
  haveI : CharP K Q.p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  have hp2 : Q.p ≠ 2 := hQq ▸ H.two
  have hp3 : Q.p ≠ 3 := hQq ▸ H.three
  have h31 : 3 ∣ Q.p ^ Q.exponent - 1 := by rwa [TauCeti.PrimePower.card_def] at h3
  have hQ5 : 5 ≤ Q.p ^ Q.exponent :=
    (hp.five_le_of_ne_two_of_ne_three hp2 hp3).trans (Nat.le_self_pow Q.exponent_pos.ne' _)
  have hnot : ∀ x : ℕ, 3 ∣ x - 1 → 3 ∣ x + 1 → 1 ≤ x → False := by
    intro x h1 h2 h0
    omega
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    have hM : Nonempty (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedSU (r + 1) (Q.p ^ Q.exponent) K)) ≃*
          Multiplicative (ZMod (Nat.gcd (r + 1) (Q.p ^ Q.exponent + 1)))) := by
      rcases hr with rfl | rfl
      · exact (CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier hK (by decide)
          (by norm_num) (by omega)).2
      · exact (CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hK hf hn
          (by decide) hq).2
    obtain ⟨eM⟩ := hM
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro hd
    exact hnot _ h31 (hd.trans (Nat.gcd_dvd_right _ _)) (by omega)
  have hcast : ∀ n : ℕ, n.Prime → Q.p ≠ n → ((n : ℕ) : K) ≠ 0 := fun n hn' hne h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hn').1 ((CharP.cast_eq_zero_iff K Q.p n).1 h))
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast hcast 2 Nat.prime_two hp2
  have h3K : (3 : K) ≠ 0 := by exact_mod_cast hcast 3 Nat.prime_three hp3
  set a : K := -(2 : K)⁻¹ with ha_def
  have ha : 2 * a + 1 = 0 := by
    rw [ha_def, mul_neg, mul_inv_cancel₀ h2K, neg_add_cancel]
  have hσa : unitaryInvolution K Q.p Q.exponent a = a := by
    rw [ha_def, map_neg, map_inv₀, map_ofNat]
  have hc0 : (1 : K) - a * a ≠ 0 := by
    intro h
    apply h3K
    have e3 : (3 : K) = 4 * (1 - a * a) := by linear_combination (2 * a - 1) * ha
    rw [e3, h, mul_zero]
  have hσc : unitaryInvolution K Q.p Q.exponent (1 - a * a) = 1 - a * a := by
    rw [map_sub, map_one, map_mul, hσa]
  obtain ⟨b, hb⟩ := exists_norm_eq_of_fixed hK hσc hc0
  obtain ⟨l, hl, hl2⟩ := exists_norm_one_sq_ne_one hK (by omega)
  have hcard : Fintype.card (Lin.Top (Fin (r - 5))) = Fintype.card (Fin (r + 1)) := by
    simp only [Lin.Top, Lin.Kap, Lin.Lam, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ
    ((projEquiv hK (Fin (r - 5)) ha hσa hb hl hl2 h3K (Fintype.equivOfCardEq hcard)).trans
      e₁.symm)
  have hk : CFSG.Open.IsQuasisimple
      ↥(suOn (unitaryInvolution K Q.p Q.exponent) (Lin.Kap (Fin (r - 5)))) :=
    isQuasisimple_suOn hK hQ5 (by simp [Lin.Kap, Lin.Lam, Fintype.card_sum])
  have hl' : CFSG.Open.IsQuasisimple
      ↥(suOn (unitaryInvolution K Q.p Q.exponent) (Lin.Lam (Fin (r - 5)))) :=
    isQuasisimple_suOn hK hQ5 (by simp [Lin.Lam, Fintype.card_sum])
  exact concA_of_modelA H hZ φ hφ hφS
    ((uniData hK (Fin (r - 5)) ha hσa hb hl hl2 h3K).modelA h3K h2K hk hl'
      (noThree_uniData hK (Fin (r - 5)) ha hσa hb hl hl2 h3K h31))

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Uni

end
