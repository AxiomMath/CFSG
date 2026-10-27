module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CarrierFactsProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.BigPrimes
public import Certificates.Certificate129040
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFischer
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22DoubleCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22TripleCover

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.F3.Native CFSG.Sporadic.Fi22 CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving (bigPrimeFacts_of_ne_M)

@[expose] def NoIrrFFOffenderCenterThree (Y : Type) [Group Y] : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L →
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn L →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Y) → Nat.card (Subgroup.center ↥L) = 3 →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
        Nat.card E * Nat.card (fixV E) < Nat.card W

@[expose] def Fi22CenterThree : Prop :=
  NoIrrFFOffenderCenterThree (TauCeti.CFSGIndex.sporadic .Fi22).Group

theorem noIrrFFOffenderCenterThree_transfer {Y Y' : Type} [Group Y] [Group Y']
    (h : NoIrrFFOffenderCenterThree Y) (f : Nonempty (Y ≃* Y')) :
    NoIrrFFOffenderCenterThree Y' := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hZ hE hEne hEel hquad
  obtain ⟨f⟩ := f
  exact h W hW L E hq hirr ⟨e.trans f.symm⟩ hZ hE hEne hEel hquad

theorem fi22_heisCfg :
    ∃ (x y : Fin 3 → NativeSporadic.Fi22) (z : NativeSporadic.Fi22),
      HeisCfg 3 3 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  Certificates.certificate129040

theorem fi22_index_inner :
    (inner NativeSporadic.Fi22).index = 2 := by
  obtain ⟨eOut⟩ := CFSG.Monster.B.Fischer.CTUC_Fi22_full_automorphism_permutation_model.2.2.2.2.2.2.2
  have h1 : Nat.card (Outer NativeSporadic.Fi22) = Nat.card (Outer CFSG.Monster.B.Fischer.fi22P) :=
    Nat.card_congr (@equivalence NativeSporadic.Fi22 CFSG.Monster.B.Fischer.fi22P Units.instGroup _
      CFSG.Monster.B.Fischer.fi22PermEquiv).toEquiv
  have h2 : Nat.card (Outer CFSG.Monster.B.Fischer.fi22P) = 2 := by
    show Nat.card (MulAut CFSG.Monster.B.Fischer.fi22P ⧸ (MulAut.conj : _ →* _).range) = 2
    rw [Nat.card_congr eOut.toEquiv]
    simp
  exact h1.trans h2

noncomputable def fi22CarrierEquiv : NativeSporadic.Fi22 ≃* NativeSporadic.Carrier .Fi22 :=
  MulEquiv.refl _

theorem fi22_hopf_card :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (NativeSporadic.Carrier .Fi22)) = 6 :=
  nativeRow_of_two_one_three_one rfl (carrierFacts_of_ne_M _ (by decide))
    CFSG.EvenSporadicStandard.rowBound_Fi22 two_dvd_card_hopfMultiplier_Fi22 nativeCell3_Fi22
    (bigPrimeFacts_of_ne_M .Fi22 (by decide))

theorem fi22_center_dvd
    (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (he : Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.Fi22)) :
    Nat.card (Subgroup.center L) ∣ 6 := by
  obtain ⟨e⟩ := he
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans fi22CarrierEquiv)
  rwa [fi22_hopf_card] at h

private theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

theorem eq_one_or_three_of_odd_dvd_six {n : ℕ} (hodd : Odd n) (hn : n ∣ 6) : n = 1 ∨ n = 3 := by
  have : n ∈ Nat.divisors 6 := by simp [hn]
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [h6] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hodd (by decide)
  · exact Or.inr rfl
  · exact absurd hodd (by decide)

theorem noIrrFFOffender_Fi22_native_of_three
    (h3 : NoIrrFFOffenderCenterThree NativeSporadic.Fi22) :
    NoIrrFFOffender NativeSporadic.Fi22 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel hquad
  rcases eq_one_or_three_of_odd_dvd_six (odd_card_center_of_isIrrOn hW hirr)
    (fi22_center_dvd ↥L hq ⟨e⟩) with h1 | hZ3
  · obtain ⟨x, y, z, h, hy⟩ := fi22_heisCfg
    refine exclusion_of_heisCfg_of_outer hW hq hirr hEN hE hel e
      (fun B _ _ => card_le_two_mul_inf_inner_of_index fi22_index_inner B)
      (by norm_num) (by rw [h1]; norm_num) h hy ?_
    rw [h1, CFSG.Sporadic.Fi22.card_Fi22, orderOf_two_zmod_three]
    norm_num
  · exact h3 W hW L E hq hirr ⟨e⟩ hZ3 hEN hE hel hquad

theorem noIrrFFOffender_Fi22_of_three
    (h3 : Fi22CenterThree) :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Fi22).Group :=
  noIrrFFOffender_transfer
    (noIrrFFOffender_Fi22_native_of_three
      (noIrrFFOffenderCenterThree_transfer h3 (CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv.map
        MulEquiv.symm)))
    CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Fi22_of_three
    (h3 : Fi22CenterThree) :
    GF2NoFFSporadicFor .Fi22 :=
  gf2NoFFSporadicFor_of_noIrrFFOffender (noIrrFFOffender_Fi22_of_three h3)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
