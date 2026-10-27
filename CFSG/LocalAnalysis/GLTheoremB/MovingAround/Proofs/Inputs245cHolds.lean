module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245c
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenG23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245c

open TauCeti CFSG.Blueprint CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank
  CFSG.SectionRank.Native

theorem coverX0_of_check {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op} {D : CpSpec}
    [hp : Fact D.p.Prime] (hp2 : D.p ≠ 2) (h : cpCheck O sA sB nregs prog D = true)
    (hNF : D.noFun = true) (hNA : cpNoAlt D = true) {Y : Type} [Group Y]
    (e : (NativeSporadic.seedMonoid c d 1 sA sB)ˣ ≃* Y) : CoverX0 Y D.p :=
  coverX0_of_mulEquiv e (coverX0_of_coverPointDatumA hp.out hp2
    (coverPointDatumA_of_check Sp hp.out hp2 h hNF hNA))

section McL

open CFSG.AGLEmbedding.R3.McLThree

theorem coverX0_McL
    (hs : IsSimpleGroup (CFSGIndex.sporadic .McL).Group) :
    CoverX0 (CFSGIndex.sporadic .McL).Group 3 := by
  haveI : IsSimpleGroup SporadicName.McL.Group := hs
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL
  exact coverX0_of_mulEquiv b.symm (coverX0_of_coverPointDatumA (Y := NativeSporadic.McL)
    Nat.prime_three (by norm_num)
    (coverPointDatumA_of_check (spec3 21) (D := cpSpec) Nat.prime_three
      (by show (3 : ℕ) ≠ 2; norm_num) Certificates.certificate9417.2.1
      Certificates.certificate9417.2.2 (by decide +kernel)))

end McL

section Suz

open CFSG.AGLEmbedding.R3.SuzThree

theorem coverX0_Suz :
    CoverX0 (CFSGIndex.sporadic .Suz).Group 3 := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Suz ≃* (CFSGIndex.sporadic .Suz).Group) :=
    CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  exact coverX0_of_mulEquiv b (coverX0_of_coverPointDatumA (Y := NativeSporadic.Suz)
    Nat.prime_three (by norm_num)
    (coverPointDatumA_of_check (spec3 64) (D := cpSpec) Nat.prime_three
      (by show (3 : ℕ) ≠ 2; norm_num) Certificates.certificate9500.2.1
      Certificates.certificate9500.2.2 (by decide +kernel)))

end Suz

section Fi22

open CFSG.AGLEmbedding.R3.Fi22Three

theorem coverX0_Fi22 :
    CoverX0 (CFSGIndex.sporadic .Fi22).Group 3 := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Fi22 ≃* (CFSGIndex.sporadic .Fi22).Group) :=
    CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact coverX0_of_mulEquiv b (coverX0_of_coverPointDatumA (Y := NativeSporadic.Fi22)
    Nat.prime_three (by norm_num)
    (coverPointDatumA_of_check (spec3 77) (D := cpSpec) Nat.prime_three
      (by show (3 : ℕ) ≠ 2; norm_num) Certificates.certificate9501.2.1
      Certificates.certificate9501.2.2 (by decide +kernel)))

end Fi22

section Fi24

open CFSG.AGLEmbedding.R3.Fi24Three

theorem coverX0_Fi24 :
    CoverX0 (CFSGIndex.sporadic .Fi24Prime).Group 3 := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Fi24Prime ≃* (CFSGIndex.sporadic .Fi24Prime).Group) :=
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  exact coverX0_of_mulEquiv b (coverX0_of_coverPointDatumA (Y := NativeSporadic.Fi24prime)
    Nat.prime_three (by norm_num)
    (coverPointDatumA_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) (D := cpSpec)
      Nat.prime_three (by show (3 : ℕ) ≠ 2; norm_num) cpCheck_Fi24 noFun_Fi24
      (by decide +kernel)))

end Fi24

section O73

open CFSG.AGLEmbedding.R3.O73Three
open CFSG.RankThree.PartOne.N143.O7 (modelEquiv)

theorem coverX0_O73 :
    ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.card = 3 →
      CoverX0 (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group 3 := by
  intro q hv hq
  have hdvd : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  have hp2 : q.p ≠ 2 := by omega
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl
    (G := (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) (MulEquiv.refl _)
  obtain ⟨-, F, _, _, hF3, ⟨eF⟩⟩ := hmodel
  have hF : Nat.card F = 3 := by rw [hF3, ← PrimePower.card_def]; exact hq
  have : Fact (Nat.Prime CFSG.AGLEmbedding.R3.O73Three.cpSpec.p) := ⟨by show Nat.Prime 3; norm_num⟩
  exact coverX0_of_check (spec3 7) (D := CFSG.AGLEmbedding.R3.O73Three.cpSpec)
    (by show (3 : ℕ) ≠ 2; norm_num) Certificates.certificate9438.1
    Certificates.certificate9438.2 (by decide +kernel)
    (CFSG.AGLEmbedding.KFactProofs.ThreeWeak.O73.seedEquivO73.trans
      (eF.trans (modelEquiv hF)).symm)

end O73

section G23

open CFSG.RankThree.PartTwo.Census CFSG.RankThree.PartTwo.Census.Carrier

theorem coverX0_G23 :
    ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.card = 3 →
      CoverX0 (CFSGIndex.lie ⟨.G2 q, hv⟩).Group 3 := by
  intro q hv hq
  have hdvd : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by rw [hp3]; norm_num) (ZMod 3)
    (by rw [Nat.card_zmod, hq])
  let e := (CFSG.AGLEmbedding.KFactProofs.ThreeWeak.seedEquivG2 (RingEquiv.refl (ZMod 3))).trans
    ((adjointQuotientG2Equiv (ZMod 3)).symm.trans b)
  have : Fact (Nat.Prime R3.G23Three.cpSpec.p) := ⟨by show Nat.Prime 3; norm_num⟩
  exact coverX0_of_check (spec3 14) (D := R3.G23Three.cpSpec) (by show (3 : ℕ) ≠ 2; norm_num)
    Certificates.certificate9436.1 Certificates.certificate9436.2.1 (by decide +kernel) e

end G23

@[expose] def U43CoverX0 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 3 →
    CoverX0 (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group 3

theorem u43CoverX0_of_coverPointDatumA
    (h : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 3 →
      CoverPointDatumA (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group 3) : U43CoverX0 :=
  fun q hv hq => coverX0_of_coverPointDatumA Nat.prime_three (by norm_num) (h q hv hq)

section Assembly


theorem threeCoverX0Table_of_u43 (hU43 : U43CoverX0) : ThreeCoverX0Table :=
  threeCoverX0Table_of coverX0_McL (fun _ => coverX0_Suz) (fun _ => coverX0_Fi22)
    (fun _ => coverX0_Fi24) (fun q hv hq _ => hU43 q hv hq) (fun q hv hq _ => coverX0_O73 q hv hq)
    (fun q hv hq _ => coverX0_G23 q hv hq)

theorem input24_5_compCover_of_u43 (hU43 : U43CoverX0) : Inputs245b.Input24_5_compCover :=
  input24_5_compCover_of_table (threeCoverX0Table_of_u43 hU43)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245c
