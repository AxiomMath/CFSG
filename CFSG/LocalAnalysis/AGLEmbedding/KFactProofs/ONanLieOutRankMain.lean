module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankPlane
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankSU
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.RankThree.PartOne.S11d.PlaneCases
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OddOutPSL2
import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms

theorem IsOuterPlane.sq_dvd_card_outer {p : ℕ} {X : Type*} [Group X] [Finite X]
    {R : Subgroup (MulAut X)} (hR : IsOuterPlane p R) : p ^ 2 ∣ Nat.card (Outer X) := by
  obtain ⟨-, hcard, hRI⟩ := hR
  set f : R →* Outer X := (QuotientGroup.mk' (inner X)).comp R.subtype with hf
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : MulAut X) ∈ inner X := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : MulAut X) ∈ R ⊓ Inn X := ⟨x.2, h1⟩
    rw [hRI] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h2))
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have h1 : Nat.card R = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← hcard, h1]
  exact Subgroup.card_subgroup_dvd_card _


theorem IsOuterPlane.false_g2 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hd : q.p = 2) {X : Type} [Group X] [Finite X]
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) {p : ℕ} (hp : p.Prime)
    {R : Subgroup (MulAut X)} (hR : IsOuterPlane p R) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
    (GaloisField q.p q.exponent) hK
  have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard' : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
  have hch : CFSG.Blueprint.ChevalleyExceptionalModel X
      CFSG.Assembly.LowTwoRank.StatedLieTag.G2 2 q.exponent :=
    ⟨⟨Nat.prime_two, q.exponent_pos, rfl, by rw [← hcard']; exact hq3⟩,
      GaloisField q.p q.exponent, inferInstance, inferInstance, by rw [hK, hcard'],
      ⟨e.trans b.symm⟩⟩
  exact PlaneCases.no_plane_of_outPChain hp (outPNice_G2 hp hch).toChain R hR.1 hR.2.1 hR.2.2

section Main

open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem kFactLieOutRank : KFactLieOutRank := by
  intro Y _ _ L J hL hcl hpar hJL hnB p hp hp5 E hEN hE hcard hdisj
  obtain ⟨hJLle, T, hT, hNJ⟩ := hpar
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have : Group.IsPerfect ↥L := CFSG.AGLEmbedding.OutElemRank.isPerfect_of_quasisimple hLq
  obtain ⟨R, hR⟩ := exists_outerPlane hEN hE hcard hdisj
  have hp2 : p ≠ 2 := by omega
  have noPlane : OutPChain p (↥L ⧸ Subgroup.center ↥L) → False := fun hch =>
    PlaneCases.no_plane_of_outPChain hp hch R hR.1 hR.2.1 hR.2.2
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hd] at h
      by_cases hr : r = 1
      · subst hr
        exact (noPlane (outPNice_PSL_two hp h).toChain).elim
      · have hn : 3 ≤ r + 1 := by
          have := h.1.2.2.1
          omega
        exact exists_quasisimple_psl hT hNJ hJLle hnB hp hp5 h (hR.sq_dvd_psl hp hp5 hn h)
    | twistedA r q =>
      change q.p = 2 at hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hd] at h
      exact exists_quasisimple_psu hT hNJ hJLle hnB hp hp5 h (hR.sq_dvd_psu hp hp5 h)
    | B r q =>
      change q.p = 2 at hd
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      by_cases h2 : r = 2
      · subst h2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rw [hd] at h
        exact (noPlane (outPNice_PSp_two hp h).toChain).elim
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
          (by omega) e
        rw [hd] at h
        exact (noPlane (outPNice_PSp_ge_three_odd hp hp2 (by omega) h).toChain).elim
    | C r q => exact hd.elim
    | D r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
      rw [hd] at h
      by_cases h4 : r = 4
      · subst h4
        exact (noPlane (outPChain_POmegaPlus_four_gen hp hp5 h)).elim
      · have h5 : 5 ≤ r := by
          have := h.1.2.2
          omega
        exact (noPlane (outPNice_POmegaPlus_gen_ge_five hp hp5 h5 h).toChain).elim
    | twistedD r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
      rw [hd] at h
      exact (noPlane (outPNice_POmegaMinus_gen hp hp5 h).toChain).elim
    | G2 q =>
      change q.p = 2 at hd
      exact (hR.false_g2 hv hd e hp).elim
    | _ => exact hd.elim
  · have hn5 : 5 ≤ n := by rcases hn with rfl | rfl | rfl <;> norm_num
    have hout : Nat.card (Outer (↥L ⧸ Subgroup.center ↥L)) ≤ 4 :=
      (Nat.card_congr (equivalence e).toEquiv).trans_le
        (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn5)
    have hle := Nat.le_of_dvd Nat.card_pos hR.sq_dvd_card_outer
    nlinarith
  · rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      have hq' := (Nat.Prime.pow_eq_iff Nat.prime_seven).1
        (by rw [← TauCeti.PrimePower.card_def]; exact hq)
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hq'.1, hq'.2] at h
      exact (noPlane (outPNice_PSL_two_odd hp (by omega) (by norm_num) h).toChain).elim
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      have hq' := (Nat.Prime.pow_eq_iff Nat.prime_three).1
        (by rw [← TauCeti.PrimePower.card_def]; exact hq)
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hq'.1, hq'.2] at h
      obtain ⟨hdvd, -⟩ := hR.dvd_psu hp hp2 (by omega) h
      have : Nat.gcd (2 + 1) (3 ^ 1 + 1) = 1 := by norm_num
      rw [this] at hdvd
      exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)

end Main

end CFSG.AGLEmbedding.LieOut
