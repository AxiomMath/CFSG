module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.Bal209TwoSLOBIn
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRank
import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdList
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Count

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (Bal209TwoInnerCompType IsLieQuot
  Bal209TwoIndex)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.RankThree.PartTwo.Sec4.Census (TripleCoverLieIndex)

theorem QSCfg.false_of_twoLocal_five {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (hc : QSCfg 3 S B T x D K) (hB : Nat.card B ≤ 3 ^ 5)
    {E : Subgroup ↥S} (hE : IsElemAbelian 3 E) (h5 : 3 ^ 5 ≤ Nat.card E)
    (hZ : E ⊓ Subgroup.center ↥S = ⊥) (hTL : T171S.TwoLocal E) : False := by
  obtain ⟨P, hP2, hP1, hEP⟩ := hTL
  set E' : Subgroup Ω := E.map S.subtype with hE'
  set Zx : Subgroup Ω := Subgroup.zpowers x with hZx
  have hZc : Zx ≤ Subgroup.center Ω :=
    Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 hc.xcen)
  have hinf : E' ⊓ Zx = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨e, he, rfl⟩, ha⟩
    have hec : e ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hZc ha) g)
    have he1 : e ∈ E ⊓ Subgroup.center ↥S := ⟨he, hec⟩
    rw [hZ, Subgroup.mem_bot] at he1
    rw [Subgroup.mem_bot, he1, map_one]
  have hxel : IsElemAbelian 3 Zx := by
    rw [hZx, Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a rfl b rfl
      rfl
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hc.elem.2 x hc.xB
  have hcard : Nat.card ↥(E' ⊔ Zx) = Nat.card E * 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E' Zx
      (hZc.trans (Subgroup.center_le_normalizer _)) (disjoint_iff.2 hinf), hE',
      Subgroup.card_map_of_injective S.subtype_injective, hZx, Nat.card_zpowers,
      orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1]
  have hFel : IsElemAbelian 3 (E' ⊔ Zx) :=
    (hE.map S.subtype).sup_of_commute hxel fun a _ b hb => Subgroup.mem_center_iff.1 (hZc hb) a
  have hPne : P.map S.subtype ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective P S.subtype_injective).1 h)
  have hFN : E' ⊔ Zx ≤ Subgroup.normalizer ((P.map S.subtype : Subgroup Ω) : Set Ω) :=
    sup_le ((Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map S.subtype))
      (hZc.trans (Subgroup.center_le_normalizer _))
  have hle := GL83.PiGen.card_le_pow_twoLocalRank hFel (hP2.map S.subtype) hPne hFN
  rw [hcard] at hle
  have h6 : 3 ^ 5 * 3 ≤ 3 ^ 5 :=
    ((Nat.mul_le_mul_right 3 h5).trans hle).trans (hc.rank.trans hB)
  norm_num at h6

theorem QSCfg.false_of_lieWit (hGA : GriessAllModelsStatement) {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (hc : QSCfg 3 S B T x D K)
    (hB : Nat.card B ≤ 3 ^ 5) {d : TauCeti.ValidLieTypeIndex}
    (f : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : ¬ TripleCoverLieIndex d.1)
    (hW : ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group,
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E) : False := by
  obtain ⟨E, hE, h5, P, hP2, hP1, hEP⟩ := hW
  haveI := (chev_pSimple_simple_nonabelian Nat.prime_three hc.comp).1
  haveI := f.injective.nontrivial
  obtain ⟨eL⟩ := HStdList.centerQuot_equiv_of_pSimple hc.quasi f
  have hcop := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
    (I1431C2.cl_not_three_dvd_center hGA hc.quasi hd eL)
  have hle : Subgroup.center ↥S ≤ GLAPPrimeCore 3 ↥S := le_sSup ⟨inferInstance, hcop⟩
  have hZ : Subgroup.center ↥S = ⊥ := le_bot_iff.1 (hle.trans hc.core.le)
  let ψ : (TauCeti.CFSGIndex.lie d).Group ≃* ↥S :=
    eL.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  refine hc.false_of_twoLocal_five hB (hE.map ψ.toMonoidHom) ?_ (by rw [hZ, inf_bot_eq])
    ⟨P.map ψ.toMonoidHom, hP2.map _,
      fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective P ψ.injective).1 h),
      (Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map _)⟩
  rwa [Subgroup.card_map_of_injective ψ.injective]

private theorem lieQuot_of_twE6 {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hcomp : GLAPComponent 3 (⊤ : Subgroup Ω) S) (hS : CFSG.Open.IsQuasisimple ↥S)
    (h : catalogIs (PSimple 3 S) S9.isTE6two) : IsLieQuot ↥S Bal209TwoIndex := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  haveI := (chev_pSimple_simple_nonabelian Nat.prime_three hcomp).1
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedE6 q =>
      haveI := f.injective.nontrivial
      obtain ⟨e⟩ := HStdList.centerQuot_equiv_of_pSimple hS f
      exact ⟨⟨.twistedE6 q, hv⟩, I1431C2.cl_primePower_card_two (q := q) hi, ⟨e⟩⟩
    | _ => exact hi.elim
  | _ => exact hi.elim


theorem QSNL.false_of_twE6_u5two (hBal : Bal209TwoInnerCompType) (hLOB : LieOrderBridge)
    (hR1 : TwE6U5Inv) {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K) (hS : catalogIs (PSimple 3 S) S9.isTE6two)
    (hK : catalogIs (PSimple 3 K) S9.isU5two) (hB : Nat.card B ≤ 3 ^ 5) {d₀ : Ω} (hd₀ : d₀ ∈ D)
    (hdx : d₀ ∉ Subgroup.zpowers x) (hd3 : d₀ ^ 3 = 1)
    (hcs : S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ Subgroup.centralizer ({d₀} : Set Ω))
    (hKc : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d₀} : Set Ω)) K) : False := by
  have hc := hN.cfg
  obtain ⟨hDB, -, -, -, -, hKcomp, -⟩ := hc.std
  by_cases hin : ∃ k ∈ S, k⁻¹ * d₀ ∈ Subgroup.centralizer (S : Set Ω)
  ·
    have hdS : d₀ ∉ Subgroup.centralizer (S : Set Ω) := fun h =>
      hdx ((hc.centB d₀ (hDB hd₀)).1 (CFSG.LocalAnalysis.GLTheoremA.centMod_of_mem_centralizer h))
    obtain ⟨⟨e, hv⟩, he, ⟨g⟩⟩ := hBal Ω S d₀ hc.quasi (lieQuot_of_twE6 hc.comp hc.quasi hS)
      hd3 hdS hin K hKc
    have h13 := CatDistinct.card_isU5two hLOB hK
    haveI : Nontrivial (PSimple 3 K) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [h13]; norm_num)
    obtain ⟨φ⟩ := HStdList.centerQuot_equiv_of_pSimple hKcomp.2.2 (MulEquiv.refl (PSimple 3 K))
    have hord : Nat.card (PSimple 3 K) = lieOrderFormula e :=
      (Nat.card_congr φ.toEquiv).symm.trans (hLOB ⟨e, hv⟩ _ ⟨g⟩)
    rw [h13] at hord
    cases e with
    | twistedA r q =>
      obtain ⟨⟨hp, hq⟩, rfl⟩ := he
      rw [show lieOrderFormula (.twistedA 5 q) = orderTwistedA 5 q.card from rfl,
        TauCeti.PrimePower.card_def, hp, hq] at hord
      exact absurd hord (by decide +kernel)
    | D r q =>
      obtain ⟨⟨hp, hq⟩, rfl⟩ := he
      rw [show lieOrderFormula (.D 4 q) = orderD 4 q.card from rfl,
        TauCeti.PrimePower.card_def, hp, hq] at hord
      exact absurd hord (by decide +kernel)
    | _ => exact he.elim
  ·
    have hdN : d₀ ∈ Subgroup.normalizer (S : Set Ω) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hc.normal]
      exact Subgroup.mem_top d₀
    obtain ⟨t, htd, htK, ht2⟩ := hR1 Ω S d₀ hc.quasi hc.core hS hdN hd3 hin K hKc hK
    have htD : t ∈ S ⊓ Subgroup.centralizer (D : Set Ω) := by
      rw [hcs]
      exact htd
    obtain ⟨E, hEDK, hE, hE6⟩ := hN.exists_elem_six (Or.inl hK)
    have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers t : Set Ω) :=
      (hEDK.trans (sup_le (Subgroup.le_centralizer_iff.1 (Subgroup.zpowers_le.2 htD.2))
        (Subgroup.le_centralizer_iff.1 (Subgroup.zpowers_le.2 htK)))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hU2 : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
    have hU1 : Subgroup.zpowers t ≠ ⊥ := fun h =>
      absurd ht2 (by rw [Subgroup.zpowers_eq_bot.1 h, orderOf_one]; norm_num)
    have h6 := (hE6.trans (GL83.PiGen.card_le_pow_twoLocalRank hE hU2 hU1 hEN)).trans
      (hc.rank.trans hB)
    norm_num at h6

end CFSG.LocalAnalysis.GLTheoremA.S265

end
