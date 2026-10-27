module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
import CFSG.Quasithin.EmptyFaithful.T1521SU3Cen
import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase
import CFSG.HardMathSupport.Dickson.I271.Support.CyclicRank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeF4Target
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims138
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi24Seven
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmRank1
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzSurvivor
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ListRankOne

open CFSG.Open
open scoped commutatorElement

variable {S : Type} [Group S] [Finite S]

theorem pRank_subgroup_eq {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {p : ℕ} (hp : 1 < p)
    (e : ↥K ≃* S) : Open.pRank p K = Open.pRank p (⊤ : Subgroup S) := by
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp e]

theorem linTwo {p : ℕ} {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = p)
    (h2 : 2 ≤ q.exponent) (hd : d.1 = .A 1 q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    2 ≤ Open.pRank p (⊤ : Subgroup S) := by
  subst hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨b⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) ⟨q, hd, rfl, rfl⟩
  have h := CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 q.exponent_pos (e.trans b)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

theorem unitary {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.p = p) (hd : d.1 = .twistedA 2 q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .twistedA 2 q := hd
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  subst hq
  by_cases hp2 : q.p = 2
  · have hn : 2 ≤ q.exponent := by
      have h3 := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
      rw [TauCeti.PrimePower.card_def, hp2] at h3
      have := q.exponent_pos
      by_contra hlt
      obtain h1 : q.exponent = 1 := by omega
      rw [h1] at h3
      norm_num at h3
    rw [hp2] at hC ⊢
    have hL : CFSG.Quasithin.IsPSU 3 2 q.exponent ↥(⊤ : Subgroup S) := by
      obtain ⟨hadm, K, h1, h2, h3, ⟨f⟩⟩ := hC
      exact ⟨hadm, K, h1, h2, h3, ⟨Subgroup.topEquiv.trans f⟩⟩
    obtain ⟨R, hR⟩ := CFSG.HardMathSupport.Cooperstein.StructureLie.exists_isSylowTwoOf
      (⊤ : Subgroup S)
    obtain ⟨Z, -, hZ, hcard, -⟩ := CFSG.Quasithin.U31521.exists_center_u3 hn hL hR
    exact CFSG.LocalAnalysis.RankFourTheoremC.le_pRank_of_isElemAbelian Nat.prime_two le_top hZ
      (by rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hn)
  · obtain ⟨-, hf, h⟩ := CFSG.SectionRank.classical_model_rank hp2 hC
    rcases h with ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · omega
    · omega
    · exact absurd h (by decide)
    · omega

theorem spFour {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsSpFourIndex p d)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain ⟨q, ⟨hq, h1, hdq⟩ | ⟨rfl, hq2, h1, hdq⟩⟩ := hd
  · simp only at hdq
    subst hdq hq
    have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    have hp2 : q.p ≠ 2 := by
      intro hp2
      have := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      rw [TauCeti.LieTypeIndex.inStandardRange_iff] at this
      exact this.2 ⟨rfl, by rw [TauCeti.PrimePower.card_def, hp2, h1]; norm_num⟩
    obtain ⟨-, hf, h⟩ := CFSG.SectionRank.classical_model_rank hp2 hC
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
    · omega
    · omega
  · simp only at hdq
    subst hdq
    exact CFSG.AGLEmbedding.two_le_pRank_three_unitaryFour q hq2 h1 hv e

theorem linThree {p : ℕ} {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = p)
    (h1 : q.exponent = 1) (hd : d.1 = .A 2 q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    2 ≤ Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .A 2 q := hd
  subst hq
  have hp2 : q.p ≠ 2 := by
    intro hp2
    have := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at this
    exact this (Or.inr (Or.inl ⟨rfl, by rw [TauCeti.PrimePower.card_def, hp2, h1]; norm_num⟩))
  obtain ⟨-, hC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_A 2 q hv e
  · obtain ⟨-, hf, h⟩ := CFSG.SectionRank.classical_model_rank hp2 hC
    rcases h with ⟨-, ⟨h, -⟩ | ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · omega
    · omega
    · omega
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
  · omega

theorem linThreeFour {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hq : q.exponent = 2) (hd : d.1 = .A 2 q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .A 2 q := hd
  obtain ⟨-, hC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_A 2 q hv e
  · exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psl_three_of_dvd hC
      (by rw [hq2, hq]; norm_num)
  · omega

section Certified


theorem reeGTwo {d : TauCeti.ValidLieTypeIndex} {m : ℕ} (hd : d.1 = .reeG2 m)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .reeG2 m := hd
  exact CFSG.HardMathSupport.Dickson.I271.reeG2_two_le_pRank CFSG.TauCetiBridge.reeG2Bridge m hv e

theorem gTwo {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hd : d.1 = .G2 q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .G2 q := hd
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_G2 hv e

theorem bTwo {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hd : d.1 = .B 2 q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .B 2 q := hd
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_B2 hv e

theorem bThree {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hq : q.exponent = 1) (hd : d.1 = .B 3 q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .B 3 q := hd
  exact CFSG.AGLEmbedding.two_le_pRank_three_typeB 3 le_rfl q hq2 hq hv e

theorem titsThree {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .tits := hd
  exact CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_of_titsModel
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)

theorem titsFive {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 5 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .tits := hd
  have h := CFSG.RankThree.Chevalley.two_le_pRank_five_of_titsModel
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h

theorem reeFFour {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 5 (⊤ : Subgroup S) := by
  have hX := CFSG.AGLEmbedding.reeTitsModel_of_catGroup_reeF4 hd
  obtain ⟨a, K, _, _, _, -, hfa, hK, ⟨f⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
  obtain rfl : a = 2 := by omega
  obtain ⟨E, hE, hc⟩ := CFSG.AGLEmbedding.exists_elemAbelian_twentyfive_reeGamma (K := K) hK
  let g : S ≃* _ := e.trans f
  exact CFSG.LocalAnalysis.RankFourTheoremC.le_pRank_of_isElemAbelian Nat.prime_five
    (le_top : E.map g.symm.toMonoidHom ≤ ⊤) (hE.map _)
    (by rw [Subgroup.card_map_of_injective g.symm.injective, hc])

end Certified

theorem altThree {n : ℕ} (hn : 6 ≤ n) (e : S ≃* alternatingGroup (Fin n)) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  have h := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_of_alternating hn e
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h

theorem altTen (e : S ≃* alternatingGroup (Fin 10)) : 2 ≤ Open.pRank 5 (⊤ : Subgroup S) :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims138.le_pRank_of_mulEquiv_alt Nat.prime_five
    (by norm_num) (Subgroup.topEquiv.trans e)

theorem of_cubic {X : Type} [Group X] {r : ℕ} (hr : r.Prime) (e : S ≃* X) {x y : X}
    (hx : x ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    2 ≤ Open.pRank r (⊤ : Subgroup S) := by
  haveI : Finite X := Finite.of_equiv S e.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.RankThree.ThinCatalog.two_le_pRank_of_cubic_witness hr hx hz1 hzx hzy

theorem of_carrier_cubic {s : TauCeti.SporadicName} {r : ℕ} (hr : r.Prime)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    (hW : ∃ x y : CFSG.Blueprint.NativeSporadic.Carrier s, x ^ r = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : 2 ≤ Open.pRank r (⊤ : Subgroup S) := by
  obtain ⟨b⟩ := hbr
  obtain ⟨x, y, hx, hz, hzx, hzy⟩ := hW
  exact of_cubic hr (e.trans b.symm) hx hz hzx hzy

theorem of_carrier_elem {s : TauCeti.SporadicName} {r k : ℕ} (hr : r.Prime)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    (hE : ∃ E : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier s), IsElemAbelian r E ∧
      Nat.card E = r ^ k)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : k ≤ Open.pRank r (⊤ : Subgroup S) := by
  obtain ⟨b⟩ := hbr
  obtain ⟨E, hE, hc⟩ := hE
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) :=
    Finite.of_equiv S (e.trans b.symm).toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (e.trans b.symm)]
  exact CFSG.LocalAnalysis.RankFourTheoremC.le_pRank_of_isElemAbelian hr le_top hE hc.ge

theorem of_noncommPair {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : CFSG.RankThree.PartOne.StrongP.HasNoncommPair r X) :
    2 ≤ Open.pRank r (⊤ : Subgroup X) := by
  obtain ⟨x, y, -, -, hxy, hP⟩ := h
  by_contra hlt
  have hle : Open.pRank r (Subgroup.closure ({x, y} : Set X)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (by omega)
  have hc := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm.isCyclic_of_pRank_le_one hr hr2 hP
    hle
  have hcomm := (IsCyclic.commGroup (α := ↥(Subgroup.closure ({x, y} : Set X)))).mul_comm
    ⟨x, Subgroup.subset_closure (by simp)⟩ ⟨y, Subgroup.subset_closure (by simp)⟩
  exact hxy (congrArg Subtype.val hcomm)

theorem of_carrier_noncomm {s : TauCeti.SporadicName} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    (hN : CFSG.RankThree.PartOne.StrongP.HasNoncommPair r (CFSG.Blueprint.NativeSporadic.Carrier s))
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : 2 ≤ Open.pRank r (⊤ : Subgroup S) := by
  obtain ⟨b⟩ := hbr
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) :=
    Finite.of_equiv S (e.trans b.symm).toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (e.trans b.symm)]
  exact of_noncommPair hr hr2 hN

theorem sporThree
    {s : TauCeti.SporadicName} (hs : s = .M11 ∨ s = .M12 ∨ s = .J3)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  rcases hs with rfl | rfl | rfl
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
    have h := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_M11 (e.trans b.symm)
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    have h := CFSG.QuasithinUnique.Vol2Native.two_le_pRank_three_M12 (e.trans b.symm)
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  · have h := of_carrier_elem (s := .J3) (k := 3) Nat.prime_three
      CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv CFSG.SectionRank.J3_elementary_three_rank_three e
    omega

theorem sporFive
    {s : TauCeti.SporadicName} (hs : s = .McL ∨ s = .HS ∨ s = .Ru)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : 2 ≤ Open.pRank 5 (⊤ : Subgroup S) := by
  rcases hs with rfl | rfl | rfl
  · exact of_carrier_noncomm (s := .McL) Nat.prime_five (by norm_num)
      CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv CFSG.RankThree.PartOne.CTP.hasNoncommPair_McL e
  · refine of_carrier_cubic (s := .HS) Nat.prime_five CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
      ?_ e
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
    exact ⟨x, y, hx, hz, hzx, hzy⟩
  · refine of_carrier_cubic (s := .Ru) Nat.prime_five CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
      ?_ e
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
    exact ⟨x, y, hx, hz, hzx, hzy⟩

theorem sporSeven
    {s : TauCeti.SporadicName} (hs : s = .ONan ∨ s = .Fi24Prime ∨ s = .He)
    (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : 2 ≤ Open.pRank 7 (⊤ : Subgroup S) := by
  have h7 : Nat.Prime 7 := by norm_num
  rcases hs with rfl | rfl | rfl
  · exact of_carrier_noncomm (s := .ONan) h7 (by norm_num)
      CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv CFSG.RankThree.PartOne.CTP.hasNoncommPair_ON e
  · refine of_carrier_cubic (s := .Fi24Prime) h7 CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv ?_ e
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ :=
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi24prime_sylow7_cubic_witness
    exact ⟨x, y, hx, hz, hzx, hzy⟩
  · refine of_carrier_cubic (s := .He) h7 CFSG.Sporadic.Bridge.He.nonempty_mulEquiv ?_ e
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
    exact ⟨x, y, hx, hz, hzx, hzy⟩

theorem sporEleven
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) : 2 ≤ Open.pRank 11 (⊤ : Subgroup S) := by
  refine of_carrier_cubic (s := .J4) (by norm_num) CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv ?_ e
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
  exact ⟨x, y, hx, hz, hzx, hzy⟩

theorem prod {L : Type} [Group L] {p : ℕ} (hp : p.Prime) (e : S ≃* L × L) {x : L}
    (hx : orderOf x = p) : 2 ≤ Open.pRank p (⊤ : Subgroup S) := by
  haveI : Finite (L × L) := Finite.of_equiv S e.toEquiv
  have h := CFSG.two_le_pRank_of_commute_independent (P := L × L) hp
    (e₁ := ((x, 1) : L × L)) (e₂ := ((1, x) : L × L))
    (Commute.prod (Commute.one_right x) (Commute.one_left x))
    (Prod.ext (by simp [← hx, pow_orderOf_eq_one]) (by simp))
    (Prod.ext (by simp) (by simp [← hx, pow_orderOf_eq_one])) (fun i j hij => by
      have h1 := congrArg Prod.fst hij
      have h2 := congrArg Prod.snd hij
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, one_zpow, mul_one,
        one_mul, Prod.fst_one, Prod.snd_one] at h1 h2
      rw [← hx]
      exact ⟨orderOf_dvd_iff_zpow_eq_one.mpr h1, orderOf_dvd_iff_zpow_eq_one.mpr h2⟩)
  rwa [← CFSG.pRank_congr_of_mulEquiv e p, CFSG.SectionRank.pRank_eq_open_pRank_top] at h

theorem exists_orderOf_of_prod {L : Type} [Group L] {p : ℕ} (hp : p.Prime) (e : S ≃* L × L)
    (h : ∀ [Finite L], p ∣ Nat.card L) : ∃ x : L, orderOf x = p := by
  haveI : Finite (L × L) := Finite.of_equiv S e.toEquiv
  haveI : Finite L := Finite.of_injective (fun g : L => (g, (1 : L))) (fun a b h => by
    simpa using congrArg Prod.fst h)
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' p h

end CFSG.LocalAnalysis.RankThreeTheoremC.ListRankOne

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.ListRankOne

theorem kFactNineThreeListRankOne_holds :
    KFactNineThreeListRankOne := by
  intro p Y _ _ K hlist hrk
  have hK : 1 < p → 2 ≤ Open.pRank p (⊤ : Subgroup ↥K) → False := fun hp h => by
    rw [pRank_subgroup_eq hp (MulEquiv.refl _)] at hrk
    omega
  rcases hlist with ⟨i, hi, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating n hn =>
      exfalso
      rcases hi with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
      · exact hK (by norm_num) (altThree (by norm_num) e)
      · exact hK (by norm_num) (altThree (by norm_num) e)
      · exact hK (by norm_num) (altTen e)
    | sporadic s =>
      exfalso
      rcases hi with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
      · exact hK (by norm_num) (sporThree hs e)
      · exact hK (by norm_num) (sporFive hs e)
      · exact hK (by norm_num) (sporSeven hs e)
      · exact hK (by norm_num) (sporEleven e)
    | lie d =>
      rcases hi with ⟨q, hq, h2, hdq⟩ | ⟨q, hq, hdq⟩ | hsp | ⟨q, hq, h1, hdq⟩ | ⟨rfl, m, hm⟩ |
        ⟨rfl, (⟨q, hq2, hq3, hdq | hdq | hdq⟩ | ⟨q, hq2, hq2', hdq⟩ | ⟨q, hq2, hq1, hdq⟩ |
          hdt)⟩ | ⟨rfl, hdt | hdt | hdt⟩
      · exact (hK (hq ▸ q.prime_p.one_lt) (linTwo hq h2 hdq e)).elim
      · exact (hK (hq ▸ q.prime_p.one_lt) (unitary hq hdq e)).elim
      · have hp : 1 < p := by
          obtain ⟨q, ⟨hq, -⟩ | ⟨rfl, -⟩⟩ := hsp
          · exact hq ▸ q.prime_p.one_lt
          · norm_num
        exact (hK hp (spFour hsp e)).elim
      · exact (hK (hq ▸ q.prime_p.one_lt) (linThree hq h1 hdq e)).elim
      · exact (hK (by norm_num) (reeGTwo hm e)).elim
      · exact ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hdq⟩, ⟨e⟩⟩
      · exact (hK (by norm_num) (gTwo hdq e)).elim
      · exact (hK (by norm_num) (bTwo hdq e)).elim
      · exact (hK (by norm_num) (linThreeFour hq2 hq2' hdq e)).elim
      · exact (hK (by norm_num) (bThree hq2 hq1 hdq e)).elim
      · exact (hK (by norm_num) (titsThree hdt e)).elim
      · exact ⟨d, Or.inr ⟨rfl, hdt⟩, ⟨e⟩⟩
      · exact (hK (by norm_num) (titsFive hdt e)).elim
      · exact (hK (by norm_num) (reeFFour hdt e)).elim
  · exfalso
    rcases hd with ⟨rfl, q, hq2, hq3, hdq⟩ | ⟨rfl, hdq⟩
    · obtain ⟨x, hx⟩ := exists_orderOf_of_prod Nat.prime_three e (fun {_} =>
        (dvd_pow_self 3 two_ne_zero).trans
          (CFSG.AGLEmbeddingD2.linTwoEight_data d q hq2 hq3 hdq (MulEquiv.refl _)).1)
      exact hK (by norm_num) (prod Nat.prime_three e hx)
    · obtain ⟨dd, hv⟩ := d
      obtain rfl : dd = .suzuki 2 := hdq
      obtain ⟨x, hx⟩ := exists_orderOf_of_prod Nat.prime_five e (fun {_} =>
        CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.five_dvd_card_of_suzukiModel
          (CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 ⟨hv, ⟨MulEquiv.refl _⟩⟩))
      exact hK (by norm_num) (prod Nat.prime_five e hx)

end CFSG.LocalAnalysis.RankThreeTheoremC
