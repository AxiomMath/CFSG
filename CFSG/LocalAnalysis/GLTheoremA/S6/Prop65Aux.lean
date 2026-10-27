module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.GL83PartI.I_33
import CFSG.RankThree.GF2n.Tim78Normal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ}

namespace P65

theorem mem_normalizer_glaPLayer {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  have key : GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
    refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g)
  rw [mem_normalizer_iff_gLBConj_eq, ← key, gLBConj_eq_of_mem_normalizer hg]

theorem le_normalizer_glaPLayer {X B : Subgroup G} (hB : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (GLAPLayer p X : Set G) := fun _ hg => mem_normalizer_glaPLayer (hB hg)

theorem glaPLayer_le_self (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hL => (show GLAPComponent p X _ from hL).1

theorem coversMod_of_le {N J : Subgroup G} (h : J ≤ N) : CoversMod p N J := by
  unfold CoversMod
  rw [inf_eq_right.2 h]
  exact sup_eq_left.2 (Subgroup.map_subtype_le _)


theorem mem_of_bmax_centralizes (hp : p.Prime) {B U : Subgroup G} {x : G} (hB : GLAIsBmax p B)
    (hxp : x ^ p = 1) (hBx : B ≤ Subgroup.centralizer ({x} : Set G)) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUx : U ≤ Subgroup.centralizer ({x} : Set G)) (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    x ∈ B := by
  have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have h : Commute a x := Subgroup.mem_centralizer_singleton_iff.1 (hBx ha)
    exact (h.zpow_right k).eq
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers x) :=
    IsElemAbelian.sup_of_commute hB.1 (CFSG.Open.isElemAbelian_zpowers hxp) hcomm
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hUx hu)
  have hEq := GLAIsBmax.eq_of_le hp hB le_sup_left hE hU hU2 (sup_le hBU hxN)
  rw [← hEq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem centModEqZpowers_of_cycMod (hp : p.Prime) {B L : Subgroup G} {x : G} (hB : IsElemAbelian p B)
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hcyc : CycModSylow p L) :
    CentModEqZpowers p B L x := by
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hxcm : Subgroup.zpowers x ≤ centModSubgroup p L :=
    Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer hxL))
  intro b hb
  constructor
  · intro hbL
    set D := Subgroup.zpowers x ⊔ Subgroup.zpowers b with hDdef
    have hDB : D ≤ B := sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hb)
    have hDexp : ∀ d ∈ D, d ^ p = 1 := fun d hd => hB.2 d (hDB hd)
    have hDcm : D ≤ centModSubgroup p L := sup_le hxcm (Subgroup.zpowers_le.2 (centMod_iff.1 hbL))
    have hDp : IsPGroup p D := isPGroup_of_isElemAbelian (isElemAbelian_mono hB hDB)
    have hcycD : IsCyclic D := hcyc D (fun g hg => centMod_iff.2 (hDcm hg)) hDp
    exact mem_zpowers_of_card_sup_le hp hxp hx1 (card_le_of_isCyclic_of_pow hp hcycD hDexp)
  · intro hbx
    exact centMod_iff.2 (hxcm hbx)


structure DJData (p q : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) : Prop where
  le_B : D ≤ B
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  mem_x : x ∈ D
  inD : InD p B x L D J
  comp : GLAPComponent p (Subgroup.centralizer (D : Set G)) J
  jtype : JType p q J
  omega : Case34 p q B x L → IsOmegaType p q J

theorem card_sup_zpowers (hp : p.Prime) {x y : G} (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (hxy : x * y = y * x) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 := by
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((show Commute y x from hxy.symm).symm.zpow_left k).eq
  have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
  have hcx : Nat.card (Subgroup.zpowers x) = p := card_zpowers_eq_of_pow hp hxp hx1
  have hcy : Nat.card (Subgroup.zpowers y) = p := card_zpowers_eq_of_pow hp hyp hy1
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    by_contra hne
    apply hyx
    have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y := inf_le_right
    have hge : Subgroup.zpowers y ≤ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).ge
      have hpos : 0 < Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) := Nat.card_pos
      have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) ∣ p := by
        rw [← hcy]; exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exfalso; apply hne; rw [Subgroup.eq_bot_iff_card]; exact h
      · rw [hcy, h]
    exact (hge (Subgroup.mem_zpowers y)).1
  rw [hinf, Subgroup.card_bot, mul_one, hcx, hcy] at h1
  rw [pow_two]
  exact h1

theorem zpowers_inf_eq_bot_of_center (hp : p.Prime) {B L : Subgroup G} {x : G}
    (hcomp : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hxB : x ∈ B)
    (hB : IsElemAbelian p B) (hx1 : x ≠ 1) (hcen : Subgroup.center (PQuot p L) = ⊥) :
    Subgroup.zpowers x ⊓ L = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hB.2 x hxB
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  by_contra hg1
  have hgp : g ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg.1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hxg : x ∈ Subgroup.zpowers g := by
    have hle : Subgroup.zpowers g ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hg.1
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_zpowers_eq_of_pow hp hxp hx1, card_zpowers_eq_of_pow hp hgp hg1])
    rw [heq]
    exact Subgroup.mem_zpowers x
  have hxL : x ∈ L := (Subgroup.zpowers_le.2 hg.2) hxg
  have hcentral : (QuotientGroup.mk (⟨x, hxL⟩ : L) : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hcomp.1 l.2))
  rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcentral
  have hxO : x ∈ GLAPPrimeCoreOf p L := ⟨⟨x, hxL⟩, hcentral, rfl⟩
  have h1 : orderOf x ∣ Nat.card (GLAPPrimeCoreOf p L) := Subgroup.orderOf_dvd_natCard _ hxO
  rw [orderOf_eq_prime hxp hx1] at h1
  exact CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf hp L h1

theorem exists_sylow_two_ne_bot (hp : p.Prime) {Y J : Subgroup G} (hJ : GLAPComponent p Y J) :
    ∃ T : Subgroup G, CFSG.Open.fusionIsSylowIn 2 T J ∧ T ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  refine ⟨(P : Subgroup J).map J.subtype, ?_, ?_⟩
  · refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, fun Q hQM hQ hSQ => ?_⟩
    have hle : (P : Subgroup J) ≤ Q.subgroupOf J := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hSQ ⟨x, hx, rfl⟩)
    have heq := P.3 (hQ.comap_subtype) hle
    rw [← heq]
    exact (Subgroup.map_subgroupOf_eq_of_le hQM).symm
  · intro hbot
    have hPbot : (P : Subgroup J) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 hbot
    have hcard : Nat.card (P : Subgroup J) = 1 := by rw [hPbot]; exact Subgroup.card_bot
    have hodd : Odd (Nat.card J) := by
      rw [Sylow.card_eq_multiplicity] at hcard
      have h0 : (Nat.card J).factorization 2 = 0 := by
        have := Nat.pow_eq_one.1 hcard
        rcases this with h | h
        · omega
        · exact h
      have hndvd : ¬ 2 ∣ Nat.card J := by
        intro hd
        have : 0 < (Nat.card J).factorization 2 :=
          Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hd
        omega
      exact Nat.odd_iff.2 (by omega)
    have hsolv : Group.IsSolvable ↥J := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
    haveI := isQuasisimple_nontrivial hq
    haveI : Group.IsSolvable (PQuot p J) :=
      inferInstanceAs (Group.IsSolvable (↥J ⧸ GLAPPrimeCore p ↥J))
    exact (IsSolvable.commutator_lt_top_of_nontrivial (PQuot p J)).ne hq.1

theorem exists_a_of_I33 (hc : S6Ctx G p) {D T : Subgroup G} {x : G} (hDel : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hxD : x ∈ D) (hx1 : x ≠ 1) (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hDT : D ≤ Subgroup.centralizer (T : Set G)) :
    ∃ a ∈ D, a ∉ Subgroup.zpowers x ∧
      (⁅D, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer ({a} : Set G)⁆ :
        Subgroup G) ≠ ⊥ := by
  have hp := hc.prime
  have hp2 := hc.odd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (T : Set G) with hM
  have hM2 : IsTwoLocal M := ⟨T, hTne, hT2, rfl⟩
  have hDM : D ≤ M := fun d hd => Subgroup.centralizer_le_normalizer _ (hDT hd)
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    have := card_le_of_isCyclic_of_pow hp hcyc (fun d hd => hDel.2 d hd)
    rw [hDcard] at this
    have h2 : p * p ≤ p := by rw [← pow_two]; exact this
    have := hp.one_lt
    nlinarith
  have hcore2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hDN : D ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := hDM.trans (le_normalizer_pCoreOf 2 M)
  obtain ⟨-, h2⟩ := GL83.I_33_1_proved G hc.charTwo p hp hp2 D (pCoreOf 2 M) hD1 hDel hcore2 hDN
    (Or.inr (Or.inl ⟨M, hM2, hDM, rfl⟩))
  obtain ⟨-, d₁, d₂, hd₁, hd₂, hd₁1, hd₂n, hne1, hne2⟩ := h2 D hD1 le_rfl hDnc
  have hxp : x ^ p = 1 := hDel.2 x hxD
  by_cases h : d₁ ∈ Subgroup.zpowers x
  · refine ⟨d₂, hd₂, fun hd₂x => hd₂n ?_, hne2⟩
    have hd1p : d₁ ^ p = 1 := hDel.2 d₁ hd₁
    have hle : Subgroup.zpowers d₁ ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 h
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_zpowers_eq_of_pow hp hxp hx1, card_zpowers_eq_of_pow hp hd1p hd₁1])
    rw [heq]
    exact hd₂x
  · exact ⟨d₁, hd₁, h, hne1⟩

theorem commutator_ne_bot_of_AxB (hp : p.Prime) (hp2 : p ≠ 2) {D T Q : Subgroup G} {a : G}
    (hDel : IsElemAbelian p D) (hQ2 : IsPGroup 2 Q) (hT2 : IsPGroup 2 T) (hTQ : T ≤ Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (haD : a ∈ D)
    (hDT : D ≤ Subgroup.centralizer (T : Set G))
    (hne : (⁅D, Q ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G) ≠ ⊥) :
    (⁅Q ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (T : Set G), D⁆ : Subgroup G) ≠ ⊥ := by
  intro hbot
  apply hne
  have hQ'2 : IsPGroup 2 (Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    hQ2.to_le inf_le_left
  have hDa : D ≤ Subgroup.centralizer ({a} : Set G) := isElemAbelian_le_centralizer hDel haD
  have hDQ' : D ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hDQ (fun g hg => Subgroup.le_normalizer (hDa hg))
  have hTa : T ≤ Subgroup.centralizer ({a} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (hDT haD) t ht)
  have hTQ' : T ≤ Q ⊓ Subgroup.centralizer ({a} : Set G) := le_inf hTQ hTa
  have hle : Q ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (T : Set G) ≤
      Subgroup.centralizer (D : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hcodd : Odd (orderOf c) := by
    have hdvd : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one (hDel.2 c hc)
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  have key := CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hQ'2 hT2 (hDQ' hc)
    (fun t ht => Subgroup.le_normalizer (hTQ' ht)) hcodd
    (fun b hb => (Subgroup.mem_centralizer_iff.1 (hDT hc) b hb).symm)
    (fun q hq hqT => by
      have hqT' : q ∈ Subgroup.centralizer (T : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun b hb => (hqT b hb).symm
      exact Subgroup.mem_centralizer_iff.1 (hle ⟨hq, hqT'⟩) c hc) q hq
  exact key.symm

theorem eq_sup_zpowers (hp : p.Prime) {D : Subgroup G} {a x : G} (hDel : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hxD : x ∈ D) (haD : a ∈ D) (hx1 : x ≠ 1)
    (hax : a ∉ Subgroup.zpowers x) : D = Subgroup.zpowers a ⊔ Subgroup.zpowers x := by
  have ha1 : a ≠ 1 := fun h => hax (h ▸ Subgroup.one_mem _)
  have hxa : x ∉ Subgroup.zpowers a := by
    intro hxa
    apply hax
    have hxp : x ^ p = 1 := hDel.2 x hxD
    have hap : a ^ p = 1 := hDel.2 a haD
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hxa
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_zpowers_eq_of_pow hp hxp hx1, card_zpowers_eq_of_pow hp hap ha1])
    rw [heq]
    exact Subgroup.mem_zpowers a
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers x ≤ D :=
    sup_le (Subgroup.zpowers_le.2 haD) (Subgroup.zpowers_le.2 hxD)
  have hcard := card_sup_zpowers hp (hDel.2 a haD) (hDel.2 x hxD) ha1 hx1 hxa
    (isElemAbelian_commute hDel haD hxD)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hDcard])).symm

theorem exists_S_package (hc : S6Ctx G p) {q : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hDJ : DJData p q B x L D J) (hx1 : x ≠ 1) :
    ∃ (a : G) (T S : Subgroup G), a ∈ D ∧ a ∉ Subgroup.zpowers x ∧
      D = Subgroup.zpowers a ⊔ Subgroup.zpowers x ∧ CFSG.Open.fusionIsSylowIn 2 T J ∧
      IsPGroup 2 S ∧ S ≠ ⊥ ∧ D ≤ Subgroup.normalizer (S : Set G) ∧ ⁅S, D⁆ = S ∧
      S ≤ Subgroup.centralizer ({a} : Set G) ∧ S ≤ Subgroup.centralizer (T : Set G) := by
  have hp := hc.prime
  have hp2 := hc.odd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTsyl, hTne⟩ := exists_sylow_two_ne_bot hp hDJ.comp
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hDT : D ≤ Subgroup.centralizer (T : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.1 (hDJ.comp.1 (hTsyl.1 ht)) d hd).symm
  obtain ⟨a, haD, hax, hne⟩ := exists_a_of_I33 hc hDJ.elem hDJ.card hDJ.mem_x hx1 hT2 hTne hDT
  have hDeq := eq_sup_zpowers hp hDJ.elem hDJ.card hDJ.mem_x haD hx1 hax
  set M := Subgroup.normalizer (T : Set G) with hM
  set Q := pCoreOf 2 M with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTQ : T ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT2
  have hDM : D ≤ M := fun d hd => Subgroup.centralizer_le_normalizer _ (hDT hd)
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := hDM.trans (le_normalizer_pCoreOf 2 M)
  have hDa : D ≤ Subgroup.centralizer ({a} : Set G) := isElemAbelian_le_centralizer hDJ.elem haD
  have hne' := commutator_ne_bot_of_AxB hp hp2 hDJ.elem hQ2 hT2 hTQ hDQ haD hDT hne
  set Y := Q ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (T : Set G) with hY
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_inf (le_normalizer_inf hDQ (fun g hg => Subgroup.le_normalizer (hDa hg)))
      (fun g hg => Subgroup.le_normalizer (hDT hg))
  have hSY : (⁅Y, D⁆ : Subgroup G) ≤ Y := commutator_le_left_of_normalizes hDY
  have hY2 : IsPGroup 2 Y := hQ2.to_le (inf_le_left.trans inf_le_left)
  refine ⟨a, T, ⁅Y, D⁆, haD, hax, hDeq, hTsyl, hY2.to_le hSY, hne', le_normalizer_commutator hDY
    Subgroup.le_normalizer, ?_, (hSY.trans inf_le_left).trans inf_le_right, hSY.trans inf_le_right⟩
  exact commutator_commutator_eq_of_isPGroup hp (isPGroup_of_isElemAbelian hDJ.elem) hY2 hp2 hDY


theorem closure_basic {a : G} {J B : Subgroup G} (haJ : J ≤ Subgroup.centralizer ({a} : Set G))
    (hBa : B ≤ Subgroup.centralizer ({a} : Set G)) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) :
    J ≤ closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) ∧
      closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) ≤ Subgroup.centralizer ({a} : Set G) ∧
      B ≤ Subgroup.normalizer (closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) : Set G) := by
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set La := GLAPLayer p Ca with hLa
  have hLaCa : La ≤ Ca := P65.glaPLayer_le_self Ca
  have hBLa : B ≤ Subgroup.normalizer (La : Set G) :=
    P65.le_normalizer_glaPLayer (fun g hg => Subgroup.le_normalizer (hBa hg))
  have hK : closureIn J La = ⨆ g ∈ La, GLBConj g J := closureIn_eq_iSup_gLBConj J La
  refine ⟨?_, ?_, ?_⟩
  · rw [hK]
    have := le_biSup (fun g => GLBConj g J) (Subgroup.one_mem La)
    simpa [gLBConj_one] using this
  · rw [hK]
    refine iSup₂_le fun g hg y hy => ?_
    rw [mem_gLBConj] at hy
    have h1 : g * y * g⁻¹ ∈ Ca := haJ hy
    have hg' : g ∈ Ca := hLaCa hg
    have := Ca.mul_mem (Ca.mul_mem (Ca.inv_mem hg') h1) hg'
    simpa [mul_assoc] using this
  · have key : ∀ b ∈ B, GLBConj b (closureIn J La) ≤ closureIn J La := by
      intro b hb
      rw [hK]
      have hsup : GLBConj b (⨆ g ∈ La, GLBConj g J) = ⨆ g ∈ La, GLBConj b (GLBConj g J) := by
        unfold GLBConj
        simp only [Subgroup.map_iSup]
      rw [hsup]
      refine iSup₂_le fun g hg => ?_
      have hg' : b⁻¹ * g * b ∈ La := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hBLa hb)) g).1 hg
        simpa using this
      have e : GLBConj b (GLBConj g J) = GLBConj (b⁻¹ * g * b) J := by
        rw [gLBConj_gLBConj]
        have : GLBConj (b⁻¹ * g * b) J = GLBConj (b⁻¹ * g * b) (GLBConj b J) := by
          rw [gLBConj_eq_of_mem_normalizer (hBJ hb)]
        rw [this, gLBConj_gLBConj]
        congr 1
        group
      rw [e]
      exact le_biSup (fun g => GLBConj g J) hg'
    intro b hb
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (key b hb) ?_
    have h2 := gLBConj_mono (g := b) (key b⁻¹ (B.inv_mem hb))
    rwa [gLBConj_gLBConj_inv] at h2

theorem closure_single_or_multi (hp : p.Prime) (hI18 : Input18_3_4) {a x : G} {B D J : Subgroup G}
    (hCa : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)))
    (hDeq : D = Subgroup.zpowers a ⊔ Subgroup.zpowers x) (hDB : D ≤ B) (hB : IsElemAbelian p B)
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J)
    (hBK : B ≤ Subgroup.normalizer
      (closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) : Set G)) :
    GLAPComponent p (Subgroup.centralizer ({a} : Set G))
        (closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G)))) ∨
      ∃ L₁ : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) L₁ ∧
        closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) = ⨆ b ∈ B, GLBConj b L₁ ∧
        x ∉ Subgroup.normalizer (L₁ : Set G) := by
  classical
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa'
  set La := GLAPLayer p Ca with hLa
  have hDel : IsElemAbelian p D := isElemAbelian_mono hB hDB
  have haD : a ∈ D := by
    rw [hDeq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hxD : x ∈ D := by
    rw [hDeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hDCa : D ≤ Ca := isElemAbelian_le_centralizer hDel haD
  have hCDa : Subgroup.centralizer (D : Set G) ≤ Ca :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)
  have hJ' : GLAPComponent p (Ca ⊓ Subgroup.centralizer (D : Set G)) J := by
    rw [inf_eq_right.2 hCDa]
    exact hJ
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := hI18 G Ca hCa p hp D hDCa hDel J hJ'
  have hK𝒞 : closureIn J La = ⨆ L ∈ 𝒞, L := (closureIn_eq_iSup_gLBConj J La).trans h𝒞sup.symm
  have hJK : J ≤ closureIn J La := by
    rw [closureIn_eq_iSup_gLBConj]
    have := le_biSup (fun g => GLBConj g J) (Subgroup.one_mem La)
    simpa [gLBConj_one] using this
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  obtain ⟨L₀, hL₀⟩ : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hJne
    rw [← le_bot_iff]
    calc J ≤ closureIn J La := hJK
      _ = ⊥ := by rw [hK𝒞, h]; simp
  have hLK : ∀ L ∈ 𝒞, L ≤ closureIn J La := fun L hL => hK𝒞 ▸ le_biSup (fun L => L) hL
  have haN : ∀ L ∈ 𝒞, a ∈ Subgroup.normalizer (L : Set G) := by
    intro L hL
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 ((h𝒞c L hL).1 hl)
  by_cases hall : ∀ L ∈ 𝒞, x ∈ Subgroup.normalizer (L : Set G)
  · left
    have huniq : ∀ L ∈ 𝒞, L = L₀ := by
      intro L hL
      obtain ⟨e, he, hee⟩ := h𝒞tr L hL L₀ hL₀
      have hDN : D ≤ Subgroup.normalizer (L : Set G) := by
        rw [hDeq]
        exact sup_le (Subgroup.zpowers_le.2 (haN L hL)) (Subgroup.zpowers_le.2 (hall L hL))
      rw [← hee, gLBConj_eq_of_mem_normalizer (hDN he)]
    have : closureIn J La = L₀ := by
      rw [hK𝒞]
      exact le_antisymm (iSup₂_le fun L hL => (huniq L hL).le) (le_biSup (fun L => L) hL₀)
    rw [this]
    exact h𝒞c L₀ hL₀
  · right
    push Not at hall
    obtain ⟨L₁, hL₁, hxL₁⟩ := hall
    refine ⟨L₁, h𝒞c L₁ hL₁, ?_, hxL₁⟩
    apply le_antisymm
    · rw [hK𝒞]
      refine iSup₂_le fun L hL => ?_
      obtain ⟨e, he, hee⟩ := h𝒞tr L₁ hL₁ L hL
      rw [← hee]
      exact le_biSup (fun b => GLBConj b L₁) (hDB he)
    · refine iSup₂_le fun b hb => ?_
      have h1 : GLBConj b L₁ ≤ GLBConj b (closureIn J La) := gLBConj_mono (g := b) (hLK L₁ hL₁)
      rwa [gLBConj_eq_of_mem_normalizer (hBK hb)] at h1

theorem isOmega_not_A2 (hni : LieTypeNonIsoAt) {q : ℕ} {J : Subgroup G} (h : IsOmegaType p q J)
    (h2 : ∃ Q : TauCeti.PrimePower,
      pSimpleIsLie p J (.A 2 Q) ∨ pSimpleIsLie p J (.twistedA 2 Q)) : False := by
  obtain ⟨Q', -, hQ'⟩ := h
  obtain ⟨Q, hQ⟩ := h2
  exact hni (PSimple p J) Q Q' hQ hQ'


theorem centMod_conj {K : Subgroup G} {n c : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hc : c ∈ centModSubgroup p K) : n * c * n⁻¹ ∈ centModSubgroup p K := by
  refine ⟨?_, fun l hl => ?_⟩
  · exact mul_mem (mul_mem hn hc.1) (inv_mem hn)
  · have hnO : n ∈ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
      normalizer_le_normalizer_glaPPrimeCoreOf p K hn
    have hl' : n⁻¹ * l * n ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) l).1 hl
      simpa using this
    have h1 : ⁅n⁻¹ * l * n, c⁆ ∈ GLAPPrimeCoreOf p K := hc.2 _ hl'
    have h2 : n * ⁅n⁻¹ * l * n, c⁆ * n⁻¹ ∈ GLAPPrimeCoreOf p K :=
      (Subgroup.mem_normalizer_iff.1 hnO _).1 h1
    have h3 : ⁅l, n * c * n⁻¹⁆ = n * ⁅n⁻¹ * l * n, c⁆ * n⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h3]
    exact h2

theorem le_normalizer_closureIn (I H : Subgroup G) :
    H ≤ Subgroup.normalizer (closureIn I H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_gLBConj_eq, closureIn_eq_iSup_gLBConj I H]
  have hsup : GLBConj h (⨆ g ∈ H, GLBConj g I) = ⨆ g ∈ H, GLBConj h (GLBConj g I) := by
    unfold GLBConj
    simp only [Subgroup.map_iSup]
  rw [hsup]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_biSup (fun g => GLBConj g I) (H.mul_mem hg hh)
  · refine iSup₂_le fun g hg => ?_
    have e : GLBConj g I = GLBConj h (GLBConj (g * h⁻¹) I) := by
      rw [gLBConj_gLBConj, inv_mul_cancel_right]
    rw [e]
    exact le_biSup (fun g' => GLBConj h (GLBConj g' I)) (H.mul_mem hg (H.inv_mem hh))

theorem sylow_not_le_centMod {K J T : Subgroup G} (hJK : J ≤ K) (hJ : ⁅J, J⁆ = J)
    (hJO : ¬ J ≤ GLAPPrimeCoreOf p K) (hT : CFSG.Open.fusionIsSylowIn 2 T J) :
    ¬ T ≤ centModSubgroup p K := by
  intro hTC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTJ : T ≤ J := hT.1
  set N : Subgroup G := closureIn T J with hN
  have hNe : N = ⨆ g ∈ J, GLBConj g T := closureIn_eq_iSup_gLBConj T J
  have hJnorm : J ≤ Subgroup.normalizer (K : Set G) := fun j hj => Subgroup.le_normalizer (hJK hj)
  have hNC : N ≤ centModSubgroup p K := by
    rw [hNe]
    refine iSup₂_le fun g hg y hy => ?_
    rw [mem_gLBConj] at hy
    have h1 : g * y * g⁻¹ ∈ centModSubgroup p K := hTC hy
    have := centMod_conj (inv_mem (hJnorm hg)) h1
    simpa [mul_assoc] using this
  have hNJ : N ≤ J := by
    rw [hNe]
    refine iSup₂_le fun g hg y hy => ?_
    rw [mem_gLBConj] at hy
    have h1 : g * y * g⁻¹ ∈ J := hTJ hy
    have := J.mul_mem (J.mul_mem (J.inv_mem hg) h1) hg
    simpa [mul_assoc] using this
  have hTN : T ≤ N := by
    rw [hNe]
    have := le_biSup (fun g => GLBConj g T) (Subgroup.one_mem J)
    simpa [gLBConj_one] using this
  have hNn : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).2 (le_normalizer_closureIn T J)
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 ↥J, (P : Subgroup ↥J).map J.subtype = T := by
    obtain ⟨hSM, hS, hmax⟩ := hT
    refine ⟨⟨T.subgroupOf J, hS.comap_subtype, fun {Q} hQ hSQ => ?_⟩, ?_⟩
    · have h1 := hmax (Q.map J.subtype) (Subgroup.map_subtype_le Q) (hQ.map J.subtype)
        fun s hs => ⟨⟨s, hSM hs⟩, hSQ (show (⟨s, hSM hs⟩ : J) ∈ T.subgroupOf J from hs), rfl⟩
      rw [← h1]
      exact (Subgroup.comap_map_eq_self_of_injective J.subtype_injective Q).symm
    · exact Subgroup.map_subgroupOf_eq_of_le hSM
  have hPT : (P : Subgroup ↥J) = T.subgroupOf J := by
    rw [← hP]
    exact (Subgroup.comap_map_eq_self_of_injective J.subtype_injective _).symm
  have hle : (P : Subgroup ↥J) ≤ N.subgroupOf J := by
    rw [hPT]
    exact fun t ht => Subgroup.mem_subgroupOf.2 (hTN (Subgroup.mem_subgroupOf.1 ht))
  have hodd : Odd (N.subgroupOf J).index := by
    have hd : (N.subgroupOf J).index ∣ (P : Subgroup ↥J).index := Subgroup.index_dvd_of_le hle
    have hn : ¬ 2 ∣ (P : Subgroup ↥J).index := P.not_dvd_index
    exact Nat.odd_iff.2 (by
      by_contra h
      exact hn ((Nat.dvd_trans (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 (fun ho => h (Nat.odd_iff.1 ho)))) hd)))
  have hJperf : commutator ↥J = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    have h1 : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  haveI : (N.subgroupOf J).Normal := hNn
  have hfin : Group.IsSolvable (↥J ⧸ N.subgroupOf J) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    exact hodd
  have hQperf : commutator (↥J ⧸ N.subgroupOf J) = ⊤ := by
    have hsurj := QuotientGroup.mk'_surjective (N.subgroupOf J)
    have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥J)) (H₂ := ⊤)
      (QuotientGroup.mk' (N.subgroupOf J))
    rw [← commutator_def, hJperf, Subgroup.map_top_of_surjective _ hsurj] at h1
    rw [commutator_def]
    exact h1.symm
  have hNtop : N.subgroupOf J = ⊤ := by
    by_contra hne
    have hidx : (N.subgroupOf J).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    haveI : Nontrivial (↥J ⧸ N.subgroupOf J) := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      have h0 : (N.subgroupOf J).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have : Nat.card (↥J ⧸ N.subgroupOf J) = (N.subgroupOf J).index := rfl
      omega
    exact (IsSolvable.commutator_lt_top_of_nontrivial (↥J ⧸ N.subgroupOf J)).ne hQperf
  have hJN : J ≤ N := fun j hj => Subgroup.mem_subgroupOf.1 (hNtop ▸ Subgroup.mem_top (⟨j, hj⟩ : ↥J))
  apply hJO
  rw [← hJ]
  refine Subgroup.commutator_le.2 fun j₁ h₁ j₂ h₂ => ?_
  exact (hNC (hJN h₂)).2 j₁ (hJK h₁)

theorem mem_normalizer_of_centralizes {X K T : Subgroup G} {s : G} (hp : p.Prime)
    (hK : GLAPComponent p X K) (hTK : T ≤ K) (hT : ¬ T ≤ centModSubgroup p K)
    (hsX : s ∈ Subgroup.normalizer (X : Set G)) (hsT : s ∈ Subgroup.centralizer (T : Set G)) :
    s ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hs
  have hK' : GLAPComponent p (GLBConj s⁻¹ X) (GLBConj s⁻¹ K) := glaPComponent_gLBConj hK s⁻¹
  have hX' : GLBConj s⁻¹ X = X := gLBConj_eq_of_mem_normalizer (inv_mem hsX)
  rw [hX'] at hK'
  have hne : GLBConj s⁻¹ K ≠ K := by
    intro h
    exact hs (inv_mem_iff.1 (mem_normalizer_iff_gLBConj_eq.2 h))
  have hTK' : T ≤ GLBConj s⁻¹ K := by
    intro t ht
    rw [mem_gLBConj]
    have h1 : t * s = s * t := Subgroup.mem_centralizer_iff.1 hsT t ht
    have h2 : s⁻¹ * t * s⁻¹⁻¹ = t := by
      rw [inv_inv]
      calc s⁻¹ * t * s = s⁻¹ * (t * s) := by group
        _ = s⁻¹ * (s * t) := by rw [h1]
        _ = t := by group
    rw [h2]
    exact hTK ht
  exact hT (hTK'.trans (le_centModSubgroup_of_ne hp hK' hK hne))

theorem le_centMod_of_comm_eq {K S D : Subgroup G} (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hD : D ≤ centModSubgroup p K) (hSD : ⁅S, D⁆ = S) : S ≤ centModSubgroup p K := by
  rw [← hSD, Subgroup.commutator_le]
  intro s hs d hd
  have h1 : s * d * s⁻¹ ∈ centModSubgroup p K := centMod_conj (hSK hs) (hD hd)
  have h2 : ⁅s, d⁆ = (s * d * s⁻¹) * d⁻¹ := by
    simp only [commutatorElement_def]
  rw [h2]
  exact mul_mem h1 (inv_mem (hD hd))

theorem commutator_le_core_of_centMod {K J S : Subgroup G} (hJK : J ≤ K) (hJ : ⁅J, J⁆ = J)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hc : ⁅J, S⁆ ≤ centModSubgroup p K) :
    ⁅J, S⁆ ≤ GLAPPrimeCoreOf p K := by
  set O := GLAPPrimeCoreOf p K with hO
  have hnorm : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p K hg) o).1 ho
  have hKn : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  let W : Subgroup G :=
    { carrier := {j | j ∈ J ∧ ∀ s ∈ S, ⁅j, s⁆ ∈ O}
      one_mem' := ⟨J.one_mem, fun s _ => by simpa using O.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haJ, ha⟩ ⟨hbJ, hb⟩
        refine ⟨J.mul_mem haJ hbJ, fun s hs => ?_⟩
        have e : ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact O.mul_mem (hnorm a (hKn (hJK haJ)) _ (hb s hs)) (ha s hs)
      inv_mem' := by
        rintro a ⟨haJ, ha⟩
        refine ⟨J.inv_mem haJ, fun s hs => ?_⟩
        have e : ⁅a⁻¹, s⁆ = a⁻¹ * ⁅a, s⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hnorm a⁻¹ (hKn (K.inv_mem (hJK haJ))) _ (O.inv_mem (ha s hs))
        simpa using this }
  have hW0 : ⁅J, J⁆ ≤ W := by
    refine Subgroup.commutator_le.2 fun j₁ h₁ j₂ h₂ => ?_
    refine ⟨hJ ▸ Subgroup.commutator_mem_commutator h₁ h₂, fun s hs => ?_⟩
    have hid : ⁅s, ⁅j₁, j₂⁆⁆ = (j₁ * s) * ⁅j₂, ⁅s⁻¹, j₁⁻¹⁆⁆⁻¹ * (j₁ * s)⁻¹ *
        ((j₁ * j₂) * ⁅j₁⁻¹, ⁅j₂⁻¹, s⁆⁆⁻¹ * (j₁ * j₂)⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    have hc1 : ⁅s⁻¹, j₁⁻¹⁆ ∈ centModSubgroup p K := by
      have h1 : ⁅j₁⁻¹, s⁻¹⁆ ∈ ⁅J, S⁆ := Subgroup.commutator_mem_commutator (J.inv_mem h₁) (S.inv_mem hs)
      have h2 : ⁅s⁻¹, j₁⁻¹⁆ = ⁅j₁⁻¹, s⁻¹⁆⁻¹ := (commutatorElement_inv _ _).symm
      rw [h2]
      exact inv_mem (hc h1)
    have hc2 : ⁅j₂⁻¹, s⁆ ∈ centModSubgroup p K :=
      hc (Subgroup.commutator_mem_commutator (J.inv_mem h₂) hs)
    have ha : ⁅j₂, ⁅s⁻¹, j₁⁻¹⁆⁆ ∈ O := hc1.2 j₂ (hJK h₂)
    have hb : ⁅j₁⁻¹, ⁅j₂⁻¹, s⁆⁆ ∈ O := hc2.2 j₁⁻¹ (K.inv_mem (hJK h₁))
    have hx1 : j₁ * s ∈ Subgroup.normalizer (K : Set G) := mul_mem (hKn (hJK h₁)) (hSK hs)
    have hx2 : j₁ * j₂ ∈ Subgroup.normalizer (K : Set G) := mul_mem (hKn (hJK h₁)) (hKn (hJK h₂))
    have key : ⁅s, ⁅j₁, j₂⁆⁆ ∈ O := by
      rw [hid]
      exact O.mul_mem (hnorm _ hx1 _ (O.inv_mem ha)) (hnorm _ hx2 _ (O.inv_mem hb))
    have e : ⁅⁅j₁, j₂⁆, s⁆ = ⁅s, ⁅j₁, j₂⁆⁆⁻¹ := (commutatorElement_inv s ⁅j₁, j₂⁆).symm
    rw [e]
    exact O.inv_mem key
  have hW : J ≤ W := hJ ▸ hW0
  exact Subgroup.commutator_le.2 fun j hj s hs => (hW hj).2 s hs

section PhiC

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.PerfectAutomorphisms

noncomputable def phiC (p : ℕ) (C : Subgroup G) :
    ↥(Subgroup.normalizer (C : Set G)) →* MulAut (PSimple p C) :=
  (centerQuotientHom (PQuot p C)).comp (barAut p C)

theorem phiC_eq_one_iff (hp : p.Prime) {X C : Subgroup G} (hC : GLAPComponent p X C) {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) : phiC p C ⟨g, hg⟩ = 1 ↔ CentMod p C g := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hC
  haveI : Group.IsPerfect (PQuot p C) := ⟨hq.1⟩
  rw [centMod_iff]
  constructor
  · intro h
    have h1 : barAut p C ⟨g, hg⟩ = 1 :=
      centerQuotientHom_injective (PQuot p C) (by
        rw [map_one]
        exact h)
    refine ⟨hg, fun l hl => ?_⟩
    have h2 := congrArg (fun σ : MulAut (PQuot p C) => σ (QuotientGroup.mk ⟨l⁻¹, C.inv_mem hl⟩)) h1
    simp only [barAut_mk, MulAut.one_apply] at h2
    have h3 := QuotientGroup.eq.1 h2
    have h4 : ((g * l⁻¹ * g⁻¹)⁻¹ * l⁻¹ : G) ∈ GLAPPrimeCoreOf p C :=
      Subgroup.mem_map_of_mem C.subtype h3
    have h5 : (⁅l, g⁆ : G) = ((g * l⁻¹ * g⁻¹)⁻¹ * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h5]
    exact Subgroup.inv_mem _ h4
  · intro h
    have h1 : barAut p C ⟨g, hg⟩ = 1 := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H x =>
        simp only [barAut_mk, MulAut.one_apply]
        rw [QuotientGroup.eq]
        have hc := h.2 ((x⁻¹ : ↥C) : G) (C.inv_mem x.2)
        obtain ⟨o', ho', hoe⟩ := Subgroup.mem_map.1 hc
        have : o' = x⁻¹ * (C.normalizerMonoidHom ⟨g, hg⟩) x := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          refine hoe.trans ?_
          show ⁅((x⁻¹ : ↥C) : G), g⁆ = ((x⁻¹ : ↥C) : G) * (g * (x : G) * g⁻¹)
          simp only [commutatorElement_def, Subgroup.coe_inv]
          group
        have h6 : ((C.normalizerMonoidHom ⟨g, hg⟩) x)⁻¹ * x = o'⁻¹ := by
          rw [this]; group
        rw [h6]
        exact Subgroup.inv_mem _ ho'
    show centerQuotientHom (PQuot p C) (barAut p C ⟨g, hg⟩) = 1
    rw [h1, map_one]

theorem exists_elemAbelian_aut (hp : p.Prime) {Y B J D : Subgroup G} (hB : IsElemAbelian p B)
    (hJ : GLAPComponent p Y J) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hDB : D ≤ B)
    (hD : ∀ b ∈ B, CentMod p J b ↔ b ∈ D) (hcard : p ^ 2 * Nat.card D ≤ Nat.card B) :
    ∃ A : Subgroup (MulAut (PSimple p J)), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A := by
  let f : ↥B →* MulAut (PSimple p J) := (phiC p J).comp (Subgroup.inclusion hBJ)
  have hfker : f.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (phiC p J) ⟨b, hBJ b.2⟩ = 1 ↔ (b : G) ∈ D
    rw [phiC_eq_one_iff hp hJ (hBJ b.2)]
    exact hD b b.2
  refine ⟨f.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    show (a : MulAut (PSimple p J)) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hB x.2 y.2)
  · obtain ⟨x, hx⟩ := ha
    rw [← hx, ← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hB.2 (x : G) x.2)
    rw [this, map_one]
  · have h1 : Nat.card ↥B = Nat.card (↥B ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥B ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.ker = Nat.card D := by
      rw [hfker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
    have hDpos : 0 < Nat.card D := Nat.card_pos
    rw [h1, h2, h3] at hcard
    exact le_of_mul_le_mul_right hcard hDpos

end PhiC

theorem inf_glaPPrimeCoreOf_le (hp : p.Prime) {J K : Subgroup G} (hJK : J ≤ K) :
    J ⊓ GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p J := by
  intro y hy
  set N : Subgroup ↥J := (J ⊓ GLAPPrimeCoreOf p K).subgroupOf J with hNdef
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2)
    · have hgK : (g : G) ∈ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
        normalizer_le_normalizer_glaPPrimeCoreOf p K (Subgroup.le_normalizer (hJK g.2))
      exact (Subgroup.mem_normalizer_iff.1 hgK _).1 hn.2
  have hcard : Nat.card N = Nat.card (J ⊓ GLAPPrimeCoreOf p K : Subgroup G) := by
    have h1 : Nat.card (N.map J.subtype) = Nat.card N :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [hNdef, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
    exact h1.symm
  have hcop : Nat.Coprime p (Nat.card N) := by
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp K)
  have hNle : N ≤ GLAPPrimeCore p ↥J := le_sSup ⟨hN, hcop⟩
  exact ⟨⟨y, hy.1⟩, hNle (Subgroup.mem_subgroupOf.2 hy), rfl⟩

theorem centModEqZpowers_of_D (hp : p.Prime) {B D J K : Subgroup G} {a x : G}
    (hDeq : D = Subgroup.zpowers a ⊔ Subgroup.zpowers x) (hD : IsElemAbelian p D)
    (haK : a ∈ Subgroup.centralizer (K : Set G))
    (hxK : ¬ CentMod p K x) (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hDJ : ∀ b ∈ B, CentMod p J b → b ∈ D) : CentModEqZpowers p B K a := by
  have hxD : x ∈ D := by rw [hDeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxK (centMod_one p K)
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hacm : Subgroup.zpowers a ≤ centModSubgroup p K :=
    Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer haK))
  intro b hb
  constructor
  · intro hbK
    have hbcm : b ∈ centModSubgroup p K := centMod_iff.1 hbK
    have hbJ : CentMod p J b := by
      rw [centMod_iff]
      refine ⟨hBJ hb, fun l hl => ?_⟩
      have h1 : ⁅l, b⁆ ∈ J := by
        have : b * l⁻¹ * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hBJ hb) l⁻¹).1 (J.inv_mem hl)
        rw [commutatorElement_def]
        simpa [mul_assoc] using J.mul_mem hl this
      exact P65.inf_glaPPrimeCoreOf_le hp hJK ⟨h1, hbcm.2 l (hJK hl)⟩
    have hbD : b ∈ D := hDJ b hb hbJ
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have hc : Commute a x := isElemAbelian_commute hD (hDeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) hxD
      exact (hc.zpow_left k).eq
    rw [hDeq, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hbD
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hbD
    have hycm : y ∈ centModSubgroup p K := hacm hy
    have hzcm : z ∈ centModSubgroup p K := by
      have := mul_mem (inv_mem hycm) hbcm
      simpa using this
    by_cases hz1 : z = 1
    · subst hz1
      simpa using hy
    · exfalso
      have hzp : z ^ p = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
      have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hz
      have heq := Subgroup.eq_of_le_of_card_ge hle (by
        rw [card_zpowers_eq_of_pow hp hxp hx1, card_zpowers_eq_of_pow hp hzp hz1])
      have hxz : x ∈ Subgroup.zpowers z := by rw [heq]; exact Subgroup.mem_zpowers x
      exact hxK (centMod_iff.2 (Subgroup.zpowers_le.2 hzcm hxz))
  · intro hba
    exact centMod_iff.2 (hacm hba)

theorem exists_twoLocal_weak_cover (hp : p.Prime) (hp2 : p ≠ 2) {a : G} {D J S : Subgroup G}
    (hDel : IsElemAbelian p D) (haD : a ∈ D) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) (hDS : D ≤ Subgroup.normalizer (S : Set G))
    (hJa : J ≤ Subgroup.centralizer ({a} : Set G))
    (hcomm : ⁅J, S⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    ∃ S₀ : Subgroup G, S₀ ≠ ⊥ ∧ IsPGroup 2 S₀ ∧ D ≤ Subgroup.normalizer (S₀ : Set G) ∧
      J ≤ (Subgroup.normalizer (S₀ : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set O := GLAPPrimeCoreOf p Ca with hO
  have hOCa : O ≤ Ca := Subgroup.map_subtype_le _
  have hCaO : Ca ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p Ca)
  have hDCa : D ≤ Ca := isElemAbelian_le_centralizer hDel haD
  set H := S ⊔ O with hH
  have hSO : S ≤ Subgroup.normalizer (O : Set G) := hSa.trans hCaO
  have hDH : D ≤ Subgroup.normalizer (H : Set G) := le_normalizer_sup hDS (hDCa.trans hCaO)
  have hkey : ∀ j ∈ J, ∀ y ∈ H, j * y * j⁻¹ ∈ H := by
    intro j hj y hy
    rw [hH, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S O hSO] at hy
    obtain ⟨s, hs, o, ho, rfl⟩ := Set.mem_mul.mp hy
    have h1 : ⁅j, s⁆ ∈ O := hcomm (Subgroup.commutator_mem_commutator hj hs)
    have h2 : j * o * j⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (hCaO (hJa hj)) o).1 ho
    have e : j * (s * o) * j⁻¹ = ⁅j, s⁆ * s * (j * o * j⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem (H.mul_mem (le_sup_right (a := S) h1) (le_sup_left (b := O) hs))
      (le_sup_right (a := S) h2)
  have hJH : J ≤ Subgroup.normalizer (H : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hkey j hj y hy, fun hy => ?_⟩
    have := hkey j⁻¹ (J.inv_mem hj) _ hy
    simpa [mul_assoc] using this
  have hHp : ¬ p ∣ Nat.card H := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := S) hSO
    rw [sup_comm] at h1
    intro hd
    have hd' : p ∣ Nat.card O * Nat.card S := by
      rw [← h1]; exact Dvd.dvd.mul_right hd _
    rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
    · exact not_dvd_card_glaPPrimeCoreOf hp Ca h
    · obtain ⟨n, hn⟩ := hS2.exists_card_eq
      rw [hn] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨S₀, hS₀, hSS₀, hDS₀⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_two (isPGroup_of_isElemAbelian hDel) hHp hDH le_sup_left hS2 hDS
  have hS₀ne : S₀ ≠ ⊥ := fun h => hSne (le_bot_iff.1 (h ▸ hSS₀))
  refine ⟨S₀, hS₀ne, hS₀.2.1, hDS₀, fun j hj => ?_⟩
  have hjH : GLBConj j H = H := gLBConj_eq_of_mem_normalizer (hJH hj)
  have hS₁ : CFSG.Open.fusionIsSylowIn 2 (GLBConj j S₀) H := by
    refine ⟨?_, hS₀.2.1.map _, fun Q hQH hQ hSQ => ?_⟩
    · have := gLBConj_mono (g := j) hS₀.1
      rwa [hjH] at this
    · have h1 : GLBConj j⁻¹ Q ≤ H := by
        have := gLBConj_mono (g := j⁻¹) hQH
        rwa [gLBConj_eq_of_mem_normalizer (hJH (J.inv_mem hj))] at this
      have h2 : S₀ ≤ GLBConj j⁻¹ Q := by
        have := gLBConj_mono (g := j⁻¹) hSQ
        rwa [gLBConj_inv_gLBConj] at this
      have h3 := hS₀.2.2 _ h1 (hQ.map _) h2
      rw [← h3, gLBConj_gLBConj_inv]
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS₀
  obtain ⟨P', hP'⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P P'
  have hmap := CFSG.Goldschmidt.G310.map_subtype_smul_sylow H g P
  rw [hg, hP', hP] at hmap
  have hS₀O : S₀ ≤ Subgroup.normalizer (O : Set G) :=
    hS₀.1.trans (sup_le hSO (hOCa.trans hCaO))
  have hgOS : (g : G) ∈ O ⊔ S₀ := by
    have hH_le : H ≤ O ⊔ S₀ := by
      rw [sup_comm O S₀]
      exact sup_le_sup_right hSS₀ O
    exact hH_le g.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O S₀ hS₀O] at hgOS
  obtain ⟨o, ho, s₀, hs₀, hgo⟩ := Set.mem_mul.mp hgOS
  have hS₀fix : S₀.map (MulAut.conj s₀).toMonoidHom = S₀ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hs₀)
  have e1 : S₀.map (MulAut.conj (g : G)).toMonoidHom = GLBConj o⁻¹ S₀ := by
    rw [← hgo]
    have : (MulAut.conj (o * s₀)).toMonoidHom =
        (MulAut.conj o).toMonoidHom.comp (MulAut.conj s₀).toMonoidHom := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, ← Subgroup.map_map, hS₀fix]
    unfold GLBConj
    rw [inv_inv]
  have e2 : GLBConj j S₀ = GLBConj o⁻¹ S₀ := hmap.trans e1
  have e3 : GLBConj (j * o) S₀ = S₀ := by
    have h1 := congrArg (GLBConj o) e2
    rw [gLBConj_gLBConj, gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1
    exact h1
  have hn : j * o ∈ Subgroup.normalizer (S₀ : Set G) := mem_normalizer_iff_gLBConj_eq.2 e3
  have hn' : j * o ∈ Subgroup.normalizer (S₀ : Set G) ⊓ Ca := ⟨hn, mul_mem (hJa hj) (hOCa ho)⟩
  have := Subgroup.mul_mem_sup hn' (O.inv_mem ho)
  simpa using this

theorem inf_eq_bot_of_isPGroup (hp : p.Prime) {D O : Subgroup G} (hD : IsPGroup p D)
    (hO : ¬ p ∣ Nat.card O) : D ⊓ O = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hn]
  exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hO)

theorem mem_centralizer_of_mem_normalizer_of_inf_eq_bot {D O : Subgroup G}
    (hDO : D ≤ Subgroup.normalizer (O : Set G)) (hbot : D ⊓ O = ⊥) {o : G} (ho : o ∈ O)
    (hoD : o ∈ Subgroup.normalizer (D : Set G)) : o ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 : o * d * o⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hoD d).1 hd
  have h2 : d * o⁻¹ * d⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hDO hd) o⁻¹).1 (O.inv_mem ho)
  have h3 : o * d * o⁻¹ * d⁻¹ ∈ D ⊓ O := by
    refine ⟨D.mul_mem h1 (D.inv_mem hd), ?_⟩
    have := O.mul_mem ho h2
    simpa [mul_assoc] using this
  rw [hbot, Subgroup.mem_bot] at h3
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)).symm

theorem fusionIsSylowIn_of_card_dvd (hp : p.Prime) {X Q : Subgroup G} {n : ℕ} (hXQ : X ≤ Q)
    (hX : IsPGroup p X) (hQ : Nat.card Q ∣ Nat.card X * n) (hn : ¬ p ∣ n) :
    fusionIsSylowIn p X Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨hXQ, hX, fun Y hYQ hY hXY => ?_⟩
  obtain ⟨m, hm⟩ := hY.exists_card_eq
  have h1 : Nat.card Y ∣ Nat.card X * n := (Subgroup.card_dvd_of_le hYQ).trans hQ
  have hcop : Nat.Coprime (Nat.card Y) n := by
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  have h2 : Nat.card Y ∣ Nat.card X := hcop.dvd_of_dvd_mul_right h1
  exact (Subgroup.eq_of_le_of_card_ge hXY (Nat.le_of_dvd Nat.card_pos h2)).symm

theorem exists_mem_conj_of_fusionIsSylowIn (hp : p.Prime) {X X' Q : Subgroup G}
    (hX : fusionIsSylowIn p X Q) (hX' : fusionIsSylowIn p X' Q) :
    ∃ q ∈ Q, X' = GLBConj q⁻¹ X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, rfl⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hX
  obtain ⟨P', rfl⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hX'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P P'
  refine ⟨g, g.2, ?_⟩
  rw [← hg, CFSG.Goldschmidt.G310.map_subtype_smul_sylow]
  unfold GLBConj
  rw [inv_inv]

theorem exists_conj_mem_centralizer (hp : p.Prime) {D O S₀ : Subgroup G} (hD : IsPGroup p D)
    (hO : ¬ p ∣ Nat.card O) (hDO : D ≤ Subgroup.normalizer (O : Set G))
    (hDS : D ≤ Subgroup.normalizer (S₀ : Set G)) {o : G} (ho : o ∈ O)
    (hDS' : D ≤ Subgroup.normalizer (GLBConj o S₀ : Set G)) :
    ∃ c ∈ O ⊓ Subgroup.centralizer (D : Set G), GLBConj o S₀ = GLBConj c S₀ := by
  have hbot : D ⊓ O = ⊥ := inf_eq_bot_of_isPGroup hp hD hO
  have hΓcard : Nat.card (D ⊔ O : Subgroup G) = Nat.card D * Nat.card O := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := D) hDO
    rw [sup_comm, inf_comm, hbot, Subgroup.card_bot, mul_one] at h1
    rw [h1, mul_comm]
  have hDQ : D ≤ Subgroup.normalizer (S₀ : Set G) ⊓ (D ⊔ O) := le_inf hDS le_sup_left
  have hQcard : Nat.card ↥(Subgroup.normalizer (S₀ : Set G) ⊓ (D ⊔ O)) ∣ Nat.card D * Nat.card O :=
    hΓcard ▸ Subgroup.card_dvd_of_le inf_le_right
  have hD'N : GLBConj o⁻¹ D ≤ Subgroup.normalizer (S₀ : Set G) := by
    intro y hy
    rw [mem_gLBConj] at hy
    have hd := Subgroup.mem_normalizer_iff.1 (hDS' hy)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key := hd (o⁻¹ * h * o)
    simp only [mem_gLBConj] at key
    have e1 : o * (o⁻¹ * h * o) * o⁻¹ = h := by group
    have e2 : o * (o⁻¹ * y * o⁻¹⁻¹ * (o⁻¹ * h * o) * (o⁻¹ * y * o⁻¹⁻¹)⁻¹) * o⁻¹ = y * h * y⁻¹ := by
      group
    rw [e1, e2] at key
    exact key
  have hD'Γ : GLBConj o⁻¹ D ≤ D ⊔ O := by
    intro y hy
    rw [mem_gLBConj] at hy
    have hd : o⁻¹ * y * o⁻¹⁻¹ ∈ D := hy
    have h2 : (o⁻¹ * y * o⁻¹⁻¹) * o⁻¹ * (o⁻¹ * y * o⁻¹⁻¹)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (hDO hd) o⁻¹).1 (O.inv_mem ho)
    have e : y = o * ((o⁻¹ * y * o⁻¹⁻¹) * o⁻¹ * (o⁻¹ * y * o⁻¹⁻¹)⁻¹) * (o⁻¹ * y * o⁻¹⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_right h2))
      (Subgroup.mem_sup_left hd)
  have hD'Q : GLBConj o⁻¹ D ≤ Subgroup.normalizer (S₀ : Set G) ⊓ (D ⊔ O) := le_inf hD'N hD'Γ
  have hD'card : Nat.card (GLBConj o⁻¹ D) = Nat.card D := by
    unfold GLBConj
    exact Subgroup.card_map_of_injective (MulAut.conj o⁻¹⁻¹).injective
  have hSylD : fusionIsSylowIn p D (Subgroup.normalizer (S₀ : Set G) ⊓ (D ⊔ O)) :=
    fusionIsSylowIn_of_card_dvd hp hDQ hD hQcard hO
  have hSylD' : fusionIsSylowIn p (GLBConj o⁻¹ D) (Subgroup.normalizer (S₀ : Set G) ⊓ (D ⊔ O)) :=
    fusionIsSylowIn_of_card_dvd hp hD'Q (hD.map _) (hD'card ▸ hQcard) hO
  obtain ⟨q, hqQ, hqD⟩ := exists_mem_conj_of_fusionIsSylowIn hp hSylD hSylD'
  have hc₁N : q⁻¹ * o ∈ Subgroup.normalizer (D : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq, ← gLBConj_gLBConj, ← hqD, gLBConj_gLBConj_inv]
  have hc₁Γ : q⁻¹ * o ∈ D ⊔ O :=
    (D ⊔ O).mul_mem ((D ⊔ O).inv_mem (Subgroup.mem_inf.1 hqQ).2) (Subgroup.mem_sup_right ho)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D O hDO] at hc₁Γ
  obtain ⟨d₁, hd₁, o₁, ho₁, hc₁⟩ := Set.mem_mul.mp hc₁Γ
  have ho₁N : o₁ ∈ Subgroup.normalizer (D : Set G) := by
    have e : o₁ = d₁⁻¹ * (q⁻¹ * o) := by rw [← hc₁]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hd₁)) hc₁N
  have ho₁C : o₁ ∈ Subgroup.centralizer (D : Set G) :=
    mem_centralizer_of_mem_normalizer_of_inf_eq_bot hDO hbot ho₁ ho₁N
  refine ⟨o₁, Subgroup.mem_inf.2 ⟨ho₁, ho₁C⟩, ?_⟩
  have hoeq : o = (q * d₁) * o₁ := by
    have : q * (d₁ * o₁) = o := by rw [hc₁]; group
    rw [← this]; group
  have hqS : GLBConj q S₀ = S₀ := gLBConj_eq_of_mem_normalizer (Subgroup.mem_inf.1 hqQ).1
  have hdS : GLBConj d₁ S₀ = S₀ := gLBConj_eq_of_mem_normalizer (hDS hd₁)
  rw [hoeq, ← gLBConj_gLBConj, ← gLBConj_gLBConj, hqS, hdS]

theorem exists_fixed_conj (hp : p.Prime) {C P S₀ : Subgroup G} (hP : IsPGroup p P)
    (hC : ¬ p ∣ Nat.card C) (hPC : P ≤ Subgroup.normalizer (C : Set G))
    (hstab : ∀ t ∈ P, ∃ c ∈ C, GLBConj t S₀ = GLBConj c S₀) :
    ∃ c ∈ C, ∀ t ∈ P, GLBConj t (GLBConj c S₀) = GLBConj c S₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Ω : Type := {X : Subgroup G // ∃ c ∈ C, X = GLBConj c S₀}
  have hCst : ∀ (c : C) (X : Ω), ∃ c' ∈ C, GLBConj (c : G)⁻¹ X.1 = GLBConj c' S₀ := by
    intro c X
    obtain ⟨c₀, hc₀, hX⟩ := X.2
    exact ⟨c₀ * (c : G)⁻¹, C.mul_mem hc₀ (C.inv_mem c.2), by rw [hX, gLBConj_gLBConj]⟩
  letI actC : MulAction C Ω :=
    { smul := fun c X => ⟨GLBConj (c : G)⁻¹ X.1, hCst c X⟩
      one_smul := fun X => Subtype.ext (by
        show GLBConj ((1 : C) : G)⁻¹ X.1 = X.1
        rw [Subgroup.coe_one, inv_one, gLBConj_one])
      mul_smul := fun a b X => Subtype.ext (by
        show GLBConj ((a * b : C) : G)⁻¹ X.1 = GLBConj (a : G)⁻¹ (GLBConj (b : G)⁻¹ X.1)
        rw [gLBConj_gLBConj, Subgroup.coe_mul, mul_inv_rev]) }
  haveI : MulAction.IsPretransitive C Ω :=
    ⟨fun X Y => by
      obtain ⟨c₁, hc₁, hX⟩ := X.2
      obtain ⟨c₂, hc₂, hY⟩ := Y.2
      refine ⟨⟨c₂⁻¹ * c₁, C.mul_mem (C.inv_mem hc₂) hc₁⟩, Subtype.ext ?_⟩
      show GLBConj (c₂⁻¹ * c₁)⁻¹ X.1 = Y.1
      rw [hX, hY, gLBConj_gLBConj]
      congr 1
      group⟩
  let Ω₀ : Ω := ⟨S₀, 1, C.one_mem, (gLBConj_one S₀).symm⟩
  have hΩ : ¬ p ∣ Nat.card Ω := by
    have h1 : (MulAction.stabilizer C Ω₀).index = Nat.card Ω :=
      MulAction.index_stabilizer_of_transitive C Ω₀
    have h2 : Nat.card Ω ∣ Nat.card C := h1 ▸ Subgroup.index_dvd_card _
    exact fun h => hC (h.trans h2)
  have hPst : ∀ (t : P) (X : Ω), ∃ c ∈ C, GLBConj (t : G)⁻¹ X.1 = GLBConj c S₀ := by
    intro t X
    obtain ⟨c₀, hc₀, hX⟩ := X.2
    obtain ⟨c', hc', hc'S⟩ := hstab (t : G)⁻¹ (P.inv_mem t.2)
    have hc'' : (t : G) * c₀ * (t : G)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.1 (hPC t.2) c₀).1 hc₀
    refine ⟨c' * ((t : G) * c₀ * (t : G)⁻¹), C.mul_mem hc' hc'', ?_⟩
    have e : GLBConj (c' * ((t : G) * c₀ * (t : G)⁻¹)) S₀ = GLBConj (c₀ * (t : G)⁻¹) S₀ := by
      rw [← gLBConj_gLBConj, ← hc'S, gLBConj_gLBConj]
      congr 1
      group
    rw [hX, gLBConj_gLBConj, e]
  letI actP : MulAction P Ω :=
    { smul := fun t X => ⟨GLBConj (t : G)⁻¹ X.1, hPst t X⟩
      one_smul := fun X => Subtype.ext (by
        show GLBConj ((1 : P) : G)⁻¹ X.1 = X.1
        rw [Subgroup.coe_one, inv_one, gLBConj_one])
      mul_smul := fun a b X => Subtype.ext (by
        show GLBConj ((a * b : P) : G)⁻¹ X.1 = GLBConj (a : G)⁻¹ (GLBConj (b : G)⁻¹ X.1)
        rw [gLBConj_gLBConj, Subgroup.coe_mul, mul_inv_rev]) }
  obtain ⟨X, hX⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Ω hΩ
  obtain ⟨c, hc, hXc⟩ := X.2
  refine ⟨c, hc, fun t ht => ?_⟩
  have h1 : (⟨t⁻¹, P.inv_mem ht⟩ : P) • X = X := MulAction.mem_fixedPoints.1 hX _
  have h2 : GLBConj (t⁻¹)⁻¹ X.1 = X.1 := congrArg Subtype.val h1
  rw [inv_inv, hXc] at h2
  exact h2

theorem conj_mem_and_comm_mem_core (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J)
    {c t : G} (hc : c ∈ GLAPPrimeCoreOf p X) (ht : t ∈ J) :
    c * t * c⁻¹ ∈ J ∧ c * t * c⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p J := by
  have hcJ : c ∈ Subgroup.normalizer (J : Set G) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPPrimeCoreOf_le_normalizer hJ hc
  have h1 : c * t * c⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hcJ t).1 ht
  refine ⟨h1, ?_⟩
  have hX : t ∈ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) :=
    le_normalizer_glaPPrimeCoreOf p X (hJ.1 ht)
  have h2 : t * c⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p X :=
    (Subgroup.mem_normalizer_iff.1 hX c⁻¹).1 (Subgroup.inv_mem _ hc)
  have h3 : c * t * c⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := Subgroup.mul_mem _ hc h2
    simpa [mul_assoc] using this
  exact inf_glaPPrimeCoreOf_le hp hJ.1 ⟨J.mul_mem h1 (J.inv_mem ht), h3⟩

theorem le_cover_of_forall_pSubgroup_le (hp : p.Prime) (hp2 : p ≠ 2) {X J R : Subgroup G}
    (hJ : GLAPComponent p X J) (hO : GLAPPrimeCoreOf p J ≤ R)
    (h : ∀ P : Subgroup G, P ≤ J → IsPGroup p P → P ≤ R) : J ≤ R := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup ↥J := GLAPPrimeCore p ↥J with hK
  set π : ↥J →* PQuot p J := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  set R' : Subgroup ↥J := R.subgroupOf J with hR'
  have hKR : K ≤ R' := fun x hx => hO ⟨x, hx, rfl⟩
  have hQ : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hPsyl : ∀ P : Sylow p ↥J, (P : Subgroup ↥J) ≤ R' := by
    intro P x hx
    have : ((P : Subgroup ↥J).map J.subtype) ≤ R :=
      h _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _)
    exact this ⟨x, hx, rfl⟩
  have hQsyl : ∀ P' : Sylow p (PQuot p J), (P' : Subgroup (PQuot p J)) ≤ R'.map π := by
    intro P'
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπs p P'
    have : (P' : Subgroup (PQuot p J)) = (P : Subgroup ↥J).map π := by
      rw [← hP]; rfl
    rw [this]
    exact Subgroup.map_mono (hPsyl P)
  have hord : ∀ y : PQuot p J, y ^ p = 1 → y ∈ R'.map π := by
    intro y hy
    have hzp : IsPGroup p (Subgroup.zpowers y) := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hy) with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
    obtain ⟨P', hP'⟩ := hzp.exists_le_sylow
    exact hQsyl P' (hP' (Subgroup.mem_zpowers y))
  obtain ⟨x₀, hx₀o, hx₀c⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center hQ hp
      hp2 (dvd_card_pQuot_of_component hp hJ)
  have hx₀p : x₀ ^ p = 1 := by
    have := pow_orderOf_eq_one x₀
    rwa [hx₀o] at this
  have hnc : Subgroup.normalClosure {x₀} ≤ R'.map π := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    have ha' : a = x₀ := ha
    subst ha'
    apply hord
    rw [conj_pow, hx₀p, mul_one, mul_inv_cancel]
  have hMtop : Subgroup.normalClosure {x₀} = ⊤ := by
    by_contra hne
    exact hx₀c ((le_center_of_normal_of_isQuasisimple hQ inferInstance hne)
      (Subgroup.subset_normalClosure rfl))
  have hall : R'.map π = ⊤ := top_le_iff.1 (hMtop ▸ hnc)
  intro g hg
  have hg' : π ⟨g, hg⟩ ∈ R'.map π := hall ▸ Subgroup.mem_top _
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.1 hg'
  have h1 : r⁻¹ * ⟨g, hg⟩ ∈ K := QuotientGroup.eq.1 hrg
  have h2 : (⟨g, hg⟩ : ↥J) = r * (r⁻¹ * ⟨g, hg⟩) := by group
  have h3 : (⟨g, hg⟩ : ↥J) ∈ R' := by rw [h2]; exact R'.mul_mem hr (hKR h1)
  exact h3

theorem pSubgroup_le_cover (hp : p.Prime) {D J S₀ : Subgroup G} {a : G}
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) (hDel : IsElemAbelian p D)
    (haD : a ∈ D) (hDS : D ≤ Subgroup.normalizer (S₀ : Set G))
    (hcov : J ≤ (Subgroup.normalizer (S₀ : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)))
    {P : Subgroup G} (hPJ : P ≤ J) (hP : IsPGroup p P) :
    P ≤ (Subgroup.normalizer (S₀ : Set G) ⊓ J) ⊔ GLAPPrimeCoreOf p J := by
  set Ca : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCa
  set O : Subgroup G := GLAPPrimeCoreOf p Ca with hO
  have hCDa : Subgroup.centralizer (D : Set G) ≤ Ca :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := hJ.1
  have hOcard : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp Ca
  have hCaO : Ca ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p Ca
  have hD : IsPGroup p D := isPGroup_of_isElemAbelian hDel
  have hDO : D ≤ Subgroup.normalizer (O : Set G) :=
    (isElemAbelian_le_centralizer hDel haD).trans hCaO
  have h0 : ∀ t ∈ J, ∃ o₀ ∈ O, GLBConj t S₀ = GLBConj o₀ S₀ := by
    intro t ht
    have ht' := hcov ht
    have hA : Subgroup.normalizer (S₀ : Set G) ⊓ Ca ≤ Subgroup.normalizer (O : Set G) :=
      inf_le_right.trans hCaO
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hA] at ht'
    obtain ⟨n, hn, o₀, ho₀, rfl⟩ := Set.mem_mul.mp ht'
    refine ⟨o₀, ho₀, ?_⟩
    rw [← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer (Subgroup.mem_inf.1 hn).1]
  set C : Subgroup G := O ⊓ Subgroup.centralizer (D : Set G) with hC
  have hCcard : ¬ p ∣ Nat.card C := fun h => hOcard (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf (fun g hg => hCaO (hCDa (hJD (hPJ hg))))
      (fun g hg => Subgroup.le_normalizer (hJD (hPJ hg)))
  have hstab : ∀ t ∈ P, ∃ c ∈ C, GLBConj t S₀ = GLBConj c S₀ := by
    intro t ht
    have htJ := hPJ ht
    obtain ⟨o₀, ho₀, hto⟩ := h0 t htJ
    have htD : ∀ d ∈ D, d * t = t * d := fun d hd => Subgroup.mem_centralizer_iff.1 (hJD htJ) d hd
    have hDt : D ≤ Subgroup.normalizer (GLBConj o₀ S₀ : Set G) := by
      rw [← hto]
      intro d hd
      rw [mem_normalizer_iff_gLBConj_eq, gLBConj_gLBConj, ← htD d hd, ← gLBConj_gLBConj,
        gLBConj_eq_of_mem_normalizer (hDS hd)]
    obtain ⟨c, hc, hco⟩ := exists_conj_mem_centralizer hp hD hOcard hDO hDS ho₀ hDt
    exact ⟨c, hc, hto.trans hco⟩
  obtain ⟨c, hc, hfix⟩ := exists_fixed_conj hp hP hCcard hPC hstab
  intro t ht
  have htJ := hPJ ht
  have hcN : c * t * c⁻¹ ∈ Subgroup.normalizer (S₀ : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have h1 := hfix t ht
    rw [gLBConj_gLBConj] at h1
    have h2 := congrArg (GLBConj c⁻¹) h1
    rwa [gLBConj_gLBConj, gLBConj_inv_gLBConj] at h2
  have hcO : c ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)) := by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp Ca
      (Subgroup.centralizer (D : Set G))
    rw [inf_eq_right.2 hCDa] at this
    exact this hc
  obtain ⟨hcJ, hcom⟩ := conj_mem_and_comm_mem_core hp hJ hcO htJ
  have e : t = (c * t * c⁻¹ * t⁻¹)⁻¹ * (c * t * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hcom))
    (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hcN, hcJ⟩))

theorem coversMod_of_weak_cover (hp : p.Prime) (hp2 : p ≠ 2) {D J S₀ : Subgroup G} {a : G}
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) (hDel : IsElemAbelian p D)
    (haD : a ∈ D) (hDS : D ≤ Subgroup.normalizer (S₀ : Set G))
    (hcov : J ≤ (Subgroup.normalizer (S₀ : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    CoversMod p (Subgroup.normalizer (S₀ : Set G)) J := by
  unfold CoversMod
  refine le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _)) ?_
  exact le_cover_of_forall_pSubgroup_le hp hp2 hJ le_sup_right
    fun P hPJ hP => pSubgroup_le_cover hp hJ hDel haD hDS hcov hPJ hP

theorem exists_twoLocal_cover_of_weak (hp : p.Prime) (hp2 : p ≠ 2) {D J S₀ : Subgroup G} {a : G}
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) (hDel : IsElemAbelian p D)
    (haD : a ∈ D) (hS₀ne : S₀ ≠ ⊥) (hS₀2 : IsPGroup 2 S₀)
    (hDS : D ≤ Subgroup.normalizer (S₀ : Set G))
    (hcov : J ≤ (Subgroup.normalizer (S₀ : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    ∃ N : Subgroup G, IsTwoLocal N ∧ D ≤ N ∧ CoversMod p N J :=
  ⟨Subgroup.normalizer (S₀ : Set G), ⟨S₀, hS₀ne, hS₀2, rfl⟩, hDS,
    coversMod_of_weak_cover hp hp2 hJ hDel haD hDS hcov⟩


theorem not_le_core_of_component (hp : p.Prime) {Y J K : Subgroup G} (hJ : GLAPComponent p Y J) :
    ¬ J ≤ GLAPPrimeCoreOf p K := by
  intro hle
  have hcop : Nat.Coprime p (Nat.card J) := by
    refine Nat.Coprime.coprime_dvd_right ?_
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp K)
    exact Subgroup.card_dvd_of_le hle
  have htop : GLAPPrimeCore p ↥J = ⊤ := by
    refine eq_top_iff.2 ?_
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact hcop
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI := isQuasisimple_nontrivial hq
  have hsub : Subsingleton (PQuot p J) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq]
        have : a⁻¹ * b ∈ GLAPPrimeCore p ↥J := htop ▸ Subgroup.mem_top _
        exact this
  exact not_subsingleton _ hsub

end P65

end CFSG.LocalAnalysis.GLTheoremA
