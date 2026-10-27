module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop65Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsShared

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure Prop65Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i268 : I268At G p
  i81 : I81At G p
  i112 : I112ChevAt G p
  i2020 : I2020At G p
  i1416 : I1416At G p
  i183 : Input18_3_4
  nonIso : LieTypeNonIsoAt

theorem not_case64i (hc : S6Ctx G p) (hin : Prop65Inputs G p) (h62 : Lemma62At G p) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : IsSStarMax p B x L) (hChev : IsChevSimple q (PSimple p L)) (hi : Case64i p q B x L) :
    False := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hT : InT p B x L := IsSStarMax.inT hc hS
  have hBmax : GLAIsBmax p B := hT.1
  have hxB : x ∈ B := hT.2.1
  have hx1 : x ≠ 1 := hT.2.2.1
  have hcomp : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hT.2.2.2.1
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) := kGroup_centralizer hc hx1
  have hlay : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := sstarMax_layer_eq hc hS
  have hBX : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hBmax.1 hxB
  have hxp : x ^ p = 1 := hBmax.1.2 x hxB
  obtain ⟨hcard4, Q, hQp, hQ⟩ := hi
  have hQ' : ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      (pSimpleIsLie p L (.A 2 Q) ∨ pSimpleIsLie p L (.twistedA 2 Q)) :=
    ⟨Q, hQp, hQ.imp (fun h => h.1) (fun h => h.1)⟩
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcomp.1 hl)
  obtain ⟨B', E, D, hB'X, hB'el, hB'card, hEB', hEcard, hDE, hDcard, ⟨U1, hU1X, hU1ne, hU1, hB'U1⟩,
    ⟨U2, hU2X, hU2ne, hU2, hDU2, hcov⟩, hJcomp, hJcent, hJE⟩ :=
    hin.i268 hp hp2 q hq hq2 hqp _ L hKX hcomp hlay hQ' (IsSStarMax.cycMod hS)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl, hx1, hxp,
        fun w hw => Subgroup.mem_centralizer_singleton_iff.1 hw⟩ ⟨B, hBX, hBmax.1, hcard4⟩
  have hrank : GLATwoLocalRank p G = 4 := by
    have h1 := hBmax.2.1
    rw [hcard4] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hB'max : GLAIsBmax p B' := ⟨hB'el, by rw [hB'card, hrank], U1, hU1ne, hU1, hB'U1⟩
  have hx' : x ∈ B' := P65.mem_of_bmax_centralizes hp hB'max hxp hB'X hU1ne hU1 hU1X hB'U1
  have hBL' : B' ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hlay]
    exact P65.le_normalizer_glaPLayer (fun g hg => Subgroup.le_normalizer (hB'X hg))
  have hcm' : CentModEqZpowers p B' L x :=
    P65.centModEqZpowers_of_cycMod hp hB'el hx' hx1 hxL (IsSStarMax.cycMod hS)
  have hT' : InT p B' x L := ⟨hB'max, hx', hx1, hcomp, hBL', hcm'⟩
  have hDB' : D ≤ B' := hDE.trans hEB'
  have hBcent : B' ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute hB'el (hDB' hd) hb
  have hB'J : B' ≤ Subgroup.normalizer
      (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)) : Set G) :=
    P65.le_normalizer_glaPLayer (le_normalizer_inf hBL' (fun g hg => Subgroup.le_normalizer (hBcent hg)))
  have hInD : InD p B' x L D (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G))) := by
    refine ⟨⟨hDB', ?_, ?_⟩, ⟨hJcomp, hB'J, hJcent⟩, fun _ => ⟨E, hEB', ?_, hEcard, hDE, hJE⟩⟩
    · rw [hDcard]
    · rw [hDcard, hB'card]
      exact (pow_add p 2 2).symm ▸ le_rfl
    · exact isElemAbelian_mono hB'el hEB'
  have hN : IsTwoLocal (Subgroup.normalizer (U2 : Set G)) := ⟨U2, hU2ne, hU2, rfl⟩
  exact h62 q hq hq2 hqp B' x L ⟨hT', hChev⟩ D _ ⟨hInD, _, hN, hDU2, hcov⟩


theorem center_eq_bot_of_case234 {q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : Case234 p q B x L) : Subgroup.center (PQuot p L) = ⊥ := by
  rcases h with h | h | h
  · exact h.2.2.1
  · exact h.2.2.1
  · exact h.2.2.1

theorem isChevSimple_of_pSimpleIsLie {q : ℕ} {J : Subgroup G} {d : TauCeti.LieTypeIndex}
    (h : pSimpleIsLie p J d) (hd : d.characteristic = q) : IsChevSimple q (PSimple p J) := by
  left
  obtain ⟨i, hi, e⟩ := h
  refine ⟨i, ?_, e⟩
  cases i with
  | lie i0 =>
      simp only [onLie] at hi ⊢
      rw [hi]
      exact hd
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

theorem isChevSimple_of_jType {q : ℕ} {J : Subgroup G} (h : JType p q J) :
    IsChevSimple q (PSimple p J) := by
  rcases h with ⟨Q, hQp, hQ, -⟩ | ⟨Q, hQp, hQ⟩
  · rcases hQ with hQ | hQ
    · exact isChevSimple_of_pSimpleIsLie hQ (by simpa using hQp)
    · exact isChevSimple_of_pSimpleIsLie hQ (by simpa using hQp)
  · rcases hQ with hQ | hQ | hQ
    · exact isChevSimple_of_pSimpleIsLie hQ (by simpa using hQp)
    · exact isChevSimple_of_pSimpleIsLie hQ (by simpa using hQp)
    · exact isChevSimple_of_pSimpleIsLie hQ (by simpa using hQp)

theorem choose_DJ (hc : S6Ctx G p) (hin : Prop65Inputs G p) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) {B : Subgroup G} {x : G} {L : Subgroup G} (hT : InTq q p B x L)
    (h234 : Case234 p q B x L) : ∃ D J : Subgroup G, P65.DJData p q B x L D J := by
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨y, hyBL, hy1, J, E, hJlay, hJcomp, hJcent, hEB, hEel, hEcard, hDE, hJE, hii, h34⟩ :=
    hin.i81 hp hp2 q hq hq2 hqp B x L hT h234
  obtain ⟨⟨hBmax, hxB, hx1, hcomp, hBL, hcm⟩, hChev⟩ := hT
  have hyB : y ∈ B := hyBL.1
  have hyL : y ∈ L := hyBL.2
  have hDB : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hyB)
  have hDel : IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :=
    isElemAbelian_mono hEel hDE
  have hxL1 : Subgroup.zpowers x ⊓ L = ⊥ :=
    P65.zpowers_inf_eq_bot_of_center hp hcomp hxB hBmax.1 hx1 (center_eq_bot_of_case234 h234)
  have hyx : y ∉ Subgroup.zpowers x := fun h =>
    hy1 (Subgroup.mem_bot.1 (hxL1 ▸ (show y ∈ Subgroup.zpowers x ⊓ L from ⟨h, hyL⟩)))
  have hDcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 :=
    P65.card_sup_zpowers hp (hBmax.1.2 x hxB) (hBmax.1.2 y hyB) hx1 hy1 hyx
      (isElemAbelian_commute hBmax.1 hxB hyB)
  have hxD : x ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  set D : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hD
  have hBcent : B ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute hBmax.1 (hDB hd) hb
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := by
    rw [← hJlay]
    exact P65.le_normalizer_glaPLayer
      (le_normalizer_inf hBL (fun g hg => Subgroup.le_normalizer (hBcent hg)))
  have hInD : InD p B x L D J := by
    refine ⟨⟨hDB, ?_, ?_⟩, ⟨hJcomp, hBJ, hJcent⟩, fun _ => ⟨E, hEB, hEel, hEcard, hDE, hJE⟩⟩
    · rw [hDcard]
    · rw [hDcard]
      have := pow_four_le_card_of_bmax hc hBmax
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card B := this
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G)) (Subgroup.centralizer (D : Set G)) := by
    have h1 := isSubnormal_inf hcomp.2.1 (Subgroup.centralizer (D : Set G))
    have heq : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer (D : Set G) :=
      inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD))
    rwa [heq] at h1
  have hcompD : GLAPComponent p (Subgroup.centralizer (D : Set G)) J :=
    glaPComponent_of_isSubnormal' hp hsub hJcomp
  exact ⟨D, J, ⟨hDB, hDel, hDcard, hxD, hInD, hcompD,
    h234.elim (fun h => Or.inl (hii h)) (fun h => Or.inr (h34 h)), h34⟩⟩


theorem core_le_of_component (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X := by
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1]
  exact inf_le_right

theorem commutator_le_core_single (hc : S6Ctx G p) (hin : Prop65Inputs G p) (h64 : Lemma64At G p)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hT : InTq q p B x L)
    (hCP : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), InTq q p B' x' L' → Case34 p q B' x' L' →
      Case34 p q B x L)
    (hDJ : P65.DJData p q B x L D J) {a : G} (haD : a ∈ D) (hax : a ∉ Subgroup.zpowers x)
    (hDeq : D = Subgroup.zpowers a ⊔ Subgroup.zpowers x) {T S K : Subgroup G}
    (hTsyl : CFSG.Open.fusionIsSylowIn 2 T J) (hS2 : IsPGroup 2 S)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hSD : ⁅S, D⁆ = S)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) (hST : S ≤ Subgroup.centralizer (T : Set G))
    (hKc : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K) (hJK : J ≤ K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hJKx : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    ⁅J, S⁆ ≤ GLAPPrimeCoreOf p K := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hBmax : GLAIsBmax p B := hT.1.1
  have hDB := hDJ.le_B
  have hxD := hDJ.mem_x
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hDJ.comp
  have haK : a ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKc.1 hk)
  have hJO : ¬ J ≤ GLAPPrimeCoreOf p K := P65.not_le_core_of_component hp hDJ.comp
  have hTJ : T ≤ J := hTsyl.1
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    have hTnot := P65.sylow_not_le_centMod hJK hJperf hJO hTsyl
    intro s hs
    refine P65.mem_normalizer_of_centralizes hp hKc (hTJ.trans hJK) hTnot ?_ (hST hs)
    exact Subgroup.le_normalizer (hSa hs)
  by_cases hcx : CentMod p K x
  ·
    have hDcm : D ≤ centModSubgroup p K := by
      rw [hDeq]
      exact sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer haK)))
        (Subgroup.zpowers_le.2 (centMod_iff.1 hcx))
    have hScm := P65.le_centMod_of_comm_eq hSK hDcm hSD
    exact Subgroup.commutator_le.2 fun j hj s hs => (hScm hs).2 j (hJK hj)
  ·
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBK (hDB hxD)
    have hxp : x ^ p = 1 := hBmax.1.2 x (hDB hxD)
    have hJchev := isChevSimple_of_jType hDJ.jtype
    have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hDJ.inD.2.1.2.1
    have hDcm : ∀ b ∈ B, CentMod p J b ↔ b ∈ D := hDJ.inD.2.1.2.2
    have ha1 : a ≠ 1 := fun h => hax (h ▸ Subgroup.one_mem _)
    have hCaK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
      kGroup_centralizer hc ha1
    obtain ⟨A, hAel, hAcard⟩ := P65.exists_elemAbelian_aut hp hBmax.1 hDJ.comp hBJ hDB hDcm
      hDJ.inD.1.2.2
    have hKchev : IsChevSimple q (PSimple p K) :=
      hin.i1416 hp hp2 q hq hq2 hqp _ K J x hCaK hKc hxN hxp hcx hJKx hJchev ⟨A, hAel, hAcard⟩
    have hcmB : CentModEqZpowers p B K a :=
      P65.centModEqZpowers_of_D hp hDeq hDJ.elem haK hcx hJK hBJ (fun b hb h => (hDcm b hb).1 h)
    have hTq' : InTq q p B a K := ⟨⟨hBmax, hDB haD, ha1, hKc, hBK, hcmB⟩, hKchev⟩
    have h64' := h64 q hq hq2 hqp B a K hTq'
    have hDcmx : D ≤ Subgroup.zpowers x ⊔ centModSubgroup p K := by
      rw [hDeq]
      exact sup_le (le_sup_of_le_right
        (Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer haK)))) le_sup_left
    have hTS : ⁅T, S⁆ ≤ centModSubgroup p K := by
      refine le_trans (Subgroup.commutator_le.2 fun t ht s hs => ?_) bot_le
      have h1 : t * s = s * t := Subgroup.mem_centralizer_iff.1 (hST hs) t ht
      rw [commutatorElement_eq_one_iff_mul_comm.2 h1]
      exact Subgroup.one_mem _
    rcases hin.i2020 hp hp2 q hq hq2 hqp B a K J T S D x hTq' h64' (hDB.trans hBK) hxD hcx hxp
      hDcmx hJKx hDJ.jtype hTsyl hS2 hSK hTS hDS hSD with h | ⟨h34, hsl3⟩
    · exact P65.commutator_le_core_of_centMod hJK hJperf hSK h
    · exfalso
      obtain ⟨Q, -, hQ, -⟩ := hsl3
      exact P65.isOmega_not_A2 hin.nonIso (hDJ.omega (hCP B a K hTq' h34)) ⟨Q, hQ⟩


theorem commutator_le_core (hc : S6Ctx G p) (hin : Prop65Inputs G p) (h64 : Lemma64At G p)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hT : InTq q p B x L)
    (hCP : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), InTq q p B' x' L' → Case34 p q B' x' L' →
      Case34 p q B x L)
    (hDJ : P65.DJData p q B x L D J) {a : G} (haD : a ∈ D) (hax : a ∉ Subgroup.zpowers x)
    (hDeq : D = Subgroup.zpowers a ⊔ Subgroup.zpowers x) {T S : Subgroup G}
    (hTsyl : CFSG.Open.fusionIsSylowIn 2 T J) (hS2 : IsPGroup 2 S)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hSD : ⁅S, D⁆ = S)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) (hST : S ≤ Subgroup.centralizer (T : Set G)) :
    ⁅J, S⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hBmax : GLAIsBmax p B := hT.1.1
  have hDB := hDJ.le_B
  have hxD := hDJ.mem_x
  have ha1 : a ≠ 1 := fun h => hax (h ▸ Subgroup.one_mem _)
  have hCaK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc ha1
  have hBCa : B ≤ Subgroup.centralizer ({a} : Set G) :=
    isElemAbelian_le_centralizer hBmax.1 (hDB haD)
  have hJCa : J ≤ Subgroup.centralizer ({a} : Set G) :=
    hDJ.comp.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD))
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hDJ.inD.2.1.2.1
  obtain ⟨hJK, hKCa, hBK⟩ := P65.closure_basic (p := p) hJCa hBCa hBJ
  set K := closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) with hK
  have hKxD : K ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hD' : D ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hDeq]
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hKCa hg.1)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hD' hd)
  have hJKx : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J :=
    glaPComponent_of_le hp hDJ.comp
      (le_inf hJK (hDJ.comp.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD))))
      hKxD
  rcases P65.closure_single_or_multi hp hin.i183 hCaK hDeq hDB hBmax.1 hDJ.comp hBK with
    hKc | ⟨L₁, hL₁, hKL₁, hxL₁⟩
  · exact (commutator_le_core_single hc hin h64 hq hq2 hqp hT hCP hDJ haD hax hDeq hTsyl hS2 hDS hSD
      hSa hST hKc hJK hBK hJKx).trans (core_le_of_component hp hKc)
  · exfalso
    have hrank : ∀ (B' U : Subgroup G), B' ≤ Subgroup.centralizer ({a} : Set G) → IsElemAbelian p B' →
        U ≤ Subgroup.centralizer ({a} : Set G) → U ≠ ⊥ → IsPGroup 2 U →
        B' ≤ Subgroup.normalizer (U : Set G) → Nat.card B' ≤ Nat.card B := by
      intro B' U _ hB' _ hU hU2 hB'U
      rw [hBmax.2.1]
      exact card_le_pow_glaTwoLocalRank hp hB' hU hU2 hB'U
    obtain ⟨h3, hcen, Q'', hQ''⟩ := hin.i112 hp hp2 q hq hq2 hqp _ B K L₁ J x hCaK hBCa hBmax.1 hrank
      hL₁ hKL₁ (hDB hxD) hxL₁ hJKx (isChevSimple_of_jType hDJ.jtype)
    rcases hDJ.jtype with ⟨Q, hQp, hQ, hc3⟩ | hom
    · exact hc3 h3 hcen
    · exact P65.isOmega_not_A2 hin.nonIso hom ⟨Q'', hQ''⟩

theorem exists_weak_cover_main (hc : S6Ctx G p) (hin : Prop65Inputs G p) (h64 : Lemma64At G p) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hT : InTq q p B x L) (h234 : Case234 p q B x L)
    (hCP : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), InTq q p B' x' L' → Case34 p q B' x' L' →
      Case34 p q B x L) :
    ∃ D J : Subgroup G, P65.DJData p q B x L D J ∧ ∃ a ∈ D, ∃ S₀ : Subgroup G, S₀ ≠ ⊥ ∧ IsPGroup 2 S₀ ∧
      D ≤ Subgroup.normalizer (S₀ : Set G) ∧
      J ≤ (Subgroup.normalizer (S₀ : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨D, J, hDJ⟩ := choose_DJ hc hin hq hq2 hqp hT h234
  obtain ⟨a, T, S, haD, hax, hDeq, hTsyl, hS2, hSne, hDS, hSD, hSa, hST⟩ :=
    P65.exists_S_package hc hDJ hT.1.2.2.1
  have hcomm := commutator_le_core hc hin h64 hq hq2 hqp hT hCP hDJ haD hax hDeq hTsyl hS2 hDS hSD hSa hST
  have hJa : J ≤ Subgroup.centralizer ({a} : Set G) :=
    hDJ.comp.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD))
  obtain ⟨S₀, hS0ne, hS02, hDS0, hcov⟩ :=
    P65.exists_twoLocal_weak_cover hp hp2 hDJ.elem haD hS2 hSne hSa hDS hJa hcomm
  exact ⟨D, J, hDJ, a, haD, S₀, hS0ne, hS02, hDS0, hcov⟩

theorem prop65_main (hc : S6Ctx G p) (hin : Prop65Inputs G p) (h62 : Lemma62At G p)
    (h64 : Lemma64At G p) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {B : Subgroup G}
    {x : G} {L : Subgroup G} (hT : InTq q p B x L) (h234 : Case234 p q B x L)
    (hCP : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), InTq q p B' x' L' → Case34 p q B' x' L' →
      Case34 p q B x L) : False := by
  obtain ⟨D, J, hDJ, a, haD, S₀, hS0ne, hS02, hDS0, hcov⟩ :=
    exists_weak_cover_main hc hin h64 hq hq2 hqp hT h234 hCP
  obtain ⟨N, hN, hDN, hcovN⟩ :=
    P65.exists_twoLocal_cover_of_weak hc.prime hc.odd hDJ.comp hDJ.elem haD hS0ne hS02 hDS0 hcov
  exact h62 q hq hq2 hqp B x L hT D J ⟨hDJ.inD, N, hN, hDN, hcovN⟩

theorem case234_of_sstarMax (hc : S6Ctx G p) (hin : Prop65Inputs G p) (h62 : Lemma62At G p)
    (h64 : Lemma64At G p) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {B : Subgroup G}
    {x : G} {L : Subgroup G} (hS : IsSStarMax p B x L) (hChev : IsChevSimple q (PSimple p L)) :
    Case234 p q B x L := by
  have hTq : InTq q p B x L := ⟨IsSStarMax.inT hc hS, hChev⟩
  rcases (lemma64Cases_iff p q B x L).1 (h64 q hq hq2 hqp B x L hTq) with hi | h234
  · exact (not_case64i hc hin h62 hq hq2 hqp hS hChev hi).elim
  · exact h234

theorem exists_choice {q : ℕ} {B₀ : Subgroup G} {x₀ : G} {L₀ : Subgroup G} (hT₀ : InTq q p B₀ x₀ L₀)
    (h₀ : Case234 p q B₀ x₀ L₀) :
    ∃ (B : Subgroup G) (x : G) (L : Subgroup G), InTq q p B x L ∧ Case234 p q B x L ∧
      ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), InTq q p B' x' L' → Case34 p q B' x' L' →
        Case34 p q B x L := by
  by_cases h : ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G), InTq q p B' x' L' ∧ Case34 p q B' x' L'
  · obtain ⟨B', x', L', hT', h34⟩ := h
    exact ⟨B', x', L', hT', Or.inr h34, fun _ _ _ _ _ => h34⟩
  · push Not at h
    exact ⟨B₀, x₀, L₀, hT₀, h₀, fun B' x' L' hT' h' => absurd h' (h B' x' L' hT')⟩

theorem prop65_holds (hc : S6Ctx G p) (hin : Prop65Inputs G p) (_h61 : Prop61At G p)
    (h62 : Lemma62At G p) (h64 : Lemma64At G p) : Prop65At G p := by
  intro q hq hq2 hqp B₀ x₀ L₀ hS₀ hChev₀
  have hT₀ : InTq q p B₀ x₀ L₀ := ⟨IsSStarMax.inT hc hS₀, hChev₀⟩
  have h₀ := case234_of_sstarMax hc hin h62 h64 hq hq2 hqp hS₀ hChev₀
  obtain ⟨B, x, L, hT, h234, hCP⟩ := exists_choice hT₀ h₀
  exact prop65_main hc hin h62 h64 hq hq2 hqp hT h234 hCP

end CFSG.LocalAnalysis.GLTheoremA
