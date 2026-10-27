module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Cor112
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerT
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure CE (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (q : ℕ) : Prop where
  hyp : Hyp111 G m p B x L
  nosplit : NoSplit16 p L
  prime : q.Prime
  odd : q ≠ 2
  rank : GLATwoLocalRank q ↥L = evenRank ↥L
  ge : m ≤ evenRank ↥L
  bad : q ∉ Mu G m
  case : m < evenRank ↥L ∨ RQuad G m p B x L

structure RedB (G : Type) [Group G] [Finite G] (p q : ℕ) (B : Subgroup G) (x : G) (L M D E F J : Subgroup G) : Prop where
  two_local : IsTwoLocal M
  closed : ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P → Subgroup.normalizer (P : Set G) ≤ M
  sylow : ∃ R : Sylow q G, GLAWeakCore q (R : Subgroup G) ≤ M
  L_le : L ≤ M
  cx_le : Subgroup.centralizer ({x} : Set G) ≤ M
  sc : IsSC p B
  q_ne : q ≠ p
  D_le : D ≤ E
  E_le : E ≤ B
  x_mem : x ∈ D
  card_D : Nat.card D = p ^ 2
  card_E : Nat.card E = p ^ 3
  J_comp : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) J
  B_norm : B ≤ Subgroup.normalizer (J : Set G)
  J_layer : GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥
  F_le : F ≤ L ⊓ Subgroup.centralizer (D : Set G)
  F_elem : IsElemAbelian q F
  F_norm : F ≤ Subgroup.normalizer (J : Set G)
  F_rank : 3 ≤ CFSG.Open.pRank q F

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

private theorem counterb_isPGroup_subgroupOf {q : ℕ} {Q L : Subgroup G} (hQ : IsPGroup q Q) :
    IsPGroup q (Q.subgroupOf L) := by
  intro g
  obtain ⟨k, hk⟩ := hQ ⟨((g : L) : G), Subgroup.mem_subgroupOf.1 g.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun y : ↥Q => (y : G)) hk
  simpa using h

private theorem counterb_twoLocalRank_le {q : ℕ} (hq : q.Prime) (L : Subgroup G) :
    GLATwoLocalRank q ↥L ≤ GLATwoLocalRank q G := by
  refine csSup_le' ?_
  rintro k ⟨H, hH, rfl⟩
  obtain ⟨P, hP, hPq, rfl⟩ := hH
  obtain ⟨E, hEH, hE, hEc⟩ :=
    CFSG.SectionRank.exists_pRank hq.one_lt (Subgroup.normalizer (P : Set ↥L))
  have hSne : P.map L.subtype ≠ ⊥ := by
    intro h
    apply hP
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have h1 : L.subtype y ∈ P.map L.subtype := Subgroup.mem_map_of_mem _ hy
    rw [h, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hEc' : Nat.card (E.map L.subtype) =
      q ^ CFSG.Open.pRank q (Subgroup.normalizer (P : Set ↥L)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]
  exact CFSG.HardMathSupport.Solomon.Coordinator.i1020_le_glaTwoLocalRank hq (hPq.map L.subtype) hSne
    ((Subgroup.map_mono hEH).trans (Subgroup.le_normalizer_map L.subtype))
    (CFSG.SectionRank.isElemAbelian_map hE L.subtype) hEc'

private theorem counterb_card_le_of_twoLocal {p : ℕ} (hp : p.Prime) {M E : Subgroup G}
    (hM : IsTwoLocal M) (hEM : E ≤ M) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ GLATwoLocalRank p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hEp : IsPGroup p ↥E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hEp
  have h1 : n ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp1 (le_refl E) hE hn
  have h2 : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p M := CFSG.SectionRank.pRank_mono hp1 hEM
  have hbdd : BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
    ⟨CFSG.Open.pRank p (⊤ : Subgroup G), by
      rintro k ⟨H, -, rfl⟩
      exact CFSG.SectionRank.pRank_mono hp1 le_top⟩
  have h3 : CFSG.Open.pRank p M ≤ GLATwoLocalRank p G := le_csSup hbdd ⟨M, hM, rfl⟩
  rw [hn]
  exact Nat.pow_le_pow_right hp.pos (h1.trans (h2.trans h3))

private theorem counterb_sup_zpowers {p : ℕ} (hp : p.Prime) {B L T : Subgroup G} {x : G}
    (hB : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hxL : ∀ l ∈ L, l * x = x * l)
    (hd : IsDirectZpowersInf B x L) (hT : IsElemAbelian p T) (hTL : T ≤ L) :
    IsElemAbelian p (T ⊔ Subgroup.zpowers x) ∧
      Nat.card ↥(T ⊔ Subgroup.zpowers x) = Nat.card ↥T * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hZ : IsElemAbelian p (Subgroup.zpowers x) := CFSG.SectionRank.QTK.isElemAbelian_zpowers hxp
  have hAB : ∀ a ∈ T, ∀ b ∈ Subgroup.zpowers x, Commute a b := by
    intro a ha b hb
    have hax : Commute a x := hxL a (hTL ha)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact hax.zpow_right n
  have hdisj : ∀ y ∈ T, y ∈ Subgroup.zpowers x → y = 1 := by
    intro y hyT hyx
    have hyB : y ∈ Subgroup.zpowers x ⊓ (B ⊓ L) :=
      ⟨hyx, (Subgroup.zpowers_le.2 hxB) hyx, hTL hyT⟩
    rw [hd.2] at hyB
    exact Subgroup.mem_bot.1 hyB
  obtain ⟨h1, h2⟩ := CFSG.SectionRank.QTK.CentreFact.layer_isElemAbelian_sup_card hT hZ hAB hdisj
  exact ⟨h1, by rw [h2, Nat.card_zpowers, hord]⟩

private theorem counterb_inf_cent_sup {K T : Subgroup G} {x : G} (hK : ∀ l ∈ K, l * x = x * l) :
    K ⊓ Subgroup.centralizer ((T ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
      K ⊓ Subgroup.centralizer (T : Set G) := by
  ext l
  constructor
  · rintro ⟨hlK, hl⟩
    exact ⟨hlK, Subgroup.centralizer_le (fun t ht => (le_sup_left : T ≤ T ⊔ Subgroup.zpowers x) ht) hl⟩
  · rintro ⟨hlK, hl⟩
    refine ⟨hlK, ?_⟩
    have hT : T ≤ Subgroup.centralizer ({l} : Set G) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hl t ht)
    have hx : Subgroup.zpowers x ≤ Subgroup.centralizer ({l} : Set G) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hK l hlK).symm)
    have hsup : T ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({l} : Set G) := sup_le hT hx
    exact Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hsup hh)

theorem ce_weakCore (hctx : ThmACtx G m) (hce : CE G m p B x L q) : q ≠ p ∧ GLAWeakCoreLocal G q := by
  have hm4 : 4 ≤ m := hctx.1.four_le
  have hmL : m ≤ GLATwoLocalRank q ↥L := by
    rw [hce.rank]
    exact hce.ge
  have hdvd : q ∣ Nat.card G := by
    obtain ⟨S₀, -, -, hS₀⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.i1020_exists_twoLocal hce.prime
        (show 1 ≤ GLATwoLocalRank q ↥L by omega)
    exact hS₀.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L))
  have hGq : m ≤ GLATwoLocalRank q G := hmL.trans (counterb_twoLocalRank_le hce.prime L)
  have hqp : q ≠ p := by
    rintro rfl
    exact hce.bad hce.hyp.mu
  refine ⟨hqp, ?_⟩
  rcases hGq.lt_or_eq with hlt | heq
  · have hβ : q ∈ GLABeta (m + 1) G :=
      show q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ m + 1 ≤ GLATwoLocalRank q G from
        ⟨hce.prime, hce.odd, hdvd, hlt⟩
    exact hctx.1.weakCore_above q hβ
  · have hβ : q ∈ GLABeta m G :=
      show q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ m ≤ GLATwoLocalRank q G from
        ⟨hce.prime, hce.odd, hdvd, hGq⟩
    rcases hctx.1.weakCore_or_delta q hβ with hwc | hdelta
    · exact hwc
    · exact absurd (show q ∈ Mu G m from ⟨hβ, heq.symm, hdelta⟩) hce.bad

theorem exists_closed_M (h2315 : I2315aAt G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L : Subgroup G} (hL : IsChev2 L)
    (h4 : 4 ≤ GLATwoLocalRank q ↥L) (hwc : GLAWeakCoreLocal G q) :
    ∃ M : Subgroup G, IsTwoLocal M ∧ L ≤ M ∧ (∃ R : Sylow q G, GLAWeakCore q (R : Subgroup G) ≤ M) ∧
      ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P →
        Subgroup.normalizer (P : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  let S : Sylow q ↥L := default
  let Qo : Subgroup G := S.toSubgroup.map L.subtype
  have hQo_q : IsPGroup q Qo := S.isPGroup'.map L.subtype
  have hQoL : Qo ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hmax : ∀ Q : Subgroup G, IsPGroup q Q → Q ≤ L → Qo ≤ Q → Q = Qo := by
    intro Q hQ hQL hQoQ
    have hQ' : IsPGroup q (Q.subgroupOf L) := counterb_isPGroup_subgroupOf hQ
    have hSQ : S.toSubgroup ≤ Q.subgroupOf L := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      exact hQoQ (Subgroup.mem_map_of_mem L.subtype hy)
    have hEq : Q.subgroupOf L = S.toSubgroup := S.is_maximal' hQ' hSQ
    calc Q = Q ⊓ L := (inf_eq_left.2 hQL).symm
      _ = (Q.subgroupOf L).map L.subtype := (Subgroup.subgroupOf_map_subtype Q L).symm
      _ = Qo := by rw [hEq]
  obtain ⟨R, hQR⟩ := hQo_q.exists_le_sylow
  have h3R : 3 ≤ CFSG.Open.pRank q (R : Subgroup G) := by
    rw [(CFSG.SectionRank.pRank_sylow R).1]
    exact hwc.1
  obtain ⟨H, hH, hWH⟩ := hwc.2 R
  have hRH : (R : Subgroup G) ≤ H :=
    (Subgroup.le_normalizer (H := (R : Subgroup G))).trans
      ((S9.normalizer_le_weakCore hq (le_refl (R : Subgroup G)) h3R).trans hWH)
  have hLH : L ≤ H := by
    refine (h2315 q hq hq2 L Qo hL hQo_q hQoL hmax h4).trans (sSup_le ?_)
    rintro N ⟨X, hXQ, h2X, h3X, rfl⟩
    have hXR : X ≤ (R : Subgroup G) := hXQ.trans hQR
    have h3R' : 3 ≤ CFSG.Open.pRank q (X ⊔ ((R : Subgroup G) ⊓ Subgroup.centralizer (X : Set G))) :=
      h3X.trans (CFSG.SectionRank.pRank_mono hq.one_lt
        (sup_le_sup_left (inf_le_inf hQR le_rfl) X))
    have hNX : Subgroup.normalizer (X : Set G) ≤ GLAWeakCore q (R : Subgroup G) := by
      unfold GLAWeakCore rankThreeAschCore
      exact le_sSup ⟨X, hXR, h2X, h3R', rfl⟩
    exact inf_le_left.trans (hNX.trans hWH)
  refine ⟨H, hH, hLH, ⟨R, hWH⟩, fun P hP hPH h3P => S9.normalizer_le_of_le_M hq R hRH ?_ hP hPH h3P⟩
  intro Q hQR' h3Q
  exact (S9.normalizer_le_weakCore hq hQR' h3Q).trans hWH

theorem cx_le_M {q : ℕ} (hq : q.Prime) (hH : Hyp111 G m p B x L) {M : Subgroup G} (hLM : L ≤ M)
    (h4 : 4 ≤ GLATwoLocalRank q ↥L)
    (hclosed : ∀ P : Subgroup G, IsPGroup q P → P ≤ M → 3 ≤ CFSG.Open.pRank q P →
      Subgroup.normalizer (P : Set G) ≤ M) : Subgroup.centralizer ({x} : Set G) ≤ M := by
  refine le_of_subnormal_of_closed hq hH.comp.2.1 hLM ?_ hclosed
  have := twoLocalRank_le_pRank hq L
  omega

theorem sc_of_cx_le_M (hH : Hyp111 G m p B x L) {M : Subgroup G} (hM : IsTwoLocal M)
    (hcx : Subgroup.centralizer ({x} : Set G) ≤ M) : IsSC p B := by
  refine isSC_of_le_M hH.prime hH.bmax hM ?_ ?_
  · intro b hb
    refine hcx ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (isElemAbelian_commute hH.elem hb hH.mem).symm ▸ rfl
  · intro g hg
    refine hcx ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hg x hH.mem).symm

theorem pRank_L_le (hH : Hyp111 G m p B x L) {M : Subgroup G} (hM : IsTwoLocal M)
    (hcx : Subgroup.centralizer ({x} : Set G) ≤ M) (hd : IsDirectZpowersInf B x L) :
    CFSG.Open.pRank p L ≤ m - 1 := by
  have hp : p.Prime := hH.prime
  have hxL : ∀ l ∈ L, l * x = x * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hH.comp.1 hl)
  have hm : GLATwoLocalRank p G = m := hH.mu.2.1
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEL hE => ?_
  obtain ⟨hE'el, hE'card⟩ := counterb_sup_zpowers hp hH.elem hH.mem hH.ne_one hxL hd hE hEL
  have hE'M : E ⊔ Subgroup.zpowers x ≤ M :=
    sup_le (hEL.trans (hH.comp.1.trans hcx))
      (Subgroup.zpowers_le.2 (hcx (Subgroup.mem_centralizer_singleton_iff.2 rfl)))
  have hle := counterb_card_le_of_twoLocal hp hM hE'M hE'el
  rw [hE'card, hm] at hle
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hle
      have h2 := hp.two_le
      have h3 : 0 < Nat.card E := Nat.card_pos
      nlinarith
    · exact h0
  have hpow : p ^ m = p ^ (m - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow] at hle
  exact Nat.le_of_mul_le_mul_right hle hp.pos

theorem isSCIn_of_isSC (hH : Hyp111 G m p B x L) (hsc : IsSC p B) (hd : IsDirectZpowersInf B x L) :
    IsSCIn p L (B ⊓ L) := by
  refine ⟨inf_le_right, isElemAbelian_mono hH.elem inf_le_left, ?_⟩
  intro g hg hord
  have hgL : g ∈ L := hg.1
  have hgC : g ∈ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G) := hg.2
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hH.comp.1 hgL)
  have hBL : B ⊓ L ≤ Subgroup.centralizer ({g} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hgC b hb)
  have hxcent : Subgroup.zpowers x ≤ Subgroup.centralizer ({g} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hgx.symm)
  have hBcent : B ≤ Subgroup.centralizer ({g} : Set G) := by
    calc B = Subgroup.zpowers x ⊔ (B ⊓ L) := hd.1
      _ ≤ Subgroup.centralizer ({g} : Set G) := sup_le hxcent hBL
  have hgB : g ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hBcent hh)
  exact ⟨hsc.2 g hgB hord, hgL⟩

theorem transfer_DEJ (hH : Hyp111 G m p B x L) (hd : IsDirectZpowersInf B x L) {D E F J : Subgroup G}
    (hDE : D ≤ E) (hEA : E ≤ B ⊓ L) (hD : Nat.card D = p) (hE : Nat.card E = p ^ 2)
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) J) (hAJ : B ⊓ L ≤ Subgroup.normalizer (J : Set G))
    (hJE : GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) (hF : F ≤ L ⊓ Subgroup.centralizer (D : Set G)) :
    ∃ D' E' : Subgroup G, D' ≤ E' ∧ E' ≤ B ∧ x ∈ D' ∧ Nat.card D' = p ^ 2 ∧ Nat.card E' = p ^ 3 ∧
      GLAPComponent p (L ⊓ Subgroup.centralizer (D' : Set G)) J ∧ B ≤ Subgroup.normalizer (J : Set G) ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (E' : Set G)) ≠ ⊥ ∧ F ≤ L ⊓ Subgroup.centralizer (D' : Set G) := by
  have hp : p.Prime := hH.prime
  have hxL : ∀ l ∈ L, l * x = x * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hH.comp.1 hl)
  have hEL : E ≤ L := hEA.trans inf_le_right
  have hDL : D ≤ L := hDE.trans hEL
  have hEB : E ≤ B := hEA.trans inf_le_left
  have hDB : D ≤ B := hDE.trans hEB
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJx : ∀ l ∈ J, l * x = x * l := fun l hl => hxL l (hJL hl)
  obtain ⟨-, hD'card⟩ :=
    counterb_sup_zpowers hp hH.elem hH.mem hH.ne_one hxL hd (isElemAbelian_mono hH.elem hDB) hDL
  obtain ⟨-, hE'card⟩ :=
    counterb_sup_zpowers hp hH.elem hH.mem hH.ne_one hxL hd (isElemAbelian_mono hH.elem hEB) hEL
  have hxnorm : x ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun j hj => hJx j hj)
  refine ⟨D ⊔ Subgroup.zpowers x, E ⊔ Subgroup.zpowers x, sup_le_sup_right hDE _,
    sup_le hEB (Subgroup.zpowers_le.2 hH.mem),
    (le_sup_right : Subgroup.zpowers x ≤ D ⊔ Subgroup.zpowers x) (Subgroup.mem_zpowers x), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hD'card, hD, pow_two]
  · rw [hE'card, hE]
    ring
  · rw [counterb_inf_cent_sup hxL]
    exact hJ
  · calc B = Subgroup.zpowers x ⊔ (B ⊓ L) := hd.1
      _ ≤ Subgroup.normalizer (J : Set G) := sup_le (Subgroup.zpowers_le.2 hxnorm) hAJ
  · rw [counterb_inf_cent_sup hJx]
    exact hJE
  · rw [counterb_inf_cent_sup hxL]
    exact hF

theorem redB (hctx : ThmACtx G m) (hsf : StageFacts G m) (h161 : I161aAt G) (h165 : I165At G) (h2315 : I2315aAt G)
    (hce : CE G m p B x L q) : ∃ M D E F J : Subgroup G, RedB G p q B x L M D E F J := by
  have hH := hce.hyp
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  have hm4 : 4 ≤ m := hctx.1.four_le
  have h4 : 4 ≤ GLATwoLocalRank q ↥L := hce.rank ▸ hm4.trans hce.ge
  obtain ⟨hqp, hwc⟩ := ce_weakCore hctx hce
  obtain ⟨M, hM, hLM, hsylow, hclosed⟩ := exists_closed_M h2315 hce.prime hce.odd hH.isChev2 h4 hwc
  have hcx : Subgroup.centralizer ({x} : Set G) ≤ M := cx_le_M hce.prime hH hLM h4 hclosed
  have hsc : IsSC p B := sc_of_cx_le_M hH hM hcx
  obtain ⟨hnoZ, hinner⟩ := h161 p hp hp2 L hH.isChev2 hce.nosplit
  have hin : ∀ b ∈ B, InducesInnerMod p L b := hinner B hH.elem hH.idiag
  have hd : IsDirectZpowersInf B x L :=
    bdecomp_of_sc hp hp2 hH.comp hH.qs hnoZ hsc hH.mem hH.ne_one hH.comp.1 hH.norm hH.cent hin
  have hcard : Nat.card ↥(B ⊓ L) = p ^ (m - 1) := card_inf_eq hH hd
  have hscL : IsSCIn p L (B ⊓ L) := isSCIn_of_isSC hH hsc hd
  have hrk : CFSG.Open.pRank p (B ⊓ L) = m - 1 := pRank_eq_of_card hp (isElemAbelian_mono hH.elem inf_le_left) hcard
  have ha : GLATwoLocalRank p ↥L ≤ CFSG.Open.pRank p (B ⊓ L) := by
    rw [hrk]
    exact (twoLocalRank_le_pRank hp L).trans (pRank_L_le hH hM hcx hd)
  have hmax : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p (B ⊓ L) := (pRank_L_le hH hM hcx hd).trans hrk.ge
  have hb : (⁅B ⊓ L, nGen (B ⊓ L) L⁆ : Subgroup G) ≠ ⊥ ∨ CFSG.Open.pRank p (B ⊓ L) + 2 ≤ evenRank ↥L := by
    rcases hce.case with hgt | hR
    · right
      rw [hrk]
      have h1 : m - 1 + 2 = m + 1 := by omega
      rw [h1]
      exact hgt
    · left
      exact (cor112_indep hctx hsf h161 hR hce.nosplit).comm
  have hc1 : evenRank ↥L = GLATwoLocalRank q ↥L := hce.rank.symm
  have hc2 : CFSG.Open.pRank p (B ⊓ L) + 1 ≤ evenRank ↥L := by
    rw [hrk]
    have := hce.ge
    omega
  have hc3 : 4 ≤ CFSG.Open.pRank p (B ⊓ L) + 1 := by
    rw [hrk]
    omega
  obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hJE, hF, hFe, hFJ, hFr⟩ :=
    h165 p q hp hp2 hce.prime hce.odd hqp L (B ⊓ L) hH.isChev2 hce.nosplit hnoZ hscL ha hmax hb hc1 hc2 hc3
  obtain ⟨D', E', hDE', hE'B, hxD, hD', hE'', hJ', hBJ, hJE', hF'⟩ := transfer_DEJ hH hd hDE hEA hD hE hJ hAJ hJE hF
  refine ⟨M, D', E', F, J, ⟨hM, hclosed, hsylow, hLM, hcx, hsc, hqp, hDE', hE'B, hxD, hD', hE'', hJ', hBJ, hJE', hF', hFe, hFJ, hFr⟩⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
