module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Common
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxN11
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Inputs121 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  common : CommonInputs G p
  rank : RankAutSmallAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i269 : I269At G
  i269six : I269SixAt G
  level2 : LevelTwoAt G
  smallBridge : StdSubSmallAt G
  lbal : LBalanceAt G p

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem l121_p_three (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) (hs : SmallType p K) : p = 3 := by
  refine hin.rank p _ K B h.prime h.odd (std_pcomp' h hin.common) hs (B_norm_K h) h.tri.bmax.1 ?_
  rw [centMod_inf_eq h hin.common, h.card_D, h.card_B, ← pow_add]
  exact Nat.pow_le_pow_right h.prime.pos h.four_le

theorem l121_all_small (h : Cfg12 G m 3 B x L D K) (hsmall : GLASmall K) :
    ∀ D' K' : Subgroup G, GLAStdSubPre 3 B x L D' K' → GLASmall K' := by
  intro D' K' hP
  by_contra hns
  exact h.std.2 ⟨rfl, D', K', hP, hns⟩ hsmall

theorem l121_small_case (h : Cfg12 G m 3 B x L D K) (hin : Inputs121 G 3) (hs : SmallType 3 K) :
    U42Type 3 K ∧ (∀ b ∈ B, InducesInnerMod 3 L b) ∧
      catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i) := by
  have hsmall : GLASmall K := hin.smallBridge B x L D K h.tri.star h.pow_four_le (h.tri.qs h.ctx) (h.tri.chev2 h.ctx) h.tri.idiag h.pre hs
  obtain ⟨hL, hinner, hU⟩ := hin.i171two B x L h.tri.star h.pow_four_le (h.tri.qs h.ctx) (h.tri.chev2 h.ctx)
    (kGroup_centralizer h.ctx.toS6 h.tri.ne_one) h.tri.idiag ⟨D, K, h.pre⟩ (l121_all_small h hsmall)
  exact ⟨hU D K h.pre, hinner, hL⟩

theorem exists_D'' (h : Cfg12 G m p B x L D K) {E : Subgroup G} (hE : IsE3 p B E) :
    ∃ D'' : Subgroup G, IsE2 p B D'' ∧ D'' ≤ Subgroup.zpowers x ⊔ E ∧ x ∉ D'' := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hzB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 h.tri.mem
  have hSB : Subgroup.zpowers x ⊔ E ≤ B := sup_le hzB hE.1
  have hSel : IsElemAbelian p (Subgroup.zpowers x ⊔ E) := isElemAbelian_mono h.tri.bmax.1 hSB
  obtain ⟨F, hFS, -, hdisj, hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing hp hSel
    (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ E) (bot_le : (⊥ : Subgroup G) ≤ Subgroup.zpowers x ⊔ E)
    (inf_bot_eq _)
  have hcard := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hSel le_sup_left hFS hdisj hsup
  have hxp : x ^ p = 1 := h.elem.2 x h.xD
  have hzc : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp h.tri.ne_one
  have hSE : p ^ 3 ≤ Nat.card ↥(Subgroup.zpowers x ⊔ E) := by
    rw [← hE.2.2]
    exact Subgroup.card_le_of_le le_sup_right
  have hFel : IsElemAbelian p F := isElemAbelian_mono hSel hFS
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hFel)
  have hk2 : 2 ≤ k := by
    rw [hzc, hk, ← pow_succ'] at hcard
    have : p ^ 3 ≤ p ^ (k + 1) := hcard ▸ hSE
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨D'', hD''F, hD''el, hD''c⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hFel
    (n := 2) (hk ▸ pow_dvd_pow p hk2)
  refine ⟨D'', ⟨(hD''F.trans hFS).trans hSB, hD''el, hD''c⟩, hD''F.trans hFS, fun hxD => ?_⟩
  have hxF : x ∈ Subgroup.zpowers x ⊓ F := ⟨Subgroup.mem_zpowers x, hD''F hxD⟩
  rw [hdisj] at hxF
  exact h.tri.ne_one (Subgroup.mem_bot.1 hxF)

theorem l121_layer_D'' (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) {E D'' : Subgroup G} (hE : IsE3 p B E)
    (hD : IsE2 p B D'') (hDE : D'' ≤ Subgroup.zpowers x ⊔ E)
    (hne : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    GLAPLayer p (L ⊓ Subgroup.centralizer (D'' : Set G)) ≠ ⊥ := by
  have hzB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 h.tri.mem
  have hE'B : Subgroup.zpowers x ⊔ E ≤ B := sup_le hzB hE.1
  have hFB : Subgroup.zpowers x ⊔ D'' ≤ B := sup_le hzB hD.1
  have hE'el : IsElemAbelian p (Subgroup.zpowers x ⊔ E) := isElemAbelian_mono h.tri.bmax.1 hE'B
  have hFel : IsElemAbelian p (Subgroup.zpowers x ⊔ D'') := isElemAbelian_mono h.tri.bmax.1 hFB
  have hxE' : x ∈ Subgroup.zpowers x ⊔ E := (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
  have hxF : x ∈ Subgroup.zpowers x ⊔ D'' := (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
  have hFE' : Subgroup.zpowers x ⊔ D'' ≤ Subgroup.zpowers x ⊔ E := sup_le le_sup_left hDE
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := h.tri.comp.1
  have hcs : ∀ H : Subgroup G, Subgroup.centralizer ((Subgroup.zpowers x ⊔ H : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (H : Set G) := fun H => by
    rw [centralizer_sup_eq, S3.centralizer_zpowers x]
  have hLH : ∀ H : Subgroup G, L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ H : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer (H : Set G) := fun H => by
    rw [hcs, ← inf_assoc, inf_eq_left.2 hLx]
  have h1 := layer_cs_eq' h hin.common.bal hE'el hxE'
  have h2 := layer_cs_eq' h hin.common.bal hFel hxF
  have hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers x ⊔ D'' : Subgroup G) : Set G)) :=
    CFSG.Open.IsKGroup.of_le (kGroup_centralizer h.ctx.toS6 h.tri.ne_one)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxF))
  have hPX : Subgroup.zpowers x ⊔ E ≤ Subgroup.centralizer ((Subgroup.zpowers x ⊔ D'' : Subgroup G) : Set G) :=
    fun e he => Subgroup.mem_centralizer_iff.2 fun f hf => isElemAbelian_commute h.tri.bmax.1 (hFB hf) (hE'B he)
  have hle := hin.lbal _ _ hX hPX (isPGroup_of_isElemAbelian hE'el)
  rw [inf_eq_right.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE'))] at hle
  intro hbot
  apply hne
  rw [← hLH E, h1]
  refine le_bot_iff.1 (hle.trans ?_)
  rw [← h2, hLH D'']
  exact hbot.le

theorem l121_card_D'' (h : Cfg12 G m p B x L D K) {D'' : Subgroup G} (hD : IsE2 p B D'') (hx : x ∉ D'') :
    Nat.card D'' = p ^ 2 * Nat.card ↥(D'' ⊓ centModSubgroup p L) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : D'' ⊓ centModSubgroup p L = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgx : g ∈ Subgroup.zpowers x := by
      rw [← B_inf_centMod_eq h]
      exact ⟨hD.1 hg.1, hg.2⟩
    by_contra hg1
    have hg1' : g ≠ 1 := fun e => hg1 (by rw [e]; exact Subgroup.one_mem _)
    have hgp : g ^ p = 1 := h.tri.bmax.1.2 g (hD.1 hg.1)
    have hordg : orderOf g = p := orderOf_eq_prime hgp hg1'
    have hordx : orderOf x = p := orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one
    have hle : Subgroup.zpowers g ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hgx
    have heq : Subgroup.zpowers g = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hordg, hordx])
    exact hx ((Subgroup.zpowers_le.2 hg.1) (heq ▸ Subgroup.mem_zpowers x))
  rw [h1, Subgroup.card_bot, mul_one]
  exact hD.2.2

theorem l121_gstar_layer (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) (hG : IsGStar p B L) :
    ∃ D'' : Subgroup G, IsE2 p B D'' ∧
      Nat.card D'' = p ^ 2 * Nat.card ↥(D'' ⊓ centModSubgroup p L) ∧
      GLAPLayer p (L ⊓ cs D'') ≠ ⊥ := by
  obtain ⟨E, hEB, hEel, hEcard, hne⟩ := hG
  rw [closureIn_eq_self h.tri.norm] at hne
  have hE : IsE3 p B E := ⟨hEB, hEel, hEcard⟩
  obtain ⟨D'', hD, hDE, hx⟩ := exists_D'' h hE
  exact ⟨D'', hD, l121_card_D'' h hD hx, l121_layer_D'' h hin hE hD hDE hne⟩

theorem l121_layer_bot (h : Cfg12 G m 3 B x L D K) (hin : Inputs121 G 3)
    (hL : catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hinner : ∀ b ∈ B, InducesInnerMod 3 L b) {D'' : Subgroup G} (hD : IsE2 3 B D'')
    (hcard : Nat.card D'' = 3 ^ 2 * Nat.card ↥(D'' ⊓ centModSubgroup 3 L)) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D'' : Set G)) = ⊥ := by
  have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    kGroup_centralizer h.ctx.toS6 h.tri.ne_one
  have hnorm : D'' ≤ Subgroup.normalizer (L : Set G) := hD.1.trans h.tri.norm
  obtain ⟨i, hi, hiso⟩ := hL
  rcases hi with hi | hi | hi
  · exact hin.i269 _ L D'' hK h.tri.comp ⟨i, Or.inr (Or.inr (Or.inl hi)), hiso⟩ hD.2.1 hnorm hcard
  · exact hin.i269 _ L D'' hK h.tri.comp ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi)))), hiso⟩ hD.2.1 hnorm hcard
  · exact hin.i269six _ L D'' hK h.tri.comp ⟨i, hi, hiso⟩ hD.2.1 hnorm
      (fun d hd => hinner d (hD.1 hd)) hcard

theorem l121_not_gstar (h : Cfg12 G m 3 B x L D K) (hin : Inputs121 G 3)
    (hL : catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hinner : ∀ b ∈ B, InducesInnerMod 3 L b) : ¬ IsGStar 3 B L := by
  intro hG
  obtain ⟨D'', hD, hcard, hne⟩ := l121_gstar_layer h hin hG
  exact hne (l121_layer_bot h hin hL hinner hD hcard)

theorem l121_d_two (h : Cfg12 G m 3 B x L D K) (hin : Inputs121 G 3)
    (hL : catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hnot : ¬ IsGStar 3 B L) : dLevel G 3 = 2 := by
  have hlev := IsSStarMax.level h.tri.star
  have h2 := hin.level2 _ L h.tri.comp hL
  rw [← hlev, tripleLevel, if_neg hnot, h2]
  norm_num

theorem l121_E_K (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) {E : Subgroup G} (hE : IsE3 p B E) (hDE : D ≤ E)
    (hne : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  have h1 := layer_cs_eq' h hin.common.bal hE.2.1 (hDE h.xD)
  have h2 := hin.common.bal h.prime h.ctx.ctx.ctx.kProper D E (isPGroup_of_isElemAbelian h.elem)
    (isPGroup_of_isElemAbelian hE.2.1) (fun d hd e he => isElemAbelian_commute hE.2.1 (hDE hd) he)
  rw [std_layer h hin.common, inf_eq_right.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDE))] at h2
  rw [h2, ← h1]
  exact hne

theorem l121_big_case (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) (hs : ¬ SmallType p K) :
    ∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  rcases hin.i265 B x L D K h.prime h.odd h.tri.star h.pow_four_le (h.tri.qs h.ctx) (h.tri.chev2 h.ctx)
      (kGroup_centralizer h.ctx.toS6 h.tri.ne_one) h.tri.idiag h.pre with h1 | ⟨hp3, hK⟩
  · exact h1
  · subst hp3
    exact absurd hK hs

theorem l121_d_five (h : Cfg12 G m p B x L D K) {E : Subgroup G} (hE : IsE3 p B E)
    (hne : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) : dLevel G p = 5 := by
  have hlev := IsSStarMax.level h.tri.star
  have hG : IsGStar p B L := ⟨E, hE.1, hE.2.1, hE.2.2, by rwa [closureIn_eq_self h.tri.norm]⟩
  rw [← hlev, tripleLevel, if_pos hG]

end S12

open S12 in
theorem lemma121 {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}
    (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) : Concl121 G p B L D K := by
  by_cases hs : SmallType p K
  · left
    have hp3 := l121_p_three h hin hs
    subst hp3
    obtain ⟨hU, hinner, hL⟩ := l121_small_case h hin hs
    exact ⟨hU, rfl, l121_d_two h hin hL (l121_not_gstar h hin hL hinner), hinner, hL⟩
  · right
    obtain ⟨E, hE, hDE, hne⟩ := l121_big_case h hin hs
    exact ⟨hs, l121_d_five h hE hne, E, hE, hDE, hne, l121_E_K h hin hE hDE hne⟩

end CFSG.LocalAnalysis.GLTheoremA
