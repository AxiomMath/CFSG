module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma103
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs104

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Lemma104Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  lemma102 : Lemma102Inputs G p
  i133 : I133At G p
  i148d : I148DownAt G
  fieldu48 : FieldU48At G
  i1431 : I1431ClAt G
  i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4
  lbal : LBalanceAt G p

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

@[expose] def isListGamma (i : TauCeti.CFSGIndex) : Prop :=
  S9.isU4eight i ∨ S9.isU5two i ∨ S9.isU6two i ∨ S9.isSp8two i ∨ S9.isD4two i

structure H104 (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b a : G) : Prop where
  mem : a ∈ Dgrp b x
  ne : a ≠ 1
  ess : IsEssential p B a
  single : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)
  lt : ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a)
  hT : ∃ T : Subgroup G, T ≤ Jpart p (Ipart p L b) a ∧ IsPGroup 2 T ∧
    B ≤ Subgroup.normalizer (T : Set G) ∧ ¬ T ≤ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a)

@[expose] def Concl104 (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b a : G) : Prop :=
  IsS2 p B a (Jpart p (Ipart p L b) a) ∧
    ((∃ d ∈ Dgrp b x, FieldOn p d (Jpart p (Ipart p L b) a)) ∨
      (p = 3 ∧ IsTD4 3 (Jpart p (Ipart p L b) a) ∧
        (∃ d ∈ Dgrp b x, NonInner 3 d (Jpart p (Ipart p L b) a)) ∧ IsG2Quot 3 (Ipart p L b)))

private theorem lemma104_mem_normalizer_inf {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hX hY ⊢
  rw [gLBConj_inf, hX, hY]

private theorem lemma104_isQuasisimple_of_marking {Q : Type} [Group Q]
    {P : CFSG.Assembly.LargeEvenMarkProp Q} (h : GLAMarking Q P) :
    CFSG.Open.IsQuasisimple Q := by
  obtain ⟨hK, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, -, θ, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨hK, θ.isSimpleGroup⟩

private theorem lemma104_closureIn_le {I A D : Subgroup G} (hID : I ≤ D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) : closureIn I A ≤ D := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  calc GLBConj a I ≤ GLBConj a D := gLBConj_mono hID
    _ = D := mem_normalizer_iff_gLBConj_eq.1 (hAD ha)

private theorem lemma104_comp_layer {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥(GLAPLayer p M) ⧸ GLAPPrimeCore p ↥(GLAPLayer p M))) :
    GLAPComponent p M (GLAPLayer p M) := by
  classical
  have hall : ∀ K : Subgroup G, GLAPComponent p M K → GLAPComponent p (GLAPLayer p M) K :=
    fun K hK => glaPComponent_of_le hp hK (le_sSup hK) (sSup_le fun K' hK' => hK'.1)
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : Subgroup G, GLAPComponent p M K₁ := by
    by_contra hcon
    push Not at hcon
    have hbot : GLAPLayer p M = ⊥ := sSup_eq_bot.2 fun K hK => (hcon K hK).elim
    obtain ⟨q₁, q₂, hne⟩ := (isQuasisimple_nontrivial hq).exists_pair_ne
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    have h1 : (g₁ : G) = 1 := Subgroup.mem_bot.1 (hbot ▸ g₁.2)
    have h2 : (g₂ : G) = 1 := Subgroup.mem_bot.1 (hbot ▸ g₂.2)
    have hg : g₁ = g₂ := Subtype.ext (h1.trans h2.symm)
    exact hne (by rw [hg])
  have hK₁I : K₁ ≤ GLAPLayer p M := le_sSup hK₁
  have hsame : ∀ K : Subgroup G, GLAPComponent p M K → K = K₁ := fun K hK =>
    glaPComponent_eq_of_isQuasisimple hq (hall K hK) (hall K₁ hK₁)
  have heq : GLAPLayer p M = K₁ :=
    le_antisymm (sSup_le fun K hK => (hsame K hK).le) hK₁I
  rw [heq]
  exact hK₁

private theorem lemma104_card_zpowers {B : Subgroup G} {p : ℕ} (hB : IsElemAbelian p B)
    (hp : p.Prime) {u : G} (hu : u ∈ B) (hu1 : u ≠ 1) : Nat.card (Subgroup.zpowers u) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 u hu) hu1]

private theorem lemma104_card_sup {B : Subgroup G} {p : ℕ} (hB : IsElemAbelian p B) (hp : p.Prime)
    {u v : G} (hu : u ∈ B) (hv : v ∈ B) (hu1 : u ≠ 1) (hvu : v ∉ Subgroup.zpowers u) :
    Nat.card ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcu : Nat.card (Subgroup.zpowers u) = p := lemma104_card_zpowers hB hp hu hu1
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ Subgroup.one_mem _)
  have hcv : Nat.card (Subgroup.zpowers v) = p := lemma104_card_zpowers hB hp hv hv1
  have hcomm : Commute u v := isElemAbelian_commute hB hu hv
  have hnorm : Subgroup.zpowers v ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun w hw => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (hcomm.zpow_left k).eq
  have hsup := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hcu, hcv] at hsup
  have hdvd : Nat.card ((Subgroup.zpowers u ⊓ Subgroup.zpowers v : Subgroup G)) ∣ p := by
    rw [← hcu]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hc1 : Nat.card ((Subgroup.zpowers u ⊓ Subgroup.zpowers v : Subgroup G)) = 1 := by
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact h1
    · exfalso
      have hle : Subgroup.zpowers u ⊓ Subgroup.zpowers v = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hcu])
      have huv : Subgroup.zpowers u ≤ Subgroup.zpowers v := inf_eq_left.1 hle
      have heq : Subgroup.zpowers u = Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge huv (by rw [hcu, hcv])
      exact hvu (by rw [heq]; exact Subgroup.mem_zpowers v)
  rw [hc1, mul_one] at hsup
  rw [hsup, sq]

private theorem lemma104_eq_sup_of_card {B D : Subgroup G} {p : ℕ} (hB : IsElemAbelian p B)
    (hp : p.Prime) (hDB : D ≤ B) (hDc : Nat.card D = p ^ 2) {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (hu1 : u ≠ 1) (hvu : v ∉ Subgroup.zpowers u) :
    D = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ D :=
    sup_le (Subgroup.zpowers_le.2 hu) (Subgroup.zpowers_le.2 hv)
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hDc, lemma104_card_sup hB hp (hDB hu) (hDB hv) hu1 hvu])).symm

private theorem lemma104_card_Dgrp {B : Subgroup G} {p : ℕ} (hB : IsElemAbelian p B) (hp : p.Prime)
    {b x : G} (hbB : b ∈ B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hbx : b ∉ Subgroup.zpowers x) :
    Nat.card (Dgrp b x) = p ^ 2 := by
  rw [dgrp_eq_sup, sup_comm]
  exact lemma104_card_sup hB hp hxB hbB hx1 hbx

private theorem lemma104_dgrp_le {B : Subgroup G} {b x : G} (hb : b ∈ B) (hx : x ∈ B) :
    Dgrp b x ≤ B :=
  (Subgroup.closure_le B).2 (Set.insert_subset_iff.2 ⟨hb, Set.singleton_subset_iff.2 hx⟩)

private theorem lemma104_b_mem {b x : G} : b ∈ Dgrp b x :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private theorem lemma104_x_mem {b x : G} : x ∈ Dgrp b x :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem lemma104_isKGroup_cx (hc : S10Ctx G p) {y : G} (hy : y ≠ 1) :
    CFSG.Open.IsKGroup ↥(cx y) :=
  isKGroup_of_isKProper hc.ctx.kProper
    (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hy)

private theorem lemma104_I_le {L : Subgroup G} {b : G} : Ipart p L b ≤ L ⊓ cx b :=
  sSup_le fun K hK => hK.1

private theorem lemma104_I_comp_C {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (hc : S10Ctx G p) (h : Cfg p B x L b) : GLAPComponent p (cx x ⊓ cx b) (Ipart p L b) := by
  have hp : p.Prime := hc.ctx.prime
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hsub : IsSubnormal (L ⊓ cx b) (cx x ⊓ cx b) := hLc.2.1.inf (cx b)
  have hq := lemma104_isQuasisimple_of_marking h.inner_I.2
  have hI : GLAPComponent p (L ⊓ cx b) (Ipart p L b) :=
    lemma104_comp_layer (M := L ⊓ cx b) hp hq
  exact glaPComponent_of_isSubnormal' hp hsub hI

private theorem lemma104_I_comp_J {B : Subgroup G} {x : G} {L : Subgroup G} {b a x' : G}
    (hc : S10Ctx G p) (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hx' : x' ∈ Dgrp b x) (hx'a : x' ∉ Subgroup.zpowers a) :
    GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx x') (Ipart p L b) := by
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hp : p.Prime := hc.ctx.prime
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hDB : Dgrp b x ≤ B := lemma104_dgrp_le h.mem hxB
  have hD : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x' :=
    lemma104_eq_sup_of_card hBel hp hDB (lemma104_card_Dgrp hBel hp h.mem hxB hx1 h.not_mem)
      ha hx' ha1 hx'a
  have hcent : cx x ⊓ cx b = cx a ⊓ cx x' := by
    apply le_antisymm
    · rintro g ⟨hgx, hgb⟩
      have hDg : Dgrp b x ≤ cx g := by
        refine (Subgroup.closure_le _).2 ?_
        rintro y (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hDg ha)).symm,
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hDg hx')).symm⟩
    · rintro g ⟨hga, hgx'⟩
      have hDg : Dgrp b x ≤ cx g := by
        rw [hD]
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 hga).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 hgx').symm
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hDg lemma104_x_mem)).symm,
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hDg lemma104_b_mem)).symm⟩
  have hA : GLAPComponent p (cx a ⊓ cx x') (Ipart p L b) := by
    rw [← hcent]
    exact lemma104_I_comp_C hc h
  have hIA : Ipart p L b ≤ cx a ⊓ cx x' := by
    rw [← hcent]
    exact (lemma104_I_comp_C hc h).1
  have hLa : GLAPLayer p (cx a) ≤ cx a := sSup_le fun K hK => hK.1
  have hJ : Jpart p (Ipart p L b) a ≤ cx a :=
    lemma104_closureIn_le (hIA.trans inf_le_left) (hLa.trans Subgroup.le_normalizer)
  exact glaPComponent_of_le hp hA (le_inf (le_closureIn_self _ _) (hIA.trans inf_le_right))
    (inf_le_inf_right _ hJ)

theorem B_le_N_J (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) :
    B ≤ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) := by
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hDB : Dgrp b x ≤ B := lemma104_dgrp_le h.mem hxB
  have hN : ∀ g ∈ B, g ∈ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) := by
    intro g hg
    have hgb : g ∈ cx b :=
      Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg h.mem)
    exact mem_normalizer_glaPLayer
      (lemma104_mem_normalizer_inf (sstar_norm h.star hg) (Subgroup.le_normalizer hgb))
  refine ⟨hN, fun g hg => ?_⟩
  have haB : a ∈ B := hDB ha
  have hga : g ∈ cx a :=
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg haB)
  exact mem_normalizer_closureIn (hN g hg) (mem_normalizer_glaPLayer (Subgroup.le_normalizer hga))

theorem exists_complement (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) :
    ∃ x' ∈ Dgrp b x, x' ∉ Subgroup.zpowers a ∧ Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x' := by
  classical
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hp : p.Prime := hc.ctx.prime
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hDB : Dgrp b x ≤ B := lemma104_dgrp_le h.mem hxB
  have haB : a ∈ B := hDB ha
  have hDc : Nat.card (Dgrp b x) = p ^ 2 := lemma104_card_Dgrp hBel hp h.mem hxB hx1 h.not_mem
  by_cases hxa : x ∈ Subgroup.zpowers a
  · have hza : Subgroup.zpowers x = Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxa) ?_
      rw [lemma104_card_zpowers hBel hp haB ha1, lemma104_card_zpowers hBel hp hxB hx1]
    have hba : b ∉ Subgroup.zpowers a := fun hb => h.not_mem (by rw [hza]; exact hb)
    exact ⟨b, lemma104_b_mem, hba,
      lemma104_eq_sup_of_card hBel hp hDB hDc ha lemma104_b_mem ha1 hba⟩
  · exact ⟨x, lemma104_x_mem, hxa,
      lemma104_eq_sup_of_card hBel hp hDB hDc ha lemma104_x_mem ha1 hxa⟩

theorem I_comp_in_J (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a x' : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hx' : x' ∈ Dgrp b x) (hx'a : x' ∉ Subgroup.zpowers a) (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) :
    GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx x') (Ipart p L b) :=
  lemma104_I_comp_J hc h ha ha1 hx' hx'a

theorem JGB_of_E (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (hA : CaseA p B x L b) :
    IsGStar p B (Jpart p (Ipart p L b) a) := by
  classical
  obtain ⟨E, hEB, hE, hEcard, hDE, hne⟩ := hA
  refine ⟨E, hEB, hE, hEcard, ?_⟩
  have hBN : B ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha).2
  rw [closureIn_eq_self hBN]
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hp : p.Prime := hc.ctx.prime
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hLc : GLAPComponent p (cx x) L := hS.2.2
  have hbB : b ∈ B := h.mem
  have hbE : b ∈ E := hDE lemma104_b_mem
  have hxE : x ∈ E := hDE lemma104_x_mem
  have hEx : E ≤ cx x := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hEB he) hxB)
  have hEb : E ≤ cx b := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hEB he) hbB)
  have hCEb : cs E ≤ cx b := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hg b hbE).symm
  have hCEx : cs E ≤ cx x := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hg x hxE).symm
  have hcx_ne : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hKx : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_of_isKProper hc.ctx.kProper hcx_ne
  have hYb_ne : cx x ⊓ cx b ≠ ⊤ := fun ht =>
    hcx_ne (top_le_iff.1 (by rw [← ht]; exact inf_le_left))
  have hKY : CFSG.Open.IsKGroup ↥(cx x ⊓ cx b) := isKGroup_of_isKProper hc.ctx.kProper hYb_ne
  have hEY : E ≤ cx x ⊓ cx b := fun e he => ⟨hEx he, hEb he⟩
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hE
  have hbal1 : GLAPLayer p ((cx x ⊓ cx b) ⊓ cs E) ≤ GLAPLayer p (cx x ⊓ cx b) :=
    hin.lbal (cx x ⊓ cx b) E hKY hEY hEp
  have hbal2 : GLAPLayer p (cx x ⊓ cx b) ≤ GLAPLayer p (cx x) := by
    have h2 := hin.lbal (cx x) (Subgroup.zpowers b) hKx (Subgroup.zpowers_le.2 (hEx hbE))
      (isPGroup_zpowers_of_mem hBel hbB)
    have e : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) = cx b := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [e] at h2
    exact h2
  have hYI : GLAPLayer p (cx x ⊓ cx b) ≤ Ipart p L b := by
    refine sSup_le fun K hK => ?_
    have hKL : K ≤ L := (le_sSup hK).trans (hbal2.trans (sstar_layer hc h.star).le)
    have hKM : K ≤ L ⊓ cx b := le_inf hKL (hK.1.trans inf_le_right)
    have hM : L ⊓ cx b ≤ cx x ⊓ cx b := inf_le_inf_right _ hLc.1
    exact le_sSup (glaPComponent_of_le hp hK hKM hM)
  have hK' : ∃ K', GLAPComponent p (L ⊓ cs E) K' ∧ K' ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hne (sSup_eq_bot.2 fun K hK => hcon K hK)
  obtain ⟨K', hK'c, hK'ne⟩ := hK'
  have hK'Y : GLAPComponent p (cx x ⊓ cs E) K' :=
    glaPComponent_of_isSubnormal' hp (hLc.2.1.inf (cs E)) hK'c
  have hK'I : K' ≤ Ipart p L b := by
    have h1 : K' ≤ GLAPLayer p (cx x ⊓ cs E) := le_sSup hK'Y
    have e : cx x ⊓ cs E = (cx x ⊓ cx b) ⊓ cs E := by
      rw [inf_assoc, inf_eq_right.2 hCEb]
    rw [e] at h1
    exact (h1.trans hbal1).trans hYI
  have hK'E : K' ≤ cs E := hK'c.1.trans inf_le_right
  have hI_L : Ipart p L b ≤ L := lemma104_I_le.trans inf_le_left
  have hK'IE : K' ≤ Ipart p L b ⊓ cs E := le_inf hK'I hK'E
  have hK'IEc : GLAPComponent p (Ipart p L b ⊓ cs E) K' :=
    glaPComponent_of_le hp hK'c hK'IE (inf_le_inf_right _ hI_L)
  have hIsub : IsSubnormal (Ipart p L b ⊓ cs E) (cs E) := by
    have h1 := (lemma104_I_comp_C hc h).2.1.inf (cs E)
    rwa [inf_eq_right.2 (le_inf hCEx hCEb)] at h1
  have hK'C : GLAPComponent p (cs E) K' := glaPComponent_of_isSubnormal' hp hIsub hK'IEc
  have hK'J : GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cs E) K' :=
    glaPComponent_of_le hp hK'C (le_inf ((hK'I).trans (le_closureIn_self _ _)) hK'E) inf_le_right
  intro hbot
  apply hK'ne
  have h3 : K' ≤ GLAPLayer p (Jpart p (Ipart p L b) a ⊓ cs E) := le_sSup hK'J
  rw [hbot] at h3
  exact le_bot_iff.1 h3

theorem D_centralizes (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hH : H104 p B x L b a)
    (hS2 : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)))
    (hcard : card2 p (Jpart p (Ipart p L b) a) ≤ 2 * card2 p (Ipart p L b)) :
    ∀ d ∈ Dgrp b x, CentMod p (Jpart p (Ipart p L b) a) d := by
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hDB : Dgrp b x ≤ B := lemma104_dgrp_le h.mem hxB
  have hDN : Dgrp b x ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    hDB.trans (B_le_N_J hc h hH.mem).2
  have hDp : IsPGroup p (Dgrp b x) := isPGroup_of_isElemAbelian (isElemAbelian_mono hBel hDB)
  have hIle : Ipart p L b ≤ L ⊓ cx b := lemma104_I_le
  have hDc : Dgrp b x ≤ cs (Ipart p L b) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.2 fun i hi =>
        Subgroup.mem_centralizer_singleton_iff.1 (hIle hi).2
    · exact Subgroup.mem_centralizer_iff.2 fun i hi =>
        Subgroup.mem_centralizer_singleton_iff.1 (hS.2.2.1 (hIle hi).1)
  exact hin.i133 hc.ctx.prime hc.ctx.odd (cx a) (Jpart p (Ipart p L b) a) (Ipart p L b) (Dgrp b x) hH.single hS2
    (le_closureIn_self _ _) hDN hDp hDc hcard

theorem not_innDiag_D (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a y : G} (h : Cfg p B x L b) (hH : H104 p B x L b a)
    (hS2 : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a))) (hyB : y ∈ B)
    (hy : FieldOn p y (Jpart p (Ipart p L b) a)) :
    ¬ InnDiagOn p (Dgrp b x) (Jpart p (Ipart p L b) a) := by
  classical
  intro hD
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hp : p.Prime := hc.ctx.prime
  have hxB : x ∈ B := hS.2.1.1
  have hDB : Dgrp b x ≤ B := lemma104_dgrp_le h.mem hxB
  have hBNJ : B ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h hH.mem).2
  have hBNI : B ≤ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) :=
    (B_le_N_J hc h hH.mem).1
  obtain ⟨x', hx'D, hx'a, -⟩ := exists_complement hc h hH.mem hH.ne
  have hcomp : GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx x') (Ipart p L b) :=
    lemma104_I_comp_J hc h hH.mem hH.ne hx'D hx'a
  by_cases hcx' : CentMod p (Jpart p (Ipart p L b) a) x'
  ·
    have hall := glaPLayer_inf_centralizer hp hH.single
      (isPGroup_zpowers_of_mem hBel (hDB hx'D)) hcx'
    have hIeq : Ipart p L b = GLAPLayer p (Jpart p (Ipart p L b) a ⊓ cx x') :=
      hall.2.1 _ hcomp
    exact hH.lt ((congrArg (fun K => K ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a)) hIeq).trans
      hall.2.2.2.2.1)
  ·
    have hx'N : x' ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
      hBNJ (hDB hx'D)
    have hx'p : x' ^ p = 1 := hBel.2 x' (hDB hx'D)
    have hyp : y ^ p = 1 := hBel.2 y hyB
    have hcomm : x' * y = y * x' := isElemAbelian_commute hBel (hDB hx'D) hyB
    have hyD : y ∉ Dgrp b x := by
      intro hyD
      have h1 := innDiagOn_mono hD (Subgroup.zpowers_le.2 hyD)
      exact (hin.lemma102.aut.field_nonInnDiag _ _ y hH.single hS2 hy).2 h1
    have hyx' : y ∉ Subgroup.zpowers x' := fun hy' => hyD ((Subgroup.zpowers_le.2 hx'D) hy')
    have hyN : y ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
      hBNJ hyB
    have himpl : (x' ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) ∧
        ¬ CentMod p (Jpart p (Ipart p L b) a) x') →
        InnDiagOn p (Subgroup.zpowers x') (Jpart p (Ipart p L b) a) ∧
          FieldOn p y (Jpart p (Ipart p L b) a) :=
      fun _ => ⟨innDiagOn_mono hD (Subgroup.zpowers_le.2 hx'D), hy⟩
    have hJx' : GLAPComponent p (closureIn (Jpart p (Ipart p L b) a) (Subgroup.zpowers x') ⊓
        cx x') (Ipart p L b) := by
      rw [closureIn_eq_self (Subgroup.zpowers_le.2 hx'N)]
      exact hcomp
    have hI155 := hin.lemma102.i155 hp hc.ctx.odd (cx a) (Jpart p (Ipart p L b) a) x' y
      (lemma104_isKGroup_cx hc hH.ne) hH.single hS2
      (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hDB hx'D) (hDB hH.mem)))
      hx'p hyp hcomm hyx' hyN himpl (Ipart p L b) hJx' (hBNI hyB)
    rcases hI155 with ⟨hNI, -⟩ | ⟨hno, -⟩
    · exact hNI.2 (innDiagOn_mono h.inner_I (Subgroup.zpowers_le.2 hyB))
    · exact absurd ⟨hx'N, hcx'⟩ hno

theorem exists_d_field (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a y : G} (h : Cfg p B x L b) (hH : H104 p B x L b a)
    (hS2 : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)))
    (hnTD : ¬ (p = 3 ∧ IsTD4 3 (Jpart p (Ipart p L b) a))) (hyB : y ∈ B)
    (hy : FieldOn p y (Jpart p (Ipart p L b) a)) :
    ∃ d ∈ Dgrp b x, FieldOn p d (Jpart p (Ipart p L b) a) := by
  by_contra hno
  push Not at hno
  have hS := sstar_triple h.star
  have hDB : Dgrp b x ≤ B := (card_Dgrp hS.1.1 hc.ctx.prime h.mem hS.2.1.1 hS.2.1.2.1 h.not_mem).1
  have hBN : B ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h hH.mem).2
  have hall : ∀ d ∈ Dgrp b x, InnDiagOn p (Subgroup.zpowers d) (Jpart p (Ipart p L b) a) := by
    intro d hd
    by_contra hnon
    rcases hin.lemma102.dich B a _ ⟨hS.1, hH.ess, hH.single⟩ (lemma104_isKGroup_cx hc hH.ne) hS2 d (hDB hd)
      ⟨hBN (hDB hd), hnon⟩ with
      hf | ⟨hp3, htd⟩
    · exact hno d hd hf
    · exact hnTD ⟨hp3, htd⟩
  exact not_innDiag_D hc hin h hH hS2 hyB hy
    (hin.lemma102.aut.innDiag_unif _ _ (Dgrp b x) hH.single hS2 (fun d hd => hBN (hDB hd)) hall)

theorem lemma104_alpha (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hA : CaseA p B x L b)
    (hH : H104 p B x L b a) : Concl104 p B x L b a := by
  classical
  set I := Ipart p L b with hI
  set J := Jpart p I a with hJ
  have hS : IsSTriple p B a J := ⟨(sstar_triple h.star).1, hH.ess, hH.single⟩
  have hG : IsGStar p B J := JGB_of_E hc hin h hH.mem hA
  have hS0 : IsS0 p B a J := ⟨hS, by
    unfold tripleLevel
    rw [if_pos hG, hd5]⟩
  have hTa : ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p (cx a) := by
    obtain ⟨T, hTJ, hT2, hTB, hTO⟩ := hH.hT
    refine ⟨T, hTJ, hT2, hTB, fun hle => hTO ?_⟩
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hc.ctx.prime hH.single.2.1]
    exact le_inf hTJ hle
  obtain ⟨B', x', L', hstar', hpump⟩ := exists_sstar_above hc hS0 hTa
  have ht2 : IsS2 p (B', x', L').1 (B', x', L').2.1 (B', x', L').2.2 :=
    ⟨sstar_triple hstar', hc.stage8.1 B' x' L' hstar'⟩
  obtain ⟨hS2, hr⟩ := lemma102 hc hin.lemma102 ht2 hpump
  have hS2' : IsS2 p B a J := hS2
  have hr2 : r2 p B J ≤ 2 * card2 p I :=
    hr.trans ((h.maximal B' x' L' hstar').trans h.r2_le)
  refine ⟨hS2', ?_⟩
  have hBel : IsElemAbelian p B := (sstar_triple h.star).1.1
  by_cases hy : ∃ y ∈ B, R2Prop p y J
  · obtain ⟨y, hyB, hyp⟩ := hy
    by_cases hTD : p = 3 ∧ IsTD4 3 J
    · obtain ⟨hp3, htd⟩ := hTD
      subst hp3
      have hyn : NonInner 3 y J := by
        rcases hyp with hf | ⟨-, -, hn⟩
        · exact absurd hf (hin.lemma102.aut.td4_not_field _ J y hH.single rfl htd)
        · exact hn
      have hR : R2TD4 3 B J := ⟨rfl, htd, y, hyB, ne_one_of_nonInner hyn, hyn⟩
      have hr3 : r2 3 B J = Nat.sqrt (card2 3 J) := by
        unfold r2
        rw [if_pos hR]
      rw [hr3] at hr2
      obtain ⟨x', hx'D, hx'a, -⟩ := exists_complement hc h hH.mem hH.ne
      have hcomp := I_comp_in_J hc hin h hH.mem hH.ne hx'D hx'a hH.single
      have hx'N : x' ∈ Subgroup.normalizer (J : Set G) := by
        have hDB : Dgrp b x ≤ B := (card_Dgrp hBel hc.ctx.prime h.mem (sstar_triple h.star).2.1.1
          (sstar_triple h.star).2.1.2.1 h.not_mem).1
        exact (B_le_N_J hc h hH.mem).2 (hDB hx'D)
      have hx'p : x' ^ 3 = 1 := hBel.2 x' ((card_Dgrp hBel hc.ctx.prime h.mem (sstar_triple h.star).2.1.1
          (sstar_triple h.star).2.1.2.1 h.not_mem).1 hx'D)
      have hDB : Dgrp b x ≤ B := (card_Dgrp hBel hc.ctx.prime h.mem (sstar_triple h.star).2.1.1
          (sstar_triple h.star).2.1.2.1 h.not_mem).1
      have hncx' : ¬ CentMod 3 J x' := by
        intro hcm
        have hall := glaPLayer_inf_centralizer hc.ctx.prime hH.single
          (isPGroup_zpowers_of_mem hBel (hDB hx'D)) hcm
        have hIeq : I = GLAPLayer 3 (J ⊓ cx x') := hall.2.1 I hcomp
        exact hH.lt ((congrArg (fun K => K ⊔ GLAPPrimeCoreOf 3 J) hIeq).trans hall.2.2.2.2.1)
      obtain ⟨hnn, hG2⟩ := hin.i148d _ J I x' hH.single hS2'.2 htd hx'N hx'p hncx' hcomp hr2
      exact Or.inr ⟨rfl, htd, ⟨x', hx'D, hnn⟩, hG2⟩
    · left
      have hyf : FieldOn p y J := by
        rcases hyp with hf | ⟨hp3, htd, -⟩
        · exact hf
        · exact absurd ⟨hp3, htd⟩ hTD
      exact exists_d_field hc hin h hH hS2.2 hTD hyB hyf
  · exfalso
    have hnR : ¬ R2TD4 p B J := by
      rintro ⟨hp3, htd, y, hyB, -, hyn⟩
      exact hy ⟨y, hyB, Or.inr ⟨hp3, htd, hyn⟩⟩
    have hnF : ¬ ∃ y ∈ B, FieldOn p y J := fun ⟨y, hyB, hyf⟩ => hy ⟨y, hyB, Or.inl hyf⟩
    have hr3 : r2 p B J = card2 p J := by
      unfold r2
      rw [if_neg hnR, dif_neg hnF]
    rw [hr3] at hr2
    have hDB : Dgrp b x ≤ B := (card_Dgrp hBel hc.ctx.prime h.mem (sstar_triple h.star).2.1.1
      (sstar_triple h.star).2.1.2.1 h.not_mem).1
    have hcent := D_centralizes hc hin h hH hS2.2 hr2
    obtain ⟨x', hx'D, hx'a, -⟩ := exists_complement hc h hH.mem hH.ne
    have hcomp := I_comp_in_J hc hin h hH.mem hH.ne hx'D hx'a hH.single
    have hall := glaPLayer_inf_centralizer hc.ctx.prime hH.single
      (isPGroup_zpowers_of_mem hBel (hDB hx'D)) (hcent x' hx'D)
    have hIeq : I = GLAPLayer p (J ⊓ cx x') := hall.2.1 I hcomp
    exact hH.lt ((congrArg (fun K => K ⊔ GLAPPrimeCoreOf p J) hIeq).trans hall.2.2.2.2.1)

@[expose] def CaseBeta (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G)
    (b : G) : Prop :=
  CaseU G p B x L b ∧ ∀ a ∈ Dgrp b x, a ≠ 1 →
    catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)

@[expose] def CaseGamma (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L : Subgroup G) (b : G) : Prop :=
  CaseU G p B x L b ∧ ¬ ∀ a ∈ Dgrp b x, a ≠ 1 →
    catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)

private theorem lemma104_prime_eq_two {q : TauCeti.PrimePower} {n : ℕ} (hq : q.card = n)
    (hn : n = 2 ∨ n = 8) : q.p = 2 := by
  have hdvd : q.p ∣ n := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  have h2 : q.p ∣ 2 := by
    rcases hn with rfl | rfl
    · exact hdvd
    · exact q.prime_p.dvd_of_dvd_pow (show q.p ∣ 2 ^ 3 by norm_num; exact hdvd)
  have h3 := Nat.le_of_dvd (by norm_num) h2
  have h4 := q.prime_p.two_le
  omega

private theorem lemma104_char_two_lie (d : TauCeti.LieTypeIndex) (hd : d.Valid)
    (hi : isListGamma (TauCeti.CFSGIndex.lie ⟨d, hd⟩)) : d.characteristic = 2 := by
  simp only [isListGamma, S9.isU4eight, S9.isU5two, S9.isU6two, S9.isSp8two, S9.isD4two,
    onLie] at hi
  rcases hi with hi | hi | hi | hi | hi
  · split at hi
    · rename_i _ q
      simp only [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact lemma104_prime_eq_two (q := q) (n := 8) hi (Or.inr rfl)
    · exact hi.elim
  · split at hi
    · rename_i _ q
      simp only [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact lemma104_prime_eq_two (q := q) (n := 2) hi (Or.inl rfl)
    · exact hi.elim
  · split at hi
    · rename_i _ q
      simp only [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact lemma104_prime_eq_two (q := q) (n := 2) hi (Or.inl rfl)
    · exact hi.elim
  · split at hi
    · rename_i _ q
      simp only [TauCeti.LieTypeIndex.characteristic_B]
      exact lemma104_prime_eq_two (q := q) (n := 2) hi (Or.inl rfl)
    · exact hi.elim
  · split at hi
    · rename_i _ q
      simp only [TauCeti.LieTypeIndex.characteristic_D]
      exact lemma104_prime_eq_two (q := q) (n := 2) hi (Or.inl rfl)
    · exact hi.elim

theorem isChevTwo_of_isListGamma {S : Type} [Group S] (h : catalogIs S isListGamma) :
    IsChevSimple 2 S := by
  obtain ⟨i, hi, e⟩ := h
  refine Or.inl ⟨i, ?_, e⟩
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hd⟩⟩ | ⟨s⟩
  · simp [isListGamma, S9.isU4eight, S9.isU5two, S9.isU6two, S9.isSp8two, S9.isD4two,
      onLie] at hi
  · simp [isListGamma, S9.isU4eight, S9.isU5two, S9.isU6two, S9.isSp8two, S9.isD4two,
      onLie] at hi
  · exact lemma104_char_two_lie d hd hi
  · simp [isListGamma, S9.isU4eight, S9.isU5two, S9.isU6two, S9.isSp8two, S9.isD4two,
      onLie] at hi

private theorem lemma104_eq_top_of_perfect {Q : Type} [Group Q] (R : Subgroup Q)
    (hQ : CFSG.Open.IsQuasisimple Q) (hdec : ∀ q : Q, ∃ r ∈ R, ∃ z ∈ Subgroup.center Q, q = r * z) :
    R = ⊤ := by
  have hle : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ := hdec g₁
    obtain ⟨r₂, hr₂, z₂, hz₂, rfl⟩ := hdec g₂
    rw [commutatorElement_mul_center_left hz₁, commutatorElement_mul_center_right hz₂,
      commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
  have htop : (⊤ : Subgroup Q) ≤ R := by
    have h := hQ.1
    rw [← h]
    exact hle
  exact eq_top_iff.2 htop

private theorem lemma104_surj_of_card {A T : Type} [Group A] [Group T] [Finite A] [Finite T]
    (K : Subgroup A) [K.Normal] (φ : A →* T)
    (hcent : ∀ m ∈ φ.ker, ∀ c : A, ⁅m, c⁆ ∈ K)
    (hcard : Nat.card ((A ⧸ K) ⧸ Subgroup.center (A ⧸ K)) = Nat.card T) :
    Function.Surjective φ := by
  classical
  let f : A →* (A ⧸ K) ⧸ Subgroup.center (A ⧸ K) :=
    (QuotientGroup.mk' (Subgroup.center (A ⧸ K))).comp (QuotientGroup.mk' K)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨g, rfl⟩
  have hK : K ≤ f.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have h1 : (QuotientGroup.mk k : A ⧸ K) = 1 := (QuotientGroup.eq_one_iff k).2 hk
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, h1]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.one_mem _)
  have hφK : φ.ker ≤ f.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    have hz : (QuotientGroup.mk m : A ⧸ K) ∈ Subgroup.center (A ⧸ K) := by
      refine Subgroup.mem_center_iff.2 fun t => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hc := hcent m⁻¹ (φ.ker.inv_mem hm) g⁻¹
      convert hc using 1
      rw [commutatorElement_def]
      group
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hz
  have hle : φ.ker ⊔ K ≤ f.ker := sup_le hφK hK
  let ψ : (A ⧸ (φ.ker ⊔ K)) →* (A ⧸ K) ⧸ Subgroup.center (A ⧸ K) :=
    QuotientGroup.lift (φ.ker ⊔ K) f hle
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg⟩ := hfs y
    exact ⟨QuotientGroup.mk g, by rw [QuotientGroup.lift_mk]; exact hg⟩
  have hW : Nat.card ((A ⧸ K) ⧸ Subgroup.center (A ⧸ K)) ≤ Nat.card (A ⧸ (φ.ker ⊔ K)) :=
    Nat.card_le_card_of_surjective ψ hψs
  have hidx : Nat.card (A ⧸ (φ.ker ⊔ K)) ≤ Nat.card (A ⧸ φ.ker) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
    exact Subgroup.index_antitone le_sup_left
  have hrng : Nat.card (A ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hT : Nat.card φ.range ≤ Nat.card T := Subgroup.card_le_card_group φ.range
  have heq : Nat.card φ.range = Nat.card T := by omega
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ heq)

private theorem lemma104_primePower_card_two {q q' : TauCeti.PrimePower} (hq : q.card = 2)
    (hq' : q'.card = 2) : q = q' := by
  have hpq : q.p = 2 := lemma104_prime_eq_two hq (Or.inl rfl)
  have hpq' : q'.p = 2 := lemma104_prime_eq_two hq' (Or.inl rfl)
  have e1 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have e2 : q'.p ^ q'.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq'
  rw [hpq] at e1
  rw [hpq'] at e2
  have he : q.exponent = 1 := Nat.pow_right_injective (le_refl 2) (e1.trans (pow_one 2).symm)
  have he' : q'.exponent = 1 := Nat.pow_right_injective (le_refl 2) (e2.trans (pow_one 2).symm)
  exact TauCeti.PrimePower.ext (hpq.trans hpq'.symm) (he.trans he'.symm)

private theorem lemma104_u4two_shape (k : TauCeti.CFSGIndex) (hk : S9.isU4two k) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid),
      k = TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ ∧ q.card = 2 := by
  rcases k with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hd⟩⟩ | ⟨s⟩
  · simp [S9.isU4two, onLie] at hk
  · simp [S9.isU4two, onLie] at hk
  · simp only [S9.isU4two, onLie] at hk
    split at hk
    · rename_i _ q
      exact ⟨q, hd, rfl, hk⟩
    · exact hk.elim
  · simp [S9.isU4two, onLie] at hk

private theorem lemma104_u4two_unique {i j : TauCeti.CFSGIndex} (hi : S9.isU4two i)
    (hj : S9.isU4two j) : i = j := by
  obtain ⟨q, hv, rfl, hqc⟩ := lemma104_u4two_shape i hi
  obtain ⟨q', hv', rfl, hqc'⟩ := lemma104_u4two_shape j hj
  have hqq : q = q' := lemma104_primePower_card_two hqc hqc'
  subst hqq
  rfl

private theorem lemma104_cover_gen {I J : Subgroup G} (hp : p.Prime) (hIJ : I ≤ J)
    (hQ : CFSG.Open.IsQuasisimple (PQuot p J))
    (hcard : Nat.card (PSimple p I) = Nat.card (PSimple p J)) :
    J ≤ I ⊔ GLAPPrimeCoreOf p J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let πJ : ↥J →* PQuot p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  let πS : PQuot p J →* PSimple p J := QuotientGroup.mk' (Subgroup.center (PQuot p J))
  let ι : ↥I →* ↥J := Subgroup.inclusion hIJ
  let φ : ↥I →* PSimple p J := πS.comp (πJ.comp ι)
  have hN : (GLAPPrimeCore p ↥J).comap ι ≤ GLAPPrimeCore p ↥I := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have hdvd : Nat.card ((GLAPPrimeCore p ↥J).comap ι) ∣ Nat.card (GLAPPrimeCore p ↥J) := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIJ)]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
  have hcent : ∀ m ∈ φ.ker, ∀ c : ↥I, ⁅m, c⁆ ∈ GLAPPrimeCore p ↥I := by
    intro m hm c
    have h0 : πS (πJ (ι m)) = 1 := (MonoidHom.mem_ker).1 hm
    have h1 : πJ (ι m) ∈ Subgroup.center (PQuot p J) := (QuotientGroup.eq_one_iff _).1 h0
    have h2 : ⁅πJ (ι m), πJ (ι c)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 h1 _).symm)
    have h3 : πJ (ι ⁅m, c⁆) = 1 := by
      rw [map_commutatorElement ι, map_commutatorElement πJ]
      exact h2
    exact hN (Subgroup.mem_comap.2 ((QuotientGroup.eq_one_iff _).1 h3))
  have hsurj : Function.Surjective φ :=
    lemma104_surj_of_card (GLAPPrimeCore p ↥I) φ hcent hcard
  have hdec : ∀ q : PQuot p J, ∃ r ∈ (πJ.comp ι).range, ∃ z ∈ Subgroup.center (PQuot p J),
      q = r * z := by
    intro q
    obtain ⟨i, hi⟩ := hsurj (πS q)
    have hi' : (πJ (ι i))⁻¹ * q ∈ Subgroup.center (PQuot p J) := QuotientGroup.eq.1 hi
    exact ⟨πJ (ι i), MonoidHom.mem_range.2 ⟨i, rfl⟩, _, hi', (mul_inv_cancel_left _ _).symm⟩
  have hR := lemma104_eq_top_of_perfect _ hQ hdec
  intro j hj
  have hq : (QuotientGroup.mk ⟨j, hj⟩ : PQuot p J) ∈ (πJ.comp ι).range := by
    rw [hR]
    exact Subgroup.mem_top _
  obtain ⟨i, hi⟩ := MonoidHom.mem_range.1 hq
  have hc : (ι i)⁻¹ * ⟨j, hj⟩ ∈ GLAPPrimeCore p ↥J := QuotientGroup.eq.1 hi
  have hcG : (((ι i)⁻¹ * ⟨j, hj⟩ : ↥J) : G) ∈ GLAPPrimeCoreOf p J :=
    Subgroup.mem_map.2 ⟨_, hc, rfl⟩
  have hj_eq : j = (i : G) * (((ι i)⁻¹ * ⟨j, hj⟩ : ↥J) : G) := by
    simp [ι]
  rw [hj_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left i.2) (Subgroup.mem_sup_right hcG)

theorem beta_type (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (hU : CaseU G p B x L b) (hH : H104 p B x L b a)
    (hβ : catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)) :
    catalogIs (PSimple p (Jpart p (Ipart p L b) a)) S9.isU4eight := by
  obtain ⟨j, hj, ⟨f⟩⟩ := hβ
  rcases hj with hj | hj
  · exfalso
    obtain ⟨i, hi, ⟨e⟩⟩ := hU.I_iso
    have hij : i = j := lemma104_u4two_unique hi hj
    subst hij
    have hcard : Nat.card (PSimple p (Ipart p L b)) =
        Nat.card (PSimple p (Jpart p (Ipart p L b) a)) :=
      Nat.card_congr (e.toEquiv.trans f.toEquiv.symm)
    have hQ := isQuasisimple_pQuot_of_glaPComponent hc.ctx.prime hH.single
    have hcov := lemma104_cover_gen hc.ctx.prime (le_closureIn_self _ _) hQ hcard
    exact hH.lt (le_antisymm (sup_le (le_closureIn_self _ _) (Subgroup.map_subtype_le _)) hcov)
  · exact ⟨j, hj, ⟨f⟩⟩

theorem lemma104_beta_field (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) (hH : H104 p B x L b a)
    (hβ : catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)) :
    ∃ d ∈ Dgrp b x, FieldOn p d (Jpart p (Ipart p L b) a) := by
  have hp3 := hU.p3
  have h48 := beta_type hc h hU hH hβ
  obtain ⟨x', hx'D, hx'a, -⟩ := exists_complement hc h hH.mem hH.ne
  have hcomp := I_comp_in_J hc hin h hH.mem hH.ne hx'D hx'a hH.single
  have hBel : IsElemAbelian p B := (sstar_triple h.star).1.1
  have hDB : Dgrp b x ≤ B := (card_Dgrp hBel hc.ctx.prime h.mem (sstar_triple h.star).2.1.1
    (sstar_triple h.star).2.1.2.1 h.not_mem).1
  have hx'N : x' ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h hH.mem).2 (hDB hx'D)
  have hx'p : x' ^ p = 1 := hBel.2 x' (hDB hx'D)
  have hIU : catalogIs (PSimple p (Ipart p L b)) S9.isU4two := hU.I_iso
  exact ⟨x', hx'D, by
    subst hp3
    exact hin.fieldu48 (cx a) _ _ x' hH.single h48 hx'N hx'p hcomp hIU⟩

theorem lemma104_beta (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) (hH : H104 p B x L b a)
    (hβ : catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)) :
    Concl104 p B x L b a := by
  have hS : IsSTriple p B a (Jpart p (Ipart p L b) a) :=
    ⟨(sstar_triple h.star).1, hH.ess, hH.single⟩
  have h48 := beta_type hc h hU hH hβ
  have hch : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) :=
    isChevTwo_of_isListGamma (catalogIs_imp (fun i hi => Or.inl hi) h48)
  exact ⟨⟨hS, hch⟩, Or.inl (lemma104_beta_field hc hin h hU hH hβ)⟩

theorem lemma104_gamma (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) (hH : H104 p B x L b a) :
    catalogIs (PSimple p (Jpart p (Ipart p L b) a)) isListGamma := by
  have hp3 := hU.p3
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x', hx'D, hx'a, -⟩ := exists_complement hc h hH.mem hH.ne
  have hcomp := I_comp_in_J hc hin h hH.mem hH.ne hx'D hx'a hH.single
  have hBel : IsElemAbelian p B := (sstar_triple h.star).1.1
  have hDB : Dgrp b x ≤ B := (card_Dgrp hBel hp h.mem (sstar_triple h.star).2.1.1
    (sstar_triple h.star).2.1.2.1 h.not_mem).1
  have hx'N : x' ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h hH.mem).2 (hDB hx'D)
  have hax : a ^ p = 1 := hBel.2 a (hDB hH.mem)
  have hx'p : x' ^ p = 1 := hBel.2 x' (hDB hx'D)
  have hx'1 : x' ≠ 1 := fun h1 => hx'a (h1 ▸ Subgroup.one_mem _)
  have hKa : CFSG.Open.IsKGroup ↥(cx a) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple
      hc.ctx.nonabelian hH.ne)
  have hx'ca : x' ∈ cx a := Subgroup.mem_centralizer_singleton_iff.2
    (isElemAbelian_commute hBel (hDB hx'D) (hDB hH.mem))
  have hnle : ¬ Jpart p (Ipart p L b) a ≤ Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) :=
    fun hle => hH.lt (le_antisymm (sup_le (le_closureIn_self _ _) (Subgroup.map_subtype_le _)) hle)
  subst hp3
  have hres := hin.i1431 a x' (Jpart 3 (Ipart 3 L b) a) (Ipart 3 L b) (orderOf_eq_prime hax hH.ne) hKa
    hx'ca (orderOf_eq_prime hx'p hx'1) hx'a hH.single hx'N hcomp hU.I_iso hnle hU.rank.le
  have hco := hc.stage8.2 rfl hU.rank a (Jpart 3 (Ipart 3 L b) a) (orderOf_eq_prime hax hH.ne) hH.single
  obtain ⟨i, hi, e⟩ := hres
  refine ⟨i, ?_, e⟩
  rcases hi with hi | hi | hi | hi | hi | hi
  · exact absurd ⟨i, hi, e⟩ hco
  · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inl hi

end S10

end CFSG.LocalAnalysis.GLTheoremA
