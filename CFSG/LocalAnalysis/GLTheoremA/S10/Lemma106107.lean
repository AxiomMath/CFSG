module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma105More

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem h104_of_concl105 {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (c : Concl105 G p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hlt : ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a)) :
    H104 p B x L b a := by
  obtain ⟨T, hTI, hT2, hTB, hTO, -, -⟩ := c.T_exists
  have hIJ : Ipart p L b ≤ Jpart p (Ipart p L b) a := le_closureIn_self _ _
  exact ⟨ha, ha1, c.essential a ha ha1, (c.single a ha ha1).1, hlt,
    ⟨T, hTI.trans hIJ, hT2, hTB, fun hle => hTO ((le_inf hTI hle).trans (core_inf_le hIJ))⟩⟩

private theorem lemma106107_dgrp_le {B : Subgroup G} {b x : G} (hb : b ∈ B) (hx : x ∈ B) :
    Dgrp b x ≤ B := by
  refine (Subgroup.closure_le B).2 ?_
  intro y hy
  rcases hy with rfl | rfl
  · exact hb
  · exact hx

private theorem lemma106107_not_isCyclic {B : Subgroup G} {b x : G} (hp : p.Prime)
    (hBel : IsElemAbelian p B) (hb : b ∈ B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hbx : b ∉ Subgroup.zpowers x) : ¬ IsCyclic (Dgrp b x) := by
  intro hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ g ∈ B, g ^ p = 1 := fun g hg => hBel.2 g hg
  have hexp : Monoid.exponent (Dgrp b x) ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    apply Subtype.ext
    simpa using hpow g.1 (lemma106107_dgrp_le hb hxB g.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton x))
  have hzx : Subgroup.zpowers x ≤ Dgrp b x := Subgroup.zpowers_le.2 hxD
  have hord : orderOf x = p := orderOf_eq_prime (hpow x hxB) hx1
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hord]
  have hle : Nat.card (Dgrp b x) ≤ p := Nat.le_of_dvd hp.pos hexp
  have hD : Subgroup.zpowers x = Dgrp b x :=
    Subgroup.eq_of_le_of_card_ge hzx (by rw [hcardx]; exact hle)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert b {x})
  rw [← hD] at hbD
  exact hbx hbD

private theorem lemma106107_normalizer_inf {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro k
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA k, hC k]

private theorem lemma106107_normalizer_cx {a g : G} (hg : g ∈ cx a) :
    g ∈ Subgroup.normalizer ((cx a : Subgroup G) : Set G) := by
  have hg' : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hgi : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hg']
      _ = a * g⁻¹ := by group
  have e1 : g * k * g⁻¹ * a = g * (k * a) * g⁻¹ := by
    calc g * k * g⁻¹ * a = g * k * (g⁻¹ * a) := by group
      _ = g * k * (a * g⁻¹) := by rw [hgi]
      _ = g * (k * a) * g⁻¹ := by group
  have e2 : a * (g * k * g⁻¹) = g * (a * k) * g⁻¹ := by
    calc a * (g * k * g⁻¹) = (a * g) * k * g⁻¹ := by group
      _ = (g * a) * k * g⁻¹ := by rw [← hg']
      _ = g * (a * k) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro hk
    rw [hk]
  · intro hk
    exact mul_left_cancel (mul_right_cancel hk)

private theorem lemma106107_gLBConj_cx {a s : G} (hs : s ∈ cx a) :
    GLBConj s (cx a) = cx a := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hs' : s * a = a * s := Subgroup.mem_centralizer_singleton_iff.1 hs
  have hsi : s⁻¹ * a = a * s⁻¹ := by
    calc s⁻¹ * a = s⁻¹ * (a * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * a) * s⁻¹ := by rw [hs']
      _ = a * s⁻¹ := by group
  have e1 : s * y * s⁻¹ * a = s * (y * a) * s⁻¹ := by
    calc s * y * s⁻¹ * a = s * y * (s⁻¹ * a) := by group
      _ = s * y * (a * s⁻¹) := by rw [hsi]
      _ = s * (y * a) * s⁻¹ := by group
  have e2 : a * (s * y * s⁻¹) = s * (a * y) * s⁻¹ := by
    calc a * (s * y * s⁻¹) = (a * s) * y * s⁻¹ := by group
      _ = (s * a) * y * s⁻¹ := by rw [← hs']
      _ = s * (a * y) * s⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro hk
    exact mul_left_cancel (mul_right_cancel hk)
  · intro hk
    rw [hk]

private theorem lemma106107_gLBConj_conj {I : Subgroup G} {g : G} (hg : GLBConj g I = I) (a : G) :
    GLBConj g (GLBConj a I) = GLBConj (g⁻¹ * a * g) I := by
  have e2 : GLBConj (g⁻¹ * a * g) (GLBConj g I) = GLBConj (g * (g⁻¹ * a * g)) I :=
    gLBConj_gLBConj (g⁻¹ * a * g) g I
  have e3 : g * (g⁻¹ * a * g) = a * g := by group
  rw [hg, e3] at e2
  rw [gLBConj_gLBConj]
  exact e2.symm

private theorem lemma106107_normalizer_closureIn {I K : Subgroup G} {g : G}
    (hgI : GLBConj g I = I) (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((closureIn I K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, closureIn_eq_iSup_gLBConj I K]
  have hsup : GLBConj g (⨆ a ∈ K, GLBConj a I) = ⨆ a ∈ K, GLBConj g (GLBConj a I) := by
    unfold GLBConj
    simp only [Subgroup.map_iSup]
  rw [hsup]
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    rw [lemma106107_gLBConj_conj hgI a]
    have hmem : g⁻¹ * a * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgK) a).1 ha
      rwa [inv_inv] at this
    exact le_biSup (fun c => GLBConj c I) hmem
  · refine iSup₂_le fun a ha => ?_
    have hmem : g * a * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgK a).1 ha
    have e : GLBConj g (GLBConj (g * a * g⁻¹) I) = GLBConj a I := by
      rw [lemma106107_gLBConj_conj hgI]
      congr 1
      group
    calc GLBConj a I = GLBConj g (GLBConj (g * a * g⁻¹) I) := e.symm
      _ ≤ _ := le_biSup (fun c => GLBConj g (GLBConj c I)) hmem

theorem exists_aT (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    ∃ (a : G) (T : Subgroup G), a ∈ Dgrp b x ∧ a ∉ Subgroup.zpowers x ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅Dgrp b x, T ⊓ cx a⁆ : Subgroup G) ≠ ⊥ := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := B_el h
  have hbB : b ∈ B := h.mem
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  obtain ⟨T₀, -, hT₀2, hT₀N, hT₀ne, -⟩ := (sstar_triple h.star).2.1.2.2
  have hT₀bot : T₀ ≠ ⊥ := by
    rintro rfl
    exact hT₀ne (by simp)
  obtain ⟨T, hT₀T, hTmax⟩ := Set.Finite.exists_le_maximal
    (Set.toFinite {T : Subgroup G | IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)})
    (show T₀ ∈ {T : Subgroup G | IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)} from
      ⟨hT₀2, hT₀N⟩)
  obtain ⟨⟨hT2, hTN⟩, hTmax'⟩ := hTmax
  have hTne : T ≠ ⊥ := fun e => hT₀bot (le_bot_iff.1 (e ▸ hT₀T))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax' (show T' ∈ {T : Subgroup G | IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G)} from ⟨h2, hN⟩) hle) hle
  have hBbot : B ≠ ⊥ := fun e => hx1 (Subgroup.mem_bot.1 (e ▸ hxB))
  obtain ⟨-, hD⟩ := GL83.I_33_1_proved G hc.ctx.charTwo p hp hp2 B T hBbot hBel hT2 hTN
    (Or.inl ⟨hTne, hmax⟩)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert b {x})
  have hDB : Dgrp b x ≤ B := lemma106107_dgrp_le hbB hxB
  have hDbot : Dgrp b x ≠ ⊥ := by
    intro e
    apply h.not_mem
    rw [e, Subgroup.mem_bot] at hbD
    rw [hbD]
    exact Subgroup.one_mem _
  obtain ⟨-, d₁, d₂, hd₁, hd₂, hd₁1, hd₂d₁, hc₁, hc₂⟩ :=
    hD (Dgrp b x) hDbot hDB (lemma106107_not_isCyclic hp hBel hbB hxB hx1 h.not_mem)
  have hpow : ∀ g ∈ B, g ^ p = 1 := fun g hg => hBel.2 g hg
  by_cases hd₁x : d₁ ∈ Subgroup.zpowers x
  · refine ⟨d₂, T, hd₂, ?_, hT2, hTN, hc₂⟩
    intro hd₂x
    have hxo : orderOf x = p := orderOf_eq_prime (hpow x hxB) hx1
    have hd1o : orderOf d₁ = p := orderOf_eq_prime (hpow d₁ (hDB hd₁)) hd₁1
    have hdx : Subgroup.zpowers d₁ = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hd₁x)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hd1o])
    rw [← hdx] at hd₂x
    exact hd₂d₁ hd₂x
  · exact ⟨d₁, T, hd₁, hd₁x, hT2, hTN, hc₁⟩

abbrev S107 (b x : G) (T : Subgroup G) (a : G) : Subgroup G := ⁅T ⊓ cx a, Dgrp b x⁆

theorem S107_basic (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {a : G} {T : Subgroup G} (haD : a ∈ Dgrp b x) (hT2 : IsPGroup 2 T)
    (hTB : B ≤ Subgroup.normalizer (T : Set G)) (hne : (⁅Dgrp b x, T ⊓ cx a⁆ : Subgroup G) ≠ ⊥) :
    IsPGroup 2 (S107 b x T a) ∧ S107 b x T a ≠ ⊥ ∧
      (⁅S107 b x T a, Dgrp b x⁆ : Subgroup G) = S107 b x T a ∧ S107 b x T a ≤ cx a ∧
      B ≤ Subgroup.normalizer ((S107 b x T a : Subgroup G) : Set G) := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := B_el h
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hDB : Dgrp b x ≤ B := lemma106107_dgrp_le h.mem hxB
  have haB : a ∈ B := hDB haD
  have hBC : B ≤ cx a := isElemAbelian_le_centralizer hBel haB
  have hDC : Dgrp b x ≤ cx a := hDB.trans hBC
  have hDN : Dgrp b x ≤ Subgroup.normalizer ((T ⊓ cx a : Subgroup G) : Set G) := fun d hd =>
    lemma106107_normalizer_inf (hTB (hDB hd)) (lemma106107_normalizer_cx (hDC hd))
  have hDp : IsPGroup p (Dgrp b x) := (isPGroup_of_isElemAbelian hBel).to_le hDB
  have hX2 : IsPGroup 2 (T ⊓ cx a : Subgroup G) := hT2.to_le inf_le_left
  have hXp : ¬ p ∣ Nat.card (T ⊓ cx a : Subgroup G) := by
    intro hdvd
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hS_le : (⁅T ⊓ cx a, Dgrp b x⁆ : Subgroup G) ≤ T ⊓ cx a := comm_le_left_of_normalizes hDN
  have hS_eq : (⁅⁅T ⊓ cx a, Dgrp b x⁆, Dgrp b x⁆ : Subgroup G) = ⁅T ⊓ cx a, Dgrp b x⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hDp hDN hXp
  refine ⟨hT2.to_le (hS_le.trans inf_le_left), ?_, hS_eq, ?_, ?_⟩
  · show (⁅T ⊓ cx a, Dgrp b x⁆ : Subgroup G) ≠ ⊥
    rw [Subgroup.commutator_comm]
    exact hne
  · exact commutator_le_of_le' inf_le_right hDC
  · intro β hβ
    rw [mem_normalizer_iff_gLBConj_eq]
    have hβX : β ∈ Subgroup.normalizer ((T ⊓ cx a : Subgroup G) : Set G) :=
      lemma106107_normalizer_inf (hTB hβ) (lemma106107_normalizer_cx (hBC hβ))
    have hβD : β ∈ Subgroup.normalizer ((Dgrp b x : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hBel (hDB hd) hβ)
    have e : GLBConj β ⁅T ⊓ cx a, Dgrp b x⁆ = ⁅GLBConj β (T ⊓ cx a), GLBConj β (Dgrp b x)⁆ :=
      Subgroup.map_commutator _ _ (MulAut.conj β⁻¹).toMonoidHom
    show GLBConj β ⁅T ⊓ cx a, Dgrp b x⁆ = ⁅T ⊓ cx a, Dgrp b x⁆
    rw [e, mem_normalizer_iff_gLBConj_eq.1 hβX, mem_normalizer_iff_gLBConj_eq.1 hβD]

theorem S_norm_J (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (c : Concl105 G p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) {S : Subgroup G}
    (hSD : (⁅S, Dgrp b x⁆ : Subgroup G) = S) (hSC : S ≤ cx a) :
    S ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) := by
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hDB : Dgrp b x ≤ B := lemma106107_dgrp_le h.mem hxB
  have hsingle := c.single a ha ha1
  set J := Jpart p (Ipart p L b) a with hJdef
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hsingle.2 J hsingle.1 ⟨MulEquiv.refl _⟩
  have hconj : ∀ s ∈ cx a, B ≤ Subgroup.normalizer ((GLBConj s J : Subgroup G) : Set G) := by
    intro s hs
    have hK : GLAPComponent p (cx a) (GLBConj s J) := by
      have h1 := glaPComponent_gLBConj hsingle.1 s
      rwa [lemma106107_gLBConj_cx hs] at h1
    exact hsingle.2 (GLBConj s J) hK ⟨(conjQuotEquiv p s J).symm⟩
  have hkey : ∀ s ∈ cx a, ∀ d ∈ Dgrp b x, s * d * s⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
    intro s hs d hd
    rw [mem_normalizer_iff_gLBConj_eq]
    have hdK := mem_normalizer_iff_gLBConj_eq.1 (hconj s hs (hDB hd))
    rw [← gLBConj_gLBConj s⁻¹ (s * d) J, ← gLBConj_gLBConj d s J, hdK, gLBConj_inv_gLBConj]
  calc S = ⁅S, Dgrp b x⁆ := hSD.symm
    _ ≤ Subgroup.normalizer (J : Set G) := by
        refine Subgroup.commutator_le.2 fun s hs d hd => ?_
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (hkey s (hSC hs) d hd) (Subgroup.inv_mem _ (hBJ (hDB hd)))

theorem S_cent_mod (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {a : G} (ha : a ∈ Dgrp b x)
    (hI : Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a)
    {S : Subgroup G} (hSD : (⁅S, Dgrp b x⁆ : Subgroup G) = S)
    (hSN : S ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G)) :
    ∀ s ∈ S, CentMod p (Jpart p (Ipart p L b) a) s := by
  have hp : p.Prime := hc.ctx.prime
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hDB : Dgrp b x ≤ B := lemma106107_dgrp_le h.mem hxB
  have hBel : IsElemAbelian p B := B_el h
  have haB : a ∈ B := hDB ha
  set I := Ipart p L b with hIdef
  set J := Jpart p I a with hJdef
  set O := GLAPPrimeCoreOf p J with hOdef
  have hIJ : I ≤ J := le_closureIn_self _ _
  have hIO : I ≤ Subgroup.normalizer (O : Set G) := hIJ.trans (le_normalizer_glaPPrimeCoreOf p J)
  have hOI : GLAPPrimeCoreOf p I ≤ O := by
    rw [(cover_facts hp hIJ hI).1]
    exact inf_le_right
  have hDI : ∀ d ∈ Dgrp b x, d ∈ Subgroup.normalizer (I : Set G) := fun d hd =>
    ((h.cent_I d (hDB hd)).2 hd).1
  have hDa : ∀ d ∈ Dgrp b x, d ∈ Subgroup.normalizer ((cx a : Subgroup G) : Set G) := fun d hd =>
    lemma106107_normalizer_cx (Subgroup.mem_centralizer_singleton_iff.2
      (isElemAbelian_commute hBel (hDB hd) haB))
  have hDN : ∀ d ∈ Dgrp b x, d ∈ Subgroup.normalizer (J : Set G) := fun d hd =>
    lemma106107_normalizer_closureIn (mem_normalizer_iff_gLBConj_eq.1 (hDI d hd))
      (mem_normalizer_glaPLayer (p := p) (hDa d hd))
  have hDC : ∀ d ∈ Dgrp b x, d ∈ centModSubgroup p J := by
    intro d hd
    refine mem_centModSubgroup.2 ⟨hDN d hd, fun l hl => ?_⟩
    have hl' : l ∈ I ⊔ O := by rw [hI]; exact hl
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I O hIO, Set.mem_mul] at hl'
    obtain ⟨i, hi, o, ho, rfl⟩ := hl'
    have hdO : d ∈ Subgroup.normalizer (O : Set G) :=
      normalizer_le_normalizer_glaPPrimeCoreOf p J (hDN d hd)
    have hO1 : ⁅o, d⁆ ∈ O := by
      have e : ⁅o, d⁆ = o * (d * o⁻¹ * d⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.1 hdO o⁻¹).1 (O.inv_mem ho))
    have hO2 : ⁅i, d⁆ ∈ O :=
      hOI (((h.cent_I d (hDB hd)).2 hd).2
        (Subgroup.commutator_mem_commutator hi (Subgroup.mem_zpowers d)))
    have e2 : ⁅i * o, d⁆ = (i * ⁅o, d⁆ * i⁻¹) * ⁅i, d⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p J (hIJ hi)) _).1
      hO1) hO2
  have hCnorm : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ c ∈ centModSubgroup p J,
      g * c * g⁻¹ ∈ centModSubgroup p J := by
    intro g hg c hc'
    obtain ⟨hcN, hcO⟩ := mem_centModSubgroup.1 hc'
    refine mem_centModSubgroup.2
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcN) (Subgroup.inv_mem _ hg), fun l hl => ?_⟩
    have hgl : g⁻¹ * l * g ∈ J := (Subgroup.mem_normalizer_iff''.1 hg l).1 hl
    have e : ⁅l, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p J hg) _).1
      (hcO _ hgl)
  have hSle : S ≤ centModSubgroup p J := by
    calc S = ⁅S, Dgrp b x⁆ := hSD.symm
      _ ≤ centModSubgroup p J := by
        refine Subgroup.commutator_le.2 fun s hs d hd => ?_
        rw [commutatorElement_def]
        exact (centModSubgroup p J).mul_mem (hCnorm s (hSN hs) d (hDC d hd))
          ((centModSubgroup p J).inv_mem (hDC d hd))
  intro s hs
  exact centMod_iff.2 (hSle hs)

theorem exists_R (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (c : Concl105 G p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) (hSB : B ≤ Subgroup.normalizer (S : Set G))
    (hSN : S ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G)) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≠ ⊥ ∧ B ≤ Subgroup.normalizer (R : Set G) ∧
      R ≤ S ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) ∧
      S ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) ≤ R ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian (B_el h)
  have hsingle := c.single a ha ha1
  set J := Jpart p (Ipart p L b) a with hJdef
  set O := GLAPPrimeCoreOf p J with hOdef
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hsingle.2 J hsingle.1 ⟨MulEquiv.refl _⟩
  have hSO : S ≤ Subgroup.normalizer (O : Set G) := hSN.trans (normalizer_le_normalizer_glaPPrimeCoreOf p J)
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    hBJ.trans (normalizer_le_normalizer_glaPPrimeCoreOf p J)
  have hOodd : Odd (Nat.card O) := by
    have hle : O ≤ GLAPPrimeCoreOf p (cx a) :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hsingle.1.2.1
    exact Odd.of_dvd_nat (c.odd_core a ha ha1) (Subgroup.card_dvd_of_le hle)
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp J
  have hS2p : ∀ X : Subgroup G, IsPGroup 2 X → ¬ p ∣ Nat.card X := by
    intro X hX hdvd
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hSO_inf : S ⊓ O = ⊥ := eq_bot_of_le_odd (hS2.to_le inf_le_left) hOodd inf_le_right
  have hW_cop : ¬ p ∣ Nat.card (S ⊔ O : Subgroup G) := by
    rw [sup_comm]
    exact not_dvd_card_sup_of_le_normalizer hp hSO hOp (hS2p S hS2)
  have hBW : B ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := by
    intro β hβ
    rw [mem_normalizer_iff_gLBConj_eq]
    have e : GLBConj β (S ⊔ O) = GLBConj β S ⊔ GLBConj β O := Subgroup.map_sup _ _ _
    rw [e, mem_normalizer_iff_gLBConj_eq.1 (hSB hβ), mem_normalizer_iff_gLBConj_eq.1 (hBO hβ)]
  obtain ⟨R, hRW, hR2, hRm, hRB⟩ := exists_invariant_sylow_two hp hp2 hBp hBW
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hW_cop)
  have hcardW : Nat.card (S ⊔ O : Subgroup G) = Nat.card O * Nat.card S := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hSO
    rw [inf_comm O S, hSO_inf, Subgroup.card_bot, mul_one, sup_comm O S] at h1
    exact h1
  have hmr : R.relIndex (S ⊔ O) * Nat.card R = Nat.card O * Nat.card S := by
    have h1 := Subgroup.relIndex_mul_card R (S ⊔ O)
    rw [inf_eq_left.2 hRW, hcardW] at h1
    exact h1
  have hrs : Nat.card R = Nat.card S := by
    obtain ⟨i, hi⟩ := hR2.exists_card_eq
    obtain ⟨j, hj⟩ := hS2.exists_card_eq
    rw [hi, hj] at hmr ⊢
    have hco2 : Nat.Coprime 2 (Nat.card O) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hOodd.not_two_dvd_nat
    have hcm2 : Nat.Coprime 2 (R.relIndex (S ⊔ O)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hRm
    have h1 : 2 ^ i ∣ Nat.card O * 2 ^ j := ⟨R.relIndex (S ⊔ O), by rw [← hmr, mul_comm]⟩
    have h2 : 2 ^ j ∣ R.relIndex (S ⊔ O) * 2 ^ i := ⟨Nat.card O, by rw [hmr, mul_comm]⟩
    have hij : i ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
      (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left i hco2) h1)
    have hji : j ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
      (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left j hcm2) h2)
    rw [le_antisymm hij hji]
  have hRne : R ≠ ⊥ := by
    intro hR
    apply hSne
    rw [← Subgroup.card_eq_one, ← hrs, hR, Subgroup.card_bot]
  have hOR : O ⊓ R = ⊥ := eq_bot_of_le_odd (hR2.to_le inf_le_right) hOodd inf_le_left
  have hRN : R ≤ Subgroup.normalizer (O : Set G) := hRW.trans (sup_le hSO Subgroup.le_normalizer)
  have hcardOR : Nat.card (O ⊔ R : Subgroup G) = Nat.card O * Nat.card R := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hRN
    rw [hOR, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hOR_eq : O ⊔ R = S ⊔ O := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le le_sup_right hRW
    · rw [hcardOR, hrs, hcardW]
  refine ⟨R, hR2, hRne, hRB, hRW, ?_⟩
  calc S ⊔ O = O ⊔ R := hOR_eq.symm
    _ ≤ R ⊔ O := le_of_eq (sup_comm _ _)

theorem I_norm_SW {I J S : Subgroup G} (hIJ : I ≤ J) (hcent : ∀ s ∈ S, CentMod p J s) :
    I ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := by
  have hJO : J ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p J)
  have key : ∀ i ∈ I, ∀ t ∈ S ⊔ GLAPPrimeCoreOf p J, i * t * i⁻¹ ∈ S ⊔ GLAPPrimeCoreOf p J := by
    intro i hi
    refine conj_mem_sup_of (fun s hs => ?_) (fun o ho => ?_)
    · have hcomm : ⁅i, s⁆ ∈ GLAPPrimeCoreOf p J := (centMod_iff.1 (hcent s hs)).2 i (hIJ hi)
      have e : i * s * i⁻¹ = ⁅i, s⁆ * s := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hs)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hJO (hIJ hi)) o).1 ho)
  intro i hi
  exact mem_normalizer_of_conj' (key i hi) (key i⁻¹ (Subgroup.inv_mem _ hi))

private theorem lemma106107_relIndex_of_card {H M : Subgroup G} {k m : ℕ} (hHM : H ≤ M)
    (hHk : Nat.card H = k) (hk : 0 < k) (hM : Nat.card M = m * k) : H.relIndex M = m := by
  have h1 := Subgroup.relIndex_mul_card H M
  rw [inf_eq_left.2 hHM, hHk, hM] at h1
  exact Nat.eq_of_mul_eq_mul_right hk h1

private theorem lemma106107_mem_cs_of {S : Subgroup G} {g : G} (h : S ≤ cx g) : g ∈ cs S :=
  Subgroup.mem_centralizer_iff.2 fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (h hs)

private theorem lemma106107_frattini {M R : Subgroup G} (hR2 : IsPGroup 2 R) (hRM : R ≤ M)
    (hodd : ¬ 2 ∣ R.relIndex M) {i : G} (hiM : i ∈ Subgroup.normalizer (M : Set G)) :
    ∃ m ∈ M, ∃ n ∈ Subgroup.normalizer (R : Set G), i = m * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R₁ : Subgroup G := R.map (MulAut.conj i).toMonoidHom with hR₁def
  have hR₁M : R₁ ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hiM r).1 (hRM hr)
  have hR₁card : Nat.card R₁ = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj i).injective
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hR₁2 : IsPGroup 2 R₁ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR2
    exact IsPGroup.of_card (n := k) (by rw [hR₁card, hk])
  have hR₁odd : ¬ 2 ∣ R₁.relIndex M := by
    have h1 := Subgroup.relIndex_mul_card R₁ M
    have h2 := Subgroup.relIndex_mul_card R M
    rw [inf_eq_left.2 hR₁M, hR₁card] at h1
    rw [inf_eq_left.2 hRM] at h2
    rw [Nat.eq_of_mul_eq_mul_right hRpos (h1.trans h2.symm)]
    exact hodd
  have hP : IsPGroup 2 (R.subgroupOf M) := hR2.comap_subtype
  have hQ : IsPGroup 2 (R₁.subgroupOf M) := hR₁2.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_iff_of_isPGroup (Γ := ↥M) hP hQ hodd hR₁odd
  have hAB : ∀ z : G, z ∈ R₁ ↔ ∃ y ∈ R, z = (g : G) * y * (g : G)⁻¹ := by
    intro z
    constructor
    · intro hz
      obtain ⟨y, hy, hzy⟩ := (hg ⟨z, hR₁M hz⟩).1 (Subgroup.mem_subgroupOf.2 hz)
      exact ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, by simpa using congrArg Subtype.val hzy⟩
    · rintro ⟨y, hy, rfl⟩
      have hyM : y ∈ M := hRM hy
      have hzM : (g : G) * y * (g : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem g.2 hyM) (M.inv_mem g.2)
      exact Subgroup.mem_subgroupOf.1 ((hg ⟨_, hzM⟩).2
        ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext (by simp)⟩)
  have hnN : (g : G)⁻¹ * i ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      obtain ⟨y, hy, hzy⟩ := (hAB (i * k * i⁻¹)).1 (Subgroup.mem_map.2 ⟨k, hk, rfl⟩)
      have e : (g : G)⁻¹ * i * k * ((g : G)⁻¹ * i)⁻¹ = (g : G)⁻¹ * (i * k * i⁻¹) * (g : G) := by
        group
      have e2 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) = y := by group
      rw [e, hzy, e2]
      exact hy
    · intro hk
      have hz : i * k * i⁻¹ ∈ R₁ :=
        (hAB _).2 ⟨(g : G)⁻¹ * i * k * ((g : G)⁻¹ * i)⁻¹, hk, by group⟩
      obtain ⟨r, hr, hrk⟩ := Subgroup.mem_map.1 hz
      have hrk' : r = k := by simpa [MulAut.conj_apply] using hrk
      rw [← hrk']
      exact hr
  exact ⟨(g : G), g.2, (g : G)⁻¹ * i, hnN, by group⟩

theorem cover_of_R (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (c : Concl105 G p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hI : Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) (hSC : S ≤ cx a)
    (hcent : ∀ s ∈ S, CentMod p (Jpart p (Ipart p L b) a) s) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hWodd : Odd (Nat.card (GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a))))
    (hIS : Ipart p L b ≤ Subgroup.normalizer
      ((S ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) : Subgroup G) : Set G))
    (hRW : R ≤ S ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a))
    (hWR : S ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) ≤ R ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a)) :
    S9.Covers p (Subgroup.normalizer (R : Set G)) (Ipart p L b) := by
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hDB : Dgrp b x ≤ B := lemma106107_dgrp_le h.mem hxB
  obtain ⟨-, hDel, -⟩ := dgrp_facts hc h
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hLeq : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hxn : cx x ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hLeq]
    exact fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hLb : L ⊓ cx b ≤ cs (Dgrp b x) := by
    intro g hg
    refine lemma106107_mem_cs_of ?_
    have hgx : g ∈ cx x := hLc.1 (Subgroup.mem_inf.1 hg).1
    have hgb : g ∈ cx b := (Subgroup.mem_inf.1 hg).2
    refine (Subgroup.closure_le _).2 ?_
    rintro k (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
  have hnorm : cs (Dgrp b x) ≤ Subgroup.normalizer ((L ⊓ cx b : Subgroup G) : Set G) := by
    intro g hg
    have hgx : g ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg x hxD).symm
    have hgb : g ∈ cx b := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg b hbD).symm
    exact lemma106107_normalizer_inf (hxn hgx) (Subgroup.le_normalizer hgb)
  have hLsub : IsSubnormal (L ⊓ cx b) (cs (Dgrp b x)) :=
    IsSubnormal.step hLb ((Subgroup.normal_subgroupOf_iff_le_normalizer hLb).2 hnorm)
      (IsSubnormal.refl _)
  have hlay : L ⊓ cx b ≤ Subgroup.normalizer ((GLAPLayer p (L ⊓ cx b) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hsubI : IsSubnormal (GLAPLayer p (L ⊓ cx b)) (cs (Dgrp b x)) :=
    (IsSubnormal.step (layer_le p (L ⊓ cx b))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (layer_le p (L ⊓ cx b))).2 hlay)
      (IsSubnormal.refl _)).trans hLsub
  have hD : IsPGroup p (Dgrp b x) := isPGroup_of_isElemAbelian hDel
  have hPP : PPrimePerfect p (Ipart p L b) := pPrimePerfect_glaPLayer p (L ⊓ cx b)
  have hsingle := c.single a ha ha1
  set I := Ipart p L b with hIdef
  set J := Jpart p I a with hJdef
  set W := GLAPPrimeCoreOf p J with hWdef
  set M : Subgroup G := S ⊔ W with hMdef
  have hIJ : I ≤ J := le_closureIn_self _ _
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hsingle.2 J hsingle.1 ⟨MulEquiv.refl _⟩
  have hBW : B ≤ Subgroup.normalizer (W : Set G) :=
    hBJ.trans (normalizer_le_normalizer_glaPPrimeCoreOf p J)
  have hIW : I ≤ Subgroup.normalizer (W : Set G) := hIJ.trans (le_normalizer_glaPPrimeCoreOf p J)
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := fun s hs =>
    normalizer_le_normalizer_glaPPrimeCoreOf p J
      (mem_centModSubgroup.1 (centMod_iff.1 (hcent s hs))).1
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := sup_le hSW Subgroup.le_normalizer
  have hRM : R ≤ M := hRW
  have hRNW : R ≤ Subgroup.normalizer (W : Set G) := hRM.trans hMW
  have hMR : M = R ⊔ W := le_antisymm hWR (sup_le hRM le_sup_right)
  have hWR_inf : R ⊓ W = ⊥ := eq_bot_of_le_odd (hR2.to_le inf_le_left) hWodd inf_le_right
  have hcardM : Nat.card M = Nat.card W * Nat.card R := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hRNW
    rw [inf_comm, hWR_inf, Subgroup.card_bot, mul_one, sup_comm] at h1
    rw [hMR]
    exact h1
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hRodd : ¬ 2 ∣ R.relIndex M := by
    rw [lemma106107_relIndex_of_card hRM rfl hRpos hcardM]
    exact hWodd.not_two_dvd_nat
  have hcov : ∀ i ∈ I, ∃ n ∈ Subgroup.normalizer (R : Set G), ∃ w ∈ W, i = n * w := by
    intro i hi
    obtain ⟨m, hm, n, hn, hin⟩ := lemma106107_frattini hR2 hRM hRodd (hIS hi)
    have hnW : n ∈ Subgroup.normalizer (W : Set G) := by
      have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMW hm)) (hIW hi)
      rw [hin, inv_mul_cancel_left] at h1
      exact h1
    obtain ⟨r, hr, w, hw, hrw⟩ : ∃ r ∈ R, ∃ w ∈ W, r * w = m := by
      have hmRW : m ∈ (R ⊔ W : Subgroup G) := by
        rw [← hMR]
        exact hm
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R W hRNW,
        Set.mem_mul] at hmRW
      obtain ⟨r, hr, w, hw, hrw⟩ := hmRW
      exact ⟨r, hr, w, hw, hrw⟩
    refine ⟨r * n, Subgroup.mul_mem _ (Subgroup.le_normalizer hr) hn, n⁻¹ * w * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnW) w).1 hw
      rwa [inv_inv] at this
    · rw [hin, ← hrw]
      group
  have hDW : Dgrp b x ≤ Subgroup.normalizer (W : Set G) := hDB.trans hBW
  have hDN : Dgrp b x ≤ Subgroup.normalizer (R : Set G) := hDB.trans hBR
  have hW : Nat.Coprime (Nat.card W) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp J)).symm
  exact covers_of_weak hD (Ipart_le_cs h) hsubI hPP hW hDW hIW hDN hcov

theorem cover_of_cent (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (c : Concl105 G p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hI : Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) (hSC : S ≤ cx a)
    (hSB : B ≤ Subgroup.normalizer (S : Set G))
    (hSN : S ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G))
    (hcent : ∀ s ∈ S, CentMod p (Jpart p (Ipart p L b) a) s) :
    ∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ S9.Covers p N (Ipart p L b) := by
  have hp : p.Prime := hc.ctx.prime
  obtain ⟨R, hR2, hR1, hRB, hRW, hWR⟩ := exists_R hc h c ha ha1 hS2 hSne hSB hSN
  have hsingle := c.single a ha ha1
  have hWodd : Odd (Nat.card (GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a))) :=
    Odd.of_dvd_nat (c.odd_core a ha ha1)
      (Subgroup.card_dvd_of_le (glaPPrimeCoreOf_le_of_isSubnormal hp hsingle.1.2.1))
  have hIS := I_norm_SW (p := p) (le_closureIn_self (Ipart p L b) (GLAPLayer p (cx a))) hcent
  exact ⟨Subgroup.normalizer (R : Set G), ⟨R, hR1, hR2, rfl⟩, hRB,
    cover_of_R hc h c ha ha1 hI hS2 hSne hSC hcent hR2 hRB hWodd hIS hRW hWR⟩

theorem lemma107 (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b)
    (c : Concl105 G p B x L b) :
    ∃ a ∈ Dgrp b x, a ∉ Subgroup.zpowers x ∧
      ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a) ∧
      Concl104 p B x L b a := by
  obtain ⟨a, T, haD, hax, hT2, hTB, hne⟩ := exists_aT hc h
  have ha1 : a ≠ 1 := fun h1 => hax (h1 ▸ Subgroup.one_mem _)
  by_cases hI : Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a
  · exfalso
    obtain ⟨hS2, hSne, hSD, hSC, hSB⟩ := S107_basic hc h haD hT2 hTB hne
    have hSN := S_norm_J hc h c haD ha1 hSD hSC
    have hcm := S_cent_mod hc h haD hI hSD hSN
    exact c.no_two_local (cover_of_cent hc h c haD ha1 hI hS2 hSne hSC hSB hSN hcm)
  · exact ⟨a, haD, hax, hI, lemma104_ab hc hin.l104 h hd5 hcase (h104_of_concl105 c haD ha1 hI)⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA
