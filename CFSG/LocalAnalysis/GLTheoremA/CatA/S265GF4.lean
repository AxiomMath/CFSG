module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CFam2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  commutator_le_left_of_le_normalizer le_normalizer_commutator_right')

set_option linter.unusedSectionVars false

section Helpers

private theorem mem_range_conj_of_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {α : MulAut G} (h : MulAut.congr e α ∈ (MulAut.conj : H →* MulAut H).range) :
    α ∈ (MulAut.conj : G →* MulAut G).range := by
  obtain ⟨c, hc⟩ := h
  refine ⟨e.symm c, ?_⟩
  ext g
  have h1 := congrArg (fun φ : MulAut H => φ (e g)) hc
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h1

private theorem card_eq_card_inf_ker_mul_card_map {Γ Γ' : Type*} [Group Γ] [Group Γ']
    (φ : Γ →* Γ') (S : Subgroup Γ) :
    Nat.card S = Nat.card (S ⊓ φ.ker : Subgroup Γ) * Nat.card (S.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp S.subtype)
  have hker : (φ.comp S.subtype).ker.map S.subtype = S ⊓ φ.ker := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_inf.2 ⟨s.2, hs⟩
    · intro hx
      obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.1 hx
      exact ⟨⟨x, hxS⟩, hxk, rfl⟩
  have hrange : (φ.comp S.subtype).range = S.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, hrange, ← hker, Subgroup.card_map_of_injective S.subtype_injective]

private theorem isPGroup_of_elemAb {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (hH : IsElemAbelian p H) : IsPGroup p H :=
  fun h => ⟨1, Subtype.ext (by simpa using hH.2 _ h.2)⟩

private theorem conj_apply_eq_mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (g : G) :
    MulAut.conj (α g) = α * MulAut.conj g * α⁻¹ := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]

private theorem centralizer_singleton_le_normalizer_zpowers {G : Type*} [Group G] (g : G) :
    Subgroup.centralizer ({g} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

end Helpers

section Lift

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}

private theorem sup_lift_data (cfg : QUCfg 3 S B T x b) {C : Type} [Group C] [Finite C]
    (hZC : Subgroup.center C = ⊥) {Φ : Ω →* MulAut C} {Λ : C →* Ω} (hΛ : Function.Injective Λ)
    (hΛΦ : ∀ g c, Λ (Φ g c) = g * Λ c * g⁻¹) (hδ : Φ b ∉ (MulAut.conj : C →* MulAut C).range)
    {F : Subgroup C} (hF : IsElemAbelian 3 F) (hFδ : ∀ c ∈ F, Φ b c = c) :
    IsElemAbelian 3 (Dgrp b x ⊔ F.map Λ) ∧
      Nat.card ↥(Dgrp b x ⊔ F.map Λ) = 3 ^ 2 * Nat.card F := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨-, hDel, hDc⟩ := S10.card_Dgrp cfg.elem hp cfg.hb cfg.xB cfg.x1 cfg.hbx
  have hΦx : Φ x = 1 := by
    ext c
    apply hΛ
    rw [hΛΦ, MulAut.one_apply, ← cfg.xcen (Λ c), mul_inv_cancel_right]
  have hD : Dgrp b x ≤ Subgroup.centralizer ((F.map Λ : Subgroup Ω) : Set Ω) := by
    rw [dgrp_eq]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro f _
      exact cfg.xcen f
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨c, hc, rfl⟩
      have h := hΛΦ b c
      rw [hFδ c hc] at h
      calc Λ c * b = b * Λ c * b⁻¹ * b := by rw [← h]
        _ = b * Λ c := by group
  have hcomm : ∀ h ∈ Dgrp b x, ∀ f ∈ F.map Λ, h * f = f * h := fun h hh f hf =>
    ((Subgroup.mem_centralizer_iff.1 (hD hh)) f hf).symm
  have hΦΛ : ∀ c, Φ (Λ c) = MulAut.conj c := conj_eq_of_lift hΛ hΛΦ
  have hbp : Φ b ^ 3 = 1 := by rw [← map_pow, cfg.elem.2 b cfg.hb, map_one]
  have hDle : Dgrp b x ≤ (Subgroup.zpowers (Φ b)).comap Φ := by
    rw [dgrp_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hΦx]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers _
  have hi : Dgrp b x ⊓ F.map Λ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyD, c, -, rfl⟩ := Subgroup.mem_inf.1 hy
    have h1 := hDle hyD
    rw [Subgroup.mem_comap, hΦΛ] at h1
    rw [eq_one_of_conj_mem_zpowers hp hZC hδ hbp h1, map_one]
    exact Subgroup.one_mem _
  refine ⟨isElemAbelian_sup_of_commute hDel (hF.map Λ) hcomm, ?_⟩
  rw [card_sup_of_commute hcomm hi, hDc, Subgroup.card_map_of_injective hΛ]

private theorem card_le_three_mul_card_map (cfg : QUCfg 3 S B T x b) {C : Type} [Group C]
    {Φ : Ω →* MulAut C} (hker : ∀ c ∈ B, Φ c = 1 → c ∈ Subgroup.zpowers x) :
    Nat.card B ≤ 3 * Nat.card ↥(B.map Φ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : B ⊓ Φ.ker ≤ Subgroup.zpowers x := fun c hc =>
    hker c (Subgroup.mem_inf.1 hc).1 (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hc).2)
  have hcard : Nat.card ↥(B ⊓ Φ.ker) ≤ 3 := by
    calc Nat.card ↥(B ⊓ Φ.ker) ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1
  rw [card_eq_card_inf_ker_mul_card_map Φ B]
  exact Nat.mul_le_mul_right _ hcard

end Lift

section F4


theorem qUFamCF4_holds : S265C.QUFamCF4 := by
  intro Ω _ _ S B T x b hN _ hF hL
  have cfg := hN.cfg
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI hSn : S.Normal := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top _
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted
    (hL.chevalleyExceptionalModel (by decide)).2
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Finite (ModGL .F4 K) := finite_modGL
  have hZC : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  have hconj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot hZC
  have hZ : Subgroup.center ↥S = ⊥ :=
    S267.BadExc.center_eq_bot_of_adjointGroup hp
      (S2019.commutator_self_eq_of_isQuasisimple cfg.quasi) cfg.core θ (by
        haveI := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier
          (K := K) (by rw [hK]; norm_num)).2
        rw [Nat.card_of_subsingleton
          (1 : CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .F4 K))]
        exact hp.not_dvd_one)
  have hβ : chevAut 3 S ⟨b, hnorm b⟩ ∉
      (MulAut.conj : PSimple 3 S →* MulAut (PSimple 3 S)).range :=
    chevAut_notMem_range_conj_of_fieldOn hp (by norm_num) hF
  have hβ3 : chevAut 3 S ⟨b, hnorm b⟩ ^ 3 = 1 := by
    have h : (⟨b, hnorm b⟩ : Subgroup.normalizer (S : Set Ω)) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using cfg.elem.2 b cfg.hb
    rw [← map_pow, h, map_one]
  have hβ'n : MulAut.congr θ.symm (chevAut 3 S ⟨b, hnorm b⟩) ∉
      (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)).range :=
    fun h => hβ (mem_range_conj_of_congr θ.symm h)
  have hβ'1 : MulAut.congr θ.symm (chevAut 3 S ⟨b, hnorm b⟩) ≠ 1 :=
    fun h => hβ'n ⟨1, by rw [map_one, h]⟩
  have hβ'ord : orderOf (MulAut.congr θ.symm (chevAut 3 S ⟨b, hnorm b⟩)) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hβ3, map_one]) hβ'1
  obtain ⟨σ, hσ, ψ, hψ⟩ := exists_conj_entrywise_of_noninner hK hβ'n hβ'ord
  obtain ⟨ε, hεβ⟩ : ∃ ε : ↥(adjointGroup .F4 K) ≃* PSimple 3 S,
      MulAut.congr ε.symm (chevAut 3 S ⟨b, hnorm b⟩) = entrywiseAdjointAut .F4 σ := by
    refine ⟨ψ.symm.trans θ, ?_⟩
    rw [← hψ]
    ext c
    rfl
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Ω →* MulAut ↥(adjointGroup .F4 K),
      ∀ g, Φ g = MulAut.congr ε.symm (chevAut 3 S ⟨g, hnorm g⟩) :=
    ⟨(MulAut.congr ε.symm).toMonoidHom.comp ((chevAut 3 S).comp
      ((MonoidHom.id Ω).codRestrict (Subgroup.normalizer (S : Set Ω)) hnorm)), fun g => rfl⟩
  have hΦb : Φ b = entrywiseAdjointAut .F4 σ := (hΦ b).trans hεβ
  have hδ : Φ b ∉
      (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)).range := by
    rw [hΦ]
    exact fun h => hβ (mem_range_conj_of_congr ε.symm h)
  obtain ⟨Λ, hΛi, -, hΛg⟩ := exists_lift cfg.comp cfg.quasi hZ hnorm ε
  have hΛΦ : ∀ g c, Λ (Φ g c) = g * Λ c * g⁻¹ := fun g c => by
    rw [hΦ]
    exact hΛg g c
  have hker : ∀ c ∈ B, Φ c = 1 → c ∈ Subgroup.zpowers x := by
    intro c hcB hc
    refine (cfg.centB c hcB).1 ((chevAut_eq_one_iff hp cfg.comp (hnorm c)).1 ?_)
    apply (MulAut.congr ε.symm).injective
    rw [← hΦ c, hc, map_one]
  have hBΦ := card_le_three_mul_card_map cfg hker
  set A₀ : Subgroup ↥(adjointGroup .F4 K) := (B.map Φ).comap
    (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)) with hA₀def
  have hA₀mem : ∀ a, a ∈ A₀ ↔ MulAut.conj a ∈ B.map Φ := fun a => by
    rw [hA₀def, Subgroup.mem_comap]
  have hA₀card : Nat.card A₀ = Nat.card ↥(B.map Φ ⊓
      (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)).range) := by
    rw [← Subgroup.card_map_of_injective hconj, hA₀def, Subgroup.map_comap_eq, inf_comm]
  have hBA₀ : Nat.card B ≤ 9 * Nat.card A₀ := by
    have h := card_le_three_mul_card_inf_conj hK (isPGroup_of_elemAb (cfg.elem.map Φ))
    rw [← hA₀card] at h
    omega
  have hA₀el : IsElemAbelian 3 A₀ := by
    rw [hA₀def]
    exact (cfg.elem.map Φ).comap hconj
  have hδB : Φ b ∈ B.map Φ := ⟨b, cfg.hb, rfl⟩
  have hA₀δ : ∀ a ∈ A₀, entrywiseAdjointAut .F4 σ a = a := by
    intro a ha
    rw [← hΦb]
    exact apply_eq_of_commute_conj ((cfg.elem.map Φ).comm hδB ((hA₀mem a).1 ha))
  have hfin : ∀ a ∈ A₀, a ≠ 1 →
      GLAPLayer 3 (fixSubgroup (entrywiseAdjointAut .F4 σ) ⊓ fixSubgroup (MulAut.conj a)) ≠ ⊥ →
      QUConcl 3 S B x b := by
    intro a ha ha1 hlay
    obtain ⟨e, heB, hea⟩ := Subgroup.mem_map.1 ((hA₀mem a).1 ha)
    exact qUConcl_of_fix cfg hnorm ε hZC Φ hΦ hδ heB ha1 hea (by rw [hΦb]; exact hlay)
  obtain ⟨E₃, t, hE₃, hE₃c, ht2, htδ, hE₃δ, hE₃t⟩ := exists_fix_elemAb_27 (σ := σ)
  obtain ⟨hE₅el, hE₅c⟩ := sup_lift_data cfg hZC hΛi hΛΦ hδ hE₃ fun c hc => by
    rw [hΦb]
    exact hE₃δ c hc
  have hΛt : Λ t ≠ 1 := fun h => by
    have ht1 : t = 1 := hΛi (h.trans (map_one Λ).symm)
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hU : Subgroup.zpowers (Λ t) ≠ ⊥ := by
    rwa [Ne, Subgroup.zpowers_eq_bot]
  have hU2 : IsPGroup 2 (Subgroup.zpowers (Λ t)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_injective Λ hΛi t, ht2, pow_one])
  have hE₅N : Dgrp b x ⊔ E₃.map Λ ≤
      Subgroup.normalizer ((Subgroup.zpowers (Λ t) : Subgroup Ω) : Set Ω) := by
    refine le_trans ?_ (centralizer_singleton_le_normalizer_zpowers (Λ t))
    refine sup_le ?_ ?_
    · rw [dgrp_eq]
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (cfg.xcen (Λ t)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h := hΛΦ b t
        rw [hΦb, htδ] at h
        calc b * Λ t = b * Λ t * b⁻¹ * b := by group
          _ = Λ t * b := by rw [← h]
    · rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg Λ (Subgroup.mem_centralizer_singleton_iff.1 (hE₃t he))
  have hE₅card : Nat.card ↥(Dgrp b x ⊔ E₃.map Λ) = 3 ^ 5 := by
    rw [hE₅c, hE₃c] <;> norm_num
  have hk5 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.le_glaTwoLocalRank_of_elemAb
    hp hU hU2 hE₅N hE₅el hE₅card
  have hB5 : 3 ^ 5 ≤ Nat.card B := le_trans (Nat.pow_le_pow_right (by norm_num) hk5) cfg.rank
  obtain ⟨E₄, hE₄, hE₄c, hE₄δ⟩ := exists_fix_elemAb_81 (σ := σ)
  obtain ⟨hE₆el, hE₆c⟩ := sup_lift_data cfg hZC hΛi hΛΦ hδ hE₄ fun c hc => by
    rw [hΦb]
    exact hE₄δ c hc
  have hE₆card : Nat.card ↥(Dgrp b x ⊔ E₄.map Λ) = 3 ^ 6 := by
    rw [hE₆c, hE₄c] <;> norm_num
  have hfin81 : 3 ^ 6 ≤ Nat.card B → QUConcl 3 S B x b := by
    intro h6
    have h81 : 3 ^ 4 ≤ Nat.card A₀ := by
      have := hBA₀
      norm_num at h6 ⊢
      omega
    obtain ⟨a, ha, ha1, hlay⟩ := exists_fix_glaPLayer_of_card_ge_81 hK hσ hA₀el hA₀δ h81
    exact hfin a ha ha1 hlay
  rcases cfg.maxc with hTB | hmax
  · have hBV : B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) :=
      le_normalizer_commutator_right' T B
    have hV2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) :=
      cfg.two.to_le (commutator_le_left_of_le_normalizer cfg.bnorm)
    by_cases hV : (⁅T, B⁆ : Subgroup Ω).map Φ = ⊥
    ·
      have hVk : ∀ v ∈ (⁅T, B⁆ : Subgroup Ω), Φ v = 1 := fun v hv => by
        have h : Φ v ∈ (⁅T, B⁆ : Subgroup Ω).map Φ := ⟨v, hv, rfl⟩
        rw [hV] at h
        exact Subgroup.mem_bot.1 h
      have hN : Dgrp b x ⊔ E₄.map Λ ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) := by
        refine sup_le ((S10.card_Dgrp cfg.elem hp cfg.hb cfg.xB cfg.x1 cfg.hbx).1.trans hBV) ?_
        rintro _ ⟨e, -, rfl⟩
        refine Subgroup.mem_normalizer_fintype fun v hv => ?_
        have h := hΛΦ v e
        rw [hVk v hv, MulAut.one_apply] at h
        have h' : Λ e * v * (Λ e)⁻¹ = v := by
          calc Λ e * v * (Λ e)⁻¹ = v * Λ e * v⁻¹ * v * (Λ e)⁻¹ := by rw [← h]
            _ = v := by group
        rw [h']
        exact hv
      have hk6 :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.le_glaTwoLocalRank_of_elemAb
          hp hTB hV2 hN hE₆el hE₆card
      exact hfin81 (le_trans (Nat.pow_le_pow_right (by norm_num) hk6) cfg.rank)
    ·
      set V : Subgroup (MulAut ↥(adjointGroup .F4 K)) := (⁅T, B⁆ : Subgroup Ω).map Φ with hVdef
      have hVinn : V ≤
          (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)).range := by
        rw [hVdef, Subgroup.map_commutator]
        exact commutator_le_range_conj hK _ _
      have hVB : ∀ e ∈ B, ∀ w ∈ V, Φ e * w * (Φ e)⁻¹ ∈ V := by
        intro e he w hw
        rw [hVdef] at hw ⊢
        exact (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer_map Φ ⟨e, hBV he, rfl⟩) w).1 hw
      set V' : Subgroup ↥(adjointGroup .F4 K) := V.comap MulAut.conj with hV'def
      have hV'mem : ∀ v, v ∈ V' ↔ MulAut.conj v ∈ V := fun v => by
        rw [hV'def, Subgroup.mem_comap]
      have hV'ne : V' ≠ ⊥ := by
        intro h
        apply hV
        rw [← Subgroup.map_comap_eq_self hVinn, ← hV'def, h, Subgroup.map_bot]
      have hV'2 : IsPGroup 2 V' := by
        rw [hV'def, hVdef]
        exact (hV2.map Φ).comap_of_injective _ hconj
      have hV'δ : V'.map (entrywiseAdjointAut .F4 σ).toMonoidHom = V' := by
        refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective
          (f := (entrywiseAdjointAut .F4 σ).toMonoidHom) (entrywiseAdjointAut .F4 σ).injective).ge
        rintro _ ⟨v, hv, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hV'mem, conj_apply_eq_mul_conj_mul_inv, ← hΦb]
        exact hVB b cfg.hb _ ((hV'mem v).1 hv)
      have hA₀V' : A₀ ≤ Subgroup.normalizer (V' : Set ↥(adjointGroup .F4 K)) := by
        intro a ha
        refine Subgroup.mem_normalizer_fintype fun v hv => ?_
        obtain ⟨e, heB, hea⟩ := Subgroup.mem_map.1 ((hA₀mem a).1 ha)
        rw [SetLike.mem_coe, hV'mem, map_mul, map_mul, map_inv, ← hea]
        exact hVB e heB _ ((hV'mem v).1 hv)
      obtain ⟨U, hU, hU2, hUδ, hA₀U⟩ := exists_fixed_two_subgroup (f := 3) ⟨1, by norm_num⟩ hK
        (by rw [← hσ]; exact pow_orderOf_eq_one σ) (isPGroup_of_elemAb hA₀el) hA₀δ hV'ne hV'2
        hV'δ hA₀V'
      obtain ⟨a, ha, ha1, hlay⟩ := exists_fix_glaPLayer_of_card_ge_27 hK hσ hA₀el hA₀δ
        (by have := hBA₀; norm_num at hB5 ⊢; omega) hU hU2 hUδ hA₀U
      exact hfin a ha ha1 hlay
  · exact hfin81 (by rw [← hE₆card]; exact hmax _ hE₆el)

end F4

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
