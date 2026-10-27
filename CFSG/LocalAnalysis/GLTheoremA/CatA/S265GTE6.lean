module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CC1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GTE6Mod
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GTE6Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GTE6Out
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GTE6Fix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  commutator_le_left_of_le_normalizer le_normalizer_commutator_right')
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Helpers

private theorem mem_range_conj_of_congr_twE6 {G H : Type*} [Group G] [Group H] (e : G ≃* H)
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

private theorem conj_injective_twE6 {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hc : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun h => by
    have h1 : g * h * g⁻¹ = h := by
      simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut G => φ h) hg
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

private theorem apply_eq_of_conj_comm_twE6 {G : Type*} [Group G]
    (hZ : Function.Injective (MulAut.conj : G →* MulAut G)) {x : G} {g : MulAut G}
    (h : g * MulAut.conj x = MulAut.conj x * g) : g x = x := by
  apply hZ
  have h1 : MulAut.conj (g x) = g * MulAut.conj x * g⁻¹ := by
    ext y
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]
  rw [h1, h, mul_inv_cancel_right]

private theorem card_eq_card_inf_ker_mul_card_map_twE6 {Γ Γ' : Type*} [Group Γ] [Group Γ']
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

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}

private theorem card_le_three_mul_card_map_twE6 (cfg : QUCfg 3 S B T x b) {C : Type} [Group C]
    {Φ : Ω →* MulAut C} (hker : ∀ c ∈ B, Φ c = 1 → c ∈ Subgroup.zpowers x) :
    Nat.card B ≤ 3 * Nat.card ↥(B.map Φ) := by
  have hle : B ⊓ Φ.ker ≤ Subgroup.zpowers x := fun c hc =>
    hker c (Subgroup.mem_inf.1 hc).1 (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hc).2)
  have hcard : Nat.card ↥(B ⊓ Φ.ker) ≤ 3 := by
    calc Nat.card ↥(B ⊓ Φ.ker) ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      _ = 3 := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1
  rw [card_eq_card_inf_ker_mul_card_map_twE6 Φ B]
  exact Nat.mul_le_mul_right _ hcard

end Helpers

section TwE6


theorem qUFamCTE6_holds : S265C.QUFamCTE6 := by
  intro Ω _ _ S B T x b hN hJcat hF hL
  have cfg := hN.cfg
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI hSn : S.Normal := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top _
  have hact := hN.nlAct
  have hJS : Ipart 3 S b ≤ S := fun y hy => (hact.comp.1 hy).1
  obtain ⟨K, _, _, σ, δ, hK, hσ, hδ, hZC, ε, hεβ⟩ :=
    exists_model_fieldActor_of_fieldOn (isQuasisimple_pQuot_of_glaPComponent hp cfg.comp) hF hL
  have hconj : Function.Injective
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) :=
    conj_injective_twE6 hZC
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Ω →* MulAut ↥(twistedE6RootGroup K σ),
      ∀ g, Φ g = MulAut.congr ε.symm (chevAut 3 S ⟨g, hnorm g⟩) :=
    ⟨(MulAut.congr ε.symm).toMonoidHom.comp ((chevAut 3 S).comp
      ((MonoidHom.id Ω).codRestrict (Subgroup.normalizer (S : Set Ω)) hnorm)), fun g => rfl⟩
  have hΦb : Φ b = fieldActor (t := TwistTag.E6) σ δ := (hΦ b).trans hεβ
  have hδ' : Φ b ∉
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range := by
    rw [hΦ]
    exact fun h => chevAut_notMem_range_conj_of_fieldOn hp (by norm_num) hF
      (mem_range_conj_of_congr_twE6 ε.symm h)
  have hker : ∀ c ∈ B, Φ c = 1 → c ∈ Subgroup.zpowers x := by
    intro c hcB hc
    refine (cfg.centB c hcB).1 ((chevAut_eq_one_iff hp cfg.comp (hnorm c)).1 ?_)
    apply (MulAut.congr ε.symm).injective
    rw [← hΦ c, hc, map_one]
  have hBΦ := card_le_three_mul_card_map_twE6 cfg hker
  have hδB : Φ b ∈ B.map Φ := ⟨b, cfg.hb, rfl⟩
  have hΦinn := card_le_three_mul_card_inf_inner_of_fieldActor Nat.prime_two (by norm_num) hK σ hσ
    (by norm_num) hδ (cfg.elem.map Φ) (by rw [← hΦb]; exact hδB)
  have hB6 := three_pow_six_le_card_of_isTE6two hN hJcat
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : Subgroup ↥(twistedE6RootGroup K σ),
      A₀ = (B.map Φ).comap MulAut.conj := ⟨_, rfl⟩
  have hA₀mem : ∀ a, a ∈ A₀ ↔ MulAut.conj a ∈ B.map Φ := fun a => by
    rw [hA₀def, Subgroup.mem_comap]
  have hA₀card : Nat.card A₀ = Nat.card ↥(B.map Φ ⊓ twistedE6Inn K σ) := by
    rw [← Subgroup.card_map_of_injective hconj, hA₀def, Subgroup.map_comap_eq]
    exact congrArg (fun H : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) => Nat.card ↥H)
      (inf_comm _ _)
  have hA81 : 3 ^ 4 ≤ Nat.card A₀ := by
    rw [hA₀card]
    have h6 : 729 ≤ Nat.card B := le_of_eq_of_le (by norm_num) hB6
    have h81 : (3 : ℕ) ^ 4 = 81 := by norm_num
    rw [h81]
    omega
  have hA₀el : IsElemAbelian 3 A₀ := by
    rw [hA₀def]
    exact (cfg.elem.map Φ).comap hconj
  have hA₀δ : ∀ a ∈ A₀, fieldActor (t := TwistTag.E6) σ δ a = a := by
    intro a ha
    rw [← hΦb]
    exact apply_eq_of_conj_comm_twE6 hconj ((cfg.elem.map Φ).comm hδB ((hA₀mem a).1 ha))
  have hfin : ∀ a ∈ A₀, a ≠ 1 →
      GLAPLayer 3 (fixSubgroup (fieldActor (t := TwistTag.E6) σ δ) ⊓
        fixSubgroup (MulAut.conj a)) ≠ ⊥ →
      QUConcl 3 S B x b := by
    intro a ha ha1 hlay
    obtain ⟨e, heB, hea⟩ := Subgroup.mem_map.1 ((hA₀mem a).1 ha)
    exact qUConcl_of_fix cfg hnorm ε hZC Φ hΦ hδ' heB ha1 hea (by rw [hΦb]; exact hlay)
  rcases S265C.C1.case1_or_case2 hSn cfg.core cfg.two cfg.bnorm cfg.rank cfg.maxc with
    hc1 | ⟨t, ht, c, hc, htc⟩
  ·
    exfalso
    have hDJ : Dgrp b x ≤ Subgroup.centralizer ((Ipart 3 S b : Subgroup Ω) : Set Ω) := by
      refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_,
        Set.singleton_subset_iff.2 (Subgroup.mem_centralizer_iff.2 fun y _ => cfg.xcen y)⟩)
      exact Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 (hact.comp.1 hy).2 b (Set.mem_singleton b)).symm
    obtain ⟨-, -, hDcard⟩ := S10.card_Dgrp cfg.elem hp cfg.hb cfg.xB cfg.x1 cfg.hbx
    exact S265C.C1.false_of_case1_lie cfg.kgroup cfg.elem cfg.big hact.le hDJ hDcard hact.comp
      hact.norm (fun E hE hEel => hc1 E hEel (hE.trans (sup_le_sup_right hJS B))) (Or.inr hJcat)
      hN.nl
  ·
    have hV2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) :=
      cfg.two.to_le (commutator_le_left_of_le_normalizer cfg.bnorm)
    have hBV : B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) :=
      le_normalizer_commutator_right' T B
    obtain ⟨V, hVdef⟩ : ∃ V : Subgroup (MulAut ↥(twistedE6RootGroup K σ)),
        V = (⁅T, B⁆ : Subgroup Ω).map Φ := ⟨_, rfl⟩
    have hΦtc : Φ ⁅t, c⁆ ≠ 1 := by
      intro h1
      apply htc
      refine centMod_iff.1 ((chevAut_eq_one_iff hp cfg.comp (hnorm _)).1 ?_)
      apply (MulAut.congr ε.symm).injective
      rw [← hΦ, h1, map_one]
    have hVne : V ≠ ⊥ := by
      intro h
      apply hΦtc
      have hmem : Φ ⁅t, c⁆ ∈ V := by
        rw [hVdef]
        exact ⟨⁅t, c⁆, Subgroup.commutator_mem_commutator ht hc, rfl⟩
      rw [h] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hVp : IsPGroup 2 V := by
      rw [hVdef]
      exact hV2.map Φ
    have hVinn : V ≤
        (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range := by
      intro v hv
      have hvI : v ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
        have hv' := hv
        rw [hVdef, Subgroup.map_commutator] at hv'
        exact commutator_le_twInndiag Nat.prime_two (by norm_num) hK σ hσ _ _ hv'
      obtain ⟨k, hk⟩ := hVp ⟨v, hv⟩
      have h2 : v ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      exact mem_inner_of_twInndiag_of_two_pow Nat.prime_two (by norm_num) hK σ hσ hvI h2
    have hVB : ∀ e ∈ B, ∀ w ∈ V, Φ e * w * (Φ e)⁻¹ ∈ V := by
      intro e he w hw
      rw [hVdef] at hw ⊢
      exact (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer_map Φ ⟨e, hBV he, rfl⟩) w).1 hw
    obtain ⟨V', hV'def⟩ : ∃ V' : Subgroup ↥(twistedE6RootGroup K σ),
        V' = V.comap MulAut.conj := ⟨_, rfl⟩
    have hV'mem : ∀ v, v ∈ V' ↔ MulAut.conj v ∈ V := fun v => by
      rw [hV'def, Subgroup.mem_comap]
    have hV'ne : V' ≠ ⊥ := by
      intro h
      apply hVne
      rw [← Subgroup.map_comap_eq_self hVinn, ← hV'def, h, Subgroup.map_bot]
    have hV'2 : IsPGroup 2 V' := by
      rw [hV'def]
      exact hVp.comap_of_injective _ hconj
    have hA₀V' : A₀ ≤ Subgroup.normalizer (V' : Set ↥(twistedE6RootGroup K σ)) := by
      intro a ha
      refine Subgroup.mem_normalizer_fintype fun v hv => ?_
      obtain ⟨e, heB, hea⟩ := Subgroup.mem_map.1 ((hA₀mem a).1 ha)
      rw [SetLike.mem_coe, hV'mem, map_mul, map_mul, map_inv, ← hea]
      exact hVB e heB _ ((hV'mem v).1 hv)
    obtain ⟨a, ha, ha1, hlay⟩ :=
      exists_fix_glaPLayer_twE6Eight hK hσ hδ hA₀el hA81 hA₀δ hV'ne hV'2 hA₀V'
    exact hfin a ha ha1 hlay

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
