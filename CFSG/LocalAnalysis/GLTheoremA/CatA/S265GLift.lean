module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.CGT.Foote81L6.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Model

variable {C H : Type*} [Group C] [Group H]

private theorem conj_injective_of_center (hZ : Subgroup.center C = ⊥) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hcZ : c ∈ Subgroup.center C := Subgroup.mem_center_iff.2 fun g => by
    have h := congrArg (fun φ : MulAut C => φ g) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * c = c * g * c⁻¹ * c := by rw [h]
      _ = c * g := by group
  rw [hZ] at hcZ
  exact Subgroup.mem_bot.1 hcZ

theorem map_fixSubgroup_congr_symm (ε : C ≃* H) (α : MulAut H) :
    (fixSubgroup (MulAut.congr ε.symm α)).map ε.toMonoidHom = fixSubgroup α := by
  ext h
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [mem_fixSubgroup, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm] at hc
    have h2 := congrArg ε hc
    rw [MulEquiv.apply_symm_apply] at h2
    exact mem_fixSubgroup.2 h2
  · intro hh
    refine ⟨ε.symm h, ?_, by simp⟩
    rw [mem_fixSubgroup, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply, mem_fixSubgroup.1 hh]

theorem eq_one_of_conj_mem_zpowers [Finite C] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center C = ⊥) {δ : MulAut C} (hδ : δ ∉ (MulAut.conj : C →* MulAut C).range)
    (hδp : δ ^ p = 1) {c : C} (hc : MulAut.conj c ∈ Subgroup.zpowers δ) : c = 1 := by
  haveI : Finite (MulAut C) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI := Fact.mk hp
  by_contra hc1
  have hconj1 : MulAut.conj c ≠ 1 := fun h =>
    hc1 (conj_injective_of_center hZ (h.trans (map_one _).symm))
  have hδ1 : δ ≠ 1 := fun h => hδ ⟨1, by rw [map_one, h]⟩
  have hδord : orderOf δ = p := orderOf_eq_prime hδp hδ1
  have hdvd : orderOf (MulAut.conj c) ∣ p := by
    rw [← hδord]
    exact orderOf_dvd_of_mem_zpowers hc
  have hord : orderOf (MulAut.conj c) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hconj1
    · exact h
  have heq : Subgroup.zpowers (MulAut.conj c) = Subgroup.zpowers δ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hδord])
  have hmem : δ ∈ Subgroup.zpowers (MulAut.conj c) := by
    rw [heq]
    exact Subgroup.mem_zpowers δ
  have hle : Subgroup.zpowers (MulAut.conj c) ≤ (MulAut.conj : C →* MulAut C).range :=
    Subgroup.zpowers_le.2 ⟨c, rfl⟩
  exact hδ (hle hmem)

end Model

section Sup

variable {G : Type*} [Group G] {p : ℕ}

theorem isElemAbelian_sup_of_commute {H F : Subgroup G} (hH : IsElemAbelian p H)
    (hF : IsElemAbelian p F) (hc : ∀ h ∈ H, ∀ f ∈ F, h * f = f * h) :
    IsElemAbelian p (H ⊔ F) := by
  have hsup : H ⊔ F = Subgroup.closure ((H : Set G) ∪ F) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a (ha | ha) b (hb | hb)
    · exact hH.comm ha hb
    · exact hc a ha b hb
    · exact (hc b hb a ha).symm
    · exact hF.comm ha hb
  · rintro a (ha | ha)
    · exact hH.2 a ha
    · exact hF.2 a ha

theorem card_sup_of_commute {H F : Subgroup G} (hc : ∀ h ∈ H, ∀ f ∈ F, h * f = f * h)
    (hi : H ⊓ F = ⊥) : Nat.card ↥(H ⊔ F) = Nat.card H * Nat.card F := by
  refine CFSG.CGT.Foote81L6.card_sup_of_le_normalizer (fun f hf => ?_) hi
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : f * h * f⁻¹ = h := by rw [← hc h hh f hf]; group
    rw [e]
    exact hh
  · intro hh
    have e : f * h * f⁻¹ = h := by
      have h' := hc _ hh f hf
      have h'' : f * h = f * (f * h * f⁻¹) := by
        calc f * h = f * h * f⁻¹ * f := by group
          _ = f * (f * h * f⁻¹) := h'
      exact (mul_left_cancel h'').symm
    rw [e] at hh
    exact hh

end Sup

section Lift

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_lift {S : Subgroup Ω} (hcomp : GLAPComponent 3 (⊤ : Subgroup Ω) S)
    (hq : CFSG.Open.IsQuasisimple ↥S) (hZ : Subgroup.center ↥S = ⊥)
    (hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω)) {C : Type*} [Group C]
    (ε : C ≃* PSimple 3 S) :
    ∃ Λ : C →* Ω, Function.Injective Λ ∧ Λ.range = S ∧
      ∀ g c, Λ (MulAut.congr ε.symm (chevAut 3 S ⟨g, hnorm g⟩) c) = g * Λ c * g⁻¹ := by
  set eS : ↥S ≃* PSimple 3 S := MulEquiv.ofBijective (chevQuotHom 3 S)
    ⟨CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1.chevQuotHom_injective_of_center hcomp hq hZ,
      chevQuotHom_surjective 3 S⟩ with heS
  refine ⟨S.subtype.comp (eS.symm.toMonoidHom.comp ε.toMonoidHom),
    S.subtype_injective.comp (eS.symm.injective.comp ε.injective), ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact (eS.symm (ε c)).2
    · intro hy
      refine ⟨ε.symm (eS ⟨y, hy⟩), ?_⟩
      simp
  · intro g c
    obtain ⟨s, hs⟩ := eS.surjective (ε c)
    have hcs : ε c = chevQuotHom 3 S s := hs.symm
    have key : eS.symm (chevAut 3 S ⟨g, hnorm g⟩ (ε c)) = S.normalizerMonoidHom ⟨g, hnorm g⟩ s := by
      rw [hcs, chevAut_chevQuotHom, MulEquiv.symm_apply_eq]
      rfl
    have hΛc : (S.subtype.comp (eS.symm.toMonoidHom.comp ε.toMonoidHom)) c = (s : Ω) := by
      show ((eS.symm (ε c) : ↥S) : Ω) = s
      rw [← hs, MulEquiv.symm_apply_apply]
    rw [hΛc]
    show ((eS.symm (ε ((MulAut.congr ε.symm (chevAut 3 S ⟨g, hnorm g⟩)) c)) : ↥S) : Ω) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply, key, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem conj_eq_of_lift {C : Type*} [Group C] {Φ : Ω →* MulAut C} {Λ : C →* Ω}
    (hΛ : Function.Injective Λ) (hΛg : ∀ g c, Λ (Φ g c) = g * Λ c * g⁻¹) (c : C) :
    Φ (Λ c) = MulAut.conj c := by
  ext c'
  apply hΛ
  rw [hΛg, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem qUConcl_of_fix {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω)) {C : Type} [Group C] [Finite C]
    (ε : C ≃* PSimple p S) (hZC : Subgroup.center C = ⊥) (Φ : Ω →* MulAut C)
    (hΦ : ∀ g, Φ g = MulAut.congr ε.symm (chevAut p S ⟨g, hnorm g⟩))
    (hδ : Φ b ∉ (MulAut.conj : C →* MulAut C).range) {e : Ω} (heB : e ∈ B) {a : C} (ha : a ≠ 1)
    (hea : Φ e = MulAut.conj a)
    (hlay : GLAPLayer p (fixSubgroup (Φ b) ⊓ fixSubgroup (MulAut.conj a)) ≠ ⊥) :
    QUConcl p S B x b := by
  classical
  have hp := cfg.prime
  have hlay' : GLAPLayer p (fixSubgroup (chevAut p S ⟨b, hnorm b⟩) ⊓
      fixSubgroup (chevAut p S ⟨e, hnorm e⟩)) ≠ ⊥ := by
    rw [← hea, hΦ b, hΦ e] at hlay
    have hmap := CFSG.glaPLayer_map_eq_of_injective hp ε.toMonoidHom ε.injective
      (fixSubgroup (MulAut.congr ε.symm (chevAut p S ⟨b, hnorm b⟩)) ⊓
        fixSubgroup (MulAut.congr ε.symm (chevAut p S ⟨e, hnorm e⟩)))
    rw [Subgroup.map_inf _ _ ε.toMonoidHom ε.injective, map_fixSubgroup_congr_symm,
      map_fixSubgroup_congr_symm] at hmap
    rw [← hmap]
    intro hbot
    exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ ε.injective).1 hbot)
  have hne := S265F3.glaPLayer_inf_cx_ne_bot_of_fix hp cfg.core (hnorm b) (hnorm e) hlay'
  have hΦx : Φ x = 1 := by
    rw [hΦ, (chevAut_eq_one_iff hp cfg.comp (hnorm x)).2
      ((cfg.centB x cfg.xB).2 (Subgroup.mem_zpowers x)), map_one]
  have hDle : Dgrp b x ≤ (Subgroup.zpowers (Φ b)).comap Φ := by
    rw [dgrp_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hΦx]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers _
  have hbp : Φ b ^ p = 1 := by rw [← map_pow, cfg.elem.2 b cfg.hb, map_one]
  have heD : e ∉ Dgrp b x := by
    intro he
    have h1 := hDle he
    rw [Subgroup.mem_comap, hea] at h1
    exact ha (eq_one_of_conj_mem_zpowers hp hZC hδ hbp h1)
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    first
    | exact cfg.xcen s
    | exact (cfg.xcen s).symm
  exact Or.inl (S265F3.exists_e3_of_layer hp cfg.elem cfg.xB cfg.x1 hSx cfg.hb cfg.hbx heB heD hne)

end Lift

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
