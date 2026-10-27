module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X1
public import CFSG.ClassicalInvolution.Asc77.AscCX6Eng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


section Core

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def QTFAt (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) : Prop :=
  ∀ {b : G}, b ∈ cA S R R' → ∀ hb2 : b * b = 1, b ≠ 1 → BadElt z b → LayerFacts hyp hb2

@[expose] def P25X_QTF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂), QTFAt hyp

theorem false_of_growth (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp)
    {D₀ D : Subgroup G} (hDA : D ≤ cA S R R') (hD₀D : D₀ ≤ D) (hbad : BadSub z D)
    (hmax : ∀ F : Subgroup G, F ≤ cA S R R' → D₀ ≤ F → BadSub z F → Nat.card F ≤ Nat.card D)
    {x b : G} (hxA : x ∈ cA S R R') (hxD : x ∉ D) (hxzD : x * z ∉ D) (hbD : b ∈ D) (hb1 : b ≠ 1)
    (hb2 : b * b = 1) (hbx : x * b = b * x) (hbc : ∀ d ∈ D, d * b = b * d) : False := by
  classical
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  set E := D ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers z with hE
  have hEA : E ≤ cA S R R' :=
    sup_le (sup_le hDA (Subgroup.zpowers_le.mpr hxA)) (Subgroup.zpowers_le.mpr hzA)
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hbc d hd)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbx)
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (hzS b (hDA hbD).1).symm)
  have hbbad : BadElt z b := badElt_of_mem hDA hyp hbad hbD
  have hQb := hQ (hDA hbD) hb2 hb1 hbbad
  have hzY := hQb.zY
  have hzb : z ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS b (hDA hbD).1).symm
  have hEY : ∀ e ∈ E, conjSub e (TwinDisc.coreLayer Ω b) = TwinDisc.coreLayer Ω b := fun e he =>
    TwinDisc.conjSub_coreLayer hΩ hb2' (hEb he)
  set lam := CX.layerHom (TwinDisc.coreLayer Ω b) E hEY with hlam
  have hlamact : ∀ e : E, lam e = actOf hyp hb2 ⟨e, hEb e.2⟩ := fun e => rfl
  have hexpP : ∀ e : E, lam e * lam e = 1 := fun e => by
    rw [hlamact]
    exact hQb.exp2 e (hEA e.2) (hEb e.2)
  have hcardP : Nat.card lam.range ≤ 4 := by
    refine le_trans (Subgroup.card_le_of_le (K := ((cA S R R').subgroupOf
      (Subgroup.centralizer ({b} : Set G))).map (actOf hyp hb2)) ?_) hQb.card
    rintro _ ⟨e, rfl⟩
    refine ⟨⟨e, hEb e.2⟩, ?_, (hlamact e).symm⟩
    exact Subgroup.mem_subgroupOf.mpr (hEA e.2)
  let z₀ : E := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hlamz : lam z₀ = MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
      ↥(TwinDisc.coreLayer Ω b) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b)) := by
    rw [hlamact]
    exact actW_eq_conj hΩ hb2' hzb hzY
  have hζ1 : lam z₀ ≠ 1 := by
    rw [hlamz]
    exact conj_ne_one_of_center_eq_bot hQb.center (mk_ne_one_of_involution hzY hz2 hz1)
  have hD : ∀ d ∈ D.subgroupOf E, lam d ≠ lam z₀ := by
    intro d hd heq
    apply hbad
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hzC : z ∈ Subgroup.centralizer (D : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun g hg => hzS g (hDA hg).1
    refine mem_zStarOf_of_layerAut_eq_conj (d := (d : G)) (H := Subgroup.centralizer (D : Set G))
      (fun h hh => TwinDisc.conjSub_coreLayer hΩ hb2'
        (Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hh) b hbD).symm))
      (fun h hh => ((Subgroup.mem_centralizer_iff.mp hh) d hdD).symm) hzC (hEY d d.2) hzY
      hQb.center ?_
    intro y
    have := congrArg (fun φ => φ y) heq
    simp only [hlamz, MulAut.conj_apply] at this
    exact this
  obtain ⟨β, hβ2, hβζ, hβr, hβD, hcov⟩ := CX.exists_beta lam hexpP hcardP hζ1 hD
  set F := ((Subgroup.zpowers β).comap lam).map E.subtype with hF
  have hzpow : ∀ γ ∈ Subgroup.zpowers β, γ = 1 ∨ γ = β := fun γ hγ =>
    CX.eq_one_or_eq_of_mem_zpowers hβ2 hγ
  have hmemF : ∀ e : E, (lam e = 1 ∨ lam e = β) → (e : G) ∈ F := by
    intro e he
    refine ⟨e, ?_, rfl⟩
    show lam e ∈ Subgroup.zpowers β
    rcases he with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers β
  have hFprop : ∀ g ∈ F, ∃ e : E, (e : G) = g ∧ (lam e = 1 ∨ lam e = β) := by
    rintro g ⟨e, he, rfl⟩
    exact ⟨e, rfl, hzpow _ he⟩
  have hDF : D ≤ F := fun d hd =>
    hmemF ⟨d, Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)⟩
      (hβD _ (Subgroup.mem_subgroupOf.mpr hd))
  have hFE : F ≤ E := Subgroup.map_subtype_le _
  have hFA : F ≤ cA S R R' := hFE.trans hEA
  have hFb : F ≤ Subgroup.centralizer ({b} : Set G) := hFE.trans hEb
  have hF2 : IsPGroup 2 F := hE2.to_le hFE
  have hFY : ∀ e ∈ F, conjSub e (TwinDisc.coreLayer Ω b) = TwinDisc.coreLayer Ω b := fun e he =>
    TwinDisc.conjSub_coreLayer hΩ hb2' (hFb he)
  let x₀ : E := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))⟩
  have hxF : x ∈ F ∨ x * z ∈ F := by
    rcases hcov x₀ with h | h
    · exact Or.inl (hmemF x₀ h)
    · exact Or.inr (hmemF (x₀ * z₀) h)
  have hDltF : Nat.card D < Nat.card F := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hDF fun hDFeq => ?_)
    rcases hxF with h | h
    · exact hxD (hDFeq ▸ h)
    · exact hxzD (hDFeq ▸ h)
  have hzC : z ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hzS g (hFA hg).1
  have hFbad : BadSub z F := by
    by_cases hβ1 : β = 1
    · refine not_mem_zStarOf_of_layerAut_trivial hF2 hFY hzC hzY hz2 hz1 hQb.center ?_
      intro g hg y
      obtain ⟨e, rfl, he⟩ := hFprop g hg
      have h1 : lam e = 1 := by
        rcases he with h | h
        · exact h
        · rw [h, hβ1]
      have := congrArg (fun φ => φ y) h1
      simpa [hlam, CX.layerHom_apply] using this
    · obtain ⟨e₁, he₁⟩ := hβr.resolve_left hβ1
      have hne1 : actOf hyp hb2 ⟨e₁, hEb e₁.2⟩ ≠ 1 := by
        rw [← hlamact, he₁]
        exact hβ1
      have hneζ : actOf hyp hb2 ⟨e₁, hEb e₁.2⟩ ≠ MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
          ↥(TwinDisc.coreLayer Ω b) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b)) := by
        rw [← hlamact, he₁, ← hlamz]
        exact hβζ
      obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hQb.refl e₁ (hEA e₁.2) (hEb e₁.2) hne1 hneζ
      refine not_mem_zStarOf_of_fix_of_normalizes hF2 hFY hzY hz2 (x := xb) ?_ hxbz hxbc
      intro g hg
      obtain ⟨e, rfl, he⟩ := hFprop g hg
      have hxe₁ : lam e₁ xb = xb := by
        rw [hlamact]
        exact hxbfix
      rcases he with h | h
      · have := congrArg (fun φ => φ xb) h
        simpa [hlam, CX.layerHom_apply] using this
      · have := congrArg (fun φ => φ xb) h
        simp only [hlam, CX.layerHom_apply] at this
        rw [this, ← he₁]
        exact hxe₁
  exact absurd (hmax F hFA (hD₀D.trans hDF) hFbad) (not_le.mpr hDltF)

theorem exists_bad_complement (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp)
    {D₀ : Subgroup G} (hD₀A : D₀ ≤ cA S R R') (hD₀bad : BadSub z D₀) (hD₀1 : D₀ ≠ ⊥)
    (hsmall : Nat.card D₀ < 4 → ∃ x ∈ cA S R R', x ∉ D₀ ∧ x * z ∉ D₀ ∧
      (∀ d ∈ D₀, x * d = d * x) ∧ (x * x ∈ D₀ ∨ x * x * z ∈ D₀)) :
    ∃ D : Subgroup G, D ≤ cA S R R' ∧ D₀ ≤ D ∧ BadSub z D ∧
      ∀ g ∈ cA S R R', g ∈ D ∨ g * z ∈ D :=
  CFSG.ClassicalInvolution.Asc77.CX6Eng.exists_bad_complement_gen hyp.std.setting.hz.sq hyp.hzS
    (z_facts hyp).1 (fun {_ _} hDA hD₀D hbad hmax {_ _} hxA hxD hxzD hbD hb1 hb2 hbx hbc =>
      false_of_growth hyp hQ hDA hD₀D hbad hmax hxA hxD hxzD hbD hb1 hb2 hbx hbc)
    CX.exists_mem_normalizer_sq_mem CX.exists_central_involution CX.inf_conjSub_ne_bot
    CX.exists_sup_central hD₀A hD₀bad hD₀1 hsmall

end Core

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
