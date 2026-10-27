module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial (pointRadical)
open CFSG.LargeExtraspecial.S2 (perp mem_perp omegaFix)
open CFSG.LargeExtraspecial.OrthoF2 (zmod2_eq_zero_or_eq_one zmod2_add_self)
open CFSG.ClassicalGroups.Orthogonal (eichler)

namespace Sec3SHatSq

section Form

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

noncomputable def projPerp (q : QuadraticForm (ZMod 2) V) (a a₁ : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id - ((polarBilin q).flip a₁).smulRight a - ((polarBilin q).flip a).smulRight a₁

theorem projPerp_apply (a a₁ x : V) :
    projPerp q a a₁ x = x - polar q x a₁ • a - polar q x a • a₁ := by
  simp [projPerp, polarBilin_apply_apply]

variable {a a₁ : V}

theorem inf_perp_eq_bot (haa₁ : polar q a a₁ = 1) :
    Submodule.span (ZMod 2) {a, a₁} ⊓ perp q (Submodule.span (ZMod 2) {a, a₁}) = ⊥ := by
  have h := CFSG.LargeExtraspecial.S2.sup_span_pair_inf_perp_eq_bot (q := q) (F := ⊥)
    (by simp) (p := a) (p₁ := a₁) (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial)
    (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial) haa₁
  rwa [bot_sup_eq] at h

theorem projPerp_mem (haa₁ : polar q a a₁ = 1) (x : V) :
    projPerp q a a₁ x ∈ perp q (Submodule.span (ZMod 2) {a, a₁}) := by
  have h := CFSG.LargeExtraspecial.S2.sub_mem_perp_sup_span_pair (q := q) (F := ⊥)
    (p := a) (p₁ := a₁) (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial)
    (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial) haa₁
    (x := x) (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial)
  rw [bot_sup_eq] at h
  rw [projPerp_apply]
  exact h

theorem projPerp_eq_self {x : V} (hx : x ∈ perp q (Submodule.span (ZMod 2) {a, a₁})) :
    projPerp q a a₁ x = x := by
  have h1 : polar q a x = 0 := mem_perp.mp hx a (Submodule.subset_span (by simp))
  have h2 : polar q a₁ x = 0 := mem_perp.mp hx a₁ (Submodule.subset_span (by simp))
  rw [projPerp_apply, polar_comm, h2, polar_comm, h1, zero_smul, zero_smul, sub_zero, sub_zero]

theorem projPerp_eq_zero (ha : q a = 0) (ha₁ : q a₁ = 0) (haa₁ : polar q a a₁ = 1) {x : V}
    (hx : x ∈ Submodule.span (ZMod 2) {a, a₁}) : projPerp q a a₁ x = 0 := by
  have haa : polar q a a = 0 := by rw [QuadraticMap.polar_self, ha, smul_zero]
  have ha₁a₁ : polar q a₁ a₁ = 0 := by rw [QuadraticMap.polar_self, ha₁, smul_zero]
  have ha₁a : polar q a₁ a = 1 := by rw [polar_comm, haa₁]
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add, map_smul, map_smul, projPerp_apply, projPerp_apply, haa₁, haa, ha₁a, ha₁a₁]
  simp

theorem projPerp_apply_of_mem {g : V ≃ₗ[ZMod 2] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hga : g a = a) (hga₁ : g a₁ = a₁)
    (x : V) : projPerp q a a₁ (g x) = g (projPerp q a a₁ x) := by
  rw [projPerp_apply, projPerp_apply, map_sub, map_sub, map_smul, map_smul, hga, hga₁]
  conv_lhs => rw [← hga, ← hga₁]
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO, hga, hga₁]

variable [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)

theorem eq_of_invariant (ha : q a = 0) (ha₁ : q a₁ = 0) (haa₁ : polar q a a₁ = 1)
    (h6 : 6 ≤ finrank (ZMod 2) (perp q (Submodule.span (ZMod 2) {a, a₁})))
    {Q' : V → ZMod 2} {β : V → V → ZMod 2}
    (hβ : ∀ x ∈ perp q (Submodule.span (ZMod 2) {a, a₁}),
      ∀ x' ∈ perp q (Submodule.span (ZMod 2) {a, a₁}),
      ∀ y ∈ perp q (Submodule.span (ZMod 2) {a, a₁}), β (x + x') y = β x y + β x' y)
    (hQ : ∀ x ∈ perp q (Submodule.span (ZMod 2) {a, a₁}),
      ∀ y ∈ perp q (Submodule.span (ZMod 2) {a, a₁}), Q' (x + y) = Q' x + Q' y + β x y)
    (hβg : ∀ g ∈ omegaFix q hq (Submodule.span (ZMod 2) {a, a₁}),
      ∀ x ∈ perp q (Submodule.span (ZMod 2) {a, a₁}),
      ∀ y ∈ perp q (Submodule.span (ZMod 2) {a, a₁}), β (g x) (g y) = β x y)
    (hQg : ∀ g ∈ omegaFix q hq (Submodule.span (ZMod 2) {a, a₁}),
      ∀ x ∈ perp q (Submodule.span (ZMod 2) {a, a₁}), Q' (g x) = Q' x)
    {x₁ x₂ : V} (hx₁ : x₁ ∈ perp q (Submodule.span (ZMod 2) {a, a₁}))
    (hx₂ : x₂ ∈ perp q (Submodule.span (ZMod 2) {a, a₁})) (h12 : β x₁ x₂ = 1) :
    ∀ x ∈ perp q (Submodule.span (ZMod 2) {a, a₁}), Q' x = q x := by
  set W₀ := Submodule.span (ZMod 2) {a, a₁} with hW₀
  set W := perp q W₀ with hW
  set π := projPerp q a a₁ with hπ
  have hF : W₀ ⊓ W = ⊥ := inf_perp_eq_bot haa₁
  have hπW : ∀ v, π v ∈ W := fun v => projPerp_mem haa₁ v
  have hsymm : ∀ x ∈ W, ∀ y ∈ W, β x y = β y x := by
    intro x hx y hy
    have h1 := hQ x hx y hy
    have h2 := hQ y hy x hx
    rw [add_comm y x, h1] at h2
    linear_combination h2
  have hβ0 : ∀ y ∈ W, β 0 y = 0 := by
    intro y hy
    have h := hβ 0 W.zero_mem 0 W.zero_mem y hy
    rw [add_zero] at h
    linear_combination -h
  have hβ0' : ∀ x ∈ W, β x 0 = 0 := fun x hx => by
    rw [hsymm x hx 0 W.zero_mem]
    exact hβ0 x hx
  have hβr : ∀ x ∈ W, ∀ y ∈ W, ∀ y' ∈ W, β x (y + y') = β x y + β x y' := by
    intro x hx y hy y' hy'
    rw [hsymm x hx _ (W.add_mem hy hy'), hβ y hy y' hy' x hx, hsymm y hy x hx,
      hsymm y' hy' x hx]
  let B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 := LinearMap.mk₂ (ZMod 2)
    (fun u v => β (π u) (π v))
    (fun u u' v => by rw [map_add]; exact hβ _ (hπW u) _ (hπW u') _ (hπW v))
    (fun c u v => by
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, map_zero, hβ0 _ (hπW v), zero_smul]
      · rw [one_smul, one_smul])
    (fun u v v' => by rw [map_add]; exact hβr _ (hπW u) _ (hπW v) _ (hπW v'))
    (fun c u v => by
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, map_zero, hβ0' _ (hπW u), zero_smul]
      · rw [one_smul, one_smul])
  let φ : V →ₗ[ZMod 2] V :=
    (LinearMap.BilinForm.toDual (polarBilin q) hq).symm.toLinearMap ∘ₗ B
  have hφ : ∀ u v, polar q (φ u) v = β (π u) (π v) := fun u v => by
    have h := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hq) (B u) v
    rw [polarBilin_apply_apply] at h
    exact h
  have hφW : ∀ u ∈ W, φ u ∈ W := by
    intro u hu
    refine mem_perp.mpr fun y hy => ?_
    rw [polar_comm, hφ, projPerp_eq_zero ha ha₁ haa₁ hy, hβ0' _ (hπW u)]
  have hcomm : ∀ g ∈ omegaFix q hq W₀, ∀ u ∈ W, φ (g u) = g (φ u) := by
    intro g hg u hu
    have hgO := CFSG.LargeExtraspecial.S2.mem_orthogonalGroup_of_mem_omegaFix hg
    have hfix := CFSG.LargeExtraspecial.S2.mem_fixGroup.mp hg.2
    have hga : g a = a := hfix a (Submodule.subset_span (by simp))
    have hga₁ : g a₁ = a₁ := hfix a₁ (Submodule.subset_span (by simp))
    have hgi : g⁻¹ ∈ omegaFix q hq W₀ := inv_mem hg
    have hgiO := CFSG.LargeExtraspecial.S2.mem_orthogonalGroup_of_mem_omegaFix hgi
    have hgia : g⁻¹ a = a := by
      conv_lhs => rw [← hga]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' g a
    have hgia₁ : g⁻¹ a₁ = a₁ := by
      conv_lhs => rw [← hga₁]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' g a₁
    have hgu : g u ∈ W := CFSG.LargeExtraspecial.S2.apply_mem_perp hgO hg.2 hu
    refine sub_eq_zero.mp (hq.1 _ fun v => ?_)
    have hv : g⁻¹ (π v) ∈ W := CFSG.LargeExtraspecial.S2.apply_mem_perp hgiO hgi.2 (hπW v)
    have hgg : g (g⁻¹ (π v)) = π v :=
      CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply' g (π v)
    have h1 : polar q (g (φ u)) v = β (g u) (π v) := by
      calc polar q (g (φ u)) v = polar q (g (φ u)) (g (g⁻¹ v)) := by
            rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply']
        _ = polar q (φ u) (g⁻¹ v) :=
            TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO _ _
        _ = β (π u) (π (g⁻¹ v)) := hφ u _
        _ = β u (g⁻¹ (π v)) := by
            rw [projPerp_eq_self hu, projPerp_apply_of_mem hgiO hgia hgia₁]
        _ = β (g u) (π v) := by rw [← hβg g hg u hu _ hv, hgg]
    rw [polarBilin_apply_apply, polar_sub_left, hφ, h1, projPerp_eq_self hgu, sub_self]
  obtain ⟨c, hc⟩ := CFSG.LargeExtraspecial.S2.timmesfeld_2_4_omega hq hF
    (h6.trans' (by norm_num)) hφW hcomm
  have hβc : ∀ u ∈ W, ∀ v ∈ W, β u v = c * polar q u v := by
    intro u hu v hv
    have h := hφ u v
    rw [projPerp_eq_self hu, projPerp_eq_self hv, hc u hu, polar_smul_left, smul_eq_mul] at h
    exact h.symm
  have hc1 : c = 1 := by
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [hβc x₁ hx₁ x₂ hx₂, zero_mul] at h12
      exact absurd h12 (by decide)
    · rfl
  have hβq : ∀ u ∈ W, ∀ v ∈ W, β u v = polar q u v := fun u hu v hv => by
    rw [hβc u hu v hv, hc1, one_mul]
  have hQ0 : Q' 0 = 0 := by
    have h := hQ 0 W.zero_mem 0 W.zero_mem
    rw [add_zero, hβ0 _ W.zero_mem, add_zero] at h
    linear_combination -h
  let K : Submodule (ZMod 2) V :=
    { carrier := {u | u ∈ W ∧ Q' u = q u}
      add_mem' := by
        rintro u v ⟨hu, hQu⟩ ⟨hv, hQv⟩
        refine ⟨W.add_mem hu hv, ?_⟩
        rw [hQ u hu v hv, hQu, hQv, hβq u hu v hv, QuadraticMap.map_add q u v]
      zero_mem' := ⟨W.zero_mem, by rw [hQ0, QuadraticMap.map_zero]⟩
      smul_mem' := by
        rintro c u ⟨hu, hQu⟩
        rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
        · rw [zero_smul]
          exact ⟨W.zero_mem, by rw [hQ0, QuadraticMap.map_zero]⟩
        · rw [one_smul]
          exact ⟨hu, hQu⟩ }
  have hK : K = W := by
    refine CFSG.ComponentClassification.AS81.PointIrr.eq_perp_of_invariant hq hF h6
      (fun u hu => hu.1) ?_ ?_
    · have hne : ∀ a b : ZMod 2, a ≠ b → a = b + 1 := by decide
      have hx₁0 : x₁ ≠ 0 := by
        rintro rfl
        rw [hβ0 _ hx₂] at h12
        exact absurd h12 (by decide)
      have hx₂0 : x₂ ≠ 0 := by
        rintro rfl
        rw [hβ0' _ hx₁] at h12
        exact absurd h12 (by decide)
      have hx₁₂ : x₁ + x₂ ≠ 0 := by
        intro h
        have h' : x₂ = x₁ := by
          rw [eq_neg_of_add_eq_zero_right h, ZModModule.neg_eq_self]
        rw [h', hβq x₁ hx₁ x₁ hx₁, QuadraticMap.polar_self, two_smul, zmod2_add_self] at h12
        exact absurd h12 (by decide)
      intro hbot
      have hmem : ∀ u ∈ K, u = 0 := fun u hu => by
        rw [hbot] at hu
        exact (Submodule.mem_bot _).mp hu
      by_cases h₁ : Q' x₁ = q x₁
      · exact hx₁0 (hmem x₁ ⟨hx₁, h₁⟩)
      by_cases h₂ : Q' x₂ = q x₂
      · exact hx₂0 (hmem x₂ ⟨hx₂, h₂⟩)
      refine hx₁₂ (hmem _ ⟨W.add_mem hx₁ hx₂, ?_⟩)
      rw [hQ x₁ hx₁ x₂ hx₂, hne _ _ h₁, hne _ _ h₂, hβq x₁ hx₁ x₂ hx₂, QuadraticMap.map_add q x₁ x₂]
      linear_combination zmod2_add_self 1
    · rintro g hg u ⟨hu, hQu⟩
      have hgO := CFSG.LargeExtraspecial.S2.mem_orthogonalGroup_of_mem_omegaFix hg
      exact ⟨CFSG.LargeExtraspecial.S2.apply_mem_perp hgO hg.2 hu, by
        rw [hQg g hg u hu, hQu, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO]⟩
  intro x hx
  rw [← hK] at hx
  exact hx.2

end Form

section Group

variable {G : Type*} [Group G]

open Classical in
noncomputable def indic (K : Subgroup G) (c : G) : ZMod 2 := if c ∈ K then 0 else 1

theorem indic_eq_zero_iff {K : Subgroup G} {c : G} : indic K c = 0 ↔ c ∈ K := by
  classical
  by_cases h : c ∈ K <;> simp [indic, h]

theorem indic_mul {K X : Subgroup G} (hK : ∀ c ∈ X, ∀ d ∈ X, c ∉ K → d ∉ K → c * d ∈ K)
    {c d : G} (hc : c ∈ X) (hd : d ∈ X) : indic K (c * d) = indic K c + indic K d := by
  classical
  by_cases hcK : c ∈ K <;> by_cases hdK : d ∈ K
  · simp [indic, hcK, hdK, mul_mem hcK hdK]
  · have h : c * d ∉ K := fun h => hdK (by simpa using mul_mem (inv_mem hcK) h)
    simp [indic, hcK, hdK, h]
  · have h : c * d ∉ K := fun h => hcK (by simpa using mul_mem h (inv_mem hdK))
    simp [indic, hcK, hdK, h]
  · simp only [indic, hcK, hdK, hK c hc d hd hcK hdK, ite_true, ite_false]
    decide

theorem mul_mul_self {s t : G} (h : Commute s (t * s * t⁻¹ * s⁻¹)) :
    s * t * (s * t) = t * s * t⁻¹ * s⁻¹ * (s * s) * (t * t) := by
  calc s * t * (s * t) = s * (t * s * t⁻¹ * s⁻¹) * s * t * t := by group
    _ = t * s * t⁻¹ * s⁻¹ * s * s * t * t := by rw [h.eq]
    _ = _ := by group

theorem comm_mul_left {s t r : G} (h : Commute s (t * r * t⁻¹ * r⁻¹)) :
    s * t * r * (s * t)⁻¹ * r⁻¹ = t * r * t⁻¹ * r⁻¹ * (s * r * s⁻¹ * r⁻¹) := by
  calc s * t * r * (s * t)⁻¹ * r⁻¹ = s * (t * r * t⁻¹ * r⁻¹) * r * s⁻¹ * r⁻¹ := by group
    _ = t * r * t⁻¹ * r⁻¹ * s * r * s⁻¹ * r⁻¹ := by rw [h.eq]
    _ = _ := by group

theorem comm_mul_right {r u v : G} (h : Commute u (r * v * r⁻¹ * v⁻¹)) :
    r * (u * v) * r⁻¹ * (u * v)⁻¹ = r * u * r⁻¹ * u⁻¹ * (r * v * r⁻¹ * v⁻¹) := by
  calc r * (u * v) * r⁻¹ * (u * v)⁻¹ = r * u * r⁻¹ * (r * v * r⁻¹ * v⁻¹) * u⁻¹ := by group
    _ = r * u * r⁻¹ * ((r * v * r⁻¹ * v⁻¹) * u⁻¹) := by group
    _ = r * u * r⁻¹ * (u⁻¹ * (r * v * r⁻¹ * v⁻¹)) := by rw [(h.inv_left).eq]
    _ = _ := by group

theorem comm_mul_central_left {s c r : G} (h : Commute c r) :
    s * c * r * (s * c)⁻¹ * r⁻¹ = s * r * s⁻¹ * r⁻¹ := by
  calc s * c * r * (s * c)⁻¹ * r⁻¹ = s * (c * r) * c⁻¹ * s⁻¹ * r⁻¹ := by group
    _ = s * (r * c) * c⁻¹ * s⁻¹ * r⁻¹ := by rw [h.eq]
    _ = _ := by group

theorem comm_mul_central_right {r s c : G} (h : Commute c r) :
    r * (s * c) * r⁻¹ * (s * c)⁻¹ = r * s * r⁻¹ * s⁻¹ := by
  calc r * (s * c) * r⁻¹ * (s * c)⁻¹ = r * s * (c * r⁻¹) * c⁻¹ * s⁻¹ := by group
    _ = r * s * (r⁻¹ * c) * c⁻¹ * s⁻¹ := by rw [(h.inv_right).eq]
    _ = _ := by group

theorem mul_mul_self_central {s c : G} (h : Commute s c) (hc : c * c = 1) :
    s * c * (s * c) = s * s := by
  calc s * c * (s * c) = s * (c * s) * c := by group
    _ = s * (s * c) * c := by rw [← h.eq]
    _ = s * s * (c * c) := by group
    _ = s * s := by rw [hc, mul_one]

end Group

section SHatE

variable {G : Type} [Group G]

@[expose] def shatE (Q₀ Q Zs : Subgroup G) (e : G) : Subgroup G where
  carrier := {s | s ∈ sec3SHat (Q₀ ⊔ Q) Zs ∧ s * e = e * s ∧
    ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e}
  mul_mem' := by
    rintro s t ⟨hs, hse, hsU⟩ ⟨ht, hte, htU⟩
    refine ⟨mul_mem hs ht, ?_, fun u hu => ?_⟩
    · calc s * t * e = s * (t * e) := mul_assoc _ _ _
        _ = s * (e * t) := by rw [hte]
        _ = s * e * t := (mul_assoc _ _ _).symm
        _ = e * s * t := by rw [hse]
        _ = e * (s * t) := mul_assoc _ _ _
    · have hc : Commute s (t * u * t⁻¹ * u⁻¹) := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (htU u hu)
        rw [← hk]
        exact Commute.zpow_right hse k
      rw [comm_mul_left hc]
      exact mul_mem (htU u hu) (hsU u hu)
  one_mem' := ⟨one_mem _, by rw [one_mul, mul_one], fun u _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro s ⟨hs, hse, hsU⟩
    have hse' : Commute s⁻¹ e := (show Commute s e from hse).inv_left
    refine ⟨inv_mem hs, hse'.eq, fun u hu => ?_⟩
    have h1 := inv_mem (hsU u hu)
    have hc : Commute s⁻¹ (s * u * s⁻¹ * u⁻¹)⁻¹ := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      rw [← hk]
      exact Commute.zpow_right hse' k
    have e1 : s⁻¹ * u * s⁻¹⁻¹ * u⁻¹ = s⁻¹ * (s * u * s⁻¹ * u⁻¹)⁻¹ * s⁻¹⁻¹ := by group
    rw [e1, hc.eq, mul_inv_cancel_right]
    exact h1

theorem SHat_le_F (Q₀ Q Zs : Subgroup G) : sec3SHat (Q₀ ⊔ Q) Zs ≤ sec3F (Q₀ ⊔ Q) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left

theorem SHat_le_centralizer (Q₀ Q Zs : Subgroup G) :
    sec3SHat (Q₀ ⊔ Q) Zs ≤ centralizer (Zs : Set G) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right

end SHatE

end Sec3SHatSq

open Sec3SHatSq

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem sq_mul_self_of_mem_Zs {c : G} (hc : c ∈ Zs) : c * c = 1 := by
  rw [← pow_two]
  exact H.sq_eq_one_of_mem_Zs hc

theorem sq_mul_mem_zpowers_e (hZQ : Zs ≤ Q) {e : G} (he : e ∈ Zs) (hez : e ∉ zpowers z) :
    ∀ c ∈ Zs, ∀ d ∈ Zs, c ∉ zpowers e → d ∉ zpowers e → c * d ∈ zpowers e := by
  have hzz : z * z = 1 := H.xsub.z_mul_z
  have hze : z * e = e * z := H.comm_of_mem_Zs H.z_mem_Zs he
  have hcases : ∀ c ∈ Zs, c ∉ zpowers e → c = z ∨ c = e * z := by
    intro c hc hce
    rcases H.mem_Zs_cases hZQ he hez hc with rfl | rfl | rfl | rfl
    · exact absurd (one_mem _) hce
    · exact Or.inl rfl
    · exact absurd (mem_zpowers _) hce
    · exact Or.inr rfl
  intro c hc d hd hce hde
  rcases hcases c hc hce with rfl | rfl <;> rcases hcases d hd hde with rfl | rfl
  · rw [hzz]
    exact one_mem _
  · rw [← mul_assoc, hze, mul_assoc, hzz, mul_one]
    exact mem_zpowers _
  · rw [mul_assoc, hzz, mul_one]
    exact mem_zpowers _
  · rw [show e * z * (e * z) = e * (z * e) * z by group, hze,
      show e * (e * z) * z = (e * e) * (z * z) by group, hzz, mul_one,
      ← pow_two, H.sq_eq_one_of_mem_Zs he]
    exact one_mem _

theorem sq_mul_mem_zpowers_z (hZQ : Zs ≤ Q) {e : G} (he : e ∈ Zs) (hez : e ∉ zpowers z) :
    ∀ c ∈ Zs, ∀ d ∈ Zs, c ∉ zpowers z → d ∉ zpowers z → c * d ∈ zpowers z := by
  have hzz : z * z = 1 := H.xsub.z_mul_z
  have hee : e * e = 1 := H.sq_mul_self_of_mem_Zs he
  have hze : z * e = e * z := H.comm_of_mem_Zs H.z_mem_Zs he
  have hcases : ∀ c ∈ Zs, c ∉ zpowers z → c = e ∨ c = e * z := by
    intro c hc hcz
    rcases H.mem_Zs_cases hZQ he hez hc with rfl | rfl | rfl | rfl
    · exact absurd (one_mem _) hcz
    · exact absurd (mem_zpowers _) hcz
    · exact Or.inl rfl
    · exact Or.inr rfl
  intro c hc d hd hcz hdz
  rcases hcases c hc hcz with rfl | rfl <;> rcases hcases d hd hdz with rfl | rfl
  · rw [hee]
    exact one_mem _
  · rw [← mul_assoc, hee, one_mul]
    exact mem_zpowers _
  · rw [mul_assoc, hze, ← mul_assoc, hee, one_mul]
    exact mem_zpowers _
  · rw [show e * z * (e * z) = e * (z * e) * z by group, hze,
      show e * (e * z) * z = (e * e) * (z * z) by group, hzz, hee, mul_one]
    exact one_mem _

theorem sq_z_not_mem_zpowers {e : G} (he : e ∈ Zs) (hez : e ∉ zpowers z) : z ∉ zpowers e := by
  intro h
  rcases Sec3SHat.eq_one_or_eq_of_mem_zpowers (H.sq_mul_self_of_mem_Zs he) h with h1 | h1
  · exact H.z_ne_one h1
  · exact hez (h1 ▸ mem_zpowers z)

theorem sq_Zs_le_shatE (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {e : G} (he : e ∈ Zs) :
    Zs ≤ shatE Q₀ Q Zs e := by
  intro c hc
  have hcC : c ∈ centralizer (Zs : Set G) :=
    mem_centralizer_iff.mpr fun d hd => H.comm_of_mem_Zs hd hc
  refine ⟨H.U_le_SHat hQF ⟨H.Q_le (hZQ hc), hcC⟩, H.comm_of_mem_Zs hc he, fun u hu => ?_⟩
  rw [mem_centralizer_iff.mp hu.2 c hc, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem sq_mem_Zs_of_ρF_eq_one (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {e : G}
    (he : e ∈ Zs) (hez : e ∉ zpowers z) {s : ↥(sec3F (Q₀ ⊔ Q))}
    (hs : (s : G) ∈ shatE Q₀ Q Zs e) (h1 : H.ρF s = 1) : (s : G) ∈ Zs := by
  have hsU := H.mem_U_of_mem_SHat hQF hZQ hs.1 h1
  rw [← H.centerIn_U hZQ he hez]
  refine ⟨hsU, mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hz := commutator_mem_of_extraspecial H.ext H.center_sup hsU.1 hu.1
  have he' := hs.2.2 u hu
  have hc1 : (s : G) * u * (s : G)⁻¹ * u⁻¹ = 1 := by
    rcases H.xsub.mem_zpowers_z_iff.mp hz with h | h
    · exact h
    · rcases Sec3SHat.eq_one_or_eq_of_mem_zpowers (H.sq_mul_self_of_mem_Zs he) he' with h' | h'
      · exact h'
      · exact absurd (by rw [show e = z from h'.symm.trans h]; exact mem_zpowers z) hez
  have h2 : (s : G) * u * (s : G)⁻¹ = u := by
    calc (s : G) * u * (s : G)⁻¹ = (s : G) * u * (s : G)⁻¹ * u⁻¹ * u := by group
      _ = u := by rw [hc1, one_mul]
  calc u * s = (s : G) * u * (s : G)⁻¹ * s := by rw [h2]
    _ = s * u := by group

theorem sq_exists_mul_of_ρF_eq (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {e : G}
    (he : e ∈ Zs) (hez : e ∉ zpowers z) {s t : ↥(sec3F (Q₀ ⊔ Q))}
    (hs : (s : G) ∈ shatE Q₀ Q Zs e) (ht : (t : G) ∈ shatE Q₀ Q Zs e) (h : H.ρF s = H.ρF t) :
    ∃ c ∈ Zs, (s : G) = t * c := by
  have hm : ((t⁻¹ * s : ↥(sec3F (Q₀ ⊔ Q))) : G) ∈ shatE Q₀ Q Zs e := mul_mem (inv_mem ht) hs
  have h1 : H.ρF (t⁻¹ * s) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  refine ⟨_, H.sq_mem_Zs_of_ρF_eq_one hQF hZQ he hez hm h1, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

theorem sq_conj_mem_shatE {e : G} (he : e ∈ Zs) {f : G} (hfF : f ∈ sec3F (Q₀ ⊔ Q))
    (hfZ : f ∈ centralizer (Zs : Set G)) {s : G} (hs : s ∈ shatE Q₀ Q Zs e) :
    f * s * f⁻¹ ∈ shatE Q₀ Q Zs e := by
  obtain ⟨hsS, hse, hsU⟩ := hs
  have hfe : f * e = e * f := (mem_centralizer_iff.mp hfZ e he).symm
  have hfN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
    (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) (mem_inf.mpr ⟨hfF, hfZ⟩)
  refine ⟨(mem_normalizer_iff.mp hfN s).mp hsS, ?_, fun u hu => ?_⟩
  · have hfe' : f⁻¹ * e = e * f⁻¹ := ((show Commute f e from hfe).inv_left).eq
    calc f * s * f⁻¹ * e = f * s * (f⁻¹ * e) := by group
      _ = f * (s * e) * f⁻¹ := by rw [hfe']; group
      _ = f * (e * s) * f⁻¹ := by rw [hse]
      _ = (f * e) * s * f⁻¹ := by group
      _ = e * (f * s * f⁻¹) := by rw [hfe]; group
  · have hfQ : f⁻¹ ∈ H.xsub.N := inv_mem (H.F_le_N hfF)
    have hu' : f⁻¹ * u * f⁻¹⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
      mem_inf.mpr ⟨H.xsub.conj_mem hfQ hu.1,
        mul_mem (mul_mem (inv_mem hfZ) hu.2) (inv_mem (inv_mem hfZ))⟩
    have h1 := hsU _ hu'
    have hc : Commute f (s * (f⁻¹ * u * f⁻¹⁻¹) * s⁻¹ * (f⁻¹ * u * f⁻¹⁻¹)⁻¹) := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      rw [← hk]
      exact Commute.zpow_right hfe k
    have e1 : f * s * f⁻¹ * u * (f * s * f⁻¹)⁻¹ * u⁻¹ =
        f * (s * (f⁻¹ * u * f⁻¹⁻¹) * s⁻¹ * (f⁻¹ * u * f⁻¹⁻¹)⁻¹) * f⁻¹ := by group
    rw [e1, hc.eq, mul_inv_cancel_right]
    exact h1

theorem exists_mem_SHatE (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {e : G} (he : e ∈ Zs) (hez : e ∉ zpowers z)
    {t : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt} (ht : t ∈ pointRadical H.xsub.q (H.xsub.cl e)) :
    ∃ s : ↥(sec3F (Q₀ ⊔ Q)), (s : G) ∈ sec3SHat (Q₀ ⊔ Q) Zs ∧ H.ρF s = t ∧
      ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), (s : G) * u * (s : G)⁻¹ * u⁻¹ ∈ zpowers e := by
  classical
  obtain ⟨s₀, hs₀, hρ₀⟩ := H.exists_mem_SHat_of_mem_pointRadical hΩ hQF hRc hZQ he hez ht
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  set A' := perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl e) with hA'
  have hUeq : U' = H.xsub.clPre A' := H.centralizer_Zs_eq_clPre hZQ he hez
  have hs₀Z : (s₀ : G) ∈ centralizer (Zs : Set G) := SHat_le_centralizer Q₀ Q Zs hs₀
  have hK := H.sq_mul_mem_zpowers_e hZQ he hez
  have hcZ : ∀ u ∈ U', (s₀ : G) * u * (s₀ : G)⁻¹ * u⁻¹ ∈ Zs := fun u hu =>
    H.commutator_mem_Zs_of_mem_U hΩ hQF hZQ he hez hs₀ hu
  have hclU : ∀ u ∈ U', H.xsub.cl u ∈ A' := fun u hu => by
    have hu' := hu
    rw [hUeq] at hu'
    exact hu'.2
  let r : H.xsub.Qt → G := fun v => Classical.choose (H.xsub.exists_cl v)
  have hr : ∀ v, r v ∈ H.xsub.Q₁ ∧ H.xsub.cl (r v) = v := fun v =>
    Classical.choose_spec (H.xsub.exists_cl v)
  have hrU : ∀ v ∈ A', r v ∈ U' := fun v hv => by
    rw [hUeq]
    exact ⟨(hr v).1, (hr v).2.symm ▸ hv⟩
  have hcl : ∀ u ∈ U', ∀ u' ∈ U', H.xsub.cl u = H.xsub.cl u' →
      (s₀ : G) * u * (s₀ : G)⁻¹ * u⁻¹ = (s₀ : G) * u' * (s₀ : G)⁻¹ * u'⁻¹ := by
    intro u hu u' hu' huu'
    have h1 := (H.xsub.cl_eq_cl_iff hu.1 hu'.1).mp huu'
    have hm : u' = u * (u⁻¹ * u') := by group
    have hmc : Commute (u⁻¹ * u') (s₀ : G) := by
      rcases H.xsub.mem_zpowers_z_iff.mp h1 with h | h
      · rw [h]
        exact Commute.one_left _
      · rw [h]
        exact (mem_centralizer_iff.mp hs₀Z z H.z_mem_Zs)
    rw [hm, comm_mul_central_right hmc]
  let c : H.xsub.Qt → G := fun v => (s₀ : G) * r v * (s₀ : G)⁻¹ * (r v)⁻¹
  have hcu : ∀ u ∈ U', c (H.xsub.cl u) = (s₀ : G) * u * (s₀ : G)⁻¹ * u⁻¹ := fun u hu =>
    hcl _ (hrU _ (hclU u hu)) u hu (hr _).2
  let δ : H.xsub.Qt → ZMod 2 := fun v => indic (zpowers e) (c v)
  have hadd : ∀ v ∈ A', ∀ w ∈ A', δ (v + w) = δ v + δ w := by
    intro v hv w hw
    have hmulU : r v * r w ∈ U' := mul_mem (hrU v hv) (hrU w hw)
    have hclvw : H.xsub.cl (r v * r w) = v + w := by
      rw [H.xsub.cl_mul (hr v).1 (hr w).1, (hr v).2, (hr w).2]
    have hcomm : Commute (r v) ((s₀ : G) * r w * (s₀ : G)⁻¹ * (r w)⁻¹) :=
      ((mem_centralizer_iff.mp (hrU v hv).2 _ (hcZ _ (hrU w hw)))).symm
    have e1 : c (v + w) = c v * c w := by
      rw [← hclvw, hcu _ hmulU]
      exact comm_mul_right hcomm
    show indic (zpowers e) (c (v + w)) = indic (zpowers e) (c v) + indic (zpowers e) (c w)
    rw [e1]
    exact indic_mul hK (hcZ _ (hrU v hv)) (hcZ _ (hrU w hw))
  let lam₀ : ↥A' →+ ZMod 2 := AddMonoidHom.mk' (fun v => δ v) fun v w => hadd v v.2 w w.2
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (lam₀.toZModLinearMap 2)
  have : Module.Finite (ZMod 2) H.xsub.Qt := Module.Finite.of_finite
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual (polarBilin H.xsub.q)
    H.xsub.q_nondegenerate).surjective Λ
  have hpol : ∀ v ∈ A', polar H.xsub.q w v = δ v := by
    intro v hv
    have h1 := LinearMap.congr_fun hw v
    rw [LinearMap.BilinForm.toDual_def, polarBilin_apply_apply] at h1
    rw [h1]
    exact LinearMap.congr_fun hΛ ⟨v, hv⟩
  have heU : e ∈ U' := mem_inf.mpr ⟨H.Q_le (hZQ he),
    mem_centralizer_iff.mpr fun d hd => H.comm_of_mem_Zs hd he⟩
  have hwA : w ∈ A' := by
    have h1 := hpol _ (hclU e heU)
    have h2 : δ (H.xsub.cl e) = 0 := by
      show indic (zpowers e) (c (H.xsub.cl e)) = 0
      rw [hcu e heU, ← mem_centralizer_iff.mp hs₀Z e he, mul_inv_cancel_right, mul_inv_cancel,
        indic_eq_zero_iff]
      exact one_mem _
    refine mem_perp.mpr fun y hy => ?_
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [polar_smul_left, polar_comm, h1, h2, smul_zero]
  set w₀ := r w with hw₀
  have hw₀U : w₀ ∈ U' := hrU w hwA
  have hw₀F : w₀ ∈ sec3F (Q₀ ⊔ Q) := hQF hw₀U.1
  refine ⟨⟨w₀, hw₀F⟩ * s₀, mul_mem (H.U_le_SHat hQF hw₀U) hs₀, ?_, fun u hu => ?_⟩
  · have hj1 : H.ρF ⟨w₀, hw₀F⟩ = 1 :=
      (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (g := ⟨w₀, H.xsub.le_N hw₀U.1⟩) hw₀U.1)
    rw [map_mul, hj1, one_mul, hρ₀]
  ·
    have hcomm : Commute w₀ ((s₀ : G) * u * (s₀ : G)⁻¹ * u⁻¹) :=
      ((mem_centralizer_iff.mp hw₀U.2 _ (hcZ u hu))).symm
    rw [Subgroup.coe_mul, comm_mul_left hcomm, ← indic_eq_zero_iff]
    have hwz := commutator_mem_of_extraspecial H.ext H.center_sup hw₀U.1 hu.1
    have hzZ : ∀ {k : G}, k ∈ zpowers z → k ∈ Zs := fun hk => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
      exact zpow_mem H.z_mem_Zs n
    rw [indic_mul hK (hcZ u hu) (hzZ hwz)]
    have h1 : indic (zpowers e) ((s₀ : G) * u * (s₀ : G)⁻¹ * u⁻¹) =
        polar H.xsub.q w (H.xsub.cl u) := by
      rw [hpol _ (hclU u hu)]
      show _ = indic (zpowers e) (c (H.xsub.cl u))
      rw [hcu u hu]
    have h2 : indic (zpowers e) (w₀ * u * w₀⁻¹ * u⁻¹) = polar H.xsub.q w (H.xsub.cl u) := by
      have hcl₀ : H.xsub.cl w₀ = w := (hr w).2
      rcases H.xsub.mem_zpowers_z_iff.mp hwz with h | h
      · have hc : w₀ * u = u * w₀ := by
          calc w₀ * u = w₀ * u * w₀⁻¹ * u⁻¹ * (u * w₀) := by group
            _ = u * w₀ := by rw [h, one_mul]
        rw [h, ← hcl₀, (H.xsub.polar_cl_eq_zero_iff hw₀U.1 hu.1).mpr hc, indic_eq_zero_iff]
        exact one_mem _
      · have hc : ¬ w₀ * u = u * w₀ := by
          intro hc
          have h3 : w₀ * u * w₀⁻¹ * u⁻¹ = 1 := by
            rw [hc, mul_inv_cancel_right, mul_inv_cancel]
          exact H.z_ne_one (h.symm.trans h3)
        have h4 : polar H.xsub.q w (H.xsub.cl u) = 1 := by
          rw [← hcl₀]
          exact CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero fun h0 =>
            hc ((H.xsub.polar_cl_eq_zero_iff hw₀U.1 hu.1).mp h0)
        rw [h4, h]
        classical
        simp [indic, H.sq_z_not_mem_zpowers he hez]
    rw [h1, h2, zmod2_add_self]

theorem sq_coord_mul_self (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {e : G} (he : e ∈ Zs) (hez : e ∉ zpowers z)
    {s₁ s₂ : G} (hs₁ : s₁ ∈ sec3SHat (Q₀ ⊔ Q) Zs) (hs₂ : s₂ ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hs₁U : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₁ * u * s₁⁻¹ * u⁻¹ ∈ zpowers e)
    (hs₂U : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₂ * u * s₂⁻¹ * u⁻¹ ∈ zpowers e)
    (h12 : s₁ * s₂ * s₁⁻¹ * s₂⁻¹ = z * e)
    {κ : G → ZMod 2} (hκ : ∀ c ∈ Zs, ∀ d ∈ Zs, κ (c * d) = κ c + κ d) (hκ1 : κ (z * e) = 1)
    {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) (hsF : s ∈ sec3F (Q₀ ⊔ Q))
    (hsU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e)
    {w : H.xsub.Qt} (hw : polar H.xsub.q (H.xsub.cl e) w = 0)
    (hρ : H.ρF ⟨s, hsF⟩ = eichler H.xsub.q (H.xsub.cl e) w) :
    κ (s * s) = H.xsub.q w := by
  have hq := H.xsub.q_nondegenerate
  set a := H.xsub.cl e with ha_def
  have ha0 : a ≠ 0 := H.cl_ne_zero hZQ he hez
  have ha : H.xsub.q a = 0 := H.q_cl_eq_zero hZQ he
  have hSF := SHat_le_F Q₀ Q Zs
  have hSe : ∀ {t : G}, t ∈ sec3SHat (Q₀ ⊔ Q) Zs →
      (∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), t * u * t⁻¹ * u⁻¹ ∈ zpowers e) →
      t ∈ shatE Q₀ Q Zs e := fun ht htU =>
    ⟨ht, (mem_centralizer_iff.mp (SHat_le_centralizer Q₀ Q Zs ht) e he).symm, htU⟩
  have hcen : ∀ {t c : G}, t ∈ shatE Q₀ Q Zs e → c ∈ Zs → Commute t c := fun ht hc =>
    (mem_centralizer_iff.mp (SHat_le_centralizer Q₀ Q Zs ht.1) _ hc).symm
  have hcomZ : ∀ {t t' : G}, t ∈ shatE Q₀ Q Zs e → t' ∈ shatE Q₀ Q Zs e →
      t * t' * t⁻¹ * t'⁻¹ ∈ Zs := fun ht ht' => H.commutator_SHat_le hΩ hQF hZQ he hez
    (by rw [← commutatorElement_def]; exact commutator_mem_commutator ht.1 ht'.1)
  have hsqZ : ∀ {t : G}, t ∈ shatE Q₀ Q Zs e → t * t ∈ Zs := fun ht =>
    H.mul_self_mem_Zs hΩ hQF hZQ he hez ht.1
  have hinvZ : ∀ {c : G}, c ∈ Zs → c⁻¹ = c := fun hc =>
    inv_eq_of_mul_eq_one_right (H.sq_mul_self_of_mem_Zs hc)
  obtain ⟨a₁, -, ha₁, haa₁⟩ := CFSG.LargeExtraspecial.S2.exists_hyperbolic_partner hq
    (F := ⊥) (by simp) (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial) ha0 ha
  have h6 : 6 ≤ finrank (ZMod 2) (perp H.xsub.q (Submodule.span (ZMod 2) {a, a₁})) := by
    have h := CFSG.LargeExtraspecial.S2.finrank_perp_sup_span_pair hq (F := ⊥) (by simp)
      (p := a) (p₁ := a₁) (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial)
      (by rw [CFSG.LargeExtraspecial.S2.perp_bot]; trivial) haa₁
    rw [bot_sup_eq, CFSG.LargeExtraspecial.S2.perp_bot, finrank_top, H.finrank_Qt] at h
    omega
  have hpolW : ∀ v ∈ perp H.xsub.q (Submodule.span (ZMod 2) {a, a₁}),
      polar H.xsub.q a v = 0 := fun v hv => mem_perp.mp hv a (Submodule.subset_span (by simp))
  have hproj : ∀ u, polar H.xsub.q a u = 0 →
      eichler H.xsub.q a (projPerp H.xsub.q a a₁ u) = eichler H.xsub.q a u := by
    intro u hu
    rw [projPerp_apply, polar_comm H.xsub.q u a, hu, zero_smul, sub_zero, sub_eq_add_neg,
      ← neg_smul, CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self ha]
  have hlift : ∀ v : H.xsub.Qt, ∃ t : ↥(sec3F (Q₀ ⊔ Q)),
      v ∈ perp H.xsub.q (Submodule.span (ZMod 2) {a, a₁}) →
      (t : G) ∈ shatE Q₀ Q Zs e ∧ H.ρF t = eichler H.xsub.q a v := by
    intro v
    by_cases hv : v ∈ perp H.xsub.q (Submodule.span (ZMod 2) {a, a₁})
    · obtain ⟨t, htS, htρ, htU⟩ := H.exists_mem_SHatE hΩ hQF hRc hZQ he hez
        (CFSG.LargeExtraspecial.eichler_mem_pointRadical ha (hpolW v hv))
      exact ⟨t, fun _ => ⟨hSe htS htU, htρ⟩⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose L hL using hlift
  set W := perp H.xsub.q (Submodule.span (ZMod 2) {a, a₁}) with hW
  have hLS : ∀ v ∈ W, ((L v : ↥(sec3F (Q₀ ⊔ Q))) : G) ∈ shatE Q₀ Q Zs e :=
    fun v hv => (hL v hv).1
  have hLρ : ∀ v ∈ W, H.ρF (L v) = eichler H.xsub.q a v := fun v hv => (hL v hv).2
  have hLadd : ∀ x ∈ W, ∀ x' ∈ W,
      ∃ c ∈ Zs, ((L (x + x') : ↥(sec3F (Q₀ ⊔ Q))) : G) = (L x : G) * L x' * c := by
    intro x hx x' hx'
    obtain ⟨c, hc, hce⟩ := H.sq_exists_mul_of_ρF_eq hQF hZQ he hez (s := L (x + x'))
      (t := L x * L x') (hLS _ (W.add_mem hx hx')) (mul_mem (hLS x hx) (hLS x' hx'))
      (by rw [map_mul, hLρ x hx, hLρ x' hx', hLρ _ (W.add_mem hx hx'),
        CFSG.ClassicalGroups.Orthogonal.eichler_mul (hpolW x hx) (hpolW x' hx')])
    exact ⟨c, hc, by rw [hce, Subgroup.coe_mul]⟩
  have hβadd : ∀ x ∈ W, ∀ x' ∈ W, ∀ y ∈ W,
      κ ((L (x + x') : G) * L y * (L (x + x') : G)⁻¹ * (L y : G)⁻¹) =
        κ ((L x : G) * L y * (L x : G)⁻¹ * (L y : G)⁻¹) +
          κ ((L x' : G) * L y * (L x' : G)⁻¹ * (L y : G)⁻¹) := by
    intro x hx x' hx' y hy
    obtain ⟨c, hc, hce⟩ := hLadd x hx x' hx'
    rw [hce, comm_mul_central_left ((hcen (hLS y hy) hc).symm),
      comm_mul_left (hcen (hLS x hx) (hcomZ (hLS x' hx') (hLS y hy))),
      hκ _ (hcomZ (hLS x' hx') (hLS y hy)) _ (hcomZ (hLS x hx) (hLS y hy)), add_comm]
  have hQadd : ∀ x ∈ W, ∀ y ∈ W, κ ((L (x + y) : G) * L (x + y)) =
      κ ((L x : G) * L x) + κ ((L y : G) * L y) +
        κ ((L x : G) * L y * (L x : G)⁻¹ * (L y : G)⁻¹) := by
    intro x hx y hy
    obtain ⟨c, hc, hce⟩ := hLadd x hx y hy
    have hxy := mul_mem (hLS x hx) (hLS y hy)
    have hcxy := hcomZ (hLS x hx) (hLS y hy)
    rw [hce, mul_mul_self_central (hcen hxy hc) (H.sq_mul_self_of_mem_Zs hc),
      mul_mul_self (hcen (hLS x hx) (hcomZ (hLS y hy) (hLS x hx)))]
    have hyx : (L y : G) * L x * (L y : G)⁻¹ * (L x : G)⁻¹ =
        (L x : G) * L y * (L x : G)⁻¹ * (L y : G)⁻¹ := by
      rw [← hinvZ hcxy]
      group
    rw [hyx, hκ _ (mul_mem hcxy (hsqZ (hLS x hx))) _ (hsqZ (hLS y hy)),
      hκ _ hcxy _ (hsqZ (hLS x hx))]
    ring
  have hlg : ∀ g ∈ omegaFix H.xsub.q hq (Submodule.span (ZMod 2) {a, a₁}),
      ∃ f : ↥(sec3F (Q₀ ⊔ Q)), (f : G) ∈ centralizer (Zs : Set G) ∧ H.ρF f = g := by
    intro g hg
    obtain ⟨f₀, hf₀⟩ := H.exists_F_of_omega hΩ hg.1
    have hga : g a = a :=
      CFSG.LargeExtraspecial.S2.mem_fixGroup.mp hg.2 a (Submodule.subset_span (by simp))
    obtain ⟨f, hfZ, hfρ⟩ := H.exists_mem_centralizer_of_apply hQF hZQ he hez f₀
      (by rw [hf₀]; exact hga)
    exact ⟨f, hfZ, hfρ.trans hf₀⟩
  have hLg : ∀ g ∈ omegaFix H.xsub.q hq (Submodule.span (ZMod 2) {a, a₁}),
      ∀ f : ↥(sec3F (Q₀ ⊔ Q)), (f : G) ∈ centralizer (Zs : Set G) → H.ρF f = g → ∀ v ∈ W,
      ∃ c ∈ Zs, ((L (g v) : ↥(sec3F (Q₀ ⊔ Q))) : G) = f * L v * (f : G)⁻¹ * c := by
    intro g hg f hfZ hfρ v hv
    have hgO := (mem_omegaGroup.mp hg.1).1
    have hga : g a = a :=
      CFSG.LargeExtraspecial.S2.mem_fixGroup.mp hg.2 a (Submodule.subset_span (by simp))
    have hgv : g v ∈ W := CFSG.LargeExtraspecial.S2.apply_mem_perp hgO hg.2 hv
    obtain ⟨c, hc, hce⟩ := H.sq_exists_mul_of_ρF_eq hQF hZQ he hez (s := L (g v))
      (t := f * L v * f⁻¹) (hLS _ hgv) (H.sq_conj_mem_shatE he f.2 hfZ (hLS v hv))
      (by rw [hLρ _ hgv, map_mul, map_mul, map_inv, hfρ, hLρ v hv,
        CFSG.ClassicalGroups.Orthogonal.eichler_conj hgO, hga])
    exact ⟨c, hc, by rw [hce]; rfl⟩
  have hQg : ∀ g ∈ omegaFix H.xsub.q hq (Submodule.span (ZMod 2) {a, a₁}), ∀ v ∈ W,
      κ ((L (g v) : G) * L (g v)) = κ ((L v : G) * L v) := by
    intro g hg v hv
    obtain ⟨f, hfZ, hfρ⟩ := hlg g hg
    obtain ⟨c, hc, hce⟩ := hLg g hg f hfZ hfρ v hv
    have hcj := H.sq_conj_mem_shatE he f.2 hfZ (hLS v hv)
    rw [hce, mul_mul_self_central (hcen hcj hc) (H.sq_mul_self_of_mem_Zs hc),
      show (f : G) * L v * (f : G)⁻¹ * ((f : G) * L v * (f : G)⁻¹) =
        (f : G) * ((L v : G) * L v) * (f : G)⁻¹ by group,
      ← mem_centralizer_iff.mp hfZ _ (hsqZ (hLS v hv)), mul_inv_cancel_right]
  have hβg : ∀ g ∈ omegaFix H.xsub.q hq (Submodule.span (ZMod 2) {a, a₁}), ∀ v ∈ W,
      ∀ v' ∈ W, κ ((L (g v) : G) * L (g v') * (L (g v) : G)⁻¹ * (L (g v') : G)⁻¹) =
        κ ((L v : G) * L v' * (L v : G)⁻¹ * (L v' : G)⁻¹) := by
    intro g hg v hv v' hv'
    obtain ⟨f, hfZ, hfρ⟩ := hlg g hg
    obtain ⟨c, hc, hce⟩ := hLg g hg f hfZ hfρ v hv
    obtain ⟨c', hc', hce'⟩ := hLg g hg f hfZ hfρ v' hv'
    have hcj := H.sq_conj_mem_shatE he f.2 hfZ (hLS v hv)
    have hcj' := H.sq_conj_mem_shatE he f.2 hfZ (hLS v' hv')
    rw [hce, hce', comm_mul_central_left
        ((hcen (mul_mem hcj' (H.sq_Zs_le_shatE hQF hZQ he hc')) hc).symm),
      comm_mul_central_right ((hcen hcj hc').symm),
      show (f : G) * L v * (f : G)⁻¹ * ((f : G) * L v' * (f : G)⁻¹) *
          ((f : G) * L v * (f : G)⁻¹)⁻¹ * ((f : G) * L v' * (f : G)⁻¹)⁻¹ =
        (f : G) * ((L v : G) * L v' * (L v : G)⁻¹ * (L v' : G)⁻¹) * (f : G)⁻¹ by group,
      ← mem_centralizer_iff.mp hfZ _ (hcomZ (hLS v hv) (hLS v' hv')), mul_inv_cancel_right]
  have hparam : ∀ {t : G} (ht : t ∈ sec3SHat (Q₀ ⊔ Q) Zs),
      ∃ v ∈ W, H.ρF ⟨t, hSF ht⟩ = eichler H.xsub.q a v := by
    intro t ht
    obtain ⟨u, hau, hρu⟩ := (CFSG.LargeExtraspecial.mem_pointRadical_iff hq ha0 ha).mp
      (H.ρF_mem_pointRadical hΩ hQF hZQ he hez (s := ⟨t, hSF ht⟩) ht)
    exact ⟨projPerp H.xsub.q a a₁ u, projPerp_mem haa₁ u, by rw [hρu, hproj u hau]⟩
  obtain ⟨x₁, hx₁, hρ₁⟩ := hparam hs₁
  obtain ⟨x₂, hx₂, hρ₂⟩ := hparam hs₂
  have h12' : κ ((L x₁ : G) * L x₂ * (L x₁ : G)⁻¹ * (L x₂ : G)⁻¹) = 1 := by
    obtain ⟨c₁, hc₁, hce₁⟩ := H.sq_exists_mul_of_ρF_eq hQF hZQ he hez (s := L x₁)
      (t := ⟨s₁, hSF hs₁⟩) (hLS x₁ hx₁) (hSe hs₁ hs₁U) (by rw [hLρ x₁ hx₁, hρ₁])
    obtain ⟨c₂, hc₂, hce₂⟩ := H.sq_exists_mul_of_ρF_eq hQF hZQ he hez (s := L x₂)
      (t := ⟨s₂, hSF hs₂⟩) (hLS x₂ hx₂) (hSe hs₂ hs₂U) (by rw [hLρ x₂ hx₂, hρ₂])
    rw [hce₁, hce₂, comm_mul_central_left
        ((hcen (mul_mem (hSe hs₂ hs₂U) (H.sq_Zs_le_shatE hQF hZQ he hc₂)) hc₁).symm),
      comm_mul_central_right ((hcen (hSe hs₁ hs₁U) hc₂).symm)]
    show κ (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) = 1
    rw [h12, hκ1]
  have hx₀ : projPerp H.xsub.q a a₁ w ∈ W := projPerp_mem haa₁ w
  obtain ⟨c, hc, hce⟩ := H.sq_exists_mul_of_ρF_eq hQF hZQ he hez
    (s := L (projPerp H.xsub.q a a₁ w)) (t := ⟨s, hsF⟩) (hLS _ hx₀) (hSe hs hsU)
    (by rw [hLρ _ hx₀, hproj w hw, hρ])
  have hmain : κ ((L (projPerp H.xsub.q a a₁ w) : G) * L (projPerp H.xsub.q a a₁ w)) =
      H.xsub.q (projPerp H.xsub.q a a₁ w) :=
    Sec3SHatSq.eq_of_invariant hq ha ha₁ haa₁ h6
      (Q' := fun v => κ ((L v : G) * L v))
      (β := fun v v' => κ ((L v : G) * L v' * (L v : G)⁻¹ * (L v' : G)⁻¹))
      hβadd hQadd hβg hQg hx₁ hx₂ h12' _ hx₀
  have hsq : (L (projPerp H.xsub.q a a₁ w) : G) * L (projPerp H.xsub.q a a₁ w) = s * s := by
    rw [hce]
    exact mul_mul_self_central (hcen (hSe hs hsU) hc) (H.sq_mul_self_of_mem_Zs hc)
  have hqx : H.xsub.q (projPerp H.xsub.q a a₁ w) = H.xsub.q w := by
    rw [projPerp_apply, polar_comm H.xsub.q w a, hw, zero_smul, sub_zero, sub_eq_add_neg,
      ← neg_smul, QuadraticMap.map_add H.xsub.q, QuadraticMap.map_smul, ha, polar_smul_right,
      polar_comm H.xsub.q w a, hw]
    simp
  rw [← hsq, hmain, hqx]

theorem mul_self_eq_of_comm_le (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {e : G} (he : e ∈ Zs) (hez : e ∉ zpowers z)
    {s₁ s₂ : G} (hs₁ : s₁ ∈ sec3SHat (Q₀ ⊔ Q) Zs) (hs₂ : s₂ ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hs₁U : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₁ * u * s₁⁻¹ * u⁻¹ ∈ zpowers e)
    (hs₂U : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₂ * u * s₂⁻¹ * u⁻¹ ∈ zpowers e)
    (h12 : s₁ * s₂ * s₁⁻¹ * s₂⁻¹ = z * e)
    {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) (hsF : s ∈ sec3F (Q₀ ⊔ Q))
    (hsU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e)
    {w : H.xsub.Qt} (hw : polar H.xsub.q (H.xsub.cl e) w = 0)
    (hρ : H.ρF ⟨s, hsF⟩ = eichler H.xsub.q (H.xsub.cl e) w) :
    s * s = if H.xsub.q w = 0 then 1 else z * e := by
  classical
  have hv₁ : indic (zpowers e) (z * e) = 1 := by
    have h : z * e ∉ zpowers e := fun h => H.sq_z_not_mem_zpowers he hez (by
      have h' := mul_mem h (inv_mem (mem_zpowers e))
      rwa [mul_inv_cancel_right] at h')
    simp [indic, h]
  have hv₂ : indic (zpowers z) (z * e) = 1 := by
    have h : z * e ∉ zpowers z := fun h => hez (by
      have h' := mul_mem (inv_mem (mem_zpowers z)) h
      rwa [inv_mul_cancel_left] at h')
    simp [indic, h]
  have h₁ := H.sq_coord_mul_self hΩ hQF hRc hZQ he hez hs₁ hs₂ hs₁U hs₂U h12
    (fun c hc d hd => indic_mul (H.sq_mul_mem_zpowers_e hZQ he hez) hc hd) hv₁ hs hsF hsU hw hρ
  have h₂ := H.sq_coord_mul_self hΩ hQF hRc hZQ he hez hs₁ hs₂ hs₁U hs₂U h12
    (fun c hc d hd => indic_mul (H.sq_mul_mem_zpowers_z hZQ he hez) hc hd) hv₂ hs hsF hsU hw hρ
  have hsZ : s * s ∈ Zs := H.mul_self_mem_Zs hΩ hQF hZQ he hez hs
  split_ifs with hq0
  · rw [hq0, indic_eq_zero_iff] at h₁ h₂
    rcases Sec3SHat.eq_one_or_eq_of_mem_zpowers (H.sq_mul_self_of_mem_Zs he) h₁ with h | h
    · exact h
    · rw [h] at h₂
      exact absurd h₂ hez
  · have hq1 : H.xsub.q w = 1 := CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero hq0
    rw [hq1] at h₁ h₂
    have hn₁ : s * s ∉ zpowers e := fun h => by
      rw [← indic_eq_zero_iff, h₁] at h
      exact absurd h (by decide)
    have hn₂ : s * s ∉ zpowers z := fun h => by
      rw [← indic_eq_zero_iff, h₂] at h
      exact absurd h (by decide)
    rcases H.mem_Zs_cases hZQ he hez hsZ with h | h | h | h
    · exact absurd (h ▸ one_mem _) hn₁
    · exact absurd (h ▸ mem_zpowers z) hn₂
    · exact absurd (h ▸ mem_zpowers e) hn₁
    · rw [h, H.comm_of_mem_Zs he H.z_mem_Zs]

end Sec38Hyp

end CFSG.ComponentClassification.AS81
