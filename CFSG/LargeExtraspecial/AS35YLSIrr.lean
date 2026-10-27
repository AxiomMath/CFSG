module

public import CFSG.LargeExtraspecial.AS35YLSIrrA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YL

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

variable {q : QuadraticForm (ZMod 2) V}

theorem polar_eq_zero_of_tv_YL {g : V ≃ₗ[ZMod 2] V} (hiso : ∀ v, q (g v) = q v) {a u v : V}
    (hgu : g u = u) (hgv : g v = v + a) : polar q u a = 0 := by
  have h := polar_map_YL hiso u v
  rw [hgu, hgv, polar_add_right] at h
  have h' := congrArg (· - polar q u v) h
  simpa using h'

theorem polar_center_eq_zero_YL {g₁ g₂ : V ≃ₗ[ZMod 2] V} (hiso₁ : ∀ v, q (g₁ v) = q v)
    (hiso₂ : ∀ v, q (g₂ v) = q v) {W : Submodule (ZMod 2) V} {a : V}
    (hg₂ : ∀ w ∈ W, g₂ w = w ∨ g₂ w = w + a) (hv : ∃ v ∈ W, g₁ v = v + a)
    (hu : ∃ u ∈ W, g₁ u = u ∧ g₂ u = u + a) : ∀ w ∈ W, polar q w a = 0 := by
  obtain ⟨v, -, hgv⟩ := hv
  obtain ⟨u, -, hgu₁, hgu₂⟩ := hu
  have hu0 : polar q u a = 0 := polar_eq_zero_of_tv_YL hiso₁ hgu₁ hgv
  intro w hw
  rcases hg₂ w hw with h | h
  · exact polar_eq_zero_of_tv_YL hiso₂ h hgu₂
  · have h' : g₂ (w + u) = w + u := by
      rw [map_add, h, hgu₂, add_add_add_comm, add_self_YL, add_zero]
    have h1 := polar_eq_zero_of_tv_YL hiso₂ h' hgu₂
    rw [polar_add_left, hu0, add_zero] at h1
    exact h1

theorem polar_twist_eq_zero_YL {g : V ≃ₗ[ZMod 2] V} (hiso : ∀ v, q (g v) = q v)
    {W₁ W₂ : Submodule (ZMod 2) V} (hg₁ : ∀ y ∈ W₁, g y ∈ W₁) (hg₂ : ∀ y ∈ W₂, g y ∈ W₂)
    (h12 : W₁ ⊓ W₂ = ⊥) {a a' v v' u : V} (ha' : a' ∈ W₁) (haa : a + a' ∈ W₂) (hv' : v' ∈ W₁)
    (hvv : v + v' ∈ W₂) (hgv : g v = v + a) (hgu : g u = u) : polar q u a' = 0 := by
  have hgv' : g v' = v' + a' := by
    have h1 : g (v + v') ∈ W₂ := hg₂ _ hvv
    have h2 : (v + v') + (a + a') ∈ W₂ := W₂.add_mem hvv haa
    have h3 : g v' - (v' + a') ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.sub_mem (hg₁ _ hv') (W₁.add_mem hv' ha'), ?_⟩
      have := W₂.sub_mem h1 h2
      rw [map_add, hgv] at this
      have e : g v' - (v' + a') = v + a + g v' - (v + v' + (a + a')) := by abel
      rw [e]
      exact this
    rw [h12, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  exact polar_eq_zero_of_tv_YL hiso hgu hgv'

theorem isom_of_mem_closure_YL {D : Set (V ≃ₗ[ZMod 2] V)} (hisom : ∀ d ∈ D, ∀ v, q (d v) = q v)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ closure D) : ∀ v, q (g v) = q v := by
  induction hg using Subgroup.closure_induction with
  | mem d hd => exact hisom d hd
  | one => exact fun v => rfl
  | mul a b _ _ ha hb => exact fun v => by rw [LinearEquiv.mul_apply, ha, hb]
  | inv a _ ha =>
    intro v
    rw [← ha (a⁻¹ v)]
    congr 1
    exact a.apply_symm_apply v

theorem orthogonal_inv_YL {D : Set (V ≃ₗ[ZMod 2] V)} (hinvol : ∀ d ∈ D, d * d = 1)
    (hisom : ∀ d ∈ D, ∀ v, q (d v) = q v) {W : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) :
    ∀ d ∈ D, ∀ u ∈ LinearMap.BilinForm.orthogonal q.polarBilin W,
      d u ∈ LinearMap.BilinForm.orthogonal q.polarBilin W := by
  intro d hd u hu
  rw [OrthoF2.mem_orthogonal_iff_polar] at hu ⊢
  intro w hw
  have hdw : d (d w) = w := by
    rw [← LinearEquiv.mul_apply, hinvol d hd]
    rfl
  rw [← hdw, polar_map_YL (hisom d hd)]
  exact hu _ (hW d hd w hw)

theorem irred_of_fpf_YL [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ D)
    (hA : ∀ d ∈ D, IsTypeA q d 2) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0)
    (hsq : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4)
    {x : V ≃ₗ[ZMod 2] V} (hxiso : ∀ v, q (x v) = q v) (hxD : ∀ d ∈ D, x⁻¹ * d * x ∈ D)
    (hxt : x * t = t * x) {k : ℕ} (hxk : x ^ (3 ^ k) = 1)
    (hxfpf : ∀ v ∈ commSpace t, x v = v → v = 0) :
    ∀ W : Submodule (ZMod 2) V, (∀ d ∈ D, ∀ w ∈ W, d w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  have hinvol : ∀ d ∈ D, d * d = 1 := fun d hd => (hA d hd).2.2.1
  have hisom : ∀ d ∈ D, ∀ v, q (d v) = q v := fun d hd => (hA d hd).1
  by_contra hcon
  push Not at hcon
  have hex : ∃ m, ∃ W : Submodule (ZMod 2) V, (∀ d ∈ D, ∀ w ∈ W, d w ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ ∧
      finrank (ZMod 2) W = m := by
    obtain ⟨W, hW, hW0, hWt⟩ := hcon
    exact ⟨_, W, hW, hW0, hWt, rfl⟩
  obtain ⟨W, hW, hW0, hWt, hWm⟩ := Nat.find_spec hex
  have hmin : ∀ U : Submodule (ZMod 2) V, (∀ d ∈ D, ∀ u ∈ U, d u ∈ U) → U ≠ ⊥ → U ≠ ⊤ →
      finrank (ZMod 2) W ≤ finrank (ZMod 2) U := by
    intro U hU hU0 hUt
    rw [hWm]
    exact Nat.find_min' hex ⟨U, hU, hU0, hUt, rfl⟩
  obtain ⟨p, hp, hp0, huniq⟩ :=
    exists_point_YL hq ht (hA t ht) hinvol hisom hconj hfix hW hW0 hWt
  have hW₁i := map_inv_YL hxD hW
  have hW₂i := map_inv_YL hxD hW₁i
  obtain ⟨hp₁, huniq₁⟩ := point_map_YL hxt hp huniq
  obtain ⟨hp₂, huniq₂⟩ := point_map_YL hxt hp₁ huniq₁
  have hp₁0 : x p ≠ 0 := fun h => hp0 (x.injective (h.trans (map_zero x).symm))
  have hp₂0 : x (x p) ≠ 0 := fun h => hp₁0 (x.injective (h.trans (map_zero x).symm))
  have hpp₁ : p ≠ x p := fun h => hp0 (hxfpf p (Submodule.mem_inf.mp hp).2 h.symm)
  have hp₁p₂ : x p ≠ x (x p) := fun h => hpp₁ (x.injective h)
  have hpp₂ : p ≠ x (x p) := fun h => hpp₁ (apply_eq_of_apply_apply_eq_YL hxk h.symm).symm
  obtain ⟨-, hs01⟩ := compl_of_points_YL hq ht (hA t ht) hinvol hisom hconj hfix hW hW₁i hp hp₁
    hp0 hp₁0 huniq huniq₁ hpp₁
  obtain ⟨h02, -⟩ := compl_of_points_YL hq ht (hA t ht) hinvol hisom hconj hfix hW hW₂i hp hp₂
    hp0 hp₂0 huniq huniq₂ hpp₂
  obtain ⟨h12, hs12⟩ := compl_of_points_YL hq ht (hA t ht) hinvol hisom hconj hfix hW₁i hW₂i hp₁
    hp₂ hp₁0 hp₂0 huniq₁ huniq₂ hp₁p₂
  obtain ⟨d, hd, e, he, h4⟩ := hnd
  obtain ⟨g₁, hg₁, g₂, hg₂, a, haW, ha0, -, hval₂, hv, hu⟩ :=
    exists_tv_pair_YL hq hA hconj hfix hsq hW hW0 hWt hd he h4
  have hiso₁ := isom_of_mem_closure_YL hisom hg₁
  have hiso₂ := isom_of_mem_closure_YL hisom hg₂
  have hWpi := orthogonal_inv_YL hinvol hisom hW
  have hdich : W ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W = ⊥ ∨
      W ≤ LinearMap.BilinForm.orthogonal q.polarBilin W := by
    by_contra hcon2
    push Not at hcon2
    obtain ⟨hne, hnle⟩ := hcon2
    have hlt : W ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W < W :=
      lt_of_le_of_ne inf_le_left (fun h => hnle (inf_eq_left.mp h))
    have := hmin (W ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W)
      (fun d hd w hw => Submodule.mem_inf.mpr ⟨hW d hd w (Submodule.mem_inf.mp hw).1,
        hWpi d hd w (Submodule.mem_inf.mp hw).2⟩) hne
      (fun h => hWt (eq_top_iff.mpr (le_trans (le_of_eq h.symm) inf_le_left)))
    exact absurd this (not_le.mpr (Submodule.finrank_lt_finrank_of_lt hlt))
  rcases hdich with hbot | hle
  ·
    have h0 := polar_center_eq_zero_YL hiso₁ hiso₂ hval₂ hv hu
    have haW' : a ∈ W ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W :=
      ⟨haW, OrthoF2.mem_orthogonal_iff_polar.mpr fun w hw => by rw [polar_comm]; exact h0 w hw⟩
    rw [hbot, Submodule.mem_bot] at haW'
    exact ha0 haW'
  ·
    have hW₁iso : ∀ y ∈ W.map (x : V →ₗ[ZMod 2] V), ∀ y' ∈ W.map (x : V →ₗ[ZMod 2] V),
        polar q y y' = 0 := by
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      simp only [LinearEquiv.coe_coe]
      rw [polar_map_YL hxiso]
      exact (OrthoF2.mem_orthogonal_iff_polar.mp (hle hw)) w' hw'
    have hdec : ∀ y : V, ∃ y' ∈ W.map (x : V →ₗ[ZMod 2] V),
        y + y' ∈ (W.map (x : V →ₗ[ZMod 2] V)).map (x : V →ₗ[ZMod 2] V) := by
      intro y
      have hy : y ∈ W.map (x : V →ₗ[ZMod 2] V) ⊔
          (W.map (x : V →ₗ[ZMod 2] V)).map (x : V →ₗ[ZMod 2] V) := hs12 ▸ Submodule.mem_top
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      refine ⟨y₁, hy₁, ?_⟩
      rw [add_comm y₁ y₂, add_assoc, add_self_YL, add_zero]
      exact hy₂
    obtain ⟨a', ha', haa⟩ := hdec a
    obtain ⟨v, -, hgv⟩ := hv
    obtain ⟨v', hv', hvv⟩ := hdec v
    obtain ⟨u, -, hgu₁, hgu₂⟩ := hu
    obtain ⟨u', hu', huu⟩ := hdec u
    have hg₁W₁ := mem_of_mem_closure_YL hinvol hW₁i hg₁
    have hg₁W₂ := mem_of_mem_closure_YL hinvol hW₂i hg₁
    have hg₂W₁ := mem_of_mem_closure_YL hinvol hW₁i hg₂
    have hg₂W₂ := mem_of_mem_closure_YL hinvol hW₂i hg₂
    have hu0 : polar q u a' = 0 :=
      polar_twist_eq_zero_YL hiso₁ hg₁W₁ hg₁W₂ h12 ha' haa hv' hvv hgv hgu₁
    have hpa : ∀ w ∈ W, polar q w a' = 0 := by
      intro w hw
      rcases hval₂ w hw with h | h
      · exact polar_twist_eq_zero_YL hiso₂ hg₂W₁ hg₂W₂ h12 ha' haa hu' huu hgu₂ h
      · have h' : g₂ (w + u) = w + u := by
          rw [map_add, h, hgu₂, add_add_add_comm, add_self_YL, add_zero]
        have h1 := polar_twist_eq_zero_YL hiso₂ hg₂W₁ hg₂W₂ h12 ha' haa hu' huu hgu₂ h'
        rw [polar_add_left, hu0, add_zero] at h1
        exact h1
    have ha'0 : a' = 0 := by
      refine hq.1 a' fun y => ?_
      have hy : y ∈ W ⊔ W.map (x : V →ₗ[ZMod 2] V) := hs01 ▸ Submodule.mem_top
      obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
      rw [polarBilin_apply_apply, polar_add_right, polar_comm, hpa y₀ hy₀, polar_comm,
        hW₁iso _ hy₁ _ ha', add_zero]
    rw [ha'0, add_zero] at haa
    have hmem : a ∈ W ⊓ (W.map (x : V →ₗ[ZMod 2] V)).map (x : V →ₗ[ZMod 2] V) := ⟨haW, haa⟩
    rw [h02, Submodule.mem_bot] at hmem
    exact ha0 hmem

end AS35YL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YL

theorem lbarIrred_of_fixFree_YL (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (h5127 : S14.Asc512FiveTwelveSevenStmt)
    (hfix : ∀ v : S.Qt, (∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v = 0) :
    S.LbarIrred_YL := by
  set D : Set (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.O.subtype '' S.DbarAsc with hDdef
  have hmemD : ∀ {σ : S.O}, σ ∈ S.DbarAsc → (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ D := fun hσ =>
    ⟨_, hσ, rfl⟩
  have hclos : ∀ {g : S.O}, g ∈ S.LbarAsc → (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ closure D := by
    intro g hg
    have h := Subgroup.mem_map_of_mem S.O.subtype hg
    rwa [MonoidHom.map_closure] at h
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨x, hxM, ⟨k, hxk⟩, hxt, hfpf⟩ := h5127 _ S hS g ht htM
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hx3 : x ^ (3 ^ k) = 1 := by rw [← hxk]; exact pow_orderOf_eq_one x
  have hA : ∀ d ∈ D, IsTypeA S.q d 2 := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact isTypeA_of_mem_DbarAsc_YL hS hσ
  have hconj : ∀ d ∈ D, ∃ h ∈ closure D,
      h * ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * h⁻¹ = d := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨h, hh, hhσ⟩ := hst.conj _ htD σ hσ
    exact ⟨_, hclos hh, congrArg Subtype.val hhσ⟩
  have hfixD : ∀ v, (∀ d ∈ D, d v = v) → v = 0 := by
    intro v hv
    refine hfix v fun l hl => ?_
    induction hl using Subgroup.closure_induction with
    | mem σ hσ => exact hv _ (hmemD hσ)
    | one => rfl
    | mul a b _ _ ha hb =>
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
      rw [hb, ha]
    | inv a _ ha =>
      have e := congrArg (((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ha
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel] at e
      exact e.symm
  have hsqD : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩ h4
    have h4' : orderOf (σ * τ) = 4 := by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      exact h4
    exact ⟨_, sq_mem_DbarAsc_YL hS hσ hτ h4', by simp⟩
  have hndD : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4 := by
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨e, he, rfl⟩, h4⟩ := hnd
    have h4' := AS35YL.orderOf_eq_four_of_mk_YL
      (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he) hd he h4
    refine ⟨_, hmemD hd, _, hmemD he, ?_⟩
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    exact h4'
  have hxD : ∀ d ∈ D, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ * d * (x : S.O) ∈ D := by
    rintro _ ⟨σ, hσ, rfl⟩
    have h := S.conj_mem_DbarAsc_L (S.Mbar.inv_mem hxM) hσ
    rw [inv_inv] at h
    exact ⟨_, h, by simp⟩
  have hirr := irred_of_fpf_YL S.q_nondegenerate (hmemD htD) hA hconj hfixD hsqD hndD
    (x := (x : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 v) hxD
    (congrArg Subtype.val hxt) (k := k) (by rw [← Subgroup.coe_pow, hx3]; rfl) hfpf
  intro W hW
  exact hirr W fun _ ⟨σ, hσ, hσd⟩ w hw => hσd ▸ hW σ (subset_closure hσ) w hw

end Setting

namespace S14

@[expose] def Asc512FixFreeStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    (Asc512PSLFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      Asc512PSpFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      Asc512POmegaFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      Asc512U33Fam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc) →
    ∀ v : S.Qt, (∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v = 0

end S14

end CFSG.LargeExtraspecial
