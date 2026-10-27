module

public import CFSG.LargeExtraspecial.AS35YLSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YL

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem span_pair_eq_YL [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V}
    (hU2 : finrank (ZMod 2) U = 2) {u v : V} (hu : u ∈ U) (hv : v ∈ U) (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (huv : u ≠ v) : Submodule.span (ZMod 2) {u, v} = U := by
  have hli : LinearIndependent (ZMod 2) ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases zmod2_cases_YL s with rfl | rfl <;> rcases zmod2_cases_YL t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst
      exact absurd hst hv0
    · simp at hst
      exact absurd hst hu0
    · simp only [one_smul] at hst
      have h' : u = v := by
        have h := congrArg (· + v) hst
        simpa only [add_assoc, add_self_YL, add_zero, zero_add] using h
      exact absurd h' huv
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hv
  · rw [hU2]
    have hr : Set.range ![u, v] = {u, v} := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have := finrank_span_eq_card hli
    rw [hr] at this
    simpa using this

theorem mem_of_mem_closure_YL {D : Set (V ≃ₗ[ZMod 2] V)} (hinvol : ∀ d ∈ D, d * d = 1)
    {W : Submodule (ZMod 2) V} (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ closure D) : ∀ w ∈ W, g w ∈ W := by
  induction hg using Subgroup.closure_induction'' with
  | mem d hd => exact hW d hd
  | inv_mem d hd =>
    rw [inv_eq_of_mul_eq_one_right (hinvol d hd)]
    exact hW d hd
  | one => exact fun w hw => hw
  | mul a b _ _ ha hb => exact fun w hw => ha _ (hb w hw)

theorem fix_of_inf_eq_bot_YL {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ D)
    (hinvol : ∀ d ∈ D, d * d = 1) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    {W : Submodule (ZMod 2) V} (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W)
    (hbot : W ⊓ commSpace t = ⊥) : ∀ d ∈ D, ∀ w ∈ W, d w = w := by
  intro d hd w hw
  obtain ⟨g, hg, rfl⟩ := hconj d hd
  have hgw : g⁻¹ w ∈ W := mem_of_mem_closure_YL hinvol hW (inv_mem hg) w hw
  have h0 : t (g⁻¹ w) - g⁻¹ w ∈ W ⊓ commSpace t :=
    ⟨W.sub_mem (hW t ht _ hgw) hgw, sub_mem_commSpace t _⟩
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at h0
  simp only [LinearEquiv.mul_apply, h0]
  exact g.apply_symm_apply w

theorem eq_bot_of_inf_eq_bot_YL {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ D)
    (hinvol : ∀ d ∈ D, d * d = 1) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0) {W : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hbot : W ⊓ commSpace t = ⊥) : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  exact (Submodule.mem_bot _).mpr
    (hfix w fun d hd => fix_of_inf_eq_bot_YL ht hinvol hconj hW hbot d hd w hw)

variable {q : QuadraticForm (ZMod 2) V}

theorem eq_top_of_le_YL [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V} (hinvol : ∀ d ∈ D, d * d = 1)
    (hisom : ∀ d ∈ D, ∀ v, q (d v) = q v) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0) {W : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hle : commSpace t ≤ W) : W = ⊤ := by
  have hcomm : ∀ d ∈ D, commSpace d ≤ W := by
    intro d hd x hx
    obtain ⟨g, hg, rfl⟩ := hconj d hd
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    have e : (g * t * g⁻¹) v - v = g (t (g⁻¹ v) - g⁻¹ v) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      rw [show g (g⁻¹ v) = v from g.apply_symm_apply v]
    rw [e]
    exact mem_of_mem_closure_YL hinvol hW hg _ (hle (sub_mem_commSpace t _))
  have hperp : LinearMap.BilinForm.orthogonal q.polarBilin W = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    refine hfix u fun d hd => ?_
    have hdd := hinvol d hd
    have h0 : ∀ v, polar q (d u - u) v = 0 := by
      intro v
      have hdv : d (d v) = v := by
        rw [← LinearEquiv.mul_apply, hdd, LinearEquiv.coe_one, id]
      have h1 : polar q (d u) v = polar q u (d v) := by
        rw [← polar_map_YL (hisom d hd) u (d v), hdv]
      have h2 : d v - v ∈ W := hcomm d hd (sub_mem_commSpace d v)
      have h3 : polar q u (d v - v) = 0 :=
        (OrthoF2.mem_orthogonal_iff_polar.mp hu) _ h2
      rw [polar_sub_left, h1, ← polar_sub_right, h3]
    have h4 : d u - u = 0 := hq.1 _ fun v => by
      rw [polarBilin_apply_apply]
      exact h0 v
    exact sub_eq_zero.mp h4
  have h := LinearMap.BilinForm.orthogonal_orthogonal hq
    (QuadraticMap.isSymm_polarBilin q).isRefl W
  rw [hperp, LinearMap.BilinForm.orthogonal_bot] at h
  exact h.symm

theorem conj_of_conj_YL {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V}
    (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d) {d : V ≃ₗ[ZMod 2] V} (hd : d ∈ D) :
    ∀ d' ∈ D, ∃ g ∈ closure D, g * d * g⁻¹ = d' := by
  intro d' hd'
  obtain ⟨g, hg, rfl⟩ := hconj d hd
  obtain ⟨g', hg', rfl⟩ := hconj d' hd'
  exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), by group⟩

theorem exists_point_YL [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ D) (htA : IsTypeA q t 2)
    (hinvol : ∀ d ∈ D, d * d = 1) (hisom : ∀ d ∈ D, ∀ v, q (d v) = q v)
    (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0) {W : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) :
    ∃ p ∈ W ⊓ commSpace t, p ≠ 0 ∧ ∀ v ∈ W ⊓ commSpace t, v = 0 ∨ v = p := by
  have hne : W ⊓ commSpace t ≠ ⊥ := fun h =>
    hW0 (eq_bot_of_inf_eq_bot_YL ht hinvol hconj hfix hW h)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨p, hp, hp0, fun v hv => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hv0, hvp⟩ := hcon
  have hspan := span_pair_eq_YL htA.2.2.2.1 (Submodule.mem_inf.mp hp).2
    (Submodule.mem_inf.mp hv).2 hp0 hv0 (Ne.symm hvp)
  have hle : commSpace t ≤ W := by
    rw [← hspan, Submodule.span_le]
    rintro y (rfl | rfl)
    · exact (Submodule.mem_inf.mp hp).1
    · exact (Submodule.mem_inf.mp hv).1
  exact hWt (eq_top_of_le_YL hq hinvol hisom hconj hfix hW hle)

theorem exists_tv_YL [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V}
    (hA : ∀ d ∈ D, IsTypeA q d 2) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0) {W : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) {d : V ≃ₗ[ZMod 2] V}
    (hd : d ∈ D) :
    ∃ a ∈ W, a ≠ 0 ∧ d a = a ∧ (∀ w ∈ W, d w - w = 0 ∨ d w - w = a) ∧
      ∃ v ∈ W, d v - v = a := by
  have hinvol : ∀ d ∈ D, d * d = 1 := fun d hd => (hA d hd).2.2.1
  have hisom : ∀ d ∈ D, ∀ v, q (d v) = q v := fun d hd => (hA d hd).1
  have hconj' := conj_of_conj_YL hconj hd
  obtain ⟨a, ha, ha0, huniq⟩ := exists_point_YL hq hd (hA d hd) hinvol hisom hconj' hfix hW hW0
    hWt
  have hda : d a = a :=
    mem_fixSpace.mp (commSpace_le_fixSpace (hinvol d hd) (Submodule.mem_inf.mp ha).2)
  have hval : ∀ w ∈ W, d w - w = 0 ∨ d w - w = a := fun w hw =>
    huniq _ ⟨W.sub_mem (hW d hd w hw) hw, sub_mem_commSpace d w⟩
  refine ⟨a, (Submodule.mem_inf.mp ha).1, ha0, hda, hval, ?_⟩
  by_contra hcon
  push Not at hcon
  have htriv : ∀ w ∈ W, d w = w := fun w hw =>
    sub_eq_zero.mp ((hval w hw).resolve_right (hcon w hw))
  refine hW0 (eq_bot_iff.mpr fun w hw => (Submodule.mem_bot _).mpr (hfix w fun d' hd' => ?_))
  obtain ⟨g, hg, rfl⟩ := hconj' d' hd'
  have hgw : g⁻¹ w ∈ W := mem_of_mem_closure_YL hinvol hW (inv_mem hg) w hw
  simp only [LinearEquiv.mul_apply, htriv _ hgw]
  exact g.apply_symm_apply w

theorem exists_tv_pair_YL [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V}
    (hA : ∀ d ∈ D, IsTypeA q d 2) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0)
    (hsq : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    {W : Submodule (ZMod 2) V} (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    {d e : V ≃ₗ[ZMod 2] V} (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    ∃ g₁ ∈ closure D, ∃ g₂ ∈ closure D, ∃ a ∈ W, a ≠ 0 ∧
      (∀ w ∈ W, g₁ w = w ∨ g₁ w = w + a) ∧ (∀ w ∈ W, g₂ w = w ∨ g₂ w = w + a) ∧
      (∃ v ∈ W, g₁ v = v + a) ∧ ∃ u ∈ W, g₁ u = u ∧ g₂ u = u + a := by
  have hinvol : ∀ d ∈ D, d * d = 1 := fun d hd => (hA d hd).2.2.1
  have hsq1 : ∀ {g : V ≃ₗ[ZMod 2] V}, g ∈ D → ∀ v, g (g v) = v := fun {g} hg v => by
    rw [← LinearEquiv.mul_apply, hinvol g hg]
    rfl
  obtain ⟨a, haW, ha0, hda, hdval, v₁, hv₁W, hv₁⟩ := exists_tv_YL hq hA hconj hfix hW hW0 hWt hd
  obtain ⟨b, hbW, hb0, heb, heval, v₂, hv₂W, hv₂⟩ := exists_tv_YL hq hA hconj hfix hW hW0 hWt he
  have hd' : ∀ w ∈ W, d w = w ∨ d w = w + a := fun w hw =>
    (hdval w hw).imp sub_eq_zero.mp sub_eq_iff_eq_add'.mp
  have he' : ∀ w ∈ W, e w = w ∨ e w = w + b := fun w hw =>
    (heval w hw).imp sub_eq_zero.mp sub_eq_iff_eq_add'.mp
  obtain ⟨c, -, hc0, -, -, w₀, hw₀W, hw₀⟩ :=
    exists_tv_YL hq hA hconj hfix hW hW0 hWt (hsq d hd e he h4)
  have hne : d (e (d (e w₀))) ≠ w₀ := by
    intro h
    simp only [pow_two, LinearEquiv.mul_apply] at hw₀
    rw [h, sub_self] at hw₀
    exact hc0 hw₀.symm
  rcases he' a haW with hea | hea <;> rcases hd' b hbW with hdb | hdb
  ·
    exfalso
    apply hne
    rcases hd' w₀ hw₀W with h1 | h1 <;> rcases he' w₀ hw₀W with h2 | h2
    · simp only [h1, h2]
    · simp only [h1, h2, map_add, hdb, heb, add_comm, add_self_add_YL]
    · simp only [h1, h2, map_add, hda, hea, add_comm, add_self_add_YL]
    · simp only [h1, h2, map_add, hda, hdb, hea, heb, add_left_comm, add_comm, add_self_add_YL]
  ·
    refine ⟨d, subset_closure hd, e * d * e, mul_mem (mul_mem (subset_closure he)
      (subset_closure hd)) (subset_closure he), a, haW, ha0, hd', fun w hw => ?_,
      ⟨v₁, hv₁W, sub_eq_iff_eq_add'.mp hv₁⟩, ?_⟩
    · simp only [LinearEquiv.mul_apply]
      rcases hd' (e w) (hW e he w hw) with h1 | h1
      · left
        rw [h1, hsq1 he]
      · right
        rw [h1, map_add, hsq1 he, hea]
    · have hw : e v₂ = v₂ + b := sub_eq_iff_eq_add'.mp hv₂
      rcases hd' v₂ hv₂W with h1 | h1
      · refine ⟨v₂, hv₂W, h1, ?_⟩
        simp only [LinearEquiv.mul_apply]
        simp only [h1, hw, map_add, hdb, hea, heb, add_left_comm, add_comm,
          add_self_add_YL]
      · refine ⟨v₂ + b, W.add_mem hv₂W hbW, ?_, ?_⟩
        · simp only [h1, map_add, hdb, add_left_comm, add_comm, add_self_add_YL,
            ]
        · simp only [LinearEquiv.mul_apply]
          simp only [h1, hw, map_add, hea, heb, add_comm,
            add_self_add_YL]
  ·
    refine ⟨e, subset_closure he, d * e * d, mul_mem (mul_mem (subset_closure hd)
      (subset_closure he)) (subset_closure hd), b, hbW, hb0, he', fun w hw => ?_,
      ⟨v₂, hv₂W, sub_eq_iff_eq_add'.mp hv₂⟩, ?_⟩
    · simp only [LinearEquiv.mul_apply]
      rcases he' (d w) (hW d hd w hw) with h1 | h1
      · left
        rw [h1, hsq1 hd]
      · right
        rw [h1, map_add, hsq1 hd, hdb]
    · have hw : d v₁ = v₁ + a := sub_eq_iff_eq_add'.mp hv₁
      rcases he' v₁ hv₁W with h1 | h1
      · refine ⟨v₁, hv₁W, h1, ?_⟩
        simp only [LinearEquiv.mul_apply]
        simp only [h1, hw, map_add, hda, hdb, hea, add_left_comm, add_comm,
          add_self_add_YL]
      · refine ⟨v₁ + a, W.add_mem hv₁W haW, ?_, ?_⟩
        · simp only [h1, map_add, hea, add_left_comm, add_comm, 
            add_self_YL, add_zero]
        · simp only [LinearEquiv.mul_apply]
          simp only [h1, hw, map_add, hda, hdb, add_left_comm, add_comm,
            add_self_add_YL]
  ·
    exfalso
    have hbraid : ∀ y ∈ W, d (e (d y)) = e (d (e y)) := by
      intro y hy
      rcases hd' y hy with h1 | h1 <;> rcases he' y hy with h2 | h2 <;>
      simp only [h1, h2, map_add, hda, hdb, hea, heb, add_left_comm, add_comm,
        add_self_add_YL]
    have h3 : ∀ w ∈ W, d (e (d (e (d (e w))))) = w := by
      intro w hw
      have hy : e (d (e w)) ∈ W := hW e he _ (hW d hd _ (hW e he w hw))
      rw [hbraid _ hy, hsq1 he, hsq1 hd, hsq1 he]
    have h4' : ∀ v, d (e (d (e (d (e (d (e v))))))) = v := by
      intro v
      have h := LinearEquiv.congr_fun (pow_orderOf_eq_one (d * e)) v
      rw [h4] at h
      simpa [pow_succ, LinearEquiv.mul_apply] using h
    have h1 : ∀ w ∈ W, d (e w) = w := by
      intro w hw
      have h := h4' w
      rwa [h3 w hw] at h
    apply hne
    rw [h1 _ (hW d hd _ (hW e he w₀ hw₀W)), h1 w₀ hw₀W]

theorem map_inv_YL {D : Set (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V}
    (hxD : ∀ d ∈ D, x⁻¹ * d * x ∈ D) {W : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) :
    ∀ d ∈ D, ∀ w ∈ W.map (x : V →ₗ[ZMod 2] V), d w ∈ W.map (x : V →ₗ[ZMod 2] V) := by
  rintro d hd _ ⟨w, hw, rfl⟩
  refine ⟨(x⁻¹ * d * x) w, hW _ (hxD d hd) w hw, ?_⟩
  simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply]
  exact x.apply_symm_apply _

theorem point_map_YL {t x : V ≃ₗ[ZMod 2] V} (hxt : x * t = t * x) {W : Submodule (ZMod 2) V}
    {p : V} (hp : p ∈ W ⊓ commSpace t) (huniq : ∀ v ∈ W ⊓ commSpace t, v = 0 ∨ v = p) :
    x p ∈ W.map (x : V →ₗ[ZMod 2] V) ⊓ commSpace t ∧
      ∀ v ∈ W.map (x : V →ₗ[ZMod 2] V) ⊓ commSpace t, v = 0 ∨ v = x p := by
  refine ⟨⟨⟨p, (Submodule.mem_inf.mp hp).1, rfl⟩,
    map_mem_commSpace_of_commute_YL hxt (Submodule.mem_inf.mp hp).2⟩, ?_⟩
  rintro v ⟨⟨u, hu, rfl⟩, hv⟩
  have hxinv : x⁻¹ * t = t * x⁻¹ := (Commute.inv_left (show Commute x t from hxt)).eq
  have hut : u ∈ commSpace t := by
    have := map_mem_commSpace_of_commute_YL hxinv hv
    simpa [LinearEquiv.coe_coe] using this
  rcases huniq u ⟨hu, hut⟩ with rfl | rfl
  · left
    simp
  · right
    rfl

theorem apply_eq_of_apply_apply_eq_YL {x : V ≃ₗ[ZMod 2] V} {k : ℕ} (hxk : x ^ (3 ^ k) = 1)
    {p : V} (h2 : x (x p) = p) : x p = p := by
  obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have h2j : ∀ i : ℕ, (x ^ (2 * i)) p = p := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, LinearEquiv.mul_apply, pow_two,
        LinearEquiv.mul_apply, h2, ih]
  have h := LinearEquiv.congr_fun hxk p
  rw [hj, pow_succ', LinearEquiv.mul_apply, h2j j] at h
  exact h

theorem compl_of_points_YL [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {D : Set (V ≃ₗ[ZMod 2] V)} {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ D) (htA : IsTypeA q t 2) (hinvol : ∀ d ∈ D, d * d = 1)
    (hisom : ∀ d ∈ D, ∀ v, q (d v) = q v) (hconj : ∀ d ∈ D, ∃ g ∈ closure D, g * t * g⁻¹ = d)
    (hfix : ∀ v, (∀ d ∈ D, d v = v) → v = 0) {W W' : Submodule (ZMod 2) V}
    (hW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W) (hW' : ∀ d ∈ D, ∀ w ∈ W', d w ∈ W') {p p' : V}
    (hp : p ∈ W ⊓ commSpace t) (hp' : p' ∈ W' ⊓ commSpace t) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0)
    (huniq : ∀ v ∈ W ⊓ commSpace t, v = 0 ∨ v = p)
    (huniq' : ∀ v ∈ W' ⊓ commSpace t, v = 0 ∨ v = p') (hpp : p ≠ p') :
    W ⊓ W' = ⊥ ∧ W ⊔ W' = ⊤ := by
  constructor
  · refine eq_bot_of_inf_eq_bot_YL ht hinvol hconj hfix
      (fun d hd w hw => ⟨hW d hd w hw.1, hW' d hd w hw.2⟩) ?_
    rw [eq_bot_iff]
    rintro v ⟨⟨hvW, hvW'⟩, hvt⟩
    rw [Submodule.mem_bot]
    rcases huniq v ⟨hvW, hvt⟩ with h | rfl
    · exact h
    · rcases huniq' v ⟨hvW', hvt⟩ with h | h
      · exact h
      · exact absurd h hpp
  · refine eq_top_of_le_YL hq hinvol hisom hconj hfix (fun d hd w hw => ?_) ?_
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      exact Submodule.add_mem_sup (hW d hd y hy) (hW' d hd z hz)
    · rw [← span_pair_eq_YL htA.2.2.2.1 (Submodule.mem_inf.mp hp).2 (Submodule.mem_inf.mp hp').2
        hp0 hp'0 hpp, Submodule.span_le]
      rintro y (rfl | rfl)
      · exact Submodule.mem_sup_left (Submodule.mem_inf.mp hp).1
      · exact Submodule.mem_sup_right (Submodule.mem_inf.mp hp').1

end AS35YL

end CFSG.LargeExtraspecial
