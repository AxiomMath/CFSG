module

public import CFSG.LargeExtraspecial.S111CMain
public import CFSG.LargeExtraspecial.S14Early

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

structure IsoCfg (S : Setting G) (t y : S.O) : Prop where
  t_mem : t ∈ S.Mbar
  y_mem : y ∈ S.Mbar
  dec : ∀ x ∈ S.Mbar, ∃ u : S.O, (u = 1 ∨ u = y ∨ u = y⁻¹) ∧ (u⁻¹ * x) * t = t * (u⁻¹ * x)
  comm : ∀ x ∈ S.Mbar, x * y = y * x ∨ (t * x) * y = y * (t * x)

theorem IsoCfg.u_mem {t y : S.O} (C : IsoCfg S t y) {u : S.O} (hu : u = 1 ∨ u = y ∨ u = y⁻¹) :
    u ∈ S.Mbar := by
  rcases hu with rfl | rfl | rfl
  · exact one_mem _
  · exact C.y_mem
  · exact inv_mem C.y_mem

theorem apply_mem_Vt' (haQ : g * S.z * g⁻¹ ∈ S.QG) {t x : S.O} (hx : x ∈ S.Mbar)
    (hxt : x * t = t * x) {v : S.Qt} (hv : v ∈ Vt S g t) :
    ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  obtain ⟨k, rfl⟩ := hx
  exact S4.apply_mem_Vt haQ hxt hv

theorem O_mul_apply (x y : S.O) (v : S.Qt) :
    ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem polar_O_apply (x : S.O) (v w : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      polar S.q v w := by
  simp only [polar, ← map_add]
  rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2]

theorem span_translates_eq_top (hirr : ¬ S.IsReducible) {s : Set S.Qt} {v : S.Qt} (hv : v ∈ s)
    (hv0 : v ≠ 0) :
    Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ s,
      w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} = ⊤ := by
  set X := Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ s,
    w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} with hX
  have hinv : ∀ x ∈ S.Mbar, ∀ u ∈ X, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ X := by
    intro x hx u hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x', hx', u', hu', rfl⟩ := hw
      exact Submodule.subset_span ⟨x * x', mul_mem hx hx', u', hu', (O_mul_apply x x' u').symm⟩
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul r w _ h => rw [map_smul]; exact Submodule.smul_mem _ r h
  rcases S14.irr_of_not_isReducible hirr X hinv with h | h
  · exfalso
    have hvX : v ∈ X := Submodule.subset_span ⟨1, one_mem _, v, hv, rfl⟩
    rw [h, Submodule.mem_bot] at hvX
    exact hv0 hvX
  · exact h

theorem IsoCfg.rbar_ne {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g) (hirr : ¬ S.IsReducible)
    (h6 : 6 ≤ S.width) (ht : t ∈ S.Lbar g) : Rbar S g t ≠ S.Lbar g := by
  classical
  intro hR
  have haQ := hy.hyp4.conj_mem
  set a := S.cl (g * S.z * g⁻¹) with ha
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have hVle := Vt_le_span_of_Rbar_eq hy.hyp4 hy.cons hR
  have hfix : ∀ x ∈ S.Mbar, x * t = t * x → ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    intro x hx hxt
    have h1 : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈ (ZMod 2) ∙ a :=
      hVle (apply_mem_Vt' haQ hx hxt (cl_a_mem_Vt ht))
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h1
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases r with rfl | rfl
    · exfalso
      rw [zero_smul] at hr
      exact ha0 (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).injective (by rw [← hr, map_zero]))
    · rw [one_smul] at hr
      exact hr.symm
  have htop := span_translates_eq_top hirr (Set.mem_singleton a) ha0
  set T : Finset S.Qt := {a, ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a,
    ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a} with hT
  have hle : Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ ({a} : Set S.Qt),
      w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} ≤ Submodule.span (ZMod 2) (T : Set S.Qt) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    obtain ⟨u, hu, hut⟩ := C.dec x hx
    have hc : u⁻¹ * x ∈ S.Mbar := mul_mem (inv_mem (C.u_mem hu)) hx
    have hxa : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
      have h1 := hfix _ hc hut
      rw [O_mul_apply] at h1
      calc ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a
          = ((u * (u⁻¹ * x) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rw [mul_inv_cancel_left]
        _ = ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rw [O_mul_apply, O_mul_apply, h1]
    rw [hxa]
    apply Submodule.subset_span
    rcases hu with rfl | rfl | rfl <;> simp [hT]
  have h1 := Submodule.finrank_mono hle
  rw [htop, finrank_top, S.finrank_Qt_eq_two_mul_width] at h1
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) (T : Set S.Qt)) ≤ T.card :=
    finrank_span_finset_le_card (R := ZMod 2) T
  have h3 : T.card ≤ 3 := Finset.card_le_three
  omega

theorem exists_moved (hy : Hyp S g) {t : S.O} (ht : t ∈ S.Lbar g) (hL : LinCase S g ht) :
    ∃ x ∈ Rbar S g t, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      S.cl (g * S.z * g⁻¹) := by
  have ha0 := cl_conj_z_ne_zero S hy.hyp4.conj_mem hy.hyp4.conj_ne
  obtain ⟨v, hvV, hva⟩ : ∃ v ∈ Vt S g t, v ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    by_contra hcon
    push Not at hcon
    have h1 := Submodule.finrank_mono (show Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) from hcon)
    rw [finrank_span_singleton ha0] at h1
    have := hL.two_le_finrank
    omega
  have hv0 : (⟨v, hvV⟩ : Vt S g t) ≠ 0 := fun h => hva (by
    have : v = 0 := congrArg Subtype.val h
    rw [this]
    exact zero_mem _)
  obtain ⟨x, hx, hxv⟩ := hL.mem_orbit ⟨v, hvV⟩ hv0
  refine ⟨x, hx, fun h => hva ?_⟩
  rw [show v = _ from hxv, h]
  exact Submodule.mem_span_singleton_self _

theorem apply_eq_self_of_linCase (hy : Hyp S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hL : LinCase S g ht) {v : S.Qt} (hv : v ∈ Vt S g t) :
    ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have haQ := hy.hyp4.conj_mem
  set a := S.cl (g * S.z * g⁻¹) with ha
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have htR : t ∈ Rbar S g t := Lbar_le_Rbar ht ht
  have hcentre : ∀ u ∈ Vt S g t, ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ (ZMod 2) ∙ a := by
    intro u hu
    have he : resV haQ t ⟨t, htR⟩ ∈ LmodN S g t := ⟨t, ht, fun w => rfl⟩
    rw [hL.LmodN_eq] at he
    have he' : ∀ w : Vt S g t, resV haQ t ⟨t, htR⟩ w - w ∈ (ZMod 2) ∙ aV ht := he
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (he' ⟨u, hu⟩)
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    have := congrArg Subtype.val hr
    simpa [coe_resV_apply, aV] using this
  obtain ⟨x, hxR, hxa⟩ := exists_moved hy ht hL
  have hxM := Rbar_le_Mbar hxR
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (Rbar_le_centralizer haQ hxR)
  have hxit : x⁻¹ * t = t * x⁻¹ := by
    calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt]
      _ = t * x⁻¹ := by group
  have hu' := apply_mem_Vt' haQ (inv_mem hxM) hxit hv
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hcentre _ hu')
  have h3 : ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      (ZMod 2) ∙ ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    have e1 : t = x * t * x⁻¹ := by rw [hxt]; group
    rw [← map_smul, hr, map_sub, ← O_mul_apply, ← O_mul_apply, ← O_mul_apply, ← e1,
      mul_inv_cancel]
    rfl
  exact sub_eq_zero.mp (eq_zero_of_mem_span_of_mem_span ha0 (Ne.symm hxa) (hcentre v hv) h3)

theorem IsoCfg.exists_realize {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (ht : t ∈ S.Lbar g) (hL : LinCase S g ht) (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) :
    ∃ c : S.O, c ∈ S.Mbar ∧ c * t = t * c ∧ c * y = y * c ∧
      ∀ w : Vt S g t, ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = e w := by
  have haQ := hy.hyp4.conj_mem
  have he : e ∈ RmodN S g t := by rw [hL.eq_top]; exact mem_top e
  obtain ⟨x, hxR, hx⟩ := mem_RmodN.mp he
  have hxM := Rbar_le_Mbar hxR
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (Rbar_le_centralizer haQ hxR)
  rcases C.comm x hxM with h | h
  · exact ⟨x, hxM, hxt, h, fun w => (hx w).symm⟩
  · refine ⟨t * x, mul_mem C.t_mem hxM, by rw [mul_assoc, hxt], h, fun w => ?_⟩
    rw [O_mul_apply, ← hx w]
    exact apply_eq_self_of_linCase hy ht hL (e w).2

theorem IsoCfg.four_le_finrank {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (hirr : ¬ S.IsReducible) (h6 : 6 ≤ S.width) (ht : t ∈ S.Lbar g) :
    4 ≤ finrank (ZMod 2) (Vt S g t) := by
  have haQ := hy.hyp4.conj_mem
  have ha0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have htop := span_translates_eq_top hirr (s := (Vt S g t : Set S.Qt)) (cl_a_mem_Vt ht) ha0
  set fy : S.Qt →ₗ[ZMod 2] S.Qt :=
    (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) with hfy
  set fy' : S.Qt →ₗ[ZMod 2] S.Qt :=
    (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) with hfy'
  have hle : Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ (Vt S g t : Set S.Qt),
      w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} ≤
      Vt S g t ⊔ (Vt S g t).map fy ⊔ (Vt S g t).map fy' := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, v, hv, rfl⟩
    obtain ⟨u, hu, hut⟩ := C.dec x hx
    have hcv := apply_mem_Vt' haQ (mul_mem (inv_mem (C.u_mem hu)) hx) hut hv
    have e1 : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((u⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      rw [← O_mul_apply, mul_inv_cancel_left]
    rw [e1]
    rcases hu with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (by simpa using hcv))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, hcv, rfl⟩)
    · exact Submodule.mem_sup_right ⟨_, hcv, rfl⟩
  have h1 := Submodule.finrank_mono hle
  rw [htop, finrank_top, S.finrank_Qt_eq_two_mul_width] at h1
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (Vt S g t ⊔ (Vt S g t).map fy) ((Vt S g t).map fy')
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (Vt S g t) ((Vt S g t).map fy)
  have h4 := Submodule.finrank_map_le fy (Vt S g t)
  have h5 := Submodule.finrank_map_le fy' (Vt S g t)
  omega

omit [Finite G] in
theorem eq_zero_of_invariant {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (h3 : 3 ≤ finrank (ZMod 2) V) (B : V → V → ZMod 2)
    (hadd : ∀ v s w, B (v + s) w = B v w + B s w)
    (hinv : ∀ (e : V ≃ₗ[ZMod 2] V) v w, B (e v) (e w) = B v w) (s w : V) : B s w = 0 := by
  classical
  have hlt : Submodule.span (ZMod 2) ({s, w} : Set V) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have h1 := finrank_span_le_card (R := ZMod 2) ({s, w} : Set V)
    have h2 : (({s, w} : Set V)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_insert_le _ _
    rw [h, finrank_top] at h1
    omega
  obtain ⟨φ, hφ0, hpφ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have hφs : φ s = 0 := hpφ (Submodule.subset_span (by simp))
  have hφw : φ w = 0 := hpφ (Submodule.subset_span (by simp))
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (LinearMap.ext hcon)
  have hv1 : φ v = 1 := (CFSG.RankThree.Literature.FSmith.zmod2_cases _).resolve_left hv
  have h := hinv (LinearEquiv.transvection (f := φ) (v := s) hφs) v w
  rw [LinearEquiv.transvection.apply, LinearEquiv.transvection.apply, hv1, hφw, one_smul,
    zero_smul, add_zero, hadd] at h
  simpa using h

theorem IsoCfg.exists_decomp {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (hirr : ¬ S.IsReducible) (ht : t ∈ S.Lbar g) (x : S.Qt) :
    ∃ v₁ ∈ Vt S g t, ∃ v₂ ∈ Vt S g t, ∃ v₃ ∈ Vt S g t,
      x = v₁ + ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₂ +
        ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₃ := by
  have haQ := hy.hyp4.conj_mem
  have ha0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have htop := span_translates_eq_top hirr (s := (Vt S g t : Set S.Qt)) (cl_a_mem_Vt ht) ha0
  set W : Submodule (ZMod 2) S.Qt :=
    { carrier := {x | ∃ v₁ ∈ Vt S g t, ∃ v₂ ∈ Vt S g t, ∃ v₃ ∈ Vt S g t,
        x = v₁ + ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₂ +
          ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v₃}
      add_mem' := by
        rintro _ _ ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩
        refine ⟨a₁ + b₁, add_mem ha₁ hb₁, a₂ + b₂, add_mem ha₂ hb₂, a₃ + b₃, add_mem ha₃ hb₃,
          ?_⟩
        rw [map_add, map_add]
        abel
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro r _ ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, rfl⟩
        refine ⟨r • a₁, Submodule.smul_mem _ r ha₁, r • a₂, Submodule.smul_mem _ r ha₂,
          r • a₃, Submodule.smul_mem _ r ha₃, ?_⟩
        rw [map_smul, map_smul, smul_add, smul_add] } with hW
  have hle : Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ (Vt S g t : Set S.Qt),
      w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, v, hv, rfl⟩
    obtain ⟨u, hu, hut⟩ := C.dec x hx
    have hcv := apply_mem_Vt' haQ (mul_mem (inv_mem (C.u_mem hu)) hx) hut hv
    have e1 : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((u⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      rw [← O_mul_apply, mul_inv_cancel_left]
    rw [e1]
    rcases hu with rfl | rfl | rfl
    · exact ⟨_, by simpa using hcv, 0, zero_mem _, 0, zero_mem _, by simp⟩
    · exact ⟨0, zero_mem _, _, hcv, 0, zero_mem _, by simp⟩
    · exact ⟨0, zero_mem _, 0, zero_mem _, _, hcv, by simp⟩
  have hx : x ∈ W := hle (htop ▸ Submodule.mem_top)
  exact hx

theorem IsoCfg.polar_eq_zero {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)) (ht : t ∈ S.Lbar g) (hL : LinCase S g ht)
    {u : S.O} (hu : u = 1 ∨ u = y ∨ u = y⁻¹) {v w : S.Qt} (hv : v ∈ Vt S g t)
    (hw : w ∈ Vt S g t) : polar S.q v (((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = 0 := by
  have hcomm : ∀ c : S.O, c * y = y * c → c * u = u * c := by
    intro c hc
    rcases hu with rfl | rfl | rfl
    · simp
    · exact hc
    · calc c * y⁻¹ = y⁻¹ * (y * c) * y⁻¹ := by group
        _ = y⁻¹ * (c * y) * y⁻¹ := by rw [hc]
        _ = y⁻¹ * c := by group
  have key := eq_zero_of_invariant h3
    (fun a b : Vt S g t => polar S.q (a : S.Qt) (((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) b))
    (fun a b c => by simp [polar_add_left])
    (fun e a b => by
      obtain ⟨c, -, -, hcy, hce⟩ := C.exists_realize hy ht hL e
      rw [← hce a, ← hce b, ← O_mul_apply, ← hcomm c hcy, O_mul_apply, polar_O_apply])
    ⟨v, hv⟩ ⟨w, hw⟩
  exact key

theorem IsoCfg.false_of_linCase {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (hirr : ¬ S.IsReducible) (h6 : 6 ≤ S.width) (ht : t ∈ S.Lbar g) (hL : LinCase S g ht) :
    False := by
  have haQ := hy.hyp4.conj_mem
  have ha0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := C.four_le_finrank hy hirr h6 ht
    omega
  have haV := cl_a_mem_Vt ht
  apply ha0
  refine S.q_nondegenerate.1 _ fun x => ?_
  rw [polarBilin_apply_apply]
  obtain ⟨v₁, h₁, v₂, h₂, v₃, h₃, rfl⟩ := C.exists_decomp hy hirr ht x
  rw [polar_add_right, polar_add_right,
    C.polar_eq_zero hy h3 ht hL (Or.inr (Or.inl rfl)) haV h₂,
    C.polar_eq_zero hy h3 ht hL (Or.inr (Or.inr rfl)) haV h₃]
  have h1 := C.polar_eq_zero hy h3 ht hL (Or.inl rfl) haV h₁
  simp only [OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h1
  rw [h1, add_zero, add_zero]

end CFSG.LargeExtraspecial.S11
