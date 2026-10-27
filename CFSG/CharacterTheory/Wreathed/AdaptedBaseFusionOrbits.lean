module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionAction

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

universe u v

section Group

variable {M : Type v} [Group M]

theorem mem_orbit_iff_exists {H : Subgroup (MulAut M)} {x y : M} :
    y ∈ MulAction.orbit H x ↔ ∃ φ ∈ H, φ x = y := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨φ, hφ⟩, rfl⟩
    exact ⟨φ, hφ, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨⟨φ, hφ⟩, rfl⟩

theorem zpowers_mul_inf_left_eq_bot {x y : M} (hc : Commute x y)
    (hord : orderOf x = orderOf y) (hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Subgroup.zpowers (x * y) ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz2
  rw [Subgroup.mem_bot]
  have hyi : y ^ i ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
    refine ⟨?_, Subgroup.zpow_mem_zpowers y i⟩
    have hyx : y ^ i = x ^ (j - i) := by
      rw [zpow_sub, hj, hc.mul_zpow, (hc.zpow_zpow i i).eq, mul_inv_cancel_right]
    rw [hyx]
    exact Subgroup.zpow_mem_zpowers x _
  rw [hinf, Subgroup.mem_bot] at hyi
  have hxi : x ^ i = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hord, orderOf_dvd_iff_zpow_eq_one]
    exact hyi
  rw [hc.mul_zpow, hxi, hyi, one_mul]

theorem orderOf_mul_of_inf_eq_bot {x y : M} (hc : Commute x y)
    (hord : orderOf x = orderOf y) (hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    orderOf (x * y) = orderOf x := by
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  rw [hc.mul_pow]
  constructor
  · intro h1
    have hmem : x ^ k ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
      refine ⟨Subgroup.npow_mem_zpowers x k, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y k)
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  · intro h1
    have hy : y ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hord, orderOf_dvd_iff_pow_eq_one]
      exact h1
    rw [h1, hy, one_mul]

end Group

variable {G : Type u} [Group G]

theorem coe_mem_zpowers {K : Subgroup G} {x y : K} (hx : x ∈ Subgroup.zpowers y) :
    (x : G) ∈ Subgroup.zpowers (y : G) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, (Subgroup.coe_zpow _ y k).symm⟩

theorem conjAut_pow_eq_one_iff (U : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) (k : ℕ) :
    conjAut U hx ^ k = 1 ↔ x⁻¹ ^ k ∈ Subgroup.centralizer (U : Set G) := by
  rw [conjAut, ← map_pow, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
    Subgroup.mem_subgroupOf, Subgroup.coe_pow]

namespace IsAdaptedBase

variable {U : Subgroup G} {a w σ υ g : G} (h : IsAdaptedBase U a w σ υ g)

@[expose] def exc : Set U :=
  (Subgroup.zpowers (h.left * h.right) : Set U) ∪ Subgroup.zpowers h.left ∪
    Subgroup.zpowers h.right

theorem aut_zpow_left (k : ℤ) : h.aut (h.left ^ k) = h.right ^ k := by
  rw [map_zpow, h.aut_left]

theorem aut_zpow_right (k : ℤ) : h.aut (h.right ^ k) = (h.left * h.right) ^ (-k) := by
  rw [map_zpow, h.aut_right, inv_zpow']

theorem aut_zpow_mul (k : ℤ) : h.aut ((h.left * h.right) ^ k) = h.left ^ (-k) := by
  rw [map_zpow, h.aut_left_mul_right, inv_zpow']

theorem aut_mem_exc {x : U} (hx : x ∈ h.exc) : h.aut x ∈ h.exc := by
  rcases hx with (hx | hx) | hx <;> obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  · rw [aut_zpow_mul]
    exact Or.inl (Or.inr (Subgroup.zpow_mem_zpowers _ _))
  · rw [aut_zpow_left]
    exact Or.inr (Subgroup.zpow_mem_zpowers _ _)
  · rw [aut_zpow_right]
    exact Or.inl (Or.inl (Subgroup.zpow_mem_zpowers _ _))

theorem aut_aut_aut (x : U) : h.aut (h.aut (h.aut x)) = x := by
  simpa only [MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun h.aut_cube x

end IsAdaptedBase

variable {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)
include h

section Values

theorem commute_left_right : Commute h.left h.right := mul_comm_base S e _ _

theorem swapAut_zpow_mul (k : ℤ) :
    swapAut S e ((h.left * h.right) ^ k) = (h.left * h.right) ^ k := by
  rw [map_zpow, swapAut_left_mul_right h]

theorem swapAut_zpow_left (k : ℤ) : swapAut S e (h.left ^ k) = h.right ^ k := by
  rw [map_zpow, swapAut_left h]

theorem swapAut_zpow_right (k : ℤ) : swapAut S e (h.right ^ k) = h.left ^ k := by
  rw [map_zpow, swapAut_right h]

theorem swapAut_mem_exc {x : modelBase S e} (hx : x ∈ h.exc) : swapAut S e x ∈ h.exc := by
  rcases hx with (hx | hx) | hx <;> obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  · rw [swapAut_zpow_mul h]
    exact Or.inl (Or.inl (Subgroup.zpow_mem_zpowers _ _))
  · rw [swapAut_zpow_left h]
    exact Or.inr (Subgroup.zpow_mem_zpowers _ _)
  · rw [swapAut_zpow_right h]
    exact Or.inl (Or.inr (Subgroup.zpow_mem_zpowers _ _))

theorem swapAut_swapAut (x : modelBase S e) : swapAut S e (swapAut S e x) = x := by
  simpa only [MulAut.mul_apply, MulAut.one_apply] using
    DFunLike.congr_fun (swapAut_mul_self h) x

theorem aut_swapAut (x : modelBase S e) :
    h.aut (swapAut S e x) = swapAut S e (h.aut (h.aut x)) := by
  simpa only [MulAut.mul_apply] using DFunLike.congr_fun (aut_mul_swapAut h) x

theorem mem_exc_of_mem_closure {φ : MulAut (modelBase S e)}
    (hφ : φ ∈ Subgroup.closure {swapAut S e, h.aut}) {x : modelBase S e} (hx : x ∈ h.exc) :
    φ x ∈ h.exc := by
  rcases mem_closure_swapAut_aut h hφ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx
  · exact h.aut_mem_exc hx
  · exact h.aut_mem_exc (h.aut_mem_exc hx)
  · exact swapAut_mem_exc h hx
  · exact swapAut_mem_exc h (h.aut_mem_exc hx)
  · exact swapAut_mem_exc h (h.aut_mem_exc (h.aut_mem_exc hx))

theorem orbit_zpow_mul (k : ℤ) :
    MulAction.orbit (Subgroup.closure {swapAut S e, h.aut}) ((h.left * h.right) ^ k) =
      {(h.left * h.right) ^ k, h.left ^ (-k), h.right ^ (-k)} := by
  have hα : swapAut S e ∈ Subgroup.closure {swapAut S e, h.aut} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hβ : h.aut ∈ Subgroup.closure {swapAut S e, h.aut} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  ext y
  rw [mem_orbit_iff_exists, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rcases mem_closure_swapAut_aut h hφ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (h.aut_zpow_mul k))
    · refine Or.inr (Or.inr ?_)
      change h.aut (h.aut _) = _
      rw [h.aut_zpow_mul, h.aut_zpow_left]
    · exact Or.inl (swapAut_zpow_mul h k)
    · refine Or.inr (Or.inr ?_)
      change swapAut S e (h.aut _) = _
      rw [h.aut_zpow_mul, swapAut_zpow_left h]
    · refine Or.inr (Or.inl ?_)
      change swapAut S e (h.aut (h.aut _)) = _
      rw [h.aut_zpow_mul, h.aut_zpow_left, swapAut_zpow_right h]
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · exact ⟨h.aut, hβ, h.aut_zpow_mul k⟩
    · refine ⟨h.aut * h.aut, Subgroup.mul_mem _ hβ hβ, ?_⟩
      change h.aut (h.aut _) = _
      rw [h.aut_zpow_mul, h.aut_zpow_left]

theorem orbit_pow_mul (k : ℕ) :
    MulAction.orbit (Subgroup.closure {swapAut S e, h.aut}) ((h.left * h.right) ^ k) =
      {(h.left * h.right) ^ k, (h.left ^ k)⁻¹, (h.right ^ k)⁻¹} := by
  have h' := orbit_zpow_mul h k
  rwa [zpow_natCast, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast] at h'

end Values

variable [Finite G]

section Intersections

theorem orderOf_left' : orderOf h.left = 2 ^ n := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_left h

theorem orderOf_right' : orderOf h.right = 2 ^ n := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_right h

theorem zpowers_left_inf_right' :
    Subgroup.zpowers h.left ⊓ Subgroup.zpowers h.right = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hmem : (x : G) ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers υ :=
    ⟨coe_mem_zpowers hx1, coe_mem_zpowers hx2⟩
  rw [zpowers_left_inf_right h, Subgroup.mem_bot] at hmem
  exact hmem

theorem zpowers_mul_inf_left :
    Subgroup.zpowers (h.left * h.right) ⊓ Subgroup.zpowers h.left = ⊥ :=
  zpowers_mul_inf_left_eq_bot (commute_left_right h)
    (by rw [orderOf_left' h, orderOf_right' h]) (zpowers_left_inf_right' h)

theorem zpowers_mul_inf_right :
    Subgroup.zpowers (h.left * h.right) ⊓ Subgroup.zpowers h.right = ⊥ := by
  rw [(commute_left_right h).eq]
  apply zpowers_mul_inf_left_eq_bot (commute_left_right h).symm
    (by rw [orderOf_left' h, orderOf_right' h])
  rw [inf_comm]
  exact zpowers_left_inf_right' h

theorem orderOf_mul' : orderOf (h.left * h.right) = 2 ^ n := by
  rw [orderOf_mul_of_inf_eq_bot (commute_left_right h)
    (by rw [orderOf_left' h, orderOf_right' h]) (zpowers_left_inf_right' h), orderOf_left' h]

theorem orbit_pow_mul_injOn :
    Set.InjOn
      (fun k : ℕ => MulAction.orbit (Subgroup.closure {swapAut S e, h.aut})
        ((h.left * h.right) ^ k)) (Set.Ico 1 (2 ^ n)) := by
  intro k hk l hl hkl
  have hmem : (h.left * h.right) ^ l ∈ MulAction.orbit (Subgroup.closure {swapAut S e, h.aut})
      ((h.left * h.right) ^ k) := by
    change _ ∈ (fun k : ℕ => MulAction.orbit (Subgroup.closure {swapAut S e, h.aut})
      ((h.left * h.right) ^ k)) k
    rw [hkl]
    exact MulAction.mem_orbit_self _
  rw [orbit_pow_mul h, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hl1 := hl.1
  have hl2 := hl.2
  have hk2 := hk.2
  have hbot : ∀ K : Subgroup (modelBase S e),
      Subgroup.zpowers (h.left * h.right) ⊓ K = ⊥ → (h.left * h.right) ^ l ∈ K → False := by
    intro K hK hlK
    have hmem' : (h.left * h.right) ^ l ∈ Subgroup.zpowers (h.left * h.right) ⊓ K :=
      ⟨Subgroup.npow_mem_zpowers _ _, hlK⟩
    rw [hK, Subgroup.mem_bot] at hmem'
    have hdvd := orderOf_dvd_of_pow_eq_one hmem'
    rw [orderOf_mul' h] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases hmem with h1 | h1 | h1
  · have hmod := pow_inj_mod.mp h1
    rw [orderOf_mul' h, Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hk2] at hmod
    exact hmod.symm
  · exact (hbot _ (zpowers_mul_inf_left h)
      (by rw [h1]; exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))).elim
  · exact (hbot _ (zpowers_mul_inf_right h)
      (by rw [h1]; exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))).elim

end Intersections

section FixedPoints

theorem eq_one_of_aut_fixed (hn : 2 ≤ n) {x : modelBase S e} (hx : h.aut x = x) : x = 1 := by
  have hkN : g⁻¹ ∈ Subgroup.normalizer (modelBase S e : Set G) :=
    (Subgroup.normalizer _).inv_mem h.mem_normalizer
  have hk3 : g⁻¹ ^ 3 ∈ Subgroup.centralizer (modelBase S e : Set G) := by
    have h3 : h.aut ^ 3 = 1 := by
      rw [pow_succ, pow_two, mul_assoc]
      exact h.aut_cube
    rw [IsAdaptedBase.aut, conjAut_pow_eq_one_iff] at h3
    exact h3
  have hk1 : g⁻¹ ∉ Subgroup.centralizer (modelBase S e : Set G) := by
    intro hg
    have h1 : h.aut ^ 1 = 1 := by
      rw [IsAdaptedBase.aut, conjAut_pow_eq_one_iff, pow_one]
      exact hg
    have hord := orderOf_aut h
    rw [pow_one] at h1
    rw [h1, orderOf_one] at hord
    omega
  apply Subtype.ext
  apply eq_one_of_conj_fixed S e hn hkN hk3 hk1 x.2
  rw [inv_inv]
  have hval := congrArg Subtype.val hx
  rw [h.aut_apply_coe] at hval
  exact hval

omit [Finite G] in
theorem mem_zpowers_of_swapAut_fixed (hn : 1 ≤ n) {x : modelBase S e}
    (hx : swapAut S e x = x) : x ∈ Subgroup.zpowers (h.left * h.right) := by
  set T := wreathModelHom S e (Original.z (2 ^ n))
  have hc : (x : G) * T = T * x := by
    have hval := congrArg Subtype.val hx
    rw [swapAut_apply_coe] at hval
    calc (x : G) * T = T * (T⁻¹ * x * T) := by group
      _ = T * x := by rw [hval]
  have hZ := mem_modelCenter_of_commute_outside S e hn x.2 (wreathModelHom_mem S e _)
    (modelHom_z_not_mem_modelBase S e) hc
  rw [modelCenter_eq_zpowers] at hZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hZ
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow, h.coe_left_mul_right]
  exact hk

theorem eq_one_of_fixed_of_not_mem_exc (hn : 2 ≤ n) {φ : MulAut (modelBase S e)}
    (hφ : φ ∈ Subgroup.closure {swapAut S e, h.aut}) {x : modelBase S e} (hxE : x ∉ h.exc)
    (hfix : φ x = x) : φ = 1 := by
  have hn1 : 1 ≤ n := by omega
  have hE1 : (1 : modelBase S e) ∈ h.exc := Or.inr (Subgroup.one_mem _)
  have haE : ∀ y ∈ Subgroup.zpowers (h.left * h.right), y ∈ h.exc :=
    fun y hy => Or.inl (Or.inl hy)
  have haE' : ∀ k : ℤ, h.aut ((h.left * h.right) ^ k) ∈ Subgroup.zpowers h.left := by
    intro k
    rw [h.aut_zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  have haE'' : ∀ k : ℤ, h.aut (h.aut ((h.left * h.right) ^ k)) ∈ Subgroup.zpowers h.right := by
    intro k
    rw [h.aut_zpow_mul, h.aut_zpow_left]
    exact Subgroup.zpow_mem_zpowers _ _
  rcases mem_closure_swapAut_aut h hφ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (eq_one_of_aut_fixed h hn hfix ▸ hE1) hxE
  ·
    have hβ : h.aut x = x := by
      have h3 := h.aut_aut_aut x
      change h.aut (h.aut x) = x at hfix
      rw [hfix] at h3
      exact h3
    exact absurd (eq_one_of_aut_fixed h hn hβ ▸ hE1) hxE
  · exact absurd (haE _ (mem_zpowers_of_swapAut_fixed h hn1 hfix)) hxE
  ·
    change swapAut S e (h.aut x) = x at hfix
    have hfix' : swapAut S e (h.aut (h.aut x)) = h.aut (h.aut x) := by
      rw [← aut_swapAut h, ← hfix, swapAut_swapAut h, hfix]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_swapAut_fixed h hn1 hfix')
    have hx : x = h.aut ((h.left * h.right) ^ k) := by rw [hk, h.aut_aut_aut]
    exact absurd (Or.inl (Or.inr (hx ▸ haE' k))) hxE
  ·
    change swapAut S e (h.aut (h.aut x)) = x at hfix
    have hfix' : swapAut S e (h.aut x) = h.aut x := by
      conv_rhs => rw [← hfix]
      rw [aut_swapAut h, h.aut_aut_aut]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_swapAut_fixed h hn1 hfix')
    have hx : x = h.aut (h.aut ((h.left * h.right) ^ k)) := by rw [hk, h.aut_aut_aut]
    exact absurd (Or.inr (hx ▸ haE'' k)) hxE

end FixedPoints

end CFSG.Wreathed.AdaptedBaseFusion
