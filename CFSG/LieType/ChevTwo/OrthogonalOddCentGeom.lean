module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.ChevTwo

open QuadraticMap Module

namespace OrthOddCentGeom

open CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {q : QuadraticForm (ZMod 2) U}

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem polar_self_eq_zero (x : U) : polar q x x = 0 := by
  rw [polar_self, two_nsmul]
  exact ZModModule.add_self _

theorem ne_zero_of_map_eq_one {a : U} (ha : q a = 1) : a ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at ha
  exact zero_ne_one ha

theorem exists_polar_eq_one_polar_eq_zero (hq : ∀ v, (∀ w, polar q v w = 0) → v = 0) {a b : U}
    (ha : a ≠ 0) (hab : a ≠ b) : ∃ c, polar q c a = 1 ∧ polar q c b = 0 := by
  by_contra! H
  obtain ⟨d, hd⟩ : ∃ d, polar q a d ≠ 0 := by
    by_contra! h
    exact ha (hq a h)
  apply hab
  rw [← sub_eq_zero]
  refine hq _ fun w => ?_
  have h3 := H (w + d)
  rw [polar_add_left, polar_add_left] at h3
  rw [polar_sub_left, polar_comm q a w, polar_comm q b w]
  rw [polar_comm] at hd
  have key : ∀ x y x' y' : ZMod 2, x' ≠ 0 → (x = 1 → y ≠ 0) → (x' = 1 → y' ≠ 0) →
      (x + x' = 1 → y + y' ≠ 0) → x - y = 0 := by decide
  exact key _ _ _ _ hd (H w) (H d) h3

variable {x y : U}

theorem reflect_mul_reflect_pow_three (hx : q x = 1) (hy : q y = 1) (hxy : polar q x y = 1) :
    (reflect q x * reflect q y) ^ 3 = 1 := by
  have e1 : reflect q x * reflect q y * reflect q x = reflect q (x + y) := by
    have h := reflect_conj (reflect_mem_orthogonalGroup q x) y
    rwa [reflect_inv, reflect_apply_of_map_eq_one hx, polar_comm, hxy, one_smul, add_comm y x]
      at h
  have e2 : reflect q y * reflect q x * reflect q y = reflect q (x + y) := by
    have h := reflect_conj (reflect_mem_orthogonalGroup q y) x
    rwa [reflect_inv, reflect_apply_of_map_eq_one hy, hxy, one_smul] at h
  calc (reflect q x * reflect q y) ^ 3
      = (reflect q x * reflect q y * reflect q x) * (reflect q y * reflect q x * reflect q y) := by
        rw [pow_three]
        simp only [mul_assoc]
    _ = 1 := by rw [e1, e2, reflect_mul_self]

theorem reflect_mul_reflect_ne_one (hx : q x = 1) (hy : q y = 1) (hxy : polar q x y = 1) :
    reflect q x * reflect q y ≠ 1 := by
  intro h
  have h' : reflect q x = reflect q y := by
    have := eq_inv_of_mul_eq_one_left h
    rwa [reflect_inv] at this
  have hxx := LinearEquiv.congr_fun h' x
  rw [reflect_apply_of_map_eq_one hx, reflect_apply_of_map_eq_one hy, polar_self_eq_zero, hxy,
    zero_smul, one_smul, add_zero] at hxx
  have hy0 : y = 0 := by simpa using hxx
  exact ne_zero_of_map_eq_one hy hy0

theorem orthogonal_normal_two_subgroup_aux [FiniteDimensional (ZMod 2) U]
    (q : QuadraticForm (ZMod 2) U)
    (hq : ∀ v, (∀ w, QuadraticMap.polar q v w = 0) → v = 0)
    (N : Subgroup (U ≃ₗ[ZMod 2] U)) (hN : N ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hNn : (N.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup q)).Normal) (hN2 : IsPGroup 2 N) :
    (∀ φ ∈ N, φ = 1) ∨
      (finrank (ZMod 2) U = 2 ∧ ∃ u : U, q u = 1 ∧ (∀ y, q y = 1 → y = u) ∧
        ∀ φ ∈ N, (∀ y, φ y = y) ∨ (∀ y, φ y = y + QuadraticMap.polar q y u • u)) := by
  have hconj : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup q, ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.normal_subgroupOf_iff hN).mp hNn n g hn hg
  have hodd : ∀ g ∈ N, g ^ 3 = 1 → g = 1 := by
    intro g hg h3
    obtain ⟨k, hk⟩ := hN2 ⟨g, hg⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k (by decide : Nat.Coprime 2 3))).mp
      ⟨hk', h3⟩
  have hthree : ∀ x y, q x = 1 → q y = 1 → polar q x y = 1 → reflect q x * reflect q y ∉ N :=
    fun x y hx hy hxy hmem => reflect_mul_reflect_ne_one hx hy hxy
      (hodd _ hmem (reflect_mul_reflect_pow_three hx hy hxy))
  have hO := reflect_mem_orthogonalGroup q
  have hA : ∀ φ ∈ N, ∀ a, q a = 1 → φ a = a := by
    intro φ hφ a ha
    have hφO := hN hφ
    have hb : q (φ a) = 1 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hφO]
      exact ha
    have hmem : reflect q (φ a) * reflect q a ∈ N := by
      have h1 := mul_mem hφ (hconj _ (hO a) _ (inv_mem hφ))
      have e : φ * (reflect q a * φ⁻¹ * (reflect q a)⁻¹) =
          (φ * reflect q a * φ⁻¹) * (reflect q a)⁻¹ := by group
      rwa [e, reflect_conj hφO, reflect_inv] at h1
    have hab : polar q (φ a) a = 0 := by
      rcases zmod_two_cases (polar q (φ a) a) with h | h
      · exact h
      · exact absurd hmem (hthree _ _ hb ha h)
    by_contra hne
    obtain ⟨c₀, hc₀a, hc₀b⟩ :=
      exists_polar_eq_one_polar_eq_zero hq (ne_zero_of_map_eq_one ha) (Ne.symm hne)
    obtain ⟨c, hc, hca, hcb⟩ : ∃ c, q c = 1 ∧ polar q c a = 1 ∧ polar q c (φ a) = 0 := by
      rcases zmod_two_cases (q c₀) with h | h
      · refine ⟨c₀ + φ a, ?_, ?_, ?_⟩
        · rw [QuadraticMap.map_add q, h, hb, hc₀b]
          decide
        · rw [polar_add_left, hc₀a, hab]
          decide
        · rw [polar_add_left, hc₀b, polar_self_eq_zero]
          decide
      · exact ⟨c₀, h, hc₀a, hc₀b⟩
    have hmem2 : reflect q (φ a) * reflect q (a + c) ∈ N := by
      have h1 := hconj _ (hO c) _ hmem
      have e1 := reflect_conj (hO c) (φ a)
      have e2 := reflect_conj (hO c) a
      rw [reflect_apply_of_map_eq_one hc, polar_comm, hcb, zero_smul, add_zero] at e1
      rw [reflect_apply_of_map_eq_one hc, polar_comm, hca, one_smul] at e2
      have e : reflect q c * (reflect q (φ a) * reflect q a) * (reflect q c)⁻¹ =
          (reflect q c * reflect q (φ a) * (reflect q c)⁻¹) *
            (reflect q c * reflect q a * (reflect q c)⁻¹) := by group
      rwa [e, e1, e2] at h1
    have hmem3 : reflect q a * reflect q (a + c) ∈ N := by
      have h1 := mul_mem (inv_mem hmem) hmem2
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left, reflect_inv] at h1
    have hac : q (a + c) = 1 := by
      rw [QuadraticMap.map_add q, ha, hc, polar_comm, hca]
      decide
    have hpac : polar q a (a + c) = 1 := by
      rw [polar_add_right, polar_self_eq_zero, polar_comm, hca]
      decide
    exact hthree _ _ ha hac hpac hmem3
  set S := Submodule.span (ZMod 2) {a : U | q a = 1}
  have hmemS : ∀ t, q t = 1 → t ∈ S := fun t ht => Submodule.subset_span ht
  by_cases hS : S = ⊤
  · left
    intro φ hφ
    have h := LinearMap.ext_on (f := (φ : U →ₗ[ZMod 2] U)) (g := LinearMap.id) hS
      fun a ha => hA φ hφ a ha
    ext y
    exact LinearMap.congr_fun h y
  right
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra! h
    exact hS (eq_top_iff.mpr fun x _ => h x)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv S.zero_mem
  have hqv : q v = 0 := by
    rcases zmod_two_cases (q v) with h | h
    · exact h
    · exact absurd (hmemS v h) hv
  have hvT : ∀ t, q t = 1 → polar q v t = 1 := by
    intro t ht
    rcases zmod_two_cases (polar q v t) with h | h
    · refine absurd ?_ hv
      have h1 : q (v + t) = 1 := by
        rw [QuadraticMap.map_add q, hqv, ht, h]
        decide
      have := S.sub_mem (hmemS _ h1) (hmemS t ht)
      rwa [add_sub_cancel_right] at this
    · exact h
  have hTT : ∀ t t', q t = 1 → q t' = 1 → polar q t t' = 0 := by
    intro t t' ht ht'
    rcases zmod_two_cases (polar q t t') with h | h
    · exact h
    · have h1 : q (t + t') = 1 := by
        rw [QuadraticMap.map_add q, ht, ht', h]
        decide
      have h2 := hvT _ h1
      rw [polar_add_right, hvT t ht, hvT t' ht'] at h2
      exact absurd h2 (by decide)
  obtain ⟨a, ha⟩ : ∃ a, q a = 1 := by
    obtain ⟨w, hw⟩ : ∃ w, polar q v w ≠ 0 := by
      by_contra! h
      exact hv0 (hq v h)
    rcases zmod_two_cases (q w) with h | h
    · refine ⟨v + w, ?_⟩
      rw [QuadraticMap.map_add q, hqv, h, zmod_two_eq_one_of_ne_zero hw]
      decide
    · exact ⟨w, h⟩
  have huniq : ∀ y, q y = 1 → y = a := by
    intro y hy
    by_contra hya
    obtain ⟨c, hcy, hca⟩ := exists_polar_eq_one_polar_eq_zero hq (ne_zero_of_map_eq_one hy) hya
    rcases zmod_two_cases (q c) with h | h
    · have h1 : q (c + a) = 1 := by
        rw [QuadraticMap.map_add q, h, ha, hca]
        decide
      have h2 := hTT _ _ h1 hy
      rw [polar_add_left, polar_comm q a y, hTT y a hy ha, hcy] at h2
      exact absurd h2 (by decide)
    · have h2 := hTT _ _ h hy
      rw [hcy] at h2
      exact absurd h2 (by decide)
  have hperp : ∀ z, polar q z a = 0 → z = 0 ∨ z = a := by
    intro z hz
    rcases zmod_two_cases (q z) with h | h
    · left
      have h1 : q (z + a) = 1 := by
        rw [QuadraticMap.map_add q, h, ha, hz]
        decide
      simpa using huniq _ h1
    · exact Or.inr (huniq z h)
  have hfour : ∀ y, y = 0 ∨ y = a ∨ y = v ∨ y = v + a := by
    intro y
    rcases zmod_two_cases (polar q y a) with h | h
    · rcases hperp y h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · have h1 : polar q (y + v) a = 0 := by
        rw [polar_add_left, h, hvT a ha]
        decide
      rcases hperp (y + v) h1 with h' | h'
      · rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h'
        exact Or.inr (Or.inr (Or.inl h'))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [← h', add_comm y v, ← add_assoc, ZModModule.add_self, zero_add]
  have hfin : finrank (ZMod 2) U = 2 := by
    have hli : LinearIndependent (ZMod 2) ![a, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · rw [zero_smul, one_smul, zero_add] at hst
        exact absurd hst hv0
      · rw [one_smul, zero_smul, add_zero] at hst
        exact absurd hst (ne_zero_of_map_eq_one ha)
      · rw [one_smul, one_smul, add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hst
        rw [hst, hqv] at ha
        exact absurd ha (by decide)
    have hsp : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ![a, v]) := by
      intro y _
      have ha' : a ∈ Submodule.span (ZMod 2) (Set.range ![a, v]) :=
        Submodule.subset_span ⟨0, rfl⟩
      have hv' : v ∈ Submodule.span (ZMod 2) (Set.range ![a, v]) :=
        Submodule.subset_span ⟨1, rfl⟩
      rcases hfour y with rfl | rfl | rfl | rfl
      · exact Submodule.zero_mem _
      · exact ha'
      · exact hv'
      · exact Submodule.add_mem _ hv' ha'
    rw [finrank_eq_card_basis (Basis.mk hli hsp), Fintype.card_fin]
  refine ⟨hfin, a, ha, huniq, fun φ hφ => ?_⟩
  have hφa := hA φ hφ a ha
  have hqφv : q (φ v) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hN hφ)]
    exact hqv
  have hφv0 : φ v ≠ 0 := fun h => hv0 (φ.injective (h.trans (map_zero φ).symm))
  rcases hfour (φ v) with h | h | h | h
  · exact absurd h hφv0
  · rw [h, ha] at hqφv
    exact absurd hqφv (by decide)
  · left
    intro y
    rcases hfour y with rfl | rfl | rfl | rfl
    · exact map_zero φ
    · exact hφa
    · exact h
    · rw [map_add, h, hφa]
  · right
    intro y
    rcases hfour y with rfl | rfl | rfl | rfl
    · rw [map_zero, polar_zero_left, zero_smul, add_zero]
    · rw [hφa, polar_self_eq_zero, zero_smul, add_zero]
    · rw [h, hvT a ha, one_smul]
    · rw [map_add, h, hφa, polar_add_left, hvT a ha, polar_self_eq_zero, add_zero, one_smul]

end OrthOddCentGeom

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

theorem orthogonal_normal_two_subgroup (q : QuadraticForm (ZMod 2) U)
    (hq : ∀ v, (∀ w, QuadraticMap.polar q v w = 0) → v = 0)
    (N : Subgroup (U ≃ₗ[ZMod 2] U)) (hN : N ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hNn : (N.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup q)).Normal) (hN2 : IsPGroup 2 N) :
    (∀ φ ∈ N, φ = 1) ∨
      (finrank (ZMod 2) U = 2 ∧ ∃ u : U, q u = 1 ∧ (∀ y, q y = 1 → y = u) ∧
        ∀ φ ∈ N, (∀ y, φ y = y) ∨ (∀ y, φ y = y + QuadraticMap.polar q y u • u)) :=
  OrthOddCentGeom.orthogonal_normal_two_subgroup_aux q hq N hN hNn hN2

end CFSG.LieType.ChevTwo
