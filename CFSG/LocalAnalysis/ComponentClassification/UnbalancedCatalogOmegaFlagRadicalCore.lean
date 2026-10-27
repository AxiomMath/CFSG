module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Submodule

namespace FlagRadical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_map_semilinear {σ : K ≃+* K} {T : V ≃+ V} (hTQ : ∀ v, Q (T v) = σ (Q v))
    (x y : V) : polar Q (T x) (T y) = σ (polar Q x y) := by
  rw [polar, polar, ← map_add T, hTQ, hTQ, hTQ, map_sub, map_sub]

theorem symm_smul {σ : K ≃+* K} {T : V ≃+ V} (hTs : ∀ (a : K) v, T (a • v) = σ a • T v)
    (a : K) (v : V) : T.symm (a • v) = σ.symm a • T.symm v := by
  apply T.injective
  rw [T.apply_symm_apply, hTs, RingEquiv.apply_symm_apply, T.apply_symm_apply]

theorem indep3_of_not_mem_span {p q r : V} (hpq : LinearIndependent K ![p, q])
    (hr : r ∉ span K {p, q}) :
    ∀ x y z : K, x • r + y • p + z • q = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  intro x y z h
  by_cases hx : x = 0
  · subst hx
    rw [zero_smul, zero_add] at h
    exact ⟨rfl, LinearIndependent.pair_iff.1 hpq y z h⟩
  · exfalso
    apply hr
    have hr' : r = (-x⁻¹ * y) • p + (-x⁻¹ * z) • q := by
      have h2 : x • r = -(y • p + z • q) := by
        rw [← sub_eq_zero, sub_neg_eq_add, ← add_assoc]
        exact h
      calc r = x⁻¹ • (x • r) := by rw [smul_smul, inv_mul_cancel₀ hx, one_smul]
        _ = _ := by rw [h2]; module
    rw [hr']
    exact add_mem (smul_mem _ _ (subset_span (by simp)))
      (smul_mem _ _ (subset_span (by simp)))

theorem exists_pair_of_two_le {L : Submodule K V} (hL : 2 ≤ finrank K L) {w : V} (hwL : w ∈ L)
    (hw0 : w ≠ 0) : ∃ u ∈ L, LinearIndependent K ![w, u] := by
  have hlt : K ∙ w < L := by
    refine lt_of_le_of_ne ((span_singleton_le_iff_mem _ _).2 hwL) fun h => ?_
    have := finrank_span_singleton (K := K) hw0
    rw [h] at this
    omega
  obtain ⟨u, huL, hu⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨u, huL, LinearIndependent.pair_iff.2 fun s t hst => ?_⟩
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hw0, rfl⟩
  · exfalso
    apply hu
    have hu' : u = (-t⁻¹ * s) • w := by
      have h2 : t • u = -(s • w) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hst
      calc u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [h2]; module
    rw [hu']
    exact smul_mem _ _ (mem_span_singleton_self w)

theorem exists_third_of_three_le {L : Submodule K V} (hL : 3 ≤ finrank K L) {p q : V}
    (hpL : p ∈ L) (hqL : q ∈ L) (hpq : LinearIndependent K ![p, q]) :
    ∃ r ∈ L, ∀ x y z : K, x • r + y • p + z • q = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  have hlt : span K {p, q} < L := by
    refine lt_of_le_of_ne (span_le.2 (by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hpL
      · exact hqL)) fun h => ?_
    have := finrank_span_eq_card hpq
    rw [Matrix.range_cons_cons_empty, Fintype.card_fin, h] at this
    omega
  obtain ⟨r, hrL, hr⟩ := IsConcreteLE.exists_of_lt hlt
  exact ⟨r, hrL, indep3_of_not_mem_span hpq hr⟩

theorem exists_eq_smul_of_mem_inter {p q r x : V}
    (hind : ∀ a b c : K, a • p + b • q + c • r = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hq : x ∈ span K {p, q}) (hr : x ∈ span K {p, r}) : ∃ c : K, x = c • p := by
  obtain ⟨a, b, rfl⟩ := mem_span_pair.1 hq
  obtain ⟨a', b', h⟩ := mem_span_pair.1 hr
  have h2 : (a - a') • p + b • q + (-b') • r = 0 := by
    rw [← sub_eq_zero.2 h.symm]
    module
  obtain ⟨-, hb, -⟩ := hind _ _ _ h2
  exact ⟨a, by rw [hb, zero_smul, add_zero]⟩

theorem eichler_sub_mem_span {w u : V} (hw : Q w = 0) (hwu : polar Q w u = 0) (y : V) :
    eichler Q w u y - y ∈ span K {w, u} := by
  rw [eichler_apply hw hwu]
  rw [show y + polar Q y w • u - (polar Q y u + Q u * polar Q y w) • w - y =
    (-(polar Q y u + Q u * polar Q y w)) • w + polar Q y w • u by module]
  exact mem_span_pair.2 ⟨_, _, rfl⟩

theorem apply_mem_span_pair [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {σ : K ≃+* K} {T : V ≃+ V} (hTs : ∀ (a : K) v, T (a • v) = σ a • T v) {w u : V}
    (hw : Q w = 0) (hwu : polar Q w u = 0) (hind : LinearIndependent K ![w, u])
    (hc : ∀ v, T (eichler Q w u v) = eichler Q w u (T v)) :
    T w ∈ span K {w, u} ∧ T u ∈ span K {w, u} := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ hind
  have h00 : polar Q w (g 0) = 1 := by simpa using hg 0 0
  have h10 : polar Q u (g 0) = 0 := by simpa using hg 1 0
  have h01 : polar Q w (g 1) = 0 := by simpa using hg 0 1
  have h11 : polar Q u (g 1) = 1 := by simpa using hg 1 1
  have hdisp : ∀ y, T (eichler Q w u y - y) ∈ span K {w, u} := fun y => by
    rw [map_sub, hc]
    exact eichler_sub_mem_span hw hwu (T y)
  have e1 : eichler Q w u (g 0) - g 0 = u - Q u • w := by
    rw [eichler_apply hw hwu, polar_comm Q (g 0) w, h00, polar_comm Q (g 0) u, h10]
    module
  have e2 : eichler Q w u (g 1) - g 1 = -w := by
    rw [eichler_apply hw hwu, polar_comm Q (g 1) w, h01, polar_comm Q (g 1) u, h11]
    module
  have hTw : T w ∈ span K {w, u} := by
    have h := hdisp (g 1)
    rw [e2, map_neg] at h
    simpa using neg_mem h
  refine ⟨hTw, ?_⟩
  have h := hdisp (g 0)
  rw [e1, map_sub, hTs] at h
  have h2 := add_mem h (smul_mem _ (σ (Q u)) hTw)
  simpa using h2

theorem exists_dual_pair [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate) {w u : V}
    (hind : LinearIndependent K ![w, u]) : ∃ x, polar Q w x = 1 ∧ polar Q u x = 0 := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ hind
  exact ⟨g 0, by simpa using hg 0 0, by simpa using hg 1 0⟩

theorem mul_eq_one_of_commute [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {T : V ≃+ V} (hTs : ∀ (a : K) v, T (a • v) = a • T v)
    (hTB : ∀ x y, polar Q (T x) (T y) = polar Q x y) {w u : V} (hw : Q w = 0)
    (hwu : polar Q w u = 0) (hind : LinearIndependent K ![w, u]) {c₀ lam : K} (hc₀ : c₀ ≠ 0)
    (hTw : T w = c₀ • w) (hTu : ∃ μ : K, T u = lam • u + μ • w)
    (hc : ∀ v, T (eichler Q w u v) = eichler Q w u (T v)) : lam * c₀ = 1 := by
  obtain ⟨x, hwx, hux⟩ := exists_dual_pair hQ hind
  obtain ⟨μ, hμ⟩ := hTu
  have hxw : polar Q x w = 1 := by rw [polar_comm]; exact hwx
  have hxu : polar Q x u = 0 := by rw [polar_comm]; exact hux
  have hTxw : polar Q (T x) w = c₀⁻¹ := by
    have h := hTB x (c₀⁻¹ • w)
    rw [hTs, hTw, smul_smul, inv_mul_cancel₀ hc₀, one_smul, polar_smul_right_eq, hxw,
      mul_one] at h
    exact h
  have h1 := hc x
  rw [eichler_apply hw hwu, eichler_apply hw hwu, hxw, hxu, hTxw] at h1
  rw [map_sub, map_add, hTs, hTs, hμ, hTw, one_smul] at h1
  have h2 : (lam - c₀⁻¹) • u + (μ - (0 + Q u * 1) * c₀ +
      (polar Q (T x) u + Q u * c₀⁻¹)) • w = 0 := by
    rw [← sub_eq_zero.2 h1]
    module
  have h3 := (LinearIndependent.pair_iff.1 hind _ _ (by rw [add_comm] at h2; exact h2)).2
  rw [sub_eq_zero] at h3
  rw [h3, inv_mul_cancel₀ hc₀]

theorem semilinear_scalar_mod {σ : K ≃+* K} {T : V ≃+ V}
    (hTs : ∀ (a : K) v, T (a • v) = σ a • T v) {L Z : Submodule K V}
    (hZ : ∀ v, T v ∈ Z → v ∈ Z) (hline : ∀ u ∈ L, ∃ c : K, T u - c • u ∈ Z)
    {u₁ u₂ : V} (hu₁ : u₁ ∈ L) (hu₂ : u₂ ∈ L)
    (hind : ∀ a b : K, a • u₁ + b • u₂ ∈ Z → a = 0 ∧ b = 0) :
    (∀ a, σ a = a) ∧ ∃ lam : K, lam ≠ 0 ∧ ∀ u ∈ L, T u - lam • u ∈ Z := by
  have huniq : ∀ u, u ∉ Z → ∀ c c' : K, T u - c • u ∈ Z → T u - c' • u ∈ Z → c = c' := by
    intro u hu c c' h h'
    by_contra hne
    apply hu
    have h2 : (c' - c) • u ∈ Z := by
      have := Z.sub_mem h h'
      rwa [show T u - c • u - (T u - c' • u) = (c' - c) • u by module] at this
    have h3 := Z.smul_mem (c' - c)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hne)), one_smul] at h3
  have hsame : ∀ u ∈ L, ∀ u' ∈ L, (∀ a b : K, a • u + b • u' ∈ Z → a = 0 ∧ b = 0) →
      ∀ c c' : K, T u - c • u ∈ Z → T u' - c' • u' ∈ Z → c = c' := by
    intro u hu u' hu' hi c c' h h'
    obtain ⟨c'', h''⟩ := hline (u + u') (L.add_mem hu hu')
    have h2 : (c'' - c) • u + (c'' - c') • u' ∈ Z := by
      have := Z.sub_mem (Z.add_mem h h') h''
      rwa [map_add, show T u - c • u + (T u' - c' • u') - (T u + T u' - c'' • (u + u')) =
        (c'' - c) • u + (c'' - c') • u' by module] at this
    obtain ⟨h3, h4⟩ := hi _ _ h2
    rw [sub_eq_zero] at h3 h4
    rw [← h3, h4]
  have hu₁Z : u₁ ∉ Z := fun h => by
    have := (hind 1 0 (by rw [one_smul, zero_smul, add_zero]; exact h)).1
    exact one_ne_zero this
  have hind' : ∀ a b : K, a • u₂ + b • u₁ ∈ Z → a = 0 ∧ b = 0 := fun a b h => by
    have := hind b a (by rw [add_comm]; exact h)
    exact ⟨this.2, this.1⟩
  obtain ⟨lam, hlam⟩ := hline u₁ hu₁
  obtain ⟨c₂, hc₂⟩ := hline u₂ hu₂
  have hc₂lam : c₂ = lam := hsame u₂ hu₂ u₁ hu₁ hind' c₂ lam hc₂ hlam
  have hall : ∀ u ∈ L, T u - lam • u ∈ Z := by
    intro u hu
    obtain ⟨c, hc⟩ := hline u hu
    by_cases h1 : ∀ a b : K, a • u + b • u₁ ∈ Z → a = 0 ∧ b = 0
    · rwa [hsame u hu u₁ hu₁ h1 c lam hc hlam] at hc
    · by_cases h2 : ∀ a b : K, a • u + b • u₂ ∈ Z → a = 0 ∧ b = 0
      · rwa [hsame u hu u₂ hu₂ h2 c c₂ hc hc₂, hc₂lam] at hc
      ·
        push Not at h1 h2
        obtain ⟨a, b, hab, hne⟩ := h1
        obtain ⟨a', b', hab', hne'⟩ := h2
        have ha : a ≠ 0 := by
          rintro rfl
          have hb : b ≠ 0 := hne rfl
          rw [zero_smul, zero_add] at hab
          exact hu₁Z (by simpa [smul_smul, inv_mul_cancel₀ hb] using Z.smul_mem b⁻¹ hab)
        have ha' : a' ≠ 0 := by
          rintro rfl
          have hb : b' ≠ 0 := hne' rfl
          rw [zero_smul, zero_add] at hab'
          have hu₂Z : u₂ ∈ Z := by
            simpa [smul_smul, inv_mul_cancel₀ hb] using Z.smul_mem b'⁻¹ hab'
          have := (hind 0 1 (by rw [zero_smul, one_smul, zero_add]; exact hu₂Z)).2
          exact one_ne_zero this
        have h3 : (a⁻¹ * b) • u₁ + (-(a'⁻¹ * b')) • u₂ ∈ Z := by
          have := Z.sub_mem (Z.smul_mem a⁻¹ hab) (Z.smul_mem a'⁻¹ hab')
          have e : a⁻¹ • (a • u + b • u₁) - a'⁻¹ • (a' • u + b' • u₂) =
              (a⁻¹ * b) • u₁ + (-(a'⁻¹ * b')) • u₂ := by
            simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ ha', one_smul]
            module
          rwa [e] at this
        obtain ⟨h4, -⟩ := hind _ _ h3
        have hb : b = 0 := by
          rcases mul_eq_zero.1 h4 with h | h
          · exact absurd h (inv_ne_zero ha)
          · exact h
        rw [hb, zero_smul, add_zero] at hab
        have huZ : u ∈ Z := by
          simpa [smul_smul, inv_mul_cancel₀ ha] using Z.smul_mem a⁻¹ hab
        have hTu : T u ∈ Z := by
          have := Z.add_mem hc (Z.smul_mem c huZ)
          rwa [sub_add_cancel] at this
        exact Z.sub_mem hTu (Z.smul_mem lam huZ)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_zero] at hlam
    exact hu₁Z (hZ u₁ hlam)
  refine ⟨fun a => ?_, lam, hlam0, hall⟩
  have h1 := hall (a • u₁) (L.smul_mem a hu₁)
  have h2 := Z.smul_mem (σ a) hlam
  have h3 : (σ a * lam - lam * a) • u₁ ∈ Z := by
    have := Z.sub_mem h2 h1
    rwa [hTs, show σ a • (T u₁ - lam • u₁) - (σ a • T u₁ - lam • a • u₁) =
      (-(σ a * lam - lam * a)) • u₁ by module, neg_smul, neg_mem_iff] at this
  have h4 : σ a * lam - lam * a = 0 := by
    by_contra hne
    have h6 := Z.smul_mem (σ a * lam - lam * a)⁻¹ h3
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h6
    exact hu₁Z h6
  have h5 : σ a * lam = a * lam := by rw [mul_comm a]; exact sub_eq_zero.1 h4
  exact mul_right_cancel₀ hlam0 h5

theorem eq_one_of_mul_self_eq_one [CharP K 2] {x : K} (hx : x * x = 1) : x = 1 := by
  rcases mul_self_eq_one_iff.mp hx with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem pow_four_of_flag [CharP K 2] {W Z : Submodule K V}
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) {T : V ≃+ V}
    (hTB : ∀ x y, polar Q (T x) (T y) = polar Q x y) (hTZ : ∀ z ∈ Z, T z = z)
    (hTL : ∀ u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W, T u - u ∈ Z) (v : V) :
    T (T (T (T v))) = v := by
  set L := LinearMap.BilinForm.orthogonal (polarBilin Q) W with hL
  have hmemL : ∀ x, x ∈ L ↔ ∀ w ∈ W, polar Q w x = 0 := fun x => by
    rw [hL, LinearMap.BilinForm.mem_orthogonal_iff]
    exact Iff.rfl
  have hWL : W ≤ L := fun x hx => (hmemL x).2 fun w hw => hWiso w hw x hx
  have hdual : ∀ y w, polar Q (T y - y) w = polar Q y (T.symm w - w) := by
    intro y w
    have h := hTB y (T.symm w)
    rw [T.apply_symm_apply] at h
    rw [polar_sub_left, polar_sub_right, h]
  have hsymmZ : ∀ z ∈ Z, T.symm z = z := fun z hz => by
    rw [AddEquiv.symm_apply_eq, hTZ z hz]
  have hsymmL : ∀ u ∈ L, T.symm u - u ∈ Z := by
    intro u hu
    have hz := hTL u hu
    have h2 := T.symm_apply_apply u
    rw [show T u = u + (T u - u) by abel, map_add, hsymmZ _ hz] at h2
    have h4 : T.symm u - u = -(T u - u) := by
      calc T.symm u - u = T.symm u - (T.symm u + (T u - u)) := by rw [h2]
        _ = -(T u - u) := by abel
    rw [h4]
    exact Z.neg_mem hz
  have hN2 : ∀ y, T (T y - y) - (T y - y) ∈ L := by
    intro y
    rw [hmemL]
    intro w hw
    rw [polar_comm, hdual, hdual]
    have h1 := hsymmL w (hWL hw)
    rw [hsymmZ _ h1, sub_self, polar_zero_right]
  have hTT : ∀ y, T (T y) = y + (T (T y - y) - (T y - y)) := by
    intro y
    rw [map_sub, ← sub_eq_zero]
    rw [show T (T y) - (y + (T (T y) - T y - (T y - y))) = (2 : K) • T y - (2 : K) • y by
      module, CharTwo.two_eq_zero, zero_smul, zero_smul, sub_zero]
  set n := T (T v - v) - (T v - v) with hn
  have hNn : T n - n ∈ Z := hTL n (hN2 v)
  have hN2n : T (T n - n) - (T n - n) = 0 := by rw [hTZ _ hNn, sub_self]
  have hnn : n + n = 0 := by rw [← two_smul K n, CharTwo.two_eq_zero, zero_smul]
  calc T (T (T (T v))) = T (T (v + n)) := by rw [hTT v]
    _ = T (T v) + T (T n) := by rw [map_add, map_add]
    _ = v + n + (n + 0) := by rw [hTT v, hTT n, hN2n]
    _ = v := by rw [add_zero, add_assoc, hnn, add_zero]

theorem semilinear_commute_eichler [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V}
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) (hW2 : 2 ≤ finrank K W)
    (hV : 6 ≤ finrank K V) {σ : K ≃+* K} {T : V ≃+ V}
    (hTs : ∀ (a : K) v, T (a • v) = σ a • T v) (hTQ : ∀ v, Q (T v) = σ (Q v))
    (hc : ∀ w ∈ W, Q w = 0 → ∀ u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
      ∀ v, T (eichler Q w u v) = eichler Q w u (T v)) :
    (∀ a, σ a = a) ∧ ∀ v, T (T (T (T v))) = v := by
  set L := LinearMap.BilinForm.orthogonal (polarBilin Q) W with hL
  have hmemL : ∀ x, x ∈ L ↔ ∀ w ∈ W, polar Q w x = 0 := fun x => by
    rw [hL, LinearMap.BilinForm.mem_orthogonal_iff]
    exact Iff.rfl
  have hWL : W ≤ L := fun x hx => (hmemL x).2 fun w hw => hWiso w hw x hx
  have hLdim : finrank K L = finrank K V - finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hQ W
  have hWLdim := Submodule.finrank_mono hWL
  have hWV := Submodule.finrank_le W
  have hL3 : 3 ≤ finrank K L := by omega
  have hspan : ∀ w ∈ W, Q w = 0 → ∀ u ∈ L, LinearIndependent K ![w, u] →
      T w ∈ span K {w, u} ∧ T u ∈ span K {w, u} := fun w hw hw0 u hu hind =>
    apply_mem_span_pair hQ hTs hw0 ((hmemL u).1 hu w hw) hind (hc w hw hw0 u hu)
  have hsing : ∀ w ∈ W, Q w = 0 → w ≠ 0 → ∃ c : K, T w = c • w := by
    intro w hw hw0 hne
    obtain ⟨u₁, hu₁, hwu₁⟩ := exists_pair_of_two_le (by omega : 2 ≤ finrank K L) (hWL hw) hne
    obtain ⟨u₂, hu₂, hind⟩ := exists_third_of_three_le hL3 (hWL hw) hu₁ hwu₁
    have hwu₂ : LinearIndependent K ![w, u₂] := LinearIndependent.pair_iff.2 fun s t hst => by
      have := hind t s 0 (by rw [zero_smul, add_zero, add_comm]; exact hst)
      exact ⟨this.2.1, this.1⟩
    exact exists_eq_smul_of_mem_inter (fun a b c' h => by
      have := hind c' a b (by
        rw [show c' • u₂ + a • w + b • u₁ = a • w + b • u₁ + c' • u₂ by abel]
        exact h)
      exact ⟨this.2.1, this.2.2, this.1⟩) (hspan w hw hw0 u₁ hu₁ hwu₁).1
      (hspan w hw hw0 u₂ hu₂ hwu₂).1
  obtain ⟨w₀, hw₀W, hw₀, hw₀ne⟩ : ∃ w ∈ W, Q w = 0 ∧ w ≠ 0 := by
    obtain ⟨a, haW, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W) fun h => by
      rw [h, finrank_bot] at hW2
      omega
    obtain ⟨b, hbW, hab⟩ := exists_pair_of_two_le hW2 haW ha0
    by_cases hQa : Q a = 0
    · exact ⟨a, haW, hQa, ha0⟩
    · obtain ⟨c, hc'⟩ := isSquare_of_charTwo' (Q b * (Q a)⁻¹)
      refine ⟨b + c • a, W.add_mem hbW (W.smul_mem c haW), ?_, fun h => ?_⟩
      · have hc2 : c ^ 2 * Q a = Q b := by rw [pow_two, ← hc', inv_mul_cancel_right₀ hQa]
        rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, polar_comm,
          hWiso a haW b hbW, mul_zero, add_zero, hc2]
        exact CharTwo.add_self_eq_zero (Q b)
      · have := LinearIndependent.pair_iff.1 hab c 1 (by rw [one_smul, add_comm]; exact h)
        exact one_ne_zero this.2
  by_cases hA : ∃ w₁ ∈ W, ∃ w₂ ∈ W, Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]
  ·
    obtain ⟨w₁, hw₁W, w₂, hw₂W, hw₁, hw₂, h12⟩ := hA
    have hline : ∀ u ∈ L, ∃ c : K, T u - c • u ∈ (⊥ : Submodule K V) := by
      intro u hu
      by_cases hu0 : u = 0
      · exact ⟨0, by rw [hu0, map_zero, smul_zero, sub_zero]; exact zero_mem _⟩
      by_cases huS : u ∈ span K {w₁, w₂}
      · have hSW : span K {w₁, w₂} ≤ W := span_le.2 (by
          intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl
          · exact hw₁W
          · exact hw₂W)
        have huQ : Q u = 0 := map_eq_zero_of_mem_span (S := {w₁, w₂})
          (by
            intro v hv
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            rcases hv with rfl | rfl
            · exact hw₁
            · exact hw₂)
          (fun x hx y hy => hWiso x (hSW (subset_span hx)) y (hSW (subset_span hy))) huS
        obtain ⟨c, hcu⟩ := hsing u (hSW huS) huQ hu0
        exact ⟨c, by rw [hcu, sub_self]; exact zero_mem _⟩
      · have hind := indep3_of_not_mem_span h12 huS
        have hi1 : LinearIndependent K ![w₁, u] := LinearIndependent.pair_iff.2 fun s t hst => by
          have := hind t s 0 (by rw [zero_smul, add_zero, add_comm]; exact hst)
          exact ⟨this.2.1, this.1⟩
        have hi2 : LinearIndependent K ![w₂, u] := LinearIndependent.pair_iff.2 fun s t hst => by
          have := hind t 0 s (by rw [zero_smul, add_zero, add_comm]; exact hst)
          exact ⟨this.2.2, this.1⟩
        have h1 := (hspan w₁ hw₁W hw₁ u hu hi1).2
        have h2 := (hspan w₂ hw₂W hw₂ u hu hi2).2
        rw [Set.pair_comm] at h1 h2
        obtain ⟨c, hcu⟩ := exists_eq_smul_of_mem_inter hind h1 h2
        exact ⟨c, by rw [hcu, sub_self]; exact zero_mem _⟩
    obtain ⟨hσ, lam, hlam0, hlam⟩ := semilinear_scalar_mod hTs (L := L)
      (Z := (⊥ : Submodule K V))
      (fun v hv => by
        rw [mem_bot] at hv ⊢
        exact T.injective (hv.trans (map_zero T).symm)) hline (hWL hw₁W) (hWL hw₂W)
      (fun a b h => LinearIndependent.pair_iff.1 h12 a b ((mem_bot K).1 h))
    have hTu : ∀ u ∈ L, T u = lam • u := fun u hu => sub_eq_zero.1 ((mem_bot K).1 (hlam u hu))
    have hTs' : ∀ (a : K) v, T (a • v) = a • T v := fun a v => by rw [hTs, hσ]
    have hTB : ∀ x y, polar Q (T x) (T y) = polar Q x y := fun x y => by
      rw [polar_map_semilinear hTQ, hσ]
    have h1 := mul_eq_one_of_commute (lam := lam) hQ hTs' hTB hw₁ (hWiso w₁ hw₁W w₂ hw₂W) h12
      hlam0
      (hTu w₁ (hWL hw₁W)) ⟨0, by rw [hTu w₂ (hWL hw₂W), zero_smul, add_zero]⟩
      (hc w₁ hw₁W hw₁ w₂ (hWL hw₂W))
    have hlam1 : lam = 1 := eq_one_of_mul_self_eq_one h1
    exact ⟨hσ, pow_four_of_flag hWiso hTB (Z := (⊥ : Submodule K V))
      (fun z hz => by rw [(mem_bot K).1 hz, map_zero])
      (fun u hu => by rw [hTu u hu, hlam1, one_smul, sub_self]; exact zero_mem _)⟩
  ·
    push Not at hA
    obtain ⟨w₁, hw₁W, h01⟩ := exists_pair_of_two_le hW2 hw₀W hw₀ne
    have hw₁Q : Q w₁ ≠ 0 := fun hQ1 => hA w₀ hw₀W w₁ hw₁W hw₀ hQ1 h01
    obtain ⟨c₀, hc₀⟩ := hsing w₀ hw₀W hw₀ hw₀ne
    have hc₀0 : c₀ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc₀
      exact hw₀ne (T.injective (hc₀.trans (map_zero T).symm))
    have hTZ' : ∀ a : K, T (a • w₀) = (σ a * c₀) • w₀ := fun a => by
      rw [hTs, hc₀, smul_smul]
    have hZ : ∀ v, T v ∈ K ∙ w₀ → v ∈ K ∙ w₀ := by
      intro v hv
      obtain ⟨a, ha⟩ := mem_span_singleton.1 hv
      have h2 : T (σ.symm (a * c₀⁻¹) • w₀) = T v := by
        rw [hTZ', RingEquiv.apply_symm_apply, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one, ha]
      rw [← T.injective h2]
      exact smul_mem _ _ (mem_span_singleton_self w₀)
    have hline : ∀ u ∈ L, ∃ c : K, T u - c • u ∈ K ∙ w₀ := by
      intro u hu
      by_cases huZ : u ∈ K ∙ w₀
      · obtain ⟨a, rfl⟩ := mem_span_singleton.1 huZ
        exact ⟨0, by
          rw [zero_smul, sub_zero, hTZ']
          exact smul_mem _ _ (mem_span_singleton_self w₀)⟩
      · have hind : LinearIndependent K ![w₀, u] :=
          LinearIndependent.pair_iff.2 fun s t hst => by
            by_cases ht : t = 0
            · subst ht
              rw [zero_smul, add_zero] at hst
              exact ⟨(smul_eq_zero.1 hst).resolve_right hw₀ne, rfl⟩
            · exfalso
              apply huZ
              have hu' : u = (-t⁻¹ * s) • w₀ := by
                have h2 : t • u = -(s • w₀) := by
                  rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
                  exact hst
                calc u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
                  _ = _ := by rw [h2]; module
              rw [hu']
              exact smul_mem _ _ (mem_span_singleton_self w₀)
        obtain ⟨a, b, hab⟩ := mem_span_pair.1 (hspan w₀ hw₀W hw₀ u hu hind).2
        exact ⟨b, by
          rw [← hab, add_sub_cancel_right]
          exact smul_mem _ _ (mem_span_singleton_self w₀)⟩
    obtain ⟨u₁, hu₁, h0u₁⟩ := exists_pair_of_two_le (by omega : 2 ≤ finrank K L) (hWL hw₀W)
      hw₀ne
    obtain ⟨u₂, hu₂, hind3⟩ := exists_third_of_three_le hL3 (hWL hw₀W) hu₁ h0u₁
    have hindZ : ∀ a b : K, a • u₁ + b • u₂ ∈ K ∙ w₀ → a = 0 ∧ b = 0 := by
      intro a b h
      obtain ⟨c, hc'⟩ := mem_span_singleton.1 h
      have := hind3 b (-c) a (by
        rw [neg_smul, hc']
        abel)
      exact ⟨this.2.2, this.1⟩
    obtain ⟨hσ, lam, hlam0, hlam⟩ := semilinear_scalar_mod hTs hZ hline hu₁ hu₂ hindZ
    have hTs' : ∀ (a : K) v, T (a • v) = a • T v := fun a v => by rw [hTs, hσ]
    have hTB : ∀ x y, polar Q (T x) (T y) = polar Q x y := fun x y => by
      rw [polar_map_semilinear hTQ, hσ]
    have hTu₁ : ∃ μ : K, T u₁ = lam • u₁ + μ • w₀ := by
      obtain ⟨μ, hμ⟩ := mem_span_singleton.1 (hlam u₁ hu₁)
      exact ⟨μ, by rw [hμ]; abel⟩
    have h1 := mul_eq_one_of_commute hQ hTs' hTB hw₀ ((hmemL u₁).1 hu₁ w₀ hw₀W) h0u₁ hc₀0 hc₀
      hTu₁ (hc w₀ hw₀W hw₀ u₁ hu₁)
    obtain ⟨μ, hμ⟩ := mem_span_singleton.1 (hlam w₁ (hWL hw₁W))
    have hTw₁ : T w₁ = lam • w₁ + μ • w₀ := by rw [hμ]; abel
    have h2 : lam * lam = 1 := by
      have h3 := hTQ w₁
      rw [hσ, hTw₁, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hw₀,
        polar_smul_left_eq, polar_smul_right_eq, hWiso w₁ hw₁W w₀ hw₀W] at h3
      have h4 : (lam * lam) * Q w₁ = 1 * Q w₁ := by linear_combination h3
      exact mul_right_cancel₀ hw₁Q h4
    have hlam1 : lam = 1 := eq_one_of_mul_self_eq_one h2
    have hc₀1 : c₀ = 1 := by rwa [hlam1, one_mul] at h1
    refine ⟨hσ, pow_four_of_flag hWiso hTB (Z := K ∙ w₀) ?_ ?_⟩
    · intro z hz
      obtain ⟨a, rfl⟩ := mem_span_singleton.1 hz
      rw [hTs', hc₀, hc₀1, one_smul]
    · intro u hu
      have h5 := hlam u hu
      rwa [hlam1, one_smul] at h5

end FlagRadical

end CFSG.ComponentClassification.UnbalancedCatalog
