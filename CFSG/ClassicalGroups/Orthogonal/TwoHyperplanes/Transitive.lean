module

public import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def reflPairsPerp (e : V) : Set (V ≃ₗ[K] V) :=
  {g | ∃ a b, polar Q e a = 0 ∧ polar Q e b = 0 ∧ Q a = Q b ∧ reflect Q a * reflect Q b = g}

theorem reflect_mul_reflect_mem_reflPairsPerp {e a b : V} (ha : polar Q e a = 0)
    (hb : polar Q e b = 0) (hab : Q a = Q b) : reflect Q a * reflect Q b ∈ reflPairsPerp Q e :=
  ⟨a, b, ha, hb, hab, rfl⟩

theorem one_mem_reflPairsPerp (e : V) : (1 : V ≃ₗ[K] V) ∈ reflPairsPerp Q e := by
  refine ⟨0, 0, by simp, by simp, by simp, ?_⟩
  rw [reflect_of_map_eq_zero (QuadraticMap.map_zero Q), one_mul]

theorem mem_orthogonalGroup_of_mem_reflPairsPerp {e : V} {g : V ≃ₗ[K] V}
    (hg : g ∈ reflPairsPerp Q e) : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨a, b, _, _, _, rfl⟩ := hg
  exact mul_mem (reflect_mem_orthogonalGroup Q a) (reflect_mem_orthogonalGroup Q b)

theorem apply_self_of_mem_reflPairsPerp {e : V} {g : V ≃ₗ[K] V} (hg : g ∈ reflPairsPerp Q e) :
    g e = e := by
  obtain ⟨a, b, ha, hb, _, rfl⟩ := hg
  rw [LinearEquiv.mul_apply,
    reflect_apply_of_polar_eq_zero (v := b) (x := e) (by rw [polar_comm]; exact hb),
    reflect_apply_of_polar_eq_zero (v := a) (x := e) (by rw [polar_comm]; exact ha)]

theorem conj_mem_reflPairsPerp {e : V} {h g : V ≃ₗ[K] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (he : h e = e)
    (hg : g ∈ reflPairsPerp Q e) : h * g * h⁻¹ ∈ reflPairsPerp Q e := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hg
  refine ⟨h a, h b, ?_, ?_, ?_, ?_⟩
  · rw [← he, polar_map_of_mem hh e a, ha]
  · rw [← he, polar_map_of_mem hh e b, hb]
  · rw [map_of_mem hh a, map_of_mem hh b, hab]
  · rw [← reflect_conj hh a, ← reflect_conj hh b]
    group

private theorem exists_twoHyperplane_scalars_key_th2b (h2 : (2 : K) ≠ 0) {z k : K}
    (hk0 : k ≠ 0) (hkz : k ^ 2 + z ≠ 0) (hkz2 : k ^ 2 ≠ z) :
    ∃ s μ t : K, z * s ^ 2 + μ ^ 2 - t ^ 2 = z ∧ μ * (μ - t) ≠ 0 ∧ μ * (μ - t) ≠ z := by
  refine ⟨0, (k + z / k) / 2, (z / k - k) / 2, ?_, ?_, ?_⟩
  · field_simp [h2, hk0]
    ring
  · have hm : ((k + z / k) / 2) * (((k + z / k) / 2) - ((z / k - k) / 2)) =
        (k ^ 2 + z) / 2 := by
      field_simp [h2, hk0]
      ring
    rw [hm]
    exact div_ne_zero hkz h2
  · have hm : ((k + z / k) / 2) * (((k + z / k) / 2) - ((z / k - k) / 2)) =
        (k ^ 2 + z) / 2 := by
      field_simp [h2, hk0]
      ring
    rw [hm]
    intro h
    have hk2 : k ^ 2 = z := by
      field_simp [h2] at h
      linear_combination h
    exact hkz2 hk2

theorem exists_twoHyperplane_scalars (h2 : (2 : K) ≠ 0) {z : K} (hz : z ≠ 0)
    (h3 : IsSquare z ∨ (3 : K) ≠ 0) :
    ∃ s μ t : K, z * s ^ 2 + μ ^ 2 - t ^ 2 = z ∧ μ * (μ - t) ≠ 0 ∧ μ * (μ - t) ≠ z := by
  by_cases hsq : IsSquare z
  · rw [isSquare_iff_exists_mul_self] at hsq
    obtain ⟨κ, rfl⟩ := hsq
    have hκ : κ ≠ 0 := by rintro rfl; exact hz (by simp)
    refine ⟨1, κ, -κ, ?_, ?_, ?_⟩
    · ring
    · rw [show κ * (κ - -κ) = 2 * κ ^ 2 by ring]
      exact mul_ne_zero h2 (pow_ne_zero 2 hκ)
    · rw [show κ * (κ - -κ) = 2 * κ ^ 2 by ring]
      intro h
      have hκ2 : κ ^ 2 = 0 := by linear_combination h
      exact pow_ne_zero 2 hκ hκ2
  · have h3' : (3 : K) ≠ 0 := h3.resolve_left hsq
    have hk : (1 : K) ^ 2 + z ≠ 0 ∨ (2 : K) ^ 2 + z ≠ 0 := by
      by_contra h
      have h1z : (1 : K) ^ 2 + z = 0 := by
        by_contra h1
        exact h (Or.inl h1)
      have h2z : (2 : K) ^ 2 + z = 0 := by
        by_contra h2'
        exact h (Or.inr h2')
      have hz3 : (3 : K) = 0 := by linear_combination h2z - h1z
      exact h3' hz3
    have key : ∀ k : K, k ≠ 0 → k ^ 2 + z ≠ 0 → k ^ 2 ≠ z →
        ∃ s μ t : K, z * s ^ 2 + μ ^ 2 - t ^ 2 = z ∧
          μ * (μ - t) ≠ 0 ∧ μ * (μ - t) ≠ z := by
      intro k hk0 hkz hkz2
      exact exists_twoHyperplane_scalars_key_th2b h2 hk0 hkz hkz2
    rcases hk with hk | hk
    · exact key 1 one_ne_zero hk (by
        intro h
        exact hsq ⟨1, by simpa [pow_two] using h.symm⟩)
    · exact key 2 h2 hk (by
        intro h
        exact hsq ⟨2, by simpa [pow_two] using h.symm⟩)

variable [Finite K] [FiniteDimensional K V]

theorem exists_mem_reflPairsPerp_polar_eq_zero (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V) {e f : V}
    (he : Q e ≠ 0) (hf : Q f ≠ 0) (hef : polar Q e f = 0) {v : V} {α : K}
    (hα : polar Q e (v - α • e) = 0) (hv : Q (v - α • e) ≠ 0) :
    ∃ g ∈ reflPairsPerp Q e, polar Q f (g v) = 0 := by
  classical
  let w := v - α • e
  have hw : polar Q e w = 0 := hα
  have hw0 : Q w ≠ 0 := hv
  obtain ⟨w', hw'e, hw'f, hQw'⟩ :=
    exists_polar_eq_zero_polar_eq_zero_map_eq h2 hQ hdim he hf hef (Q w)
  obtain ⟨a, b, ha, hb, hab, hmove⟩ :=
    exists_reflect_mul_reflect_apply_eq h2 hQ hdim he hw hw'e hQw'.symm hw0
  have hmem : reflect Q a * reflect Q b ∈ reflPairsPerp Q e :=
    reflect_mul_reflect_mem_reflPairsPerp ha hb hab
  refine ⟨reflect Q a * reflect Q b, hmem, ?_⟩
  have hge : (reflect Q a * reflect Q b) e = e := apply_self_of_mem_reflPairsPerp hmem
  have hv_eq : v = w + α • e := by
    dsimp [w]
    rw [sub_add_cancel]
  have hgv : (reflect Q a * reflect Q b) v = w' + α • e := by
    rw [hv_eq, map_add, map_smul, hmove, hge]
  have hfe : polar Q f e = 0 := by rw [polar_comm]; exact hef
  rw [hgv, polar_add_right, polar_smul_right, hw'f, hfe, smul_zero, add_zero]

omit [Finite K] [FiniteDimensional K V] in
private theorem polar_reflect_eq_of_polar_eq_zero_th2b {u w x : V} (hQu : Q u ≠ 0)
    (h : polar Q x u = 0) : polar Q x (reflect Q u w) = polar Q x w := by
  rw [reflect_apply hQu, polar_sub_right, polar_smul_right_eq, h, mul_zero, sub_zero]

omit [Finite K] [FiniteDimensional K V] in
private theorem exists_doubly_singular_x_th2b {e f v : V} {α β : K}
    (hf : Q f ≠ 0) (hv : Q v ≠ 0) (hef : polar Q e f = 0)
    (hα : polar Q e (v - α • e) = 0) (hβ : polar Q f (v - β • f) = 0)
    (hαv : Q (v - α • e) = 0) (hβv : Q (v - β • f) = 0) :
    ∃ x : V, v = x + α • e + β • f ∧ Q x ≠ 0 ∧ polar Q e x = 0 ∧
      polar Q f x = 0 ∧ Q x = -(β ^ 2 * Q f) ∧ Q v = β ^ 2 * Q f ∧ β ≠ 0 := by
  let x : V := v - α • e - β • f
  have hfe : polar Q f e = 0 := by rw [polar_comm]; exact hef
  have hxe : polar Q e x = 0 := by
    change polar Q e ((v - α • e) - β • f) = 0
    rw [polar_sub_right, polar_smul_right_eq, hef, mul_zero, sub_zero, hα]
  have hxf : polar Q f x = 0 := by
    change polar Q f ((v - α • e) - β • f) = 0
    rw [sub_right_comm, polar_sub_right, polar_smul_right_eq, hfe, mul_zero, sub_zero, hβ]
  have hQv : Q v = β ^ 2 * Q f := by
    have h1 : Q ((v - β • f) + β • f) = Q (v - β • f) + Q (β • f) +
        polar Q (v - β • f) (β • f) := QuadraticMap.map_add Q (v - β • f) (β • f)
    rw [sub_add_cancel] at h1
    have hc : polar Q (v - β • f) (β • f) = 0 := by
      rw [polar_smul_right_eq, (show polar Q (v - β • f) f = 0 by rw [polar_comm]; exact hβ),
        mul_zero]
    rw [hβv, map_smul_eq_sq Q β f, hc, add_zero, zero_add] at h1
    exact h1
  have hQx : Q x = -(β ^ 2 * Q f) := by
    have h1 : Q (x + β • f) = Q x + Q (β • f) + polar Q x (β • f) :=
      QuadraticMap.map_add Q x (β • f)
    have hc : polar Q x (β • f) = 0 := by
      rw [polar_smul_right_eq, (show polar Q x f = 0 by rw [polar_comm]; exact hxf), mul_zero]
    have hxβ : x + β • f = v - α • e := by
      change (v - α • e - β • f) + β • f = v - α • e
      rw [sub_add_cancel]
    rw [hxβ, hαv, map_smul_eq_sq Q β f, hc, add_zero] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  have hβne : β ≠ 0 := by
    rintro rfl
    rw [hQv, pow_two, zero_mul, zero_mul] at hv
    exact hv rfl
  have hQxne : Q x ≠ 0 := by
    rw [hQx]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hβne) hf)
  have hvx : v = x + α • e + β • f := by
    change v = (v - α • e - β • f) + α • e + β • f
    rw [add_assoc, add_comm (α • e) (β • f), ← add_assoc, sub_add_cancel, sub_add_cancel]
  exact ⟨x, hvx, hQxne, hxe, hxf, hQx, hQv, hβne⟩

private theorem exists_doubly_singular_y_th2b (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f x : V}
    (he : Q e ≠ 0) (hf : Q f ≠ 0) (hQx : Q x ≠ 0)
    (hef : polar Q e f = 0) (hex : polar Q e x = 0) (hfx : polar Q f x = 0) :
    ∃ y : V, polar Q e y = 0 ∧ polar Q f y = 0 ∧ polar Q x y = 0 ∧
      Q y ≠ 0 ∧ (IsSquare (Q y / Q f) ∨ (3 : K) ≠ 0) := by
  classical
  have hpair : (({e, f, x} : Finset V) : Set V).Pairwise fun u w => polar Q u w = 0 := by
    intro u hu w hw hne
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      simp_all [polar_comm]
  have hs : ∀ u ∈ ({e, f, x} : Finset V), Q u ≠ 0 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact he
    · exact hf
    · exact hQx
  have hcard : ({e, f, x} : Finset V).card ≤ 3 := Finset.card_le_three
  by_cases hdim5 : 5 ≤ Module.finrank K V
  · have hcard5 : ({e, f, x} : Finset V).card + 2 ≤ Module.finrank K V :=
      (Nat.add_le_add_right hcard 2).trans hdim5
    obtain ⟨y, hy, hQy⟩ := exists_forall_polar_eq_zero_map_eq h2 hQ hs hpair hcard5 (Q f)
    refine ⟨y, hy e (by simp), hy f (by simp), hy x (by simp), ?_, Or.inl ?_⟩
    · rw [hQy]; exact hf
    · rw [hQy, div_self hf]; exact IsSquare.one
  · have h3' : (3 : K) ≠ 0 := h3.resolve_right hdim5
    have hcard4 : ({e, f, x} : Finset V).card + 1 ≤ Module.finrank K V :=
      (Nat.add_le_add_right hcard 1).trans hdim
    obtain ⟨y, hy, hQy⟩ := exists_forall_polar_eq_zero_ne_zero h2 hQ hs hpair hcard4
    exact ⟨y, hy e (by simp), hy f (by simp), hy x (by simp), hQy, Or.inr h3'⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem doubly_singular_b_basic_th2b {b e f x y : V} {β s μ t z : K}
    (hb : b = s • y + μ • f + (t / β) • x)
    (hex : polar Q e x = 0) (hef : polar Q e f = 0) (hye : polar Q e y = 0)
    (hfy : polar Q f y = 0) (hfx : polar Q f x = 0) (hxy : polar Q x y = 0)
    (hf : Q f ≠ 0) (hβ : β ≠ 0) (hQx : Q x = -(β ^ 2 * Q f))
    (hzy : Q y = z * Q f) (hscal : z * s ^ 2 + μ ^ 2 - t ^ 2 = z) :
    polar Q e b = 0 ∧ Q b = Q y := by
  constructor
  · rw [hb, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_smul_right_eq, hye, hef, hex]
    ring
  · rw [hb]
    have h1 : Q (s • y + μ • f + (t / β) • x) =
        Q (s • y) + Q (μ • f) + Q ((t / β) • x) := by
      have hpyf : polar Q (s • y) (μ • f) = 0 := by
        rw [polar_smul_left_eq, polar_smul_right_eq,
          (show polar Q y f = 0 by rw [polar_comm]; exact hfy)]
        ring
      have hpyx : polar Q (s • y) ((t / β) • x) = 0 := by
        rw [polar_smul_left_eq, polar_smul_right_eq,
          (show polar Q y x = 0 by rw [polar_comm]; exact hxy)]
        ring
      have hpfx : polar Q (μ • f) ((t / β) • x) = 0 := by
        rw [polar_smul_left_eq, polar_smul_right_eq, hfx]
        ring
      rw [QuadraticMap.map_add Q (s • y + μ • f) ((t / β) • x),
        QuadraticMap.map_add Q (s • y) (μ • f), polar_add_left, hpyf, hpyx, hpfx]
      ring
    rw [h1, map_smul_eq_sq Q s y, map_smul_eq_sq Q μ f, map_smul_eq_sq Q (t / β) x,
      hQx, hzy]
    have ht : (t / β) ^ 2 * (-(β ^ 2 * Q f)) = -t ^ 2 * Q f := by
      field_simp [hβ]
    rw [ht]
    linear_combination Q f * hscal

omit [Finite K] [FiniteDimensional K V] in
private theorem doubly_singular_b_polar_th2b {v b e f x y : V} {α β s μ t : K}
    (hb : b = s • y + μ • f + (t / β) • x)
    (hvx : v = x + α • e + β • f) (hbe : polar Q e b = 0)
    (hef : polar Q e f = 0) (hxy : polar Q x y = 0)
    (hfy : polar Q f y = 0) (hfx : polar Q f x = 0)
    (hQx : Q x = -(β ^ 2 * Q f)) :
    polar Q f b = 2 * (μ * Q f) ∧ polar Q b v = 2 * (β * Q f) * (μ - t) ∧
      polar Q f v = 2 * (β * Q f) := by
  have hfe : polar Q f e = 0 := by rw [polar_comm]; exact hef
  have hyx : polar Q y x = 0 := by rw [polar_comm]; exact hxy
  have hbe' : polar Q b e = 0 := by rw [polar_comm]; exact hbe
  have hff : polar Q f f = 2 * Q f := polar_self_eq_two_mul Q f
  have hbf : polar Q f b = 2 * (μ * Q f) := by
    rw [hb, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_smul_right_eq, hfy, hff, hfx]
    ring
  have hb_f : polar Q b f = 2 * (μ * Q f) := by
    rw [polar_comm]; exact hbf
  have hb_x : polar Q b x = -2 * (β * t * Q f) := by
    rw [hb, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      polar_smul_left_eq, hyx, hfx, polar_self_eq_two_mul Q x, hQx]
    field_simp
    ring
  refine ⟨hbf, ?_, ?_⟩
  · rw [hvx, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      hb_x, hbe', hb_f]
    ring
  · rw [hvx, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      hfx, hfe, hff]
    ring

omit [Finite K] [FiniteDimensional K V] in
private theorem doubly_singular_polar_g_th2b {v b y f : V} {β μ t z γ : K}
    (hz : z ≠ 0) (hf : Q f ≠ 0) (hQy : Q y ≠ 0) (hQb : Q b = Q y)
    (hzy : Q y = z * Q f) (hyf : polar Q f y = 0)
    (hfv : polar Q f v = 2 * (β * Q f)) (hbf : polar Q f b = 2 * (μ * Q f))
    (hbv : polar Q b v = 2 * (β * Q f) * (μ - t))
    (hγ : γ = β * (1 - 2 * ((μ * (μ - t)) / z))) :
    polar Q f ((reflect Q y * reflect Q b) v) = 2 * (Q f * γ) := by
  have hQbne : Q b ≠ 0 := by rw [hQb]; exact hQy
  rw [LinearEquiv.mul_apply, polar_reflect_eq_of_polar_eq_zero_th2b hQy hyf]
  rw [reflect_apply hQbne, polar_sub_right, polar_smul_right_eq, hfv, hbf, hbv, hQb, hzy,
    hγ]
  field_simp [hf, hz]

omit [Finite K] [FiniteDimensional K V] in
private theorem doubly_singular_map_final_th2b (h2 : (2 : K) ≠ 0) {v b y f : V}
    {β μ t z γ : K} (hz : z ≠ 0) (hf : Q f ≠ 0) (hβ : β ≠ 0)
    (hm0 : μ * (μ - t) ≠ 0) (hmz : μ * (μ - t) ≠ z)
    (hQv : Q v = β ^ 2 * Q f)
    (hgO : (reflect Q y * reflect Q b) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgf : polar Q f ((reflect Q y * reflect Q b) v) = 2 * (Q f * γ))
    (hγ : γ = β * (1 - 2 * ((μ * (μ - t)) / z))) :
    Q ((reflect Q y * reflect Q b) v - γ • f) ≠ 0 := by
  have hQsub : Q ((reflect Q y * reflect Q b) v - γ • f) = Q v - γ ^ 2 * Q f := by
    have hcross : polar Q ((reflect Q y * reflect Q b) v) (-(γ • f)) =
        -2 * γ ^ 2 * Q f := by
      rw [QuadraticMap.polar_neg_right, polar_smul_right_eq,
        (show polar Q ((reflect Q y * reflect Q b) v) f = 2 * (Q f * γ) by
          rw [polar_comm]; exact hgf)]
      ring
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      map_smul_eq_sq Q γ f, map_of_mem hgO, hcross]
    ring
  have hγfac : β ^ 2 - γ ^ 2 = 4 * β ^ 2 * (μ * (μ - t)) *
      (z - μ * (μ - t)) / z ^ 2 := by
    rw [hγ]
    field_simp [hz]
    ring
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 ^ 2 := by ring
    rw [h]
    exact pow_ne_zero 2 h2
  have hne : β ^ 2 - γ ^ 2 ≠ 0 := by
    rw [hγfac]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hβ)) hm0)
      (sub_ne_zero.mpr (Ne.symm hmz))) (pow_ne_zero 2 hz)
  rw [hQsub, hQv]
  have hfac : β ^ 2 * Q f - γ ^ 2 * Q f = Q f * (β ^ 2 - γ ^ 2) := by ring
  rw [hfac]
  exact mul_ne_zero hf hne

theorem exists_mem_reflPairsPerp_of_map_sub_eq_zero (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f : V} (he : Q e ≠ 0) (hf : Q f ≠ 0)
    (hef : polar Q e f = 0) {v : V} (hv : Q v ≠ 0) {α β : K}
    (hα : polar Q e (v - α • e) = 0) (hβ : polar Q f (v - β • f) = 0)
    (hαv : Q (v - α • e) = 0) (hβv : Q (v - β • f) = 0) :
    ∃ g ∈ reflPairsPerp Q e, ∃ γ : K, polar Q f (g v - γ • f) = 0 ∧ Q (g v - γ • f) ≠ 0 := by
  obtain ⟨x, hvx, hQxne, hex, hfx, hQx, hQv, hβne⟩ :=
    exists_doubly_singular_x_th2b hf hv hef hα hβ hαv hβv
  obtain ⟨y, hye, hyf, hyx, hQyne, hzsq⟩ :=
    exists_doubly_singular_y_th2b h2 hQ hdim h3 he hf hQxne hef hex hfx
  let z : K := Q y / Q f
  have hz : z ≠ 0 := div_ne_zero hQyne hf
  have hzy : Q y = z * Q f := by
    change Q y = Q y / Q f * Q f
    exact (div_mul_cancel₀ (Q y) hf).symm
  obtain ⟨s, μ, t, hscal, hm0, hmz⟩ := exists_twoHyperplane_scalars h2 hz hzsq
  let b : V := s • y + μ • f + (t / β) • x
  have hb_basic : polar Q e b = 0 ∧ Q b = Q y :=
    doubly_singular_b_basic_th2b (b := b) rfl hex hef hye hyf hfx hyx hf hβne hQx hzy hscal
  have hb_polar : polar Q f b = 2 * (μ * Q f) ∧
      polar Q b v = 2 * (β * Q f) * (μ - t) ∧ polar Q f v = 2 * (β * Q f) :=
    doubly_singular_b_polar_th2b (b := b) rfl hvx hb_basic.1 hef hyx hyf hfx hQx
  let γ : K := β * (1 - 2 * ((μ * (μ - t)) / z))
  have hgf : polar Q f ((reflect Q y * reflect Q b) v) = 2 * (Q f * γ) :=
    doubly_singular_polar_g_th2b hz hf hQyne hb_basic.2 hzy hyf hb_polar.2.2 hb_polar.1
      hb_polar.2.1 rfl
  have hmem : reflect Q y * reflect Q b ∈ reflPairsPerp Q e :=
    reflect_mul_reflect_mem_reflPairsPerp hye hb_basic.1 hb_basic.2.symm
  have hgO : reflect Q y * reflect Q b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mem_orthogonalGroup_of_mem_reflPairsPerp hmem
  refine ⟨reflect Q y * reflect Q b, hmem, γ, ?_, ?_⟩
  · rw [polar_sub_right, polar_smul_right_eq, hgf, polar_self_eq_two_mul Q f]
    ring
  · exact doubly_singular_map_final_th2b h2 hz hf hβne hm0 hmz hQv hgO hgf rfl

theorem exists_mem_reflPairsPerp_map_sub_ne_zero (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f : V} (he : Q e ≠ 0) (hf : Q f ≠ 0)
    (hef : polar Q e f = 0) {v : V} (hv : Q v ≠ 0) :
    ∃ g ∈ reflPairsPerp Q e, ∃ γ : K, polar Q f (g v - γ • f) = 0 ∧ Q (g v - γ • f) ≠ 0 := by
  let α : K := polar Q e v / polar Q e e
  let β : K := polar Q f v / polar Q f f
  have hpe : polar Q e e ≠ 0 := by
    rw [polar_self_eq_two_mul Q e]
    exact mul_ne_zero h2 he
  have hpf : polar Q f f ≠ 0 := by
    rw [polar_self_eq_two_mul Q f]
    exact mul_ne_zero h2 hf
  have hα : polar Q e (v - α • e) = 0 := by
    change polar Q e (v - (polar Q e v / polar Q e e) • e) = 0
    rw [polar_sub_right, polar_smul_right_eq, div_mul_cancel₀ (polar Q e v) hpe, sub_self]
  have hβ : polar Q f (v - β • f) = 0 := by
    change polar Q f (v - (polar Q f v / polar Q f f) • f) = 0
    rw [polar_sub_right, polar_smul_right_eq, div_mul_cancel₀ (polar Q f v) hpf, sub_self]
  by_cases hβv : Q (v - β • f) ≠ 0
  · refine ⟨1, one_mem_reflPairsPerp (Q := Q) e, β, ?_, ?_⟩
    · simpa using hβ
    · simpa using hβv
  · have hβv0 : Q (v - β • f) = 0 := not_not.mp hβv
    by_cases hαv : Q (v - α • e) ≠ 0
    · obtain ⟨g, hg, hgf⟩ :=
        exists_mem_reflPairsPerp_polar_eq_zero h2 hQ hdim he hf hef hα hαv
      refine ⟨g, hg, 0, ?_, ?_⟩
      · simpa using hgf
      · simpa [map_of_mem (mem_orthogonalGroup_of_mem_reflPairsPerp hg)] using hv
    · have hαv0 : Q (v - α • e) = 0 := not_not.mp hαv
      exact exists_mem_reflPairsPerp_of_map_sub_eq_zero h2 hQ hdim h3 he hf hef hv
        hα hβ hαv0 hβv0

theorem exists_mem_closure_reflPairsPerp_polar_eq_zero (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f : V} (he : Q e ≠ 0) (hf : Q f ≠ 0)
    (hef : polar Q e f = 0) {v : V} (hv : Q v ≠ 0) :
    ∃ g ∈ Subgroup.closure (reflPairsPerp Q e ∪ reflPairsPerp Q f), polar Q f (g v) = 0 := by
  obtain ⟨g₁, hg₁, γ, hγ, hQγ⟩ :=
    exists_mem_reflPairsPerp_map_sub_ne_zero h2 hQ hdim h3 he hf hef hv
  have hfe : polar Q f e = 0 := by rw [polar_comm]; exact hef
  obtain ⟨g₂, hg₂, h₂⟩ :=
    exists_mem_reflPairsPerp_polar_eq_zero h2 hQ hdim hf he hfe hγ hQγ
  have hQv₁ : Q (g₁ v) = Q v :=
    map_of_mem (mem_orthogonalGroup_of_mem_reflPairsPerp hg₁) v
  have hQv₂ : Q (g₂ (g₁ v)) = Q v := by
    rw [map_of_mem (mem_orthogonalGroup_of_mem_reflPairsPerp hg₂), hQv₁]
  have hα0 : polar Q e (g₂ (g₁ v) - (0 : K) • e) = 0 := by simpa using h₂
  have hQ0 : Q (g₂ (g₁ v) - (0 : K) • e) ≠ 0 := by simpa [hQv₂] using hv
  obtain ⟨g₃, hg₃, h₃⟩ :=
    exists_mem_reflPairsPerp_polar_eq_zero h2 hQ hdim he hf hef hα0 hQ0
  refine ⟨g₃ * g₂ * g₁, ?_, ?_⟩
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Or.inl hg₃)
      · exact Subgroup.subset_closure (Or.inr hg₂)
    · exact Subgroup.subset_closure (Or.inl hg₁)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact h₃

end CFSG.ClassicalGroups.Orthogonal

end
