module

public import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Transitive

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap
open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private def reflectPairClosure_th2c (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {x | ∃ a b : V, Q a = Q b ∧ reflect Q a * reflect Q b = x}

private theorem conj_reflect_mul_reflect_mem_closure_th2c {Q : QuadraticForm K V}
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a b : V}
    (hab : Q a = Q b) :
    g * (reflect Q a * reflect Q b) * g⁻¹ ∈ reflectPairClosure_th2c Q := by
  unfold reflectPairClosure_th2c
  have h : g * (reflect Q a * reflect Q b) * g⁻¹ =
      reflect Q (g a) * reflect Q (g b) := by
    calc g * (reflect Q a * reflect Q b) * g⁻¹ =
        (g * reflect Q a * g⁻¹) * (g * reflect Q b * g⁻¹) := by group
      _ = reflect Q (g a) * reflect Q (g b) := by
        rw [reflect_conj hg, reflect_conj hg]
  rw [h]
  exact Subgroup.subset_closure
    ⟨g a, g b, by rw [map_of_mem hg, map_of_mem hg, hab], rfl⟩

private theorem conj_mem_reflectPairClosure_th2c {Q : QuadraticForm K V}
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {x : V ≃ₗ[K] V} (hx : x ∈ reflectPairClosure_th2c Q) :
    g * x * g⁻¹ ∈ reflectPairClosure_th2c Q := by
  unfold reflectPairClosure_th2c at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact conj_reflect_mul_reflect_mem_closure_th2c hg hab
  | one => simp
  | mul x y _ _ ihx ihy =>
    have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem (Subgroup.closure _) ihx ihy
  | inv x _ ihx =>
    have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [h]
    exact Subgroup.inv_mem (Subgroup.closure _) ihx

private theorem reflectPairClosure_le_orthogonalGroup_th2c (Q : QuadraticForm K V) :
    reflectPairClosure_th2c Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  unfold reflectPairClosure_th2c
  rw [Subgroup.closure_le]
  rintro x ⟨a, b, _, rfl⟩
  exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
    (reflect_mem_orthogonalGroup Q a) (reflect_mem_orthogonalGroup Q b)

theorem commutator_orthogonalGroup_le_of_reflect_mul_reflect_mem [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {X : Subgroup (V ≃ₗ[K] V)}
    (hX : ∀ a b : V, Q a = Q b → reflect Q a * reflect Q b ∈ X) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ X := by
  let S : Set (V ≃ₗ[K] V) := Set.range (reflect Q)
  have hN : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ x ∈ reflectPairClosure_th2c Q, g * x * g⁻¹ ∈ reflectPairClosure_th2c Q :=
    fun g hg x hx => conj_mem_reflectPairClosure_th2c hg hx
  have hNO := reflectPairClosure_le_orthogonalGroup_th2c Q
  have hSO : S ⊆ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨v, rfl⟩
    exact reflect_mem_orthogonalGroup Q v
  have hO : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (S ∪ reflectPairClosure_th2c Q) :=
    (orthogonalGroup_le_closure_reflect h2 hQ).trans
      (Subgroup.closure_mono Set.subset_union_left)
  have hS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ reflectPairClosure_th2c Q := by
    rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩
    have h : ⁅reflect Q a, reflect Q b⁆ =
        reflect Q a * reflect Q (reflect Q b a) := by
      rw [commutatorElement_def, reflect_inv]
      rw [← reflect_conj (reflect_mem_orthogonalGroup Q b), reflect_inv]
      group
    rw [h]
    unfold reflectPairClosure_th2c
    exact Subgroup.subset_closure
      ⟨a, reflect Q b a, by rw [map_of_mem (reflect_mem_orthogonalGroup Q b)], rfl⟩
  have hNX : reflectPairClosure_th2c Q ≤ X := by
    unfold reflectPairClosure_th2c
    rw [Subgroup.closure_le]
    rintro x ⟨a, b, hab, rfl⟩
    exact hX a b hab
  exact (commutator_le_of_le_closure (N := reflectPairClosure_th2c Q) (S := S)
    hN hNO hSO hO hS).trans hNX

variable [Finite K] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
private theorem mem_closure_reflPairsPerp_and_conj_th2c {e f w₀ : V}
    (hwe : polar Q e w₀ = 0) (hwf : polar Q f w₀ = 0)
    {X : Subgroup (V ≃ₗ[K] V)} (hXe : reflPairsPerp Q e ⊆ X)
    (hXf : reflPairsPerp Q f ⊆ X) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.closure (reflPairsPerp Q e ∪ reflPairsPerp Q f)) :
    g ∈ X ∧ reflect Q w₀ * g * reflect Q w₀ ∈ X := by
  have hrO : reflect Q w₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    reflect_mem_orthogonalGroup Q w₀
  have hre : reflect Q w₀ e = e :=
    reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact hwe)
  have hrf : reflect Q w₀ f = f :=
    reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact hwf)
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · exact ⟨hXe hg, hXe (by simpa [reflect_inv] using
        conj_mem_reflPairsPerp hrO hre hg)⟩
    · exact ⟨hXf hg, hXf (by simpa [reflect_inv] using
        conj_mem_reflPairsPerp hrO hrf hg)⟩
  | one =>
    refine ⟨X.one_mem, ?_⟩
    rw [mul_one, reflect_mul_self]
    exact X.one_mem
  | mul g h _ _ ihg ihh =>
    refine ⟨X.mul_mem ihg.1 ihh.1, ?_⟩
    have hrr : reflect Q w₀ * reflect Q w₀ = 1 := reflect_mul_self Q w₀
    have hid : reflect Q w₀ * (g * h) * reflect Q w₀ =
        (reflect Q w₀ * g * reflect Q w₀) * (reflect Q w₀ * h * reflect Q w₀) := by
      simp only [mul_assoc]
      rw [← mul_assoc (reflect Q w₀) (reflect Q w₀) (h * reflect Q w₀), hrr, one_mul]
    rw [hid]
    exact X.mul_mem ihg.2 ihh.2
  | inv g _ ihg =>
    refine ⟨X.inv_mem ihg.1, ?_⟩
    have hid : reflect Q w₀ * g⁻¹ * reflect Q w₀ =
        (reflect Q w₀ * g * reflect Q w₀)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, reflect_inv]
      group
    rw [hid]
    exact X.inv_mem ihg.2

omit [Finite K] [FiniteDimensional K V] in
private theorem closure_reflPairsPerp_le_orthogonalGroup_th2c (e f : V) :
    Subgroup.closure (reflPairsPerp Q e ∪ reflPairsPerp Q f) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [Subgroup.closure_le]
  rintro g (hg | hg)
  · exact mem_orthogonalGroup_of_mem_reflPairsPerp hg
  · exact mem_orthogonalGroup_of_mem_reflPairsPerp hg

omit [Finite K] [FiniteDimensional K V] in
private theorem reflect_mul_reflect_mem_of_mem_closure_th2c {e f w₀ : V}
    (hwe : polar Q e w₀ = 0) (hwf : polar Q f w₀ = 0)
    {X : Subgroup (V ≃ₗ[K] V)} (hXe : reflPairsPerp Q e ⊆ X)
    (hXf : reflPairsPerp Q f ⊆ X) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.closure (reflPairsPerp Q e ∪ reflPairsPerp Q f)) {v : V}
    (hv : reflect Q v * reflect Q w₀ ∈ X) :
    reflect Q (g v) * reflect Q w₀ ∈ X := by
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    closure_reflPairsPerp_le_orthogonalGroup_th2c e f hg
  have hgmem := mem_closure_reflPairsPerp_and_conj_th2c hwe hwf hXe hXf hg
  have hginv := mem_closure_reflPairsPerp_and_conj_th2c hwe hwf hXe hXf
    (Subgroup.inv_mem _ hg)
  have hmem : g * (reflect Q v * reflect Q w₀) ∈ X := X.mul_mem hgmem.1 hv
  have hEq : reflect Q (g v) * reflect Q w₀ =
      (g * (reflect Q v * reflect Q w₀)) * (reflect Q w₀ * g⁻¹ * reflect Q w₀) := by
    rw [← reflect_conj hgO]
    have hrr : reflect Q w₀ * reflect Q w₀ = 1 := reflect_mul_self Q w₀
    simp only [mul_assoc]
    rw [← mul_assoc (reflect Q w₀) (reflect Q w₀) (g⁻¹ * reflect Q w₀), hrr, one_mul]
  rw [hEq]
  exact X.mul_mem hmem hginv.2

private theorem reflect_mul_reflect_mem_of_map_eq_th2c (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f w₀ : V} (he : Q e ≠ 0)
    (hf : Q f ≠ 0) (hef : polar Q e f = 0) (hwe : polar Q e w₀ = 0)
    (hwf : polar Q f w₀ = 0) {X : Subgroup (V ≃ₗ[K] V)}
    (hXe : reflPairsPerp Q e ⊆ X) (hXf : reflPairsPerp Q f ⊆ X) {v : V}
    (hv : Q v = Q w₀) (hv0 : Q v ≠ 0) :
    reflect Q v * reflect Q w₀ ∈ X := by
  obtain ⟨g, hg, hgf⟩ :=
    exists_mem_closure_reflPairsPerp_polar_eq_zero h2 hQ hdim h3 he hf hef hv0
  have hgv : Q (g v) = Q w₀ := by
    rw [map_of_mem (closure_reflPairsPerp_le_orthogonalGroup_th2c e f hg), hv]
  have hmem : reflect Q (g v) * reflect Q w₀ ∈ reflPairsPerp Q f :=
    reflect_mul_reflect_mem_reflPairsPerp hgf hwf hgv
  have hXmem : reflect Q (g v) * reflect Q w₀ ∈ X := hXf hmem
  have hres := reflect_mul_reflect_mem_of_mem_closure_th2c hwe hwf hXe hXf
    (Subgroup.inv_mem _ hg) hXmem
  simpa [LinearEquiv.inv_apply_apply'] using hres

theorem reflect_mul_reflect_mem_of_reflPairsPerp_subset (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f : V} (he : Q e ≠ 0) (hf : Q f ≠ 0)
    (hef : polar Q e f = 0) {X : Subgroup (V ≃ₗ[K] V)} (hXe : reflPairsPerp Q e ⊆ X)
    (hXf : reflPairsPerp Q f ⊆ X) {a b : V} (hab : Q a = Q b) :
    reflect Q a * reflect Q b ∈ X := by
  by_cases hQa : Q a = 0
  · have hQb : Q b = 0 := by rw [← hab]; exact hQa
    rw [reflect_of_map_eq_zero hQa, reflect_of_map_eq_zero hQb, one_mul]
    exact X.one_mem
  · obtain ⟨w₀, hwe, hwf, hw₀⟩ :=
      exists_polar_eq_zero_polar_eq_zero_map_eq h2 hQ hdim he hf hef (Q a)
    have hwa : Q a = Q w₀ := hw₀.symm
    have hwb : Q b = Q w₀ := by rw [← hab]; exact hwa
    have haX := reflect_mul_reflect_mem_of_map_eq_th2c h2 hQ hdim h3 he hf hef
      hwe hwf hXe hXf hwa hQa
    have hbX := reflect_mul_reflect_mem_of_map_eq_th2c h2 hQ hdim h3 he hf hef
      hwe hwf hXe hXf hwb (by rw [← hab]; exact hQa)
    have hEq : (reflect Q a * reflect Q w₀) * (reflect Q b * reflect Q w₀)⁻¹ =
        reflect Q a * reflect Q b := by
      rw [mul_inv_rev, reflect_inv, reflect_inv]
      have hrr : reflect Q w₀ * reflect Q w₀ = 1 := reflect_mul_self Q w₀
      simp only [mul_assoc]
      rw [← mul_assoc (reflect Q w₀) (reflect Q w₀) (reflect Q b), hrr, one_mul]
    have hmem : (reflect Q a * reflect Q w₀) * (reflect Q b * reflect Q w₀)⁻¹ ∈ X :=
      X.mul_mem haX (X.inv_mem hbX)
    rwa [hEq] at hmem

theorem commutator_orthogonalGroup_le_of_reflPairsPerp_subset (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (h3 : (3 : K) ≠ 0 ∨ 5 ≤ Module.finrank K V) {e f : V} (he : Q e ≠ 0) (hf : Q f ≠ 0)
    (hef : polar Q e f = 0) {X : Subgroup (V ≃ₗ[K] V)} (hXe : reflPairsPerp Q e ⊆ X)
    (hXf : reflPairsPerp Q f ⊆ X) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ X := by
  exact commutator_orthogonalGroup_le_of_reflect_mul_reflect_mem h2 hQ fun a b hab =>
    reflect_mul_reflect_mem_of_reflPairsPerp_subset h2 hQ hdim h3 he hf hef hXe hXf hab

end CFSG.ClassicalGroups.Orthogonal

end
