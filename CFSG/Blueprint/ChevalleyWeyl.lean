module

public import CFSG.Blueprint.ChevalleySimpleRoots
public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.Blueprint.ChevalleyGenerators
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

private theorem rootVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

private theorem natAbs_cartan_self (i : Fin τ.rank) : (((τ.cartan i i).natAbs : ℕ) : R) = 2 := by
  rw [τ.cartan_self]
  norm_num

private theorem xOp_hVec (i j : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
  change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

private theorem xOp_hVec_self (i : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R i) = hVec τ R i + (2 * c) • rootVec τ R (Pi.single i 1) := by
  rw [xOp_hVec, natAbs_cartan_self]

private theorem xOp_rootVec_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_single τ i), xOp, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left rfl

private theorem xOp_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
      rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

private theorem xOp_rootVec_of_ne (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringUp τ i α + 1),
        (((stringDown τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, xOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

private theorem yOp_hVec (i j : Fin τ.rank) (c : R) :
    yOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1) := by
  change yOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

private theorem yOp_hVec_self (i : Fin τ.rank) (c : R) :
    yOp τ R i c (hVec τ R i) = hVec τ R i + (2 * c) • rootVec τ R (-Pi.single i 1) := by
  rw [yOp_hVec, natAbs_cartan_self]

private theorem yOp_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (-Pi.single i 1)) = rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_neg_single τ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

private theorem yOp_rootVec_single (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (Pi.single i 1)) =
      rootVec τ R (Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_of_isRoot (isRoot_single τ i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

private theorem yOp_rootVec_of_ne (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringDown τ i α + 1),
        (((stringUp τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α - (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_of_isRoot hα, yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₂).trans (ite_eq_right h₁)

private theorem end_ext {f g : Module.End R (RootModule τ R)}
    (hh : ∀ j, f (hVec τ R j) = g (hVec τ R j))
    (hr : ∀ α, IsRoot τ α → f (rootVec τ R α) = g (rootVec τ R α)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · rw [← rootVec_of_isRoot hα]
    exact hr α hα

section Definitions

variable (τ R)

@[expose] def xUnit (i : Fin τ.rank) (c : R) : (Module.End R (RootModule τ R))ˣ where
  val := xOp τ R i c
  inv := xOp τ R i (-c)
  val_inv := xOp_mul_xOp_neg (upTransport τ) i c
  inv_val := xOp_neg_mul_xOp (upTransport τ) i c

@[expose] def yUnit (i : Fin τ.rank) (c : R) : (Module.End R (RootModule τ R))ˣ where
  val := yOp τ R i c
  inv := yOp τ R i (-c)
  val_inv := yOp_mul_yOp_neg (downTransport τ) i c
  inv_val := yOp_neg_mul_yOp (downTransport τ) i c

@[expose] def weylElt (i : Fin τ.rank) (t : Rˣ) : (Module.End R (RootModule τ R))ˣ where
  val := xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t
  inv := xOp τ R i (-(t : R)) * yOp τ R i ((t⁻¹ : Rˣ) : R) * xOp τ R i (-(t : R))
  val_inv := by
    calc xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t *
          (xOp τ R i (-(t : R)) * yOp τ R i ((t⁻¹ : Rˣ) : R) * xOp τ R i (-(t : R))) =
        xOp τ R i t * (yOp τ R i (-((t⁻¹ : Rˣ) : R)) *
          (xOp τ R i t * xOp τ R i (-(t : R))) * yOp τ R i ((t⁻¹ : Rˣ) : R)) *
            xOp τ R i (-(t : R)) := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [xOp_mul_xOp_neg (upTransport τ), mul_one, yOp_neg_mul_yOp (downTransport τ),
            mul_one, xOp_mul_xOp_neg (upTransport τ)]
  inv_val := by
    calc xOp τ R i (-(t : R)) * yOp τ R i ((t⁻¹ : Rˣ) : R) * xOp τ R i (-(t : R)) *
          (xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t) =
        xOp τ R i (-(t : R)) * (yOp τ R i ((t⁻¹ : Rˣ) : R) *
          (xOp τ R i (-(t : R)) * xOp τ R i t) * yOp τ R i (-((t⁻¹ : Rˣ) : R))) *
            xOp τ R i t := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [xOp_neg_mul_xOp (upTransport τ), mul_one, yOp_mul_yOp_neg (downTransport τ),
            mul_one, xOp_neg_mul_xOp (upTransport τ)]

@[expose] def torusElt (i : Fin τ.rank) (t : Rˣ) : (Module.End R (RootModule τ R))ˣ :=
  weylElt τ R i t * weylElt τ R i (-1)

end Definitions

theorem coe_xUnit (i : Fin τ.rank) (c : R) :
    (xUnit τ R i c : Module.End R (RootModule τ R)) = xOp τ R i c :=
  rfl

theorem coe_xUnit_inv (i : Fin τ.rank) (c : R) :
    (((xUnit τ R i c)⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) =
      xOp τ R i (-c) :=
  rfl

theorem coe_yUnit (i : Fin τ.rank) (c : R) :
    (yUnit τ R i c : Module.End R (RootModule τ R)) = yOp τ R i c :=
  rfl

theorem coe_yUnit_inv (i : Fin τ.rank) (c : R) :
    (((yUnit τ R i c)⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) =
      yOp τ R i (-c) :=
  rfl

theorem coe_weylElt (i : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) =
      xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t :=
  rfl

theorem coe_weylElt_inv (i : Fin τ.rank) (t : Rˣ) :
    (((weylElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) =
      xOp τ R i (-(t : R)) * yOp τ R i ((t⁻¹ : Rˣ) : R) * xOp τ R i (-(t : R)) :=
  rfl

theorem coe_torusElt (i : Fin τ.rank) (t : Rˣ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) =
      (weylElt τ R i t : Module.End R (RootModule τ R)) *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) :=
  rfl

theorem weylElt_eq_xUnit_mul (i : Fin τ.rank) (t : Rˣ) :
    weylElt τ R i t = xUnit τ R i t * yUnit τ R i (-((t⁻¹ : Rˣ) : R)) * xUnit τ R i t :=
  Units.ext rfl

theorem xUnit_mem_adjointGroup {K : Type*} [Field K] (i : Fin τ.rank) (c : K) :
    xUnit τ K i c ∈ adjointGroup τ K :=
  Subgroup.subset_closure ⟨i, c, Or.inl rfl⟩

theorem yUnit_mem_adjointGroup {K : Type*} [Field K] (i : Fin τ.rank) (c : K) :
    yUnit τ K i c ∈ adjointGroup τ K :=
  Subgroup.subset_closure ⟨i, c, Or.inr rfl⟩

theorem weylElt_mem_adjointGroup {K : Type*} [Field K] (i : Fin τ.rank) (t : Kˣ) :
    weylElt τ K i t ∈ adjointGroup τ K := by
  rw [weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (xUnit_mem_adjointGroup i _) (yUnit_mem_adjointGroup i _))
    (xUnit_mem_adjointGroup i _)

theorem torusElt_mem_adjointGroup {K : Type*} [Field K] (i : Fin τ.rank) (t : Kˣ) :
    torusElt τ K i t ∈ adjointGroup τ K :=
  mul_mem (weylElt_mem_adjointGroup i t) (weylElt_mem_adjointGroup i (-1))

theorem simple_weyl_torus_elements (i : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) =
        xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t ∧
      (((weylElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
        xOp τ R i (-(t : R)) * yOp τ R i ((t⁻¹ : Rˣ) : R) * xOp τ R i (-(t : R)) ∧
      torusElt τ R i t = weylElt τ R i t * weylElt τ R i (-1) :=
  ⟨rfl, rfl, rfl⟩

theorem weylElt_torusElt_mem_adjointGroup {K : Type*} [Field K] (i : Fin τ.rank) (t : Kˣ) :
    weylElt τ K i t ∈ adjointGroup τ K ∧ torusElt τ K i t ∈ adjointGroup τ K :=
  ⟨weylElt_mem_adjointGroup i t, torusElt_mem_adjointGroup i t⟩

private theorem word_hVec (i j : Fin τ.rank) {t s : R} (hts : t * s = 1) :
    xOp τ R i t (yOp τ R i (-s) (xOp τ R i t (hVec τ R j))) =
      hVec τ R j - ((τ.cartan j i).natAbs : R) • hVec τ R i := by
  simp only [xOp_hVec, map_add, map_smul, yOp_hVec, yOp_rootVec_single, xOp_rootVec_neg_single,
    xOp_rootVec_single, natAbs_cartan_self]
  linear_combination (norm := module) hts •
    ((((τ.cartan j i).natAbs : R) * t * (t * s - 2)) • rootVec τ R (Pi.single i 1) +
      (((τ.cartan j i).natAbs : R) * (t * s - 1)) • hVec τ R i +
      (((τ.cartan j i).natAbs : R) * s) • rootVec τ R (-Pi.single i 1))

private theorem word_rootVec_single (i : Fin τ.rank) {t s : R} (hts : t * s = 1) :
    xOp τ R i t (yOp τ R i (-s) (xOp τ R i t (rootVec τ R (Pi.single i 1)))) =
      s ^ 2 • rootVec τ R (-Pi.single i 1) := by
  simp only [xOp_rootVec_single, yOp_rootVec_single, map_add, map_smul, xOp_hVec_self,
    xOp_rootVec_neg_single]
  linear_combination (norm := module) hts •
    ((t * s - 1) • rootVec τ R (Pi.single i 1) + s • hVec τ R i)

private theorem word_rootVec_neg_single (i : Fin τ.rank) {t s : R} (hts : t * s = 1) :
    xOp τ R i t (yOp τ R i (-s) (xOp τ R i t (rootVec τ R (-Pi.single i 1)))) =
      t ^ 2 • rootVec τ R (Pi.single i 1) := by
  simp only [xOp_rootVec_neg_single, map_add, map_smul, yOp_rootVec_neg_single, yOp_hVec_self,
    yOp_rootVec_single, xOp_hVec_self, xOp_rootVec_single]
  linear_combination (norm := module) hts •
    ((t ^ 2 * (t * s - 3)) • rootVec τ R (Pi.single i 1) + (t * (t * s - 2)) • hVec τ R i +
      (t * s - 1) • rootVec τ R (-Pi.single i 1))

theorem weylElt_hVec (i j : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R j) =
      hVec τ R j - ((τ.cartan j i).natAbs : R) • hVec τ R i := by
  rw [coe_weylElt, Module.End.mul_apply, Module.End.mul_apply]
  exact word_hVec i j (Units.mul_inv t)

theorem weylElt_hVec_self (i : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R i) = -hVec τ R i := by
  rw [weylElt_hVec, natAbs_cartan_self]
  module

theorem weylElt_rootVec_single (i : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R (Pi.single i 1)) =
      ((t⁻¹ : Rˣ) : R) ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [coe_weylElt, Module.End.mul_apply, Module.End.mul_apply]
  exact word_rootVec_single i (Units.mul_inv t)

theorem weylElt_rootVec_neg_single (i : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R (-Pi.single i 1)) =
      (t : R) ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [coe_weylElt, Module.End.mul_apply, Module.End.mul_apply]
  exact word_rootVec_neg_single i (Units.mul_inv t)

private def stringRoot (i : Fin τ.rank) (α : Fin τ.rank → ℤ) (j : ℕ) : Fin τ.rank → ℤ :=
  α + ((j : ℤ) - stringDown τ i α) • Pi.single i 1

variable (R) in
private def stringMap (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    (Fin (stringUp τ i α + stringDown τ i α + 1) →₀ R) →ₗ[R] RootModule τ R :=
  Finsupp.linearCombination R fun j => rootVec τ R (stringRoot i α j)

private theorem stringMap_single (i : Fin τ.rank) (α : Fin τ.rank → ℤ)
    (j : Fin (stringUp τ i α + stringDown τ i α + 1)) :
    stringMap R i α (Finsupp.single j 1) = rootVec τ R (stringRoot i α j) := by
  rw [stringMap, Finsupp.linearCombination_single, one_smul]

private theorem stringRoot_stringDown (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    stringRoot i α (stringDown τ i α) = α := by
  simp [stringRoot]

private theorem rootVec_eq_stringMap (i : Fin τ.rank) (α : Fin τ.rank → ℤ)
    (hq : stringDown τ i α < stringUp τ i α + stringDown τ i α + 1) :
    rootVec τ R α = stringMap R i α (Finsupp.single ⟨stringDown τ i α, hq⟩ 1) := by
  rw [stringMap_single, Fin.val_mk, stringRoot_stringDown]

private theorem stringRoot_stringUp {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    stringRoot i α (stringUp τ i α) = reflect τ i α := by
  rw [(root_string_reflection hα i).2.1, stringRoot]

private theorem stringRoot_add (i : Fin τ.rank) (α : Fin τ.rank → ℤ) (j k : ℕ) :
    stringRoot i α j + (k : ℤ) • Pi.single i 1 = stringRoot i α (j + k) := by
  simp only [stringRoot, Nat.cast_add]
  rw [add_assoc, ← add_smul, sub_add_eq_add_sub]

private theorem stringRoot_sub (i : Fin τ.rank) (α : Fin τ.rank → ℤ) {j k : ℕ} (h : k ≤ j) :
    stringRoot i α j - (k : ℤ) • Pi.single i 1 = stringRoot i α (j - k) := by
  simp only [stringRoot, Nat.cast_sub h]
  rw [add_sub_assoc, ← sub_smul, sub_right_comm]

private theorem stringRoot_spec {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) {j : ℕ}
    (hj : j ≤ stringUp τ i α + stringDown τ i α) :
    IsRoot τ (stringRoot i α j) ∧ stringRoot i α j ≠ Pi.single i 1 ∧
      stringRoot i α j ≠ -Pi.single i 1 ∧
      stringUp τ i (stringRoot i α j) = stringUp τ i α + stringDown τ i α - j ∧
      stringDown τ i (stringRoot i α j) = j := by
  obtain ⟨-, -, htr⟩ := root_string_transport hα i h₁ h₂
  obtain ⟨r, r₁, r₂, hu, hd⟩ := htr ((j : ℤ) - stringDown τ i α) (by omega) (by omega)
  unfold stringRoot
  exact ⟨r, r₁, r₂, by omega, by omega⟩

private theorem xOp_stringMap {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (c : R)
    (w : Fin (stringUp τ i α + stringDown τ i α + 1) →₀ R) :
    xOp τ R i c (stringMap R i α w) = stringMap R i α (binomX _ c w) := by
  suffices h : xOp τ R i c ∘ₗ stringMap R i α = stringMap R i α ∘ₗ binomX _ c from
    LinearMap.congr_fun h w
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  obtain ⟨r, r₁, r₂, hu, hd⟩ := stringRoot_spec hα h₁ h₂ (Nat.le_of_lt_succ j.2)
  rw [stringMap_single, xOp_rootVec_of_ne i c r r₁ r₂, hu, hd, binomX_single, map_sum,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_smul, stringMap_single, stringRoot_add]

private theorem yOp_stringMap {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (c : R)
    (w : Fin (stringUp τ i α + stringDown τ i α + 1) →₀ R) :
    yOp τ R i c (stringMap R i α w) = stringMap R i α (binomY _ c w) := by
  suffices h : yOp τ R i c ∘ₗ stringMap R i α = stringMap R i α ∘ₗ binomY _ c from
    LinearMap.congr_fun h w
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  obtain ⟨r, r₁, r₂, hu, hd⟩ := stringRoot_spec hα h₁ h₂ (Nat.le_of_lt_succ j.2)
  rw [stringMap_single, yOp_rootVec_of_ne i c r r₁ r₂, hu, hd, binomY_single, map_sum,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_smul, stringMap_single, stringRoot_sub i α (Nat.le_of_lt_succ k.2)]

private theorem weylElt_stringMap {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (t : Rˣ)
    (w : Fin (stringUp τ i α + stringDown τ i α + 1) →₀ R) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (stringMap R i α w) =
      stringMap R i α (binomN _ t w) := by
  simp only [coe_weylElt, binomN, Module.End.mul_apply]
  rw [xOp_stringMap hα h₁ h₂, yOp_stringMap hα h₁ h₂, xOp_stringMap hα h₁ h₂]

private theorem weylElt_rootVec_of_ne (i : Fin τ.rank) (t : Rˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R α) =
      ((-1) ^ stringDown τ i α * ((t ^ (-∑ j, τ.cartan i j * α j) : Rˣ) : R)) •
        rootVec τ R (reflect τ i α) := by
  have hq : stringDown τ i α < stringUp τ i α + stringDown τ i α + 1 := by omega
  have hrev : ((Fin.rev (⟨stringDown τ i α, hq⟩ :
      Fin (stringUp τ i α + stringDown τ i α + 1)) : ℕ)) = stringUp τ i α := by
    rw [Fin.val_rev, Fin.val_mk]
    omega
  have hexp : ((stringUp τ i α + stringDown τ i α : ℕ) : ℤ) - 2 * (stringDown τ i α : ℤ) =
      -∑ j, τ.cartan i j * α j := by
    rw [(root_string_reflection hα i).1]
    push_cast
    ring
  rw [rootVec_eq_stringMap i α hq, weylElt_stringMap hα h₁ h₂, binomN_single, map_smul,
    stringMap_single, hrev, stringRoot_stringUp hα, Fin.val_mk, hexp]

theorem weylElt_rootVec (i : Fin τ.rank) (t : Rˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R α) =
      ((-1) ^ stringDown τ i α * ((t ^ (-∑ j, τ.cartan i j * α j) : Rˣ) : R)) •
        rootVec τ R (reflect τ i α) := by
  by_cases h₁ : α = Pi.single i 1
  · subst h₁
    rw [weylElt_rootVec_single, stringDown_single, sum_cartan_mul_single, reflect_single_self,
      neg_one_sq, one_mul, zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val]
  by_cases h₂ : α = -Pi.single i 1
  · subst h₂
    have hsum : ∑ j, τ.cartan i j * (-Pi.single i 1 : Fin τ.rank → ℤ) j = -2 := by
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_cartan_mul_single]
    have hr : reflect τ i (-Pi.single i 1) = Pi.single i 1 := by
      rw [← reflect_single_self, reflect_reflect]
    rw [weylElt_rootVec_neg_single, stringDown_neg_single, hsum, hr, neg_neg, pow_zero, one_mul,
      zpow_ofNat, Units.val_pow_eq_pow_val]
  exact weylElt_rootVec_of_ne i t hα h₁ h₂

theorem weylElt_inv (i : Fin τ.rank) (t : Rˣ) : (weylElt τ R i t)⁻¹ = weylElt τ R i (-t) := by
  refine Units.ext ?_
  rw [coe_weylElt_inv, coe_weylElt, Units.val_neg, inv_neg, Units.val_neg, neg_neg]

theorem simple_weyl_basis_action (i : Fin τ.rank) (t : Rˣ) :
    (∀ j : Fin τ.rank, (weylElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R j) =
        hVec τ R j - ((τ.cartan j i).natAbs : R) • hVec τ R i) ∧
      (∀ α : Fin τ.rank → ℤ, IsRoot τ α →
        (weylElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R α) =
          ((-1) ^ stringDown τ i α * ((t ^ (-∑ j, τ.cartan i j * α j) : Rˣ) : R)) •
            rootVec τ R (reflect τ i α)) ∧
      (weylElt τ R i t)⁻¹ = weylElt τ R i (-t) :=
  ⟨fun j => weylElt_hVec i j t, fun _ hα => weylElt_rootVec i t hα, weylElt_inv i t⟩

private theorem neg_one_pow_mul_zpow_mul_pow (p q : ℕ) :
    (-1 : R) ^ q * (((-1 : Rˣ) ^ (-((q : ℤ) - p)) : Rˣ) : R) * (-1 : R) ^ p = 1 := by
  have h : (-1 : Rˣ) ^ q * (-1) ^ (-((q : ℤ) - p)) * (-1) ^ p = 1 := by
    rw [← zpow_natCast (-1 : Rˣ) q, ← zpow_natCast (-1 : Rˣ) p, ← zpow_add, ← zpow_add,
      show (q : ℤ) + -((q : ℤ) - p) + p = 2 * p by ring]
    exact Even.neg_one_zpow (even_two_mul _)
  have h' := congrArg Units.val h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h'
  exact h'

theorem torusElt_hVec (i j : Fin τ.rank) (t : Rˣ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R j) = hVec τ R j := by
  simp only [coe_torusElt, Module.End.mul_apply, weylElt_hVec, map_sub, map_smul,
    natAbs_cartan_self]
  module

theorem torusElt_rootVec (i : Fin τ.rank) (t : Rˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R α) =
      ((t ^ (∑ j, τ.cartan i j * α j) : Rˣ) : R) • rootVec τ R α := by
  obtain ⟨hm, -, -, hd⟩ := root_string_reflection hα i
  rw [coe_torusElt, Module.End.mul_apply, weylElt_rootVec i (-1) hα, map_smul,
    weylElt_rootVec i t (IsRoot.reflect i hα), reflect_reflect, sum_cartan_mul_reflect, hd,
    neg_neg, smul_smul]
  congr 1
  rw [hm]
  linear_combination ((t ^ ((stringDown τ i α : ℤ) - stringUp τ i α) : Rˣ) : R) *
    neg_one_pow_mul_zpow_mul_pow (R := R) (stringUp τ i α) (stringDown τ i α)

theorem torusElt_one (i : Fin τ.rank) : torusElt τ R i 1 = 1 := by
  refine Units.ext (end_ext (fun j => ?_) (fun α hα => ?_))
  · rw [torusElt_hVec, Units.val_one, Module.End.one_apply]
  · simp only [torusElt_rootVec i 1 hα, one_zpow, Units.val_one, one_smul, Module.End.one_apply]

theorem torusElt_mul (i : Fin τ.rank) (t u : Rˣ) :
    torusElt τ R i (t * u) = torusElt τ R i t * torusElt τ R i u := by
  refine Units.ext (end_ext (fun j => ?_) (fun α hα => ?_))
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_hVec]
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ hα, map_smul, smul_smul,
      mul_zpow]
    congr 1
    ring

theorem torusElt_mul_comm (i j : Fin τ.rank) (t u : Rˣ) :
    torusElt τ R i t * torusElt τ R j u = torusElt τ R j u * torusElt τ R i t := by
  refine Units.ext (end_ext (fun k => ?_) (fun α hα => ?_))
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_hVec]
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ hα, map_smul,
      smul_smul]
    congr 1
    ring

theorem simple_torus_basis_action (i : Fin τ.rank) (t : Rˣ) :
    (∀ j : Fin τ.rank,
        (torusElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R j) = hVec τ R j) ∧
      (∀ α : Fin τ.rank → ℤ, IsRoot τ α →
        (torusElt τ R i t : Module.End R (RootModule τ R)) (rootVec τ R α) =
          ((t ^ (∑ j, τ.cartan i j * α j) : Rˣ) : R) • rootVec τ R α) ∧
      torusElt τ R i 1 = 1 ∧
      (∀ u : Rˣ, torusElt τ R i (t * u) = torusElt τ R i t * torusElt τ R i u) ∧
      ∀ (j : Fin τ.rank) (u : Rˣ),
        torusElt τ R i t * torusElt τ R j u = torusElt τ R j u * torusElt τ R i t :=
  ⟨fun j => torusElt_hVec i j t, fun _ hα => torusElt_rootVec i t hα, torusElt_one i,
    fun u => torusElt_mul i t u, fun j u => torusElt_mul_comm i j t u⟩

theorem weylElt_mul_xOp (i : Fin τ.rank) (t : Rˣ) (c : R) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) * xOp τ R i c =
      yOp τ R i (-c * ((t⁻¹ : Rˣ) : R) ^ 2) *
        (weylElt τ R i t : Module.End R (RootModule τ R)) := by
  refine end_ext (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, xOp_hVec, map_add, map_smul, weylElt_hVec,
      weylElt_rootVec_single, map_sub, yOp_hVec, natAbs_cartan_self]
    module
  simp only [Module.End.mul_apply]
  by_cases h₁ : α = Pi.single i 1
  · subst h₁
    rw [xOp_rootVec_single, weylElt_rootVec_single, map_smul, yOp_rootVec_neg_single]
  by_cases h₂ : α = -Pi.single i 1
  · subst h₂
    simp only [xOp_rootVec_neg_single, map_add, map_smul, weylElt_rootVec_neg_single,
      weylElt_hVec_self, weylElt_rootVec_single, yOp_rootVec_single]
    linear_combination (norm := module) (Units.mul_inv t) •
      ((c * ((t : R) * ((t⁻¹ : Rˣ) : R) + 1)) • hVec τ R i -
        (c ^ 2 * ((t⁻¹ : Rˣ) : R) ^ 2 * ((t : R) * ((t⁻¹ : Rˣ) : R) + 1)) •
          rootVec τ R (-Pi.single i 1))
  have hq : stringDown τ i α < stringUp τ i α + stringDown τ i α + 1 := by omega
  have key := LinearMap.congr_fun (binomN_mul_binomX t c)
    (Finsupp.single (⟨stringDown τ i α, hq⟩ : Fin (stringUp τ i α + stringDown τ i α + 1)) 1)
  rw [Module.End.mul_apply, Module.End.mul_apply, Units.val_pow_eq_pow_val] at key
  rw [rootVec_eq_stringMap i α hq, xOp_stringMap hα h₁ h₂, weylElt_stringMap hα h₁ h₂,
    weylElt_stringMap hα h₁ h₂, yOp_stringMap hα h₁ h₂, key]

theorem weylElt_mul_yOp (i : Fin τ.rank) (t : Rˣ) (c : R) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) * yOp τ R i c =
      xOp τ R i (-c * (t : R) ^ 2) * (weylElt τ R i t : Module.End R (RootModule τ R)) := by
  refine end_ext (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, yOp_hVec, map_add, map_smul, weylElt_hVec,
      weylElt_rootVec_neg_single, map_sub, xOp_hVec, natAbs_cartan_self]
    module
  simp only [Module.End.mul_apply]
  by_cases h₁ : α = Pi.single i 1
  · subst h₁
    simp only [yOp_rootVec_single, map_add, map_smul, weylElt_rootVec_single,
      weylElt_hVec_self, weylElt_rootVec_neg_single, xOp_rootVec_neg_single]
    linear_combination (norm := module) (Units.mul_inv t) •
      ((c * ((t : R) * ((t⁻¹ : Rˣ) : R) + 1)) • hVec τ R i -
        (c ^ 2 * (t : R) ^ 2 * ((t : R) * ((t⁻¹ : Rˣ) : R) + 1)) •
          rootVec τ R (Pi.single i 1))
  by_cases h₂ : α = -Pi.single i 1
  · subst h₂
    rw [yOp_rootVec_neg_single, weylElt_rootVec_neg_single, map_smul, xOp_rootVec_single]
  have hq : stringDown τ i α < stringUp τ i α + stringDown τ i α + 1 := by omega
  have key := LinearMap.congr_fun (binomN_mul_binomY t c)
    (Finsupp.single (⟨stringDown τ i α, hq⟩ : Fin (stringUp τ i α + stringDown τ i α + 1)) 1)
  rw [Module.End.mul_apply, Module.End.mul_apply, Units.val_pow_eq_pow_val] at key
  rw [rootVec_eq_stringMap i α hq, yOp_stringMap hα h₁ h₂, weylElt_stringMap hα h₁ h₂,
    weylElt_stringMap hα h₁ h₂, xOp_stringMap hα h₁ h₂, key]

theorem weylElt_mul_xOp_mul_inv (i : Fin τ.rank) (t : Rˣ) (c : R) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) * xOp τ R i c *
        (((weylElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      yOp τ R i (-c * ((t⁻¹ : Rˣ) : R) ^ 2) := by
  rw [weylElt_mul_xOp, Units.mul_inv_cancel_right]

theorem weylElt_mul_yOp_mul_inv (i : Fin τ.rank) (t : Rˣ) (c : R) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) * yOp τ R i c *
        (((weylElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      xOp τ R i (-c * (t : R) ^ 2) := by
  rw [weylElt_mul_yOp, Units.mul_inv_cancel_right]

private theorem units_conj_mul_mul {M : Type*} [Monoid M] (g : Mˣ) (a b c : M) :
    (g : M) * (a * b * c) * ((g⁻¹ : Mˣ) : M) =
      (g : M) * a * ((g⁻¹ : Mˣ) : M) * ((g : M) * b * ((g⁻¹ : Mˣ) : M)) *
        ((g : M) * c * ((g⁻¹ : Mˣ) : M)) := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem coe_weylElt_eq_yOp_mul (i : Fin τ.rank) (t : Rˣ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) =
      yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) := by
  have h₁ : -(t : R) * ((t⁻¹ : Rˣ) : R) ^ 2 = -((t⁻¹ : Rˣ) : R) := by
    linear_combination (-((t⁻¹ : Rˣ) : R)) * Units.mul_inv t
  have h₂ : -(-((t⁻¹ : Rˣ) : R)) * (t : R) ^ 2 = t := by
    linear_combination (t : R) * Units.mul_inv t
  have h := units_conj_mul_mul (weylElt τ R i t) (xOp τ R i t)
    (yOp τ R i (-((t⁻¹ : Rˣ) : R))) (xOp τ R i t)
  rw [← coe_weylElt, Units.mul_inv_cancel_right, weylElt_mul_xOp_mul_inv,
    weylElt_mul_yOp_mul_inv, h₁, h₂] at h
  exact h

theorem simple_weyl_rank_one_conjugation (i : Fin τ.rank) (t : Rˣ) (c : R) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) * xOp τ R i c *
          (((weylElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) =
        yOp τ R i (-c * ((t⁻¹ : Rˣ) : R) ^ 2) ∧
      (weylElt τ R i t : Module.End R (RootModule τ R)) * yOp τ R i c *
          (((weylElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) =
        xOp τ R i (-c * (t : R) ^ 2) ∧
      (weylElt τ R i t : Module.End R (RootModule τ R)) =
        yOp τ R i (-((t⁻¹ : Rˣ) : R)) * xOp τ R i t * yOp τ R i (-((t⁻¹ : Rˣ) : R)) :=
  ⟨weylElt_mul_xOp_mul_inv i t c, weylElt_mul_yOp_mul_inv i t c, coe_weylElt_eq_yOp_mul i t⟩

end CFSG.Blueprint.Chevalley
