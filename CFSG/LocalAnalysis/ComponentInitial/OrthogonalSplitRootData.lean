module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise

section Roots

variable (r : ℕ)

@[expose] def eps (i : Fin r) : Fin r → ℤ := Pi.single i 1

@[expose] def roots : Set (Fin r → ℤ) :=
  {α | ∃ i j : Fin r, i < j ∧ (α = eps r i - eps r j ∨ α = -eps r i + eps r j ∨
    α = eps r i + eps r j ∨ α = -eps r i - eps r j)}

@[expose] def posRoots : Set (Fin r → ℤ) :=
  {α | ∃ i j : Fin r, i < j ∧ (α = eps r i - eps r j ∨ α = eps r i + eps r j)}

@[expose] def simpleRoot (i : Fin r) : Fin r → ℤ :=
  if h : i.val + 1 < r then eps r i - eps r ⟨i.val + 1, h⟩
  else eps r ⟨r - 2, by have := i.isLt; omega⟩ + eps r i

variable {r}

theorem eps_apply (i j : Fin r) : eps r i j = if j = i then 1 else 0 := by
  simp [eps, Pi.single_apply]

theorem posRoots_subset_roots : posRoots r ⊆ roots r := by
  rintro α ⟨i, j, hij, h | h⟩
  · exact ⟨i, j, hij, Or.inl h⟩
  · exact ⟨i, j, hij, Or.inr (Or.inr (Or.inl h))⟩

theorem eps_sub_eps_inj {i j k l : Fin r} (hij : i < j)
    (h : eps r i - eps r j = eps r k - eps r l) : i = k ∧ j = l := by
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.sub_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem neg_eps_add_eps_inj {i j k l : Fin r} (hij : i < j)
    (h : -eps r i + eps r j = -eps r k + eps r l) : i = k ∧ j = l := by
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.neg_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem eps_add_eps_inj {i j k l : Fin r} (hij : i < j) (hkl : k < l)
    (h : eps r i + eps r j = eps r k + eps r l) : i = k ∧ j = l := by
  have hi := congrFun h i
  have hj := congrFun h j
  have hk := congrFun h k
  simp only [Pi.add_apply, eps_apply] at hi hj hk
  split_ifs at hi hj hk <;> omega

theorem neg_eps_sub_eps_inj {i j k l : Fin r} (hij : i < j) (hkl : k < l)
    (h : -eps r i - eps r j = -eps r k - eps r l) : i = k ∧ j = l := by
  have hi := congrFun h i
  have hj := congrFun h j
  have hk := congrFun h k
  simp only [Pi.sub_apply, Pi.neg_apply, eps_apply] at hi hj hk
  split_ifs at hi hj hk <;> omega

theorem neg_eps_add_eps_ne_eps_sub_eps {i j k l : Fin r} (hij : i < j) (hkl : k < l) :
    -eps r i + eps r j ≠ eps r k - eps r l := by
  intro h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem eps_add_eps_ne_eps_sub_eps {i j k l : Fin r} (hij : i < j) :
    eps r i + eps r j ≠ eps r k - eps r l := by
  intro h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.sub_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem eps_add_eps_ne_neg_eps_add_eps {i j k l : Fin r} (hij : i < j) :
    eps r i + eps r j ≠ -eps r k + eps r l := by
  intro h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.neg_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem neg_eps_sub_eps_ne_eps_sub_eps {i j k l : Fin r} (hij : i < j) :
    -eps r i - eps r j ≠ eps r k - eps r l := by
  intro h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.sub_apply, Pi.neg_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem neg_eps_sub_eps_ne_neg_eps_add_eps {i j k l : Fin r} (hij : i < j) :
    -eps r i - eps r j ≠ -eps r k + eps r l := by
  intro h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, eps_apply] at hi hj
  split_ifs at hi hj <;> omega

theorem neg_eps_sub_eps_ne_eps_add_eps {i j k l : Fin r} :
    -eps r i - eps r j ≠ eps r k + eps r l := by
  intro h
  have hi := congrFun h i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, eps_apply] at hi
  split_ifs at hi <;> omega

end Roots

section Weyl

variable (r : ℕ)

@[expose] def signedPermAut (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) :
    (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) where
  toFun x j := (δ (σ⁻¹ j) : ℤ) * x (σ⁻¹ j)
  invFun y i := (δ i : ℤ) * y (σ i)
  left_inv x := funext fun i => by
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, ← mul_assoc, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_mul]
  right_inv y := funext fun j => by
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, ← mul_assoc, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_mul]
  map_add' x y := funext fun j => by simp only [Pi.add_apply, mul_add]
  map_smul' c x := funext fun j => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm]

variable {r}

theorem signedPermAut_apply (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) (x : Fin r → ℤ)
    (j : Fin r) : signedPermAut r σ δ x j = (δ (σ⁻¹ j) : ℤ) * x (σ⁻¹ j) :=
  rfl

theorem signedPermAut_eps (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) (i : Fin r) :
    signedPermAut r σ δ (eps r i) = (δ i : ℤ) • eps r (σ i) := by
  funext j
  rw [signedPermAut_apply, Pi.smul_apply, eps_apply, eps_apply, smul_eq_mul]
  by_cases h : j = σ i
  · subst h
    simp
  · have h' : σ⁻¹ j ≠ i := fun h' => h (Equiv.Perm.inv_eq_iff_eq.1 h')
    rw [ite_eq_right h, ite_eq_right h', mul_zero, mul_zero]

theorem signedPermAut_mul (σ τ : Equiv.Perm (Fin r)) (δ ε : Fin r → ℤˣ) :
    signedPermAut r σ δ * signedPermAut r τ ε =
      signedPermAut r (σ * τ) fun i => ε i * δ (τ i) := by
  ext x j
  simp only [LinearEquiv.mul_apply, signedPermAut_apply, mul_inv_rev, Equiv.Perm.mul_apply,
    Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Units.val_mul]
  ring

theorem signedPermAut_one : signedPermAut r 1 1 = 1 := by
  ext x j
  simp [signedPermAut_apply]

theorem signedPermAut_inv (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) :
    (signedPermAut r σ δ)⁻¹ = signedPermAut r σ⁻¹ fun i => δ (σ⁻¹ i) := by
  rw [inv_eq_iff_mul_eq_one, signedPermAut_mul]
  ext x j
  simp [signedPermAut_apply, Int.units_mul_self]

variable (r)

@[expose] def weylGroup : Subgroup ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) where
  carrier := {w | ∃ (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ), ∏ i, δ i = 1 ∧
    w = signedPermAut r σ δ}
  mul_mem' := by
    rintro _ _ ⟨σ, δ, hδ, rfl⟩ ⟨τ, ε, hε, rfl⟩
    refine ⟨σ * τ, fun i => ε i * δ (τ i), ?_, signedPermAut_mul σ τ δ ε⟩
    rw [Finset.prod_mul_distrib, hε, Equiv.prod_comp τ δ, hδ, one_mul]
  one_mem' := ⟨1, 1, by simp, signedPermAut_one.symm⟩
  inv_mem' := by
    rintro _ ⟨σ, δ, hδ, rfl⟩
    refine ⟨σ⁻¹, fun i => δ (σ⁻¹ i), ?_, signedPermAut_inv σ δ⟩
    rw [Equiv.prod_comp σ⁻¹ δ, hδ]

variable {r}

theorem mem_weylGroup {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} :
    w ∈ weylGroup r ↔ ∃ (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ), ∏ i, δ i = 1 ∧
      w = signedPermAut r σ δ :=
  Iff.rfl

end Weyl

section RootElt

variable (r : ℕ) (K : Type*) [Field K]

open Classical in
@[expose] noncomputable def rootElt (α : Fin r → ℤ) (t : K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = eps r p.1 - eps r p.2 then
    eichler (quadPlus r K) (Pi.single (Sum.inl h.choose.1) 1)
      ((-t) • Pi.single (Sum.inr h.choose.2) 1)
  else if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = -eps r p.1 + eps r p.2 then
    eichler (quadPlus r K) (Pi.single (Sum.inl h.choose.2) 1)
      ((-t) • Pi.single (Sum.inr h.choose.1) 1)
  else if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = eps r p.1 + eps r p.2 then
    eichler (quadPlus r K) (Pi.single (Sum.inl h.choose.1) 1)
      ((-t) • Pi.single (Sum.inl h.choose.2) 1)
  else if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = -eps r p.1 - eps r p.2 then
    eichler (quadPlus r K) (Pi.single (Sum.inr h.choose.2) 1)
      ((-t) • Pi.single (Sum.inr h.choose.1) 1)
  else 1

variable {r K}

theorem polar_single (v : Fin r ⊕ Fin r → K) (c : Fin r ⊕ Fin r) :
    polar (quadPlus r K) v (Pi.single c 1) = v c.swap := by
  rcases c with i | i
  · exact polar_quadPlus_single_inl r K v i
  · exact polar_quadPlus_single_inr r K v i

theorem polar_single_single {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) :
    polar (quadPlus r K) (Pi.single c 1) (Pi.single d 1) = 0 := by
  rw [polar_comm, polar_single, Pi.single_apply, ite_eq_right]
  intro h'
  exact absurd h'.symm h

theorem polar_single_smul_single {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (t : K) :
    polar (quadPlus r K) (Pi.single c 1) (t • Pi.single d 1) = 0 := by
  rw [polar_smul_right_eq, polar_single_single h, mul_zero]

theorem coe_eichler_single {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (t : K) :
    ((eichler (quadPlus r K) (Pi.single c 1) (t • Pi.single d 1) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus r K) (Pi.single c 1) (t • Pi.single d 1) :=
  LinearMap.ext fun x =>
    eichler_apply (quadPlus_single c) (polar_single_smul_single h t) x

theorem eichler_single_mul {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (s t : K) :
    eichler (quadPlus r K) (Pi.single c 1) (s • Pi.single d 1) *
        eichler (quadPlus r K) (Pi.single c 1) (t • Pi.single d 1) =
      eichler (quadPlus r K) (Pi.single c 1) ((s + t) • Pi.single d 1) := by
  rw [eichler_mul (polar_single_smul_single h s) (polar_single_smul_single h t), add_smul]

theorem rootElt_eps_sub_eps' {i j : Fin r} (hij : i < j) (t : K) :
    rootElt r K (eps r i - eps r j) t =
      eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1) := by
  have h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ eps r i - eps r j = eps r p.1 - eps r p.2 :=
    ⟨(i, j), hij, rfl⟩
  rw [rootElt, dite_eq_left h]
  obtain ⟨h1, h2⟩ := eps_sub_eps_inj hij h.choose_spec.2
  rw [← h1, ← h2]

theorem rootElt_neg_eps_add_eps' {i j : Fin r} (hij : i < j) (t : K) :
    rootElt r K (-eps r i + eps r j) t =
      eichler (quadPlus r K) (Pi.single (Sum.inl j) 1) ((-t) • Pi.single (Sum.inr i) 1) := by
  have h0 : ¬∃ p : Fin r × Fin r, p.1 < p.2 ∧ -eps r i + eps r j = eps r p.1 - eps r p.2 :=
    fun ⟨p, hp, hp'⟩ => neg_eps_add_eps_ne_eps_sub_eps hij hp hp'
  have h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ -eps r i + eps r j = -eps r p.1 + eps r p.2 :=
    ⟨(i, j), hij, rfl⟩
  rw [rootElt, dite_eq_right h0, dite_eq_left h]
  obtain ⟨h1, h2⟩ := neg_eps_add_eps_inj hij h.choose_spec.2
  rw [← h1, ← h2]

theorem rootElt_eps_add_eps' {i j : Fin r} (hij : i < j) (t : K) :
    rootElt r K (eps r i + eps r j) t =
      eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inl j) 1) := by
  have h0 : ¬∃ p : Fin r × Fin r, p.1 < p.2 ∧ eps r i + eps r j = eps r p.1 - eps r p.2 :=
    fun ⟨_, _, hp'⟩ => eps_add_eps_ne_eps_sub_eps hij hp'
  have h1 : ¬∃ p : Fin r × Fin r, p.1 < p.2 ∧ eps r i + eps r j = -eps r p.1 + eps r p.2 :=
    fun ⟨_, _, hp'⟩ => eps_add_eps_ne_neg_eps_add_eps hij hp'
  have h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ eps r i + eps r j = eps r p.1 + eps r p.2 :=
    ⟨(i, j), hij, rfl⟩
  rw [rootElt, dite_eq_right h0, dite_eq_right h1, dite_eq_left h]
  obtain ⟨h1, h2⟩ := eps_add_eps_inj hij h.choose_spec.1 h.choose_spec.2
  rw [← h1, ← h2]

theorem rootElt_neg_eps_sub_eps' {i j : Fin r} (hij : i < j) (t : K) :
    rootElt r K (-eps r i - eps r j) t =
      eichler (quadPlus r K) (Pi.single (Sum.inr j) 1) ((-t) • Pi.single (Sum.inr i) 1) := by
  have h0 : ¬∃ p : Fin r × Fin r, p.1 < p.2 ∧ -eps r i - eps r j = eps r p.1 - eps r p.2 :=
    fun ⟨_, _, hp'⟩ => neg_eps_sub_eps_ne_eps_sub_eps hij hp'
  have h1 : ¬∃ p : Fin r × Fin r, p.1 < p.2 ∧ -eps r i - eps r j = -eps r p.1 + eps r p.2 :=
    fun ⟨_, _, hp'⟩ => neg_eps_sub_eps_ne_neg_eps_add_eps hij hp'
  have h2 : ¬∃ p : Fin r × Fin r, p.1 < p.2 ∧ -eps r i - eps r j = eps r p.1 + eps r p.2 :=
    fun ⟨_, _, hp'⟩ => neg_eps_sub_eps_ne_eps_add_eps hp'
  have h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ -eps r i - eps r j = -eps r p.1 - eps r p.2 :=
    ⟨(i, j), hij, rfl⟩
  rw [rootElt, dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_left h]
  obtain ⟨h1, h2⟩ := neg_eps_sub_eps_inj hij h.choose_spec.1 h.choose_spec.2
  rw [← h1, ← h2]

theorem rootElt_eps_sub_eps {i j : Fin r} (hij : i < j) (t : K) :
    ((rootElt r K (eps r i - eps r j) t : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) :
      (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus r K) (Pi.single (Sum.inl i) 1)
        ((-t) • Pi.single (Sum.inr j) 1) := by
  rw [rootElt_eps_sub_eps' hij]
  exact coe_eichler_single (by simp [hij.ne']) _

theorem rootElt_neg_eps_add_eps {i j : Fin r} (hij : i < j) (t : K) :
    ((rootElt r K (-eps r i + eps r j) t : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) :
      (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus r K) (Pi.single (Sum.inl j) 1)
        ((-t) • Pi.single (Sum.inr i) 1) := by
  rw [rootElt_neg_eps_add_eps' hij]
  exact coe_eichler_single (by simp [hij.ne]) _

theorem rootElt_eps_add_eps {i j : Fin r} (hij : i < j) (t : K) :
    ((rootElt r K (eps r i + eps r j) t : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) :
      (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus r K) (Pi.single (Sum.inl i) 1)
        ((-t) • Pi.single (Sum.inl j) 1) := by
  rw [rootElt_eps_add_eps' hij]
  exact coe_eichler_single (by simp) _

theorem rootElt_neg_eps_sub_eps {i j : Fin r} (hij : i < j) (t : K) :
    ((rootElt r K (-eps r i - eps r j) t : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) :
      (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus r K) (Pi.single (Sum.inr j) 1)
        ((-t) • Pi.single (Sum.inr i) 1) := by
  rw [rootElt_neg_eps_sub_eps' hij]
  exact coe_eichler_single (by simp) _

theorem rootElt_mem (α : Fin r → ℤ) (t : K) :
    rootElt r K α t ∈ orthElementaryGroup (quadPlus r K) := by
  unfold rootElt
  split_ifs <;> first | exact eichler_mem_elementaryGroup _ _ _ | exact Subgroup.one_mem _

theorem rootElt_mul (α : Fin r → ℤ) (s t : K) :
    rootElt r K α s * rootElt r K α t = rootElt r K α (s + t) := by
  unfold rootElt
  split_ifs with h0 h1 h2 h3
  · rw [eichler_single_mul (by simp [h0.choose_spec.1.ne']), neg_add]
  · rw [eichler_single_mul (by simp [h1.choose_spec.1.ne]), neg_add]
  · rw [eichler_single_mul (by simp), neg_add]
  · rw [eichler_single_mul (by simp), neg_add]
  · rw [mul_one]

theorem rootElt_zero (α : Fin r → ℤ) : rootElt r K α 0 = 1 := by
  have h := rootElt_mul (r := r) α (0 : K) 0
  rw [add_zero] at h
  exact mul_eq_left.1 h

theorem rootElt_inv (α : Fin r → ℤ) (t : K) : (rootElt r K α t)⁻¹ = rootElt r K α (-t) := by
  rw [inv_eq_iff_mul_eq_one, rootElt_mul, add_neg_cancel, rootElt_zero]

variable (r K)

@[expose] noncomputable def rootSubgroup (α : Fin r → ℤ) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) where
  carrier := {g | ∃ t : K, rootElt r K α t = g}
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, (rootElt_mul α s t).symm⟩
  one_mem' := ⟨0, rootElt_zero α⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨-t, (rootElt_inv α t).symm⟩

@[expose] noncomputable def unipotent :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  ⨆ α ∈ posRoots r, rootSubgroup r K α

variable {r K}

theorem mem_rootSubgroup {α : Fin r → ℤ} {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ rootSubgroup r K α ↔ ∃ t : K, rootElt r K α t = g :=
  Iff.rfl

theorem rootElt_mem_rootSubgroup (α : Fin r → ℤ) (t : K) :
    rootElt r K α t ∈ rootSubgroup r K α :=
  ⟨t, rfl⟩

theorem rootSubgroup_le (α : Fin r → ℤ) :
    rootSubgroup r K α ≤ orthElementaryGroup (quadPlus r K) := by
  rintro _ ⟨t, rfl⟩
  exact rootElt_mem α t

theorem rootSubgroup_le_unipotent {α : Fin r → ℤ} (hα : α ∈ posRoots r) :
    rootSubgroup r K α ≤ unipotent r K :=
  le_iSup₂ (f := fun α (_ : α ∈ posRoots r) => rootSubgroup r K α) α hα

theorem unipotent_le : unipotent r K ≤ orthElementaryGroup (quadPlus r K) :=
  iSup₂_le fun α _ => rootSubgroup_le α

end RootElt

section Borel

variable (r : ℕ) (K : Type*) [Field K]

@[expose] def flag (i : ℕ) : Submodule K (Fin r ⊕ Fin r → K) :=
  Submodule.span K
    ((fun j : Fin r => (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) '' {j | (j : ℕ) < i})

@[expose] noncomputable def borel : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  orthElementaryGroup (quadPlus r K) ⊓
    ⨅ i ∈ Set.Icc 1 r, MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] _) (flag r K i)

variable {r K}

theorem mem_borel {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ borel r K ↔ g ∈ orthElementaryGroup (quadPlus r K) ∧
      ∀ i, 1 ≤ i → i ≤ r → (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] _) = flag r K i := by
  simp only [borel, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_Icc, and_imp,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem borel_le : borel r K ≤ orthElementaryGroup (quadPlus r K) :=
  inf_le_left

end Borel

section Torus

variable (r : ℕ) (K : Type*) [Field K]

@[expose] noncomputable def torusElt :
    (Fin r → Kˣ) →* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) where
  toFun a := LinearEquiv.piCongrRight fun c => LinearEquiv.smulOfUnit (Sum.elim a a⁻¹ c : Kˣ)
  map_one' := by
    ext v c
    rcases c with i | i <;> simp [LinearEquiv.smulOfUnit]
  map_mul' a b := by
    ext v c
    rcases c with i | i <;> simp [LinearEquiv.smulOfUnit, mul_smul, mul_comm]

@[expose] noncomputable def torus : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  orthElementaryGroup (quadPlus r K) ⊓ (torusElt r K).range

variable {r K}

theorem torusElt_apply (a : Fin r → Kˣ) (v : Fin r ⊕ Fin r → K) (c : Fin r ⊕ Fin r) :
    torusElt r K a v c = ((Sum.elim a a⁻¹ c : Kˣ) : K) * v c :=
  rfl

theorem torusElt_injective : Function.Injective (torusElt r K) := by
  intro a b h
  funext i
  apply Units.ext
  have := congrFun (LinearEquiv.congr_fun h (Pi.single (Sum.inl i) 1)) (Sum.inl i)
  simpa [torusElt_apply] using this

theorem mem_torus {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ torus r K ↔ g ∈ orthElementaryGroup (quadPlus r K) ∧ ∃ a, torusElt r K a = g :=
  Iff.rfl

theorem torus_le : torus r K ≤ orthElementaryGroup (quadPlus r K) :=
  inf_le_left

end Torus

section TorusWeyl

variable (r : ℕ) (K : Type*) [Field K]

@[expose] noncomputable def weylElt (i : Fin r) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  rootElt r K (simpleRoot r i) 1 * rootElt r K (-simpleRoot r i) (-1) *
    rootElt r K (simpleRoot r i) 1

@[expose] noncomputable def torusWeyl : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  Subgroup.closure ((torus r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] _)) ∪ Set.range (weylElt r K))

variable {r K}

theorem weylElt_mem (i : Fin r) : weylElt r K i ∈ orthElementaryGroup (quadPlus r K) :=
  mul_mem (mul_mem (rootElt_mem _ _) (rootElt_mem _ _)) (rootElt_mem _ _)

theorem torus_le_torusWeyl : torus r K ≤ torusWeyl r K :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem weylElt_mem_torusWeyl (i : Fin r) : weylElt r K i ∈ torusWeyl r K :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem torusWeyl_le : torusWeyl r K ≤ orthElementaryGroup (quadPlus r K) := by
  rw [torusWeyl, Subgroup.closure_le]
  rintro _ (hx | ⟨i, rfl⟩)
  · exact torus_le hx
  · exact weylElt_mem i

end TorusWeyl

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
