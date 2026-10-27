module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailBDescent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailShortRoot

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]

section Space

variable (r : ℕ) (qA : QuadraticForm K A)

@[expose] noncomputable def quadTail : QuadraticForm K ((Fin r ⊕ Fin r → K) × A) :=
  (quadPlus r K).prod qA

variable {r qA}

theorem quadTail_apply (v : (Fin r ⊕ Fin r → K) × A) :
    quadTail r qA v = quadPlus r K v.1 + qA v.2 :=
  QuadraticMap.prod_apply _ _ _

theorem polar_quadTail (v w : (Fin r ⊕ Fin r → K) × A) :
    polar (quadTail r qA) v w = polar (quadPlus r K) v.1 w.1 + polar qA v.2 w.2 :=
  polar_prod _ _ v w

variable (K A) in
@[expose] def hypVec {r : ℕ} (c : Fin r ⊕ Fin r) : (Fin r ⊕ Fin r → K) × A :=
  (Pi.single c 1, 0)

theorem quadTail_hypVec (c : Fin r ⊕ Fin r) : quadTail r qA (hypVec K A c) = 0 := by
  rw [quadTail_apply, hypVec, quadPlus_single, QuadraticMap.map_zero, add_zero]

theorem quadTail_tail (a : A) : quadTail r qA ((0, a) : (Fin r ⊕ Fin r → K) × A) = qA a := by
  rw [quadTail_apply, QuadraticMap.map_zero, zero_add]

theorem polar_hypVec (v : (Fin r ⊕ Fin r → K) × A) (c : Fin r ⊕ Fin r) :
    polar (quadTail r qA) v (hypVec K A c) = v.1 c.swap := by
  rw [polar_quadTail, hypVec, polar_single, polar_zero_right, add_zero]

theorem polar_hypVec_hypVec (c d : Fin r ⊕ Fin r) :
    polar (quadTail r qA) (hypVec K A c) (hypVec K A d) = if d = c.swap then 1 else 0 := by
  rw [polar_hypVec]
  by_cases h : d = c.swap
  · subst h
    simp [hypVec]
  · have h' : d.swap ≠ c := fun h' => h (by rw [← h', Sum.swap_swap])
    simp [hypVec, h, h']

theorem polar_hypVec_tail (c : Fin r ⊕ Fin r) (a : A) :
    polar (quadTail r qA) (hypVec K A c) ((0, a) : (Fin r ⊕ Fin r → K) × A) = 0 := by
  rw [polar_comm, polar_hypVec]
  rfl

theorem polar_tail_tail (a b : A) :
    polar (quadTail r qA) ((0, a) : (Fin r ⊕ Fin r → K) × A) (0, b) = polar qA a b := by
  rw [polar_quadTail, polar_zero_left, zero_add]

variable (r qA) in
@[expose] def hypPairT (i : Fin r) : HypPair (quadTail r qA) where
  e := hypVec K A (.inl i)
  f := hypVec K A (.inr i)
  Q_e := quadTail_hypVec _
  Q_f := quadTail_hypVec _
  polar_ef := by rw [polar_hypVec_hypVec, Sum.swap_inl, ite_eq_left rfl]

theorem hypPairT_e (i : Fin r) : (hypPairT r qA i).e = hypVec K A (.inl i) :=
  rfl

theorem hypPairT_f (i : Fin r) : (hypPairT r qA i).f = hypVec K A (.inr i) :=
  rfl

theorem tail_mem_perp_hypPairT (i : Fin r) (a : A) :
    ((0, a) : (Fin r ⊕ Fin r → K) × A) ∈ (hypPairT r qA i).perp :=
  HypPair.mem_perp.2 ⟨polar_hypVec_tail _ a, polar_hypVec_tail _ a⟩

theorem eichler_prod_fst (u w : Fin r ⊕ Fin r → K) :
    eichler (quadTail r qA) (u, 0) (w, 0) =
      (eichler (quadPlus r K) u w).prodCongr (LinearEquiv.refl K A) := by
  by_cases h : quadPlus r K u = 0 ∧ polar (quadPlus r K) u w = 0
  · have hu : quadTail r qA ((u, 0) : (Fin r ⊕ Fin r → K) × A) = 0 := by
      rw [quadTail_apply, h.1, QuadraticMap.map_zero, add_zero]
    have hw : polar (quadTail r qA) ((u, 0) : (Fin r ⊕ Fin r → K) × A) (w, 0) = 0 := by
      rw [polar_quadTail, h.2, polar_zero_left, add_zero]
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply hu hw, LinearEquiv.prodCongr_apply, eichler_apply h.1 h.2]
    simp only [polar_quadTail, quadTail_apply, polar_zero_right, add_zero, QuadraticMap.map_zero,
      LinearEquiv.refl_apply]
    ext <;> simp
  · have h' : ¬(quadTail r qA ((u, 0) : (Fin r ⊕ Fin r → K) × A) = 0 ∧
        polar (quadTail r qA) ((u, 0) : (Fin r ⊕ Fin r → K) × A) (w, 0) = 0) := by
      rwa [quadTail_apply, polar_quadTail, polar_zero_left, add_zero, QuadraticMap.map_zero,
        add_zero]
    rw [eichler_of_not h', eichler_of_not h]
    exact LinearEquiv.ext fun x => rfl

theorem hypVec_smul (c : Fin r ⊕ Fin r) (t : K) :
    t • hypVec K A c = ((t • Pi.single c 1, 0) : (Fin r ⊕ Fin r → K) × A) := by
  rw [hypVec, Prod.smul_mk, smul_zero]

end Space

section Roots

variable (r : ℕ) (qA : QuadraticForm K A)

open Classical in
@[expose] noncomputable def tailLongElt (α : Fin r → ℤ) (t : K) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = eps r p.1 - eps r p.2 then
    eichler (quadTail r qA) (hypVec K A (.inl h.choose.1)) ((-t) • hypVec K A (.inr h.choose.2))
  else if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = -eps r p.1 + eps r p.2 then
    eichler (quadTail r qA) (hypVec K A (.inl h.choose.2)) ((-t) • hypVec K A (.inr h.choose.1))
  else if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = eps r p.1 + eps r p.2 then
    eichler (quadTail r qA) (hypVec K A (.inl h.choose.1)) ((-t) • hypVec K A (.inl h.choose.2))
  else if h : ∃ p : Fin r × Fin r, p.1 < p.2 ∧ α = -eps r p.1 - eps r p.2 then
    eichler (quadTail r qA) (hypVec K A (.inr h.choose.2)) ((-t) • hypVec K A (.inr h.choose.1))
  else 1

open Classical in
@[expose] noncomputable def tailShortElt (α : Fin r → ℤ) (a : A) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  if h : ∃ i : Fin r, α = eps r i then eichler (quadTail r qA) (hypVec K A (.inl h.choose)) (0, a)
  else if h : ∃ i : Fin r, α = -eps r i then
    eichler (quadTail r qA) (hypVec K A (.inr h.choose)) (0, a)
  else 1

variable {r qA}

theorem tailLongElt_eq_prodCongr (α : Fin r → ℤ) (t : K) :
    tailLongElt r qA α t = (rootElt r K α t).prodCongr (LinearEquiv.refl K A) := by
  unfold tailLongElt rootElt
  split_ifs <;>
    first
    | (rw [hypVec_smul, hypVec, eichler_prod_fst])
    | exact LinearEquiv.ext fun x => rfl

theorem tailLongElt_eps_sub_eps {i j : Fin r} (hij : i < j) (t : K) :
    tailLongElt r qA (eps r i - eps r j) t =
      eichler (quadTail r qA) (hypVec K A (.inl i)) ((-t) • hypVec K A (.inr j)) := by
  rw [tailLongElt_eq_prodCongr, rootElt_eps_sub_eps' hij, hypVec_smul, hypVec, eichler_prod_fst]

theorem tailLongElt_neg_eps_add_eps {i j : Fin r} (hij : i < j) (t : K) :
    tailLongElt r qA (-eps r i + eps r j) t =
      eichler (quadTail r qA) (hypVec K A (.inl j)) ((-t) • hypVec K A (.inr i)) := by
  rw [tailLongElt_eq_prodCongr, rootElt_neg_eps_add_eps' hij, hypVec_smul, hypVec,
    eichler_prod_fst]

theorem tailLongElt_eps_add_eps {i j : Fin r} (hij : i < j) (t : K) :
    tailLongElt r qA (eps r i + eps r j) t =
      eichler (quadTail r qA) (hypVec K A (.inl i)) ((-t) • hypVec K A (.inl j)) := by
  rw [tailLongElt_eq_prodCongr, rootElt_eps_add_eps' hij, hypVec_smul, hypVec, eichler_prod_fst]

theorem tailLongElt_neg_eps_sub_eps {i j : Fin r} (hij : i < j) (t : K) :
    tailLongElt r qA (-eps r i - eps r j) t =
      eichler (quadTail r qA) (hypVec K A (.inr j)) ((-t) • hypVec K A (.inr i)) := by
  rw [tailLongElt_eq_prodCongr, rootElt_neg_eps_sub_eps' hij, hypVec_smul, hypVec,
    eichler_prod_fst]

theorem polar_hypVec_smul_hypVec {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (t : K) :
    polar (quadTail r qA) (hypVec K A c) (t • hypVec K A d) = 0 := by
  rw [polar_smul_right_eq, polar_hypVec_hypVec, ite_eq_right h, mul_zero]

theorem coe_eichler_hypVec {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (t : K) :
    ((eichler (quadTail r qA) (hypVec K A c) (t • hypVec K A d) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) =
      orthElementaryMap (quadTail r qA) (hypVec K A c) (t • hypVec K A d) :=
  LinearMap.ext fun x => eichler_apply (quadTail_hypVec c) (polar_hypVec_smul_hypVec h t) x

theorem coe_eichler_tail (c : Fin r ⊕ Fin r) (a : A) :
    ((eichler (quadTail r qA) (hypVec K A c) ((0, a) : (Fin r ⊕ Fin r → K) × A) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) =
      orthElementaryMap (quadTail r qA) (hypVec K A c) (0, a) :=
  LinearMap.ext fun x => eichler_apply (quadTail_hypVec c) (polar_hypVec_tail c a) x

theorem tailLongElt_mem (α : Fin r → ℤ) (t : K) :
    tailLongElt r qA α t ∈ orthElementaryGroup (quadTail r qA) := by
  unfold tailLongElt
  split_ifs <;> first | exact eichler_mem_elementaryGroup _ _ _ | exact Subgroup.one_mem _

theorem tailLongElt_mul (α : Fin r → ℤ) (s t : K) :
    tailLongElt r qA α s * tailLongElt r qA α t = tailLongElt r qA α (s + t) := by
  rw [tailLongElt_eq_prodCongr, tailLongElt_eq_prodCongr, tailLongElt_eq_prodCongr,
    ← rootElt_mul]
  exact LinearEquiv.ext fun x => rfl

theorem tailLongElt_zero (α : Fin r → ℤ) : tailLongElt r qA α 0 = 1 := by
  rw [tailLongElt_eq_prodCongr, rootElt_zero]
  exact LinearEquiv.ext fun x => rfl

theorem tailLongElt_inv (α : Fin r → ℤ) (t : K) :
    (tailLongElt r qA α t)⁻¹ = tailLongElt r qA α (-t) := by
  rw [inv_eq_iff_mul_eq_one, tailLongElt_mul, add_neg_cancel, tailLongElt_zero]

theorem eps_injective : Function.Injective (eps r) := by
  intro i j h
  have := congrFun h j
  rw [eps_apply, eps_apply, ite_eq_left rfl] at this
  by_contra hij
  rw [ite_eq_right (Ne.symm hij)] at this
  exact zero_ne_one this

theorem neg_eps_ne_eps (i j : Fin r) : -eps r i ≠ eps r j := by
  intro h
  have := congrFun h j
  rw [Pi.neg_apply, eps_apply, eps_apply, ite_eq_left rfl] at this
  by_cases hji : j = i
  · rw [ite_eq_left hji] at this
    norm_num at this
  · rw [ite_eq_right hji] at this
    norm_num at this

theorem tailShortElt_eps (i : Fin r) (a : A) :
    tailShortElt r qA (eps r i) a = eichler (quadTail r qA) (hypVec K A (.inl i)) (0, a) := by
  have h : ∃ j : Fin r, eps r i = eps r j := ⟨i, rfl⟩
  rw [tailShortElt, dite_eq_left h, ← eps_injective h.choose_spec]

theorem tailShortElt_neg_eps (i : Fin r) (a : A) :
    tailShortElt r qA (-eps r i) a = eichler (quadTail r qA) (hypVec K A (.inr i)) (0, a) := by
  have h0 : ¬∃ j : Fin r, -eps r i = eps r j := fun ⟨j, hj⟩ => neg_eps_ne_eps i j hj
  have h : ∃ j : Fin r, -eps r i = -eps r j := ⟨i, rfl⟩
  rw [tailShortElt, dite_eq_right h0, dite_eq_left h,
    ← eps_injective (neg_injective h.choose_spec)]

theorem tailShortElt_of_not {α : Fin r → ℤ} (h : α ∉ shortRootsB r) (a : A) :
    tailShortElt r qA α a = 1 := by
  have h0 : ¬∃ j : Fin r, α = eps r j := fun ⟨j, hj⟩ => h ⟨j, Or.inl hj⟩
  have h1 : ¬∃ j : Fin r, α = -eps r j := fun ⟨j, hj⟩ => h ⟨j, Or.inr hj⟩
  rw [tailShortElt, dite_eq_right h0, dite_eq_right h1]

theorem tailShortElt_mem (α : Fin r → ℤ) (a : A) :
    tailShortElt r qA α a ∈ orthElementaryGroup (quadTail r qA) := by
  unfold tailShortElt
  split_ifs <;> first | exact eichler_mem_elementaryGroup _ _ _ | exact Subgroup.one_mem _

theorem tailShortElt_mul (α : Fin r → ℤ) (a b : A) :
    tailShortElt r qA α a * tailShortElt r qA α b = tailShortElt r qA α (a + b) := by
  unfold tailShortElt
  split_ifs
  · rw [eichler_mul (polar_hypVec_tail _ a) (polar_hypVec_tail _ b), Prod.mk_add_mk, add_zero]
  · rw [eichler_mul (polar_hypVec_tail _ a) (polar_hypVec_tail _ b), Prod.mk_add_mk, add_zero]
  · rw [mul_one]

theorem tailShortElt_zero (α : Fin r → ℤ) : tailShortElt r qA α 0 = 1 := by
  have h := tailShortElt_mul (qA := qA) α (0 : A) 0
  rw [add_zero] at h
  exact mul_eq_left.1 h

theorem tailShortElt_inv (α : Fin r → ℤ) (a : A) :
    (tailShortElt r qA α a)⁻¹ = tailShortElt r qA α (-a) := by
  rw [inv_eq_iff_mul_eq_one, tailShortElt_mul, add_neg_cancel, tailShortElt_zero]

variable (r qA)

@[expose] noncomputable def tailLongGroup (α : Fin r → ℤ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | ∃ t : K, tailLongElt r qA α t = g}
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, (tailLongElt_mul α s t).symm⟩
  one_mem' := ⟨0, tailLongElt_zero α⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨-t, (tailLongElt_inv α t).symm⟩

@[expose] noncomputable def tailShortGroup (α : Fin r → ℤ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | ∃ a : A, tailShortElt r qA α a = g}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (tailShortElt_mul α a b).symm⟩
  one_mem' := ⟨0, tailShortElt_zero α⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (tailShortElt_inv α a).symm⟩

open Classical in
@[expose] noncomputable def tailRootGroup (α : Fin r → ℤ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  if α ∈ roots r then tailLongGroup r qA α else tailShortGroup r qA α

@[expose] noncomputable def tailUnipotent :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  ⨆ α ∈ posRootsB r, tailRootGroup r qA α

variable {r qA}

theorem tailRootGroup_of_mem_roots {α : Fin r → ℤ} (hα : α ∈ roots r) :
    tailRootGroup r qA α = tailLongGroup r qA α := by
  rw [tailRootGroup, ite_eq_left hα]

theorem tailRootGroup_of_not_mem_roots {α : Fin r → ℤ} (hα : α ∉ roots r) :
    tailRootGroup r qA α = tailShortGroup r qA α := by
  rw [tailRootGroup, ite_eq_right hα]

theorem eps_not_mem_roots (i : Fin r) : eps r i ∉ roots r := by
  intro h
  obtain ⟨a, b, hab, s, t, hs, ht, h⟩ := mem_roots_iff_sign.1 h
  exact sign_eps_ne_sign_vec hab hs ht (u := 1) (c := i) (by rw [one_smul, h])

theorem neg_eps_not_mem_roots (i : Fin r) : -eps r i ∉ roots r := fun h =>
  eps_not_mem_roots i (by rw [← neg_neg (eps r i)]; exact neg_mem_roots h)

theorem mem_tailRootGroup_eps {i : Fin r} {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} :
    g ∈ tailRootGroup r qA (eps r i) ↔
      ∃ a : A, eichler (quadTail r qA) (hypVec K A (.inl i)) (0, a) = g := by
  rw [tailRootGroup_of_not_mem_roots (eps_not_mem_roots i)]
  simp only [tailShortGroup, Subgroup.mem_mk, tailShortElt_eps]
  rfl

theorem mem_tailRootGroup_neg_eps {i : Fin r} {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} :
    g ∈ tailRootGroup r qA (-eps r i) ↔
      ∃ a : A, eichler (quadTail r qA) (hypVec K A (.inr i)) (0, a) = g := by
  rw [tailRootGroup_of_not_mem_roots (neg_eps_not_mem_roots i)]
  simp only [tailShortGroup, Subgroup.mem_mk, tailShortElt_neg_eps]
  rfl

theorem mem_tailRootGroup_long {α : Fin r → ℤ} (hα : α ∈ roots r)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} :
    g ∈ tailRootGroup r qA α ↔ ∃ t : K, tailLongElt r qA α t = g := by
  rw [tailRootGroup_of_mem_roots hα]
  rfl

theorem tailRootGroup_le (α : Fin r → ℤ) :
    tailRootGroup r qA α ≤ orthElementaryGroup (quadTail r qA) := by
  unfold tailRootGroup
  split_ifs
  · rintro _ ⟨t, rfl⟩
    exact tailLongElt_mem α t
  · rintro _ ⟨a, rfl⟩
    exact tailShortElt_mem α a

theorem tailRootGroup_le_tailUnipotent {α : Fin r → ℤ} (hα : α ∈ posRootsB r) :
    tailRootGroup r qA α ≤ tailUnipotent r qA :=
  le_iSup₂ (f := fun α (_ : α ∈ posRootsB r) => tailRootGroup r qA α) α hα

theorem tailUnipotent_le : tailUnipotent r qA ≤ orthElementaryGroup (quadTail r qA) :=
  iSup₂_le fun α _ => tailRootGroup_le α

end Roots

section Borel

variable (K A) in
@[expose] def tailFlag (r i : ℕ) : Submodule K ((Fin r ⊕ Fin r → K) × A) :=
  Submodule.span K ((fun j : Fin r => hypVec K A (.inl j)) '' {j | (j : ℕ) < i})

variable (r : ℕ) (qA : QuadraticForm K A)

@[expose] noncomputable def tailBorel :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  orthElementaryGroup (quadTail r qA) ⊓
    ⨅ i ∈ Set.Icc 1 r, MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) (tailFlag K A r i)

variable {r qA}

theorem mem_tailBorel {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ tailBorel r qA ↔ g ∈ orthElementaryGroup (quadTail r qA) ∧
      ∀ i, 1 ≤ i → i ≤ r →
        (tailFlag K A r i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r i := by
  simp only [tailBorel, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_Icc, and_imp,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem tailBorel_le : tailBorel r qA ≤ orthElementaryGroup (quadTail r qA) :=
  inf_le_left

end Borel

section Torus

variable (r : ℕ) (qA : QuadraticForm K A)

@[expose] noncomputable def tailDiag (t : Fin r → Kˣ) (h : A ≃ₗ[K] A) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  (torusElt r K t).prodCongr h

variable {r} in
theorem tailDiag_apply (t : Fin r → Kˣ) (h : A ≃ₗ[K] A) (v : (Fin r ⊕ Fin r → K) × A) :
    tailDiag r t h v = (torusElt r K t v.1, h v.2) :=
  rfl

variable {r} in
theorem tailDiag_mul (t t' : Fin r → Kˣ) (h h' : A ≃ₗ[K] A) :
    tailDiag r t h * tailDiag r t' h' = tailDiag r (t * t') (h * h') := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, tailDiag_apply, tailDiag_apply, tailDiag_apply, map_mul,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply]

@[expose] noncomputable def tailDiagGroup :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | ∃ (t : Fin r → Kˣ) (h : A ≃ₗ[K] A),
    h ∈ TauCeti.QuadraticMap.orthogonalGroup qA ∧ tailDiag r t h = g}
  mul_mem' := by
    rintro _ _ ⟨t, h, hh, rfl⟩ ⟨t', h', hh', rfl⟩
    exact ⟨t * t', h * h', mul_mem hh hh', (tailDiag_mul t t' h h').symm⟩
  one_mem' := ⟨1, 1, one_mem _, LinearEquiv.ext fun v => by
    rw [tailDiag_apply, map_one]
    rfl⟩
  inv_mem' := by
    rintro _ ⟨t, h, hh, rfl⟩
    refine ⟨t⁻¹, h⁻¹, inv_mem hh, ?_⟩
    rw [eq_inv_iff_mul_eq_one, tailDiag_mul, inv_mul_cancel, inv_mul_cancel]
    refine LinearEquiv.ext fun v => ?_
    rw [tailDiag_apply, map_one]
    rfl

@[expose] noncomputable def tailTorus :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  orthElementaryGroup (quadTail r qA) ⊓ tailDiagGroup r qA

variable {r qA}

theorem mem_tailTorus {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ tailTorus r qA ↔ g ∈ orthElementaryGroup (quadTail r qA) ∧
      ∃ (t : Fin r → Kˣ) (h : A ≃ₗ[K] A),
        h ∈ TauCeti.QuadraticMap.orthogonalGroup qA ∧ tailDiag r t h = g :=
  Iff.rfl

theorem tailTorus_le : tailTorus r qA ≤ orthElementaryGroup (quadTail r qA) :=
  inf_le_left

end Torus

section TorusWeyl

variable (r : ℕ) (qA : QuadraticForm K A)

@[expose] noncomputable def tailWeylElt (a₀ : A) (i : Fin r) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  if i.val + 1 < r then
    tailLongElt r qA (simpleRootB r i) 1 * tailLongElt r qA (-simpleRootB r i) (-1) *
      tailLongElt r qA (simpleRootB r i) 1
  else
    eichler (quadTail r qA) (hypVec K A (.inl i)) (0, a₀) *
      eichler (quadTail r qA) (hypVec K A (.inr i)) (0, (qA a₀)⁻¹ • a₀) *
      eichler (quadTail r qA) (hypVec K A (.inl i)) (0, a₀)

@[expose] noncomputable def tailTorusWeyl (a₀ : A) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  Subgroup.closure ((tailTorus r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∪
    Set.range (tailWeylElt r qA a₀))

variable {r qA}

theorem tailWeylElt_of_lt (a₀ : A) {i : Fin r} (h : i.val + 1 < r) :
    tailWeylElt r qA a₀ i =
      tailLongElt r qA (simpleRootB r i) 1 * tailLongElt r qA (-simpleRootB r i) (-1) *
        tailLongElt r qA (simpleRootB r i) 1 := by
  rw [tailWeylElt, ite_eq_left h]

theorem tailWeylElt_of_not_lt (a₀ : A) {i : Fin r} (h : ¬i.val + 1 < r) :
    tailWeylElt r qA a₀ i = shortWeyl (hypPairT r qA i) ((0, a₀) : (Fin r ⊕ Fin r → K) × A) := by
  rw [tailWeylElt, ite_eq_right h, shortWeyl, hypPairT_e, hypPairT_f, quadTail_tail, Prod.smul_mk,
    smul_zero]

theorem tailWeylElt_eq_prodCongr (a₀ : A) {i : Fin r} (h : i.val + 1 < r) :
    tailWeylElt r qA a₀ i = (weylElt r K i).prodCongr (LinearEquiv.refl K A) := by
  rw [tailWeylElt_of_lt a₀ h, tailLongElt_eq_prodCongr, tailLongElt_eq_prodCongr,
    simpleRootB_eq_simpleRoot h, weylElt]
  exact LinearEquiv.ext fun x => rfl

theorem tailWeylElt_mem (a₀ : A) (i : Fin r) :
    tailWeylElt r qA a₀ i ∈ orthElementaryGroup (quadTail r qA) := by
  unfold tailWeylElt
  split_ifs
  · exact mul_mem (mul_mem (tailLongElt_mem _ _) (tailLongElt_mem _ _)) (tailLongElt_mem _ _)
  · exact mul_mem (mul_mem (eichler_mem_elementaryGroup _ _ _)
      (eichler_mem_elementaryGroup _ _ _)) (eichler_mem_elementaryGroup _ _ _)

theorem tailTorus_le_tailTorusWeyl (a₀ : A) : tailTorus r qA ≤ tailTorusWeyl r qA a₀ :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem tailWeylElt_mem_tailTorusWeyl (a₀ : A) (i : Fin r) :
    tailWeylElt r qA a₀ i ∈ tailTorusWeyl r qA a₀ :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem tailTorusWeyl_le (a₀ : A) :
    tailTorusWeyl r qA a₀ ≤ orthElementaryGroup (quadTail r qA) := by
  rw [tailTorusWeyl, Subgroup.closure_le]
  rintro _ (hx | ⟨i, rfl⟩)
  · exact tailTorus_le hx
  · exact tailWeylElt_mem a₀ i

theorem qA_ne_zero (hqA : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) : qA a₀ ≠ 0 :=
  fun h => ha₀ (hqA a₀ h)

end TorusWeyl

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
