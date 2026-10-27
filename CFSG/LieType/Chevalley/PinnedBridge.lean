module

public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.Blueprint.ChevalleyRootGroups
public import CFSG.Blueprint.ChevalleyPinnedBridge

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] def wordSmulRoot
    (w : List ℕ) (β : Root τ) : Root τ :=
  w.foldl (fun γ i => simple τ (τ.idx i) • γ) β

theorem coe_wordSmulRoot
    (w : List ℕ) (β : Root τ) :
    (wordSmulRoot w β).1 = w.foldl (fun v i => reflect τ (τ.idx i) v) β.1 := by
  induction w generalizing β with
  | nil => rfl
  | cons i w ih =>
    rw [List.foldl_cons, ← simple_smul, ← coe_smul_root]
    exact ih _

theorem wordSmulRoot_pinnedData
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    wordSmulRoot (pinnedData τ α).2.1 (simpleRoot τ (pinnedData τ α).1) = ⟨α, hα⟩ :=
  Subtype.ext ((coe_wordSmulRoot _ _).trans (foldl_reflect_pinnedData hα))

namespace RootOperatorFamily

variable (F : RootOperatorFamily τ)

@[expose] def wordSign
    : List ℕ → Root τ → ℤ
  | [], _ => 1
  | i :: w, β => F.sign (τ.idx i) β * wordSign w (simple τ (τ.idx i) • β)

theorem wordSign_eq
    (w : List ℕ) (β : Root τ) : F.wordSign w β = 1 ∨ F.wordSign w β = -1 := by
  induction w generalizing β with
  | nil => exact .inl rfl
  | cons i w ih =>
    rcases F.sign_eq (τ.idx i) β with h | h <;>
      rcases ih (simple τ (τ.idx i) • β) with h' | h' <;>
        simp [wordSign, h, h']

theorem weylElt_mul_D_mul_inv
    (R : Type) [CommRing R] (i : Fin τ.rank) (β : Root τ) (k : ℕ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * F.D R β k *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      ((F.sign i β ^ k : ℤ) : R) • F.D R (simple τ i • β) k := by
  rw [F.conj, smul_mul_assoc, Units.mul_inv_cancel_right]

theorem prod_weylElt_mul_D_mul_inv
    (R : Type) [CommRing R] (w : List ℕ) (β : Root τ) (k : ℕ) :
    ((((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) * F.D R β k *
        (((((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod)⁻¹ :
          (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) =
      ((F.wordSign w β ^ k : ℤ) : R) • F.D R (wordSmulRoot w β) k := by
  induction w generalizing β with
  | nil => simp [wordSign, wordSmulRoot]
  | cons i w ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      mul_inv_rev, Units.val_mul]
    set W := ((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod
    calc (W : Module.End R (RootModule τ R)) * (weylElt τ R (τ.idx i) 1 :
            Module.End R (RootModule τ R)) * F.D R β k *
          ((((weylElt τ R (τ.idx i) 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) *
            ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))) =
        (W : Module.End R (RootModule τ R)) *
          ((weylElt τ R (τ.idx i) 1 : Module.End R (RootModule τ R)) * F.D R β k *
            (((weylElt τ R (τ.idx i) 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
              Module.End R (RootModule τ R))) *
          ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) := by
          simp only [mul_assoc]
      _ = ((F.sign (τ.idx i) β ^ k : ℤ) : R) • ((W : Module.End R (RootModule τ R)) *
            F.D R (simple τ (τ.idx i) • β) k *
            ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))) := by
          rw [F.weylElt_mul_D_mul_inv, mul_smul_comm, smul_mul_assoc]
      _ = ((F.wordSign (i :: w) β ^ k : ℤ) : R) • F.D R (wordSmulRoot (i :: w) β) k := by
          rw [ih, smul_smul, wordSign, mul_pow, Int.cast_mul]
          rfl

@[expose] def pinnedFamilySign
    (α : Fin τ.rank → ℤ) : ℤ :=
  F.wordSign (pinnedData τ α).2.1 (simpleRoot τ (pinnedData τ α).1) * (pinnedData τ α).2.2

theorem pinnedFamilySign_eq
    (α : Fin τ.rank → ℤ) :
    F.pinnedFamilySign α = 1 ∨ F.pinnedFamilySign α = -1 := by
  unfold pinnedFamilySign
  rcases F.wordSign_eq (pinnedData τ α).2.1 (simpleRoot τ (pinnedData τ α).1) with h | h <;>
    rcases pinnedSign_eq τ α with h' | h' <;> simp [h, h']

theorem pinnedFamilySign_mul_self
    (R : Type) [CommRing R] (α : Fin τ.rank → ℤ) :
    (F.pinnedFamilySign α : R) * (F.pinnedFamilySign α : R) = 1 := by
  rcases F.pinnedFamilySign_eq α with h | h <;> rw [h] <;> norm_num

theorem pinnedCoeff_eq_smul_D
    (R : Type) [CommRing R] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (k : ℕ) :
    pinnedCoeff τ R α k = ((F.pinnedFamilySign α ^ k : ℤ) : R) • F.D R ⟨α, hα⟩ k := by
  have h := F.prod_weylElt_mul_D_mul_inv R (pinnedData τ α).2.1
    (simpleRoot τ (pinnedData τ α).1) k
  rw [F.D_simple, wordSmulRoot_pinnedData hα] at h
  rw [pinnedCoeff, pinnedWeyl, h, smul_smul, pinnedFamilySign, mul_pow, Int.cast_mul, mul_comm]

theorem pinnedE_eq_smul_D
    (R : Type) [CommRing R] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    pinnedE τ R α = (F.pinnedFamilySign α : R) • F.D R ⟨α, hα⟩ 1 := by
  rw [← pinnedCoeff_one, F.pinnedCoeff_eq_smul_D R hα, pow_one]

theorem pinnedX_eq_eltUnit
    (R : Type) [CommRing R] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (c : R) : pinnedX τ R α c = F.eltUnit R ⟨α, hα⟩ ((F.pinnedFamilySign α : R) * c) := by
  refine Units.ext ?_
  rw [pinnedX_eq_sum, coe_eltUnit, elt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [F.pinnedCoeff_eq_smul_D R hα, smul_smul, mul_pow, Int.cast_pow, mul_comm (c ^ k)]

theorem subgroupOf_rootSubgroup_eq
    (K : Type) [Field K] (α : Root τ) :
    (CFSG.Blueprint.Chevalley.rootSubgroup τ K α.1).subgroupOf (adjointGroup τ K) =
      F.rootSubgroup K α := by
  ext g
  rw [Subgroup.mem_subgroupOf, CFSG.Blueprint.Chevalley.mem_rootSubgroup, F.mem_rootSubgroup]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(F.pinnedFamilySign α.1 : K) * c, Subtype.ext ?_⟩
    rw [coe_eltElement, ← hc, F.pinnedX_eq_eltUnit K α.2]
  · rintro ⟨c, rfl⟩
    refine ⟨(F.pinnedFamilySign α.1 : K) * c, ?_⟩
    rw [F.pinnedX_eq_eltUnit K α.2, ← mul_assoc, F.pinnedFamilySign_mul_self, one_mul]
    rfl

end RootOperatorFamily

variable (τ) in
@[expose] def pinnedRootSubgroups
    (K : Type) [Field K] : RootSubgroups τ K where
  X α := (CFSG.Blueprint.Chevalley.rootSubgroup τ K α.1).subgroupOf (adjointGroup τ K)
  mem_simple i g := by
    simp only [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq]
    exact (rootOperatorFamily τ).mem_rootSubgroup_simple i g
  mem_neg_simple i g := by
    simp only [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq]
    exact (rootOperatorFamily τ).mem_rootSubgroup_neg_simple i g
  weight_shift α := by
    simp only [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq]
    exact (rootOperatorFamily τ).rootSubgroup_weight_shift α
  conj_weyl i α := by
    simp only [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq]
    exact (rootOperatorFamily τ).map_conj_weylElement i α
  conj_torus i t α := by
    simp only [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq]
    exact (rootOperatorFamily τ).map_conj_torusElement i t α
  comm i β hβ hne := by
    simp only [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq]
    exact commContained_simpleRoot τ K i β hβ hne

theorem pinnedRootSubgroups_X
    (K : Type) [Field K] (α : Root τ) :
    (pinnedRootSubgroups τ K).X α =
      (CFSG.Blueprint.Chevalley.rootSubgroup τ K α.1).subgroupOf (adjointGroup τ K) :=
  rfl

end CFSG.LieType.Chevalley
