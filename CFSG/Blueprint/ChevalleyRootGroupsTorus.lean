module

public import CFSG.Blueprint.ChevalleyPinnedBridge
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

@[expose] def Label.latticeWeight : Label τ → Fin τ.rank → ℤ
  | .inl _ => 0
  | .inr α => α.1

theorem Label.weight_eq_height_latticeWeight (a : Label τ) :
    a.weight = height a.latticeWeight := by
  rcases a with i | α
  · simp [Label.weight, Label.latticeWeight, height]
  · rfl

theorem rootVec_eq_single_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem latticeWeight_of_rootVec_apply_ne_zero {γ : Fin τ.rank → ℤ} {a : Label τ}
    (h : rootVec τ R γ a ≠ 0) : a.latticeWeight = γ := by
  by_cases hγ : IsRoot τ γ
  · rw [rootVec_eq_single_of_isRoot hγ] at h
    obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
    rfl
  · rw [rootVec, dite_eq_right hγ] at h
    exact absurd rfl h

theorem latticeWeight_of_hVec_apply_ne_zero {l : Fin τ.rank} {a : Label τ}
    (h : hVec τ R l a ≠ 0) : a.latticeWeight = 0 := by
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
  rfl

@[expose] def MapsWeights (f : Module.End R (RootModule τ R))
    (φ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) : Prop :=
  ∀ a b : Label τ, f (Finsupp.single b 1) a ≠ 0 → a.latticeWeight = φ b.latticeWeight

namespace MapsWeights

variable {f g : Module.End R (RootModule τ R)} {φ ψ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem one : MapsWeights (1 : Module.End R (RootModule τ R)) id := fun a b hab => by
  rw [Module.End.one_apply] at hab
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 hab
  rfl

theorem mul (hf : MapsWeights f φ) (hg : MapsWeights g ψ) : MapsWeights (f * g) (φ ∘ ψ) := by
  intro a b hab
  rw [Module.End.mul_apply, ← Finsupp.sum_single (g (Finsupp.single b 1)), Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  rw [hf a c (right_ne_zero_of_mul hc'), hg c b (Finsupp.mem_support_iff.mp hc)]
  rfl

theorem smul (hf : MapsWeights f φ) (r : R) : MapsWeights (r • f) φ := fun a b hab => by
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hab
  exact hf a b (right_ne_zero_of_mul hab)

theorem congr (hf : MapsWeights f φ) (h : ∀ μ, φ μ = ψ μ) : MapsWeights f ψ := fun a b hab =>
  (hf a b hab).trans (h _)

end MapsWeights

theorem mapsWeights_xCoeff (j : Fin τ.rank) {k : ℕ} (hk : 1 ≤ k) :
    MapsWeights (xCoeff τ R j k) (· + k • Pi.single j 1) := by
  intro a b hab
  rcases b with l | ⟨β, hβ⟩
  · change xCoeff τ R j k (hVec τ R l) a ≠ 0 at hab
    rw [xCoeff_hVec, ite_eq_right (by omega)] at hab
    split_ifs at hab with hk1
    · subst hk1
      rw [Finsupp.smul_apply, smul_eq_mul] at hab
      rw [latticeWeight_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab)]
      simp [Label.latticeWeight]
    · exact absurd rfl hab
  · rw [← rootVec_eq_single_of_isRoot hβ] at hab
    by_cases h₁ : β = Pi.single j 1
    · subst h₁
      rw [xCoeff_rootVec_single, ite_eq_right (by omega)] at hab
      exact absurd rfl hab
    by_cases h₂ : β = -Pi.single j 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single, ite_eq_right (by omega)] at hab
      split_ifs at hab with hk1 hk2
      · subst hk1
        rw [latticeWeight_of_hVec_apply_ne_zero hab]
        simp [Label.latticeWeight]
      · subst hk2
        rw [latticeWeight_of_rootVec_apply_ne_zero hab]
        simp only [Label.latticeWeight]
        rw [two_nsmul]
        abel
      · exact absurd rfl hab
    · rw [xCoeff_rootVec_of_ne j k hβ h₁ h₂, Finsupp.smul_apply, smul_eq_mul] at hab
      rw [latticeWeight_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab), natCast_zsmul]
      rfl

theorem mapsWeights_weylElt (i : Fin τ.rank) (t : Rˣ) :
    MapsWeights (weylElt τ R i t : Module.End R (RootModule τ R)) (reflect τ i) := by
  intro a b hab
  rcases b with l | ⟨β, hβ⟩
  · change (weylElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R l) a ≠ 0 at hab
    rw [weylElt_hVec] at hab
    have ha : a.latticeWeight = 0 := by
      rcases a with m | ⟨γ, hγ⟩
      · rfl
      · simp [hVec] at hab
    rw [ha]
    simp [Label.latticeWeight, reflect]
  · rw [← rootVec_eq_single_of_isRoot hβ, weylElt_rootVec i t hβ, Finsupp.smul_apply,
      smul_eq_mul] at hab
    exact latticeWeight_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab)

variable (τ) in
@[expose] def wordReflect (w : List ℕ) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  w.foldl (fun u i => reflect τ (τ.idx i) u) v

variable (τ) in
@[expose] def wordReflectInv (w : List ℕ) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  w.foldr (fun i u => reflect τ (τ.idx i) u) v

theorem wordReflect_cons (i : ℕ) (w : List ℕ) (v : Fin τ.rank → ℤ) :
    wordReflect τ (i :: w) v = wordReflect τ w (reflect τ (τ.idx i) v) :=
  rfl

theorem wordReflectInv_cons (i : ℕ) (w : List ℕ) (v : Fin τ.rank → ℤ) :
    wordReflectInv τ (i :: w) v = reflect τ (τ.idx i) (wordReflectInv τ w v) :=
  rfl

theorem wordReflect_wordReflectInv (w : List ℕ) (v : Fin τ.rank → ℤ) :
    wordReflect τ w (wordReflectInv τ w v) = v := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordReflectInv_cons, wordReflect_cons, reflect_reflect, ih]

theorem wordReflect_add (w : List ℕ) (u v : Fin τ.rank → ℤ) :
    wordReflect τ w (u + v) = wordReflect τ w u + wordReflect τ w v := by
  induction w generalizing u v with
  | nil => rfl
  | cons i w ih =>
    rw [wordReflect_cons, wordReflect_cons, wordReflect_cons, ← reflectHom_apply, map_add,
      reflectHom_apply, reflectHom_apply, ih]

theorem wordReflect_nsmul (w : List ℕ) (k : ℕ) (v : Fin τ.rank → ℤ) :
    wordReflect τ w (k • v) = k • wordReflect τ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
    rw [wordReflect_cons, wordReflect_cons, ← reflectHom_apply, map_nsmul, reflectHom_apply, ih]

theorem mapsWeights_prod_weylElt (w : List ℕ) :
    MapsWeights ((((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) (wordReflect τ w) ∧
      MapsWeights (((((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod)⁻¹ :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
        (wordReflectInv τ w) := by
  induction w with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.prod_nil, inv_one, Units.val_one]
    exact ⟨MapsWeights.one, MapsWeights.one⟩
  | cons i w ih =>
    have hn := mapsWeights_weylElt (R := R) (τ.idx i) 1
    have hn' : MapsWeights (((weylElt τ R (τ.idx i) 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) (reflect τ (τ.idx i)) := by
      rw [weylElt_inv]
      exact mapsWeights_weylElt (τ.idx i) (-1)
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      mul_inv_rev, Units.val_mul]
    exact ⟨(ih.1.mul hn).congr fun μ => rfl, (hn'.mul ih.2).congr fun μ => rfl⟩

theorem mapsWeights_pinnedCoeff {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {k : ℕ} (hk : 1 ≤ k) :
    MapsWeights (pinnedCoeff τ R α k) (· + k • α) := by
  obtain ⟨hW, hW'⟩ := mapsWeights_prod_weylElt (τ := τ) (R := R) (pinnedData τ α).2.1
  have h := ((hW.mul (mapsWeights_xCoeff (pinnedData τ α).1 hk)).mul hW').smul
    ((((pinnedData τ α).2.2 ^ k : ℤ)) : R)
  refine h.congr fun μ => ?_
  simp only [Function.comp_apply]
  rw [wordReflect_add, wordReflect_wordReflectInv, wordReflect_nsmul]
  exact congrArg (μ + k • ·) (foldl_reflect_pinnedData hα)

theorem pinnedX_weight_shift {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : R) (a b : Label τ)
    (h : (pinnedX τ R α c : Module.End R (RootModule τ R)) (Finsupp.single b 1) a ≠
      (Finsupp.single b 1 : RootModule τ R) a) :
    ∃ k : ℕ, 1 ≤ k ∧ a.latticeWeight = b.latticeWeight + k • α := by
  rw [pinnedX_eq_sum, Finset.sum_range_succ', pow_zero, one_smul, pinnedCoeff_zero,
    LinearMap.add_apply, Module.End.one_apply, Finsupp.add_apply, Ne, add_eq_right,
    LinearMap.sum_apply, Finsupp.finsetSum_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hk
  exact ⟨k + 1, by omega, mapsWeights_pinnedCoeff hα (by omega) a b (right_ne_zero_of_mul hk)⟩

theorem torusElt_single_eq (i : Fin τ.rank) (t : Rˣ) (b : Label τ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) (Finsupp.single b 1) =
      ((t ^ (∑ j, τ.cartan i j * b.latticeWeight j) : Rˣ) : R) • Finsupp.single b 1 := by
  rcases b with l | ⟨β, hβ⟩
  · simp only [Label.latticeWeight, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zpow_zero,
      Units.val_one, one_smul]
    exact torusElt_hVec i l t
  · have h := torusElt_rootVec (R := R) i t hβ
    rw [rootVec_eq_single_of_isRoot hβ] at h
    exact h

theorem torusElt_apply_eq (i : Fin τ.rank) (t : Rˣ) (x : RootModule τ R) (a : Label τ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) x a =
      ((t ^ (∑ j, τ.cartan i j * a.latticeWeight j) : Rˣ) : R) * x a := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, torusElt_single_eq, smul_smul, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
    split_ifs with hba
    · subst hba
      ring
    · simp

theorem torusElt_mul_pinnedCoeff (i : Fin τ.rank) (t : Rˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (k : ℕ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) * pinnedCoeff τ R α k =
      (((t ^ (∑ j, τ.cartan i j * α j) : Rˣ) : R) ^ k) •
        (pinnedCoeff τ R α k * (torusElt τ R i t : Module.End R (RootModule τ R))) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.smul_apply, torusElt_single_eq, map_smul, Finsupp.smul_apply, smul_eq_mul,
    torusElt_apply_eq]
  by_cases hD : pinnedCoeff τ R α k (Finsupp.single b 1) a = 0
  · rw [hD]
    ring
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pinnedCoeff_zero, Module.End.one_apply] at hD ⊢
    obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 hD
    ring
  · have hw : a.latticeWeight = b.latticeWeight + k • α := mapsWeights_pinnedCoeff hα hk a b hD
    have hsum : ∑ j, τ.cartan i j * a.latticeWeight j =
        ∑ j, τ.cartan i j * b.latticeWeight j + (∑ j, τ.cartan i j * α j) * k := by
      rw [hw, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      ring
    rw [hsum, zpow_add, zpow_mul, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
    ring

theorem root_torus_conjugation (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (t : Rˣ)
    (c : R) :
    torusElt τ R i t * pinnedX τ R α c * (torusElt τ R i t)⁻¹ =
      pinnedX τ R α (((t ^ (∑ j, τ.cartan i j * α j) : Rˣ) : R) * c) := by
  have key : (torusElt τ R i t : Module.End R (RootModule τ R)) * pinnedX τ R α c =
      pinnedX τ R α (((t ^ (∑ j, τ.cartan i j * α j) : Rˣ) : R) * c) *
        (torusElt τ R i t : Module.End R (RootModule τ R)) := by
    simp only [pinnedX_eq_sum, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      torusElt_mul_pinnedCoeff i t hα, smul_smul, mul_pow]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, key, Units.mul_inv_cancel_right]

end CFSG.Blueprint.Chevalley
