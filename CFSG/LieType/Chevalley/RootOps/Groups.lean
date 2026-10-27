module

public import CFSG.LieType.Chevalley.RootOps.Family
public import CFSG.LieType.Chevalley.NativeHolds
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

section Weights

variable {τ : Tag} {R : Type} [CommRing R]

@[expose] def MapsLabelWt (f : Module.End R (RootModule τ R))
    (φ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) : Prop :=
  ∀ a b : Label τ, f (Finsupp.single b 1) a ≠ 0 → labelWt τ a = φ (labelWt τ b)

namespace MapsLabelWt

variable {f g : Module.End R (RootModule τ R)} {φ ψ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem mul (hf : MapsLabelWt f φ) (hg : MapsLabelWt g ψ) : MapsLabelWt (f * g) (φ ∘ ψ) := by
  intro a b hab
  rw [Module.End.mul_apply, ← Finsupp.sum_single (g (Finsupp.single b 1)), Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  rw [hf a c (right_ne_zero_of_mul hc'), hg c b (Finsupp.mem_support_iff.mp hc)]
  rfl

theorem smul (hf : MapsLabelWt f φ) (r : R) : MapsLabelWt (r • f) φ := fun a b hab => by
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hab
  exact hf a b (right_ne_zero_of_mul hab)

theorem congr (hf : MapsLabelWt f φ) (h : ∀ μ, φ μ = ψ μ) : MapsLabelWt f ψ := fun a b hab =>
  (hf a b hab).trans (h _)

end MapsLabelWt

theorem rootVec_eq_single' {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem labelWt_of_rootVec_apply_ne_zero {γ : Fin τ.rank → ℤ} {a : Label τ}
    (h : rootVec τ R γ a ≠ 0) : labelWt τ a = γ := by
  by_cases hγ : IsRoot τ γ
  · rw [rootVec_eq_single' hγ] at h
    obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
    rfl
  · rw [rootVec, dite_eq_right hγ] at h
    exact absurd rfl h

theorem labelWt_of_hVec_apply_ne_zero {l : Fin τ.rank} {a : Label τ} (h : hVec τ R l a ≠ 0) :
    labelWt τ a = 0 := by
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
  rfl

theorem mapsLabelWt_xCoeff (j : Fin τ.rank) {k : ℕ} (hk : 1 ≤ k) :
    MapsLabelWt (xCoeff τ R j k) (· + k • Pi.single j 1) := by
  intro a b hab
  rcases b with l | ⟨β, hβ⟩
  · change xCoeff τ R j k (hVec τ R l) a ≠ 0 at hab
    rw [xCoeff_hVec, ite_eq_right (by omega)] at hab
    split_ifs at hab with hk1
    · subst hk1
      rw [Finsupp.smul_apply, smul_eq_mul] at hab
      rw [labelWt_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab)]
      simp [labelWt]
    · exact absurd rfl hab
  · rw [← rootVec_eq_single' hβ] at hab
    by_cases h₁ : β = Pi.single j 1
    · subst h₁
      rw [xCoeff_rootVec_single, ite_eq_right (by omega)] at hab
      exact absurd rfl hab
    by_cases h₂ : β = -Pi.single j 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single, ite_eq_right (by omega)] at hab
      split_ifs at hab with hk1 hk2
      · subst hk1
        rw [labelWt_of_hVec_apply_ne_zero hab]
        simp [labelWt]
      · subst hk2
        rw [labelWt_of_rootVec_apply_ne_zero hab]
        simp only [labelWt]
        rw [two_nsmul]
        abel
      · exact absurd rfl hab
    · rw [xCoeff_rootVec_of_ne j k hβ h₁ h₂, Finsupp.smul_apply, smul_eq_mul] at hab
      rw [labelWt_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab), natCast_zsmul]
      rfl

theorem mapsLabelWt_weylElt (i : Fin τ.rank) (t : Rˣ) :
    MapsLabelWt (weylElt τ R i t : Module.End R (RootModule τ R)) (reflect τ i) := by
  intro a b hab
  rcases b with l | ⟨β, hβ⟩
  · change (weylElt τ R i t : Module.End R (RootModule τ R)) (hVec τ R l) a ≠ 0 at hab
    rw [weylElt_hVec] at hab
    have ha : labelWt τ a = 0 := by
      rcases a with m | ⟨γ, hγ⟩
      · rfl
      · simp [hVec] at hab
    rw [ha]
    simp [labelWt, reflect]
  · rw [← rootVec_eq_single' hβ, weylElt_rootVec i t hβ, Finsupp.smul_apply, smul_eq_mul] at hab
    exact labelWt_of_rootVec_apply_ne_zero (right_ne_zero_of_mul hab)

theorem torusElt_single (i : Fin τ.rank) (t : Rˣ) (b : Label τ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) (Finsupp.single b 1) =
      ((t ^ (∑ j, τ.cartan i j * labelWt τ b j) : Rˣ) : R) • Finsupp.single b 1 := by
  rcases b with l | ⟨β, hβ⟩
  · simp only [labelWt, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zpow_zero, Units.val_one,
      one_smul]
    exact torusElt_hVec i l t
  · have h := torusElt_rootVec (R := R) i t hβ
    rw [rootVec_eq_single' hβ] at h
    exact h

theorem torusElt_apply (i : Fin τ.rank) (t : Rˣ) (x : RootModule τ R) (a : Label τ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) x a =
      ((t ^ (∑ j, τ.cartan i j * labelWt τ a j) : Rˣ) : R) * x a := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, torusElt_single, smul_smul, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
    split_ifs with hba
    · subst hba
      ring
    · simp

end Weights

namespace RootOperatorFamily

variable {τ : Tag} (F : RootOperatorFamily τ)

section Ring

variable (R : Type) [CommRing R]

@[expose] noncomputable def elt (α : Root τ) (c : R) : Module.End R (RootModule τ R) :=
  ∑ k ∈ Finset.range 4, c ^ k • F.D R α k

variable {R}

theorem elt_simple (j : Fin τ.rank) (c : R) : F.elt R (simpleRoot τ j) c = xOp τ R j c := by
  simp only [elt, F.D_simple, xOp_eq_sum_xCoeff]

theorem elt_neg_simple (j : Fin τ.rank) (c : R) :
    F.elt R (-simpleRoot τ j) c = yOp τ R j c := by
  simp only [elt, F.D_neg_simple, yOp_eq_sum_yCoeff]

theorem elt_zero (α : Root τ) : F.elt R α 0 = 1 := by
  rw [elt, Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => by
    rw [zero_pow (Nat.succ_ne_zero k), zero_smul], zero_add, pow_zero, one_smul, F.D_zero]

theorem sign_mul_self (i : Fin τ.rank) (α : Root τ) : F.sign i α * F.sign i α = 1 := by
  rcases F.sign_eq i α with h | h <;> rw [h] <;> norm_num

theorem sign_cast_mul_self (i : Fin τ.rank) (α : Root τ) :
    (F.sign i α : R) * (F.sign i α : R) = 1 := by
  rw [← Int.cast_mul, F.sign_mul_self, Int.cast_one]

theorem weylElt_mul_elt (i : Fin τ.rank) (α : Root τ) (c : R) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * F.elt R α c =
      F.elt R (simple τ i • α) ((F.sign i α : R) * c) *
        (weylElt τ R i 1 : Module.End R (RootModule τ R)) := by
  simp only [elt, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, F.conj,
    smul_smul, mul_pow, Int.cast_pow]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem weylElt_inv_mul_elt (i : Fin τ.rank) (α : Root τ) (c : R) :
    (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) * F.elt R (simple τ i • α) c =
      F.elt R α ((F.sign i α : R) * c) *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) := by
  have h := F.weylElt_mul_elt i α ((F.sign i α : R) * c)
  rw [← mul_assoc, F.sign_cast_mul_self, one_mul] at h
  rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, h, Units.mul_inv_cancel_right]

theorem weylElt_mul_elt_mul_inv (i : Fin τ.rank) (α : Root τ) (c : R) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * F.elt R α c *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      F.elt R (simple τ i • α) ((F.sign i α : R) * c) := by
  rw [F.weylElt_mul_elt, Units.mul_inv_cancel_right]

theorem weylElt_inv_mul_elt_mul (i : Fin τ.rank) (α : Root τ) (c : R) :
    (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) * F.elt R (simple τ i • α) c *
        (weylElt τ R i 1 : Module.End R (RootModule τ R)) =
      F.elt R α ((F.sign i α : R) * c) := by
  rw [F.weylElt_inv_mul_elt, Units.inv_mul_cancel_right]

variable (R) in
theorem exists_elt_eq_conj (α : Root τ) :
    ∃ (j : Fin τ.rank) (ε : ℤ) (m : (Module.End R (RootModule τ R))ˣ),
      (ε = 1 ∨ ε = -1) ∧ m ∈ Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ R i 1) ∧
      ∀ c : R, F.elt R α c = (m : Module.End R (RootModule τ R)) * xOp τ R j ((ε : R) * c) *
        ((m⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨j, 1, 1, .inl rfl, one_mem _, fun c => ?_⟩
    rw [Int.cast_one, one_mul, inv_one, Units.val_one, one_mul, mul_one]
    exact F.elt_simple j c
  | @reflect i v hv ih =>
    obtain ⟨j, ε, m, hε, hm, h⟩ := ih
    have hα : simple τ i • (⟨v, hv⟩ : Root τ) = ⟨reflect τ i v, IsRoot.reflect i hv⟩ :=
      Subtype.ext (simple_smul i v)
    refine ⟨j, ε * F.sign i ⟨v, hv⟩, weylElt τ R i 1 * m, ?_,
      mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) hm, fun c => ?_⟩
    · rcases hε with rfl | rfl <;> rcases F.sign_eq i ⟨v, hv⟩ with h | h <;> rw [h] <;> norm_num
    · have key := F.weylElt_mul_elt i ⟨v, hv⟩ ((F.sign i ⟨v, hv⟩ : R) * c)
      rw [← mul_assoc, F.sign_cast_mul_self, one_mul, hα] at key
      rw [← Units.mul_inv_cancel_right (F.elt R _ c) (weylElt τ R i 1), ← key, h, mul_inv_rev,
        Units.val_mul, Units.val_mul, Int.cast_mul, mul_assoc (ε : R)]
      simp only [mul_assoc]

theorem elt_add (α : Root τ) (c d : R) : F.elt R α (c + d) = F.elt R α c * F.elt R α d := by
  obtain ⟨j, ε, m, -, -, h⟩ := F.exists_elt_eq_conj R α
  rw [h, h, h, mul_add, ← xOp_mul_xOp (upTransport τ)]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem elt_mul_elt_neg (α : Root τ) (c : R) : F.elt R α c * F.elt R α (-c) = 1 := by
  rw [← F.elt_add, add_neg_cancel, F.elt_zero]

theorem elt_neg_mul_elt (α : Root τ) (c : R) : F.elt R α (-c) * F.elt R α c = 1 := by
  rw [← F.elt_add, neg_add_cancel, F.elt_zero]

variable (R) in
@[expose] noncomputable def eltUnit (α : Root τ) (c : R) : (Module.End R (RootModule τ R))ˣ where
  val := F.elt R α c
  inv := F.elt R α (-c)
  val_inv := F.elt_mul_elt_neg α c
  inv_val := F.elt_neg_mul_elt α c

@[simp] theorem coe_eltUnit (α : Root τ) (c : R) :
    (F.eltUnit R α c : Module.End R (RootModule τ R)) = F.elt R α c :=
  rfl

theorem eltUnit_inv (α : Root τ) (c : R) : (F.eltUnit R α c)⁻¹ = F.eltUnit R α (-c) :=
  Units.ext rfl

theorem eltUnit_add (α : Root τ) (c d : R) :
    F.eltUnit R α (c + d) = F.eltUnit R α c * F.eltUnit R α d :=
  Units.ext (F.elt_add α c d)

theorem eltUnit_zero (α : Root τ) : F.eltUnit R α 0 = 1 :=
  Units.ext (F.elt_zero α)

theorem eltUnit_simple (j : Fin τ.rank) (c : R) :
    F.eltUnit R (simpleRoot τ j) c = xUnit τ R j c :=
  Units.ext (F.elt_simple j c)

theorem eltUnit_neg_simple (j : Fin τ.rank) (c : R) :
    F.eltUnit R (-simpleRoot τ j) c = yUnit τ R j c :=
  Units.ext (F.elt_neg_simple j c)

variable (R) in
theorem exists_eltUnit_eq_conj (α : Root τ) :
    ∃ (j : Fin τ.rank) (ε : ℤ) (m : (Module.End R (RootModule τ R))ˣ),
      (ε = 1 ∨ ε = -1) ∧ m ∈ Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ R i 1) ∧
      ∀ c : R, F.eltUnit R α c = m * xUnit τ R j ((ε : R) * c) * m⁻¹ := by
  obtain ⟨j, ε, m, hε, hm, h⟩ := F.exists_elt_eq_conj R α
  exact ⟨j, ε, m, hε, hm, fun c => Units.ext (h c)⟩

theorem weylElt_mul_eltUnit_mul_inv (i : Fin τ.rank) (α : Root τ) (c : R) :
    weylElt τ R i 1 * F.eltUnit R α c * (weylElt τ R i 1)⁻¹ =
      F.eltUnit R (simple τ i • α) ((F.sign i α : R) * c) :=
  Units.ext (F.weylElt_mul_elt_mul_inv i α c)

theorem D_simple_smul (i : Fin τ.rank) (α : Root τ) (k : ℕ) :
    F.D R (simple τ i • α) k = ((F.sign i α ^ k : ℤ) : R) •
      ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * F.D R α k *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R))) := by
  rw [← weylElt_inv, F.conj, smul_mul_assoc, Units.mul_inv_cancel_right, smul_smul,
    ← Int.cast_mul, ← mul_pow, F.sign_mul_self, one_pow, Int.cast_one, one_smul]

theorem mapsLabelWt_D (α : Root τ) {k : ℕ} (hk : 1 ≤ k) :
    MapsLabelWt (F.D R α k) (· + k • α.1) := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    change MapsLabelWt (F.D R (simpleRoot τ j) k) _
    rw [F.D_simple]
    exact mapsLabelWt_xCoeff j hk
  | @reflect i v hv ih =>
    have hα : simple τ i • (⟨v, hv⟩ : Root τ) = ⟨reflect τ i v, IsRoot.reflect i hv⟩ :=
      Subtype.ext (simple_smul i v)
    rw [← hα, F.D_simple_smul]
    refine ((((mapsLabelWt_weylElt i 1).mul ih).mul (mapsLabelWt_weylElt i (-1))).smul
      _).congr fun μ => ?_
    change reflectHom τ i (reflect τ i μ + k • v) = μ + k • (simple τ i • v)
    rw [map_add, map_nsmul, reflectHom_apply, reflectHom_apply, reflect_reflect, simple_smul]

theorem D_weight_shift (α : Root τ) {k : ℕ} (hk : 1 ≤ k) (a b : Label τ)
    (h : F.D R α k (Finsupp.single b 1) a ≠ 0) : labelWt τ a = labelWt τ b + k • α.1 :=
  F.mapsLabelWt_D α hk a b h

theorem elt_weight_shift (α : Root τ) (c : R) (a b : Label τ)
    (h : F.elt R α c (Finsupp.single b 1) a - (Finsupp.single b 1 : RootModule τ R) a ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • α.1 := by
  rw [elt, Finset.sum_range_succ', pow_zero, one_smul, F.D_zero, LinearMap.add_apply,
    Module.End.one_apply, Finsupp.add_apply, add_sub_cancel_right, LinearMap.sum_apply,
    Finsupp.finsetSum_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hk
  exact ⟨k + 1, by omega, F.mapsLabelWt_D α (by omega) a b (right_ne_zero_of_mul hk)⟩

theorem torusElt_mul_D (i : Fin τ.rank) (t : Rˣ) (α : Root τ) (k : ℕ) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) * F.D R α k =
      (((t ^ (∑ j, τ.cartan i j * α.1 j) : Rˣ) : R) ^ k) •
        (F.D R α k * (torusElt τ R i t : Module.End R (RootModule τ R))) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.smul_apply, torusElt_single, map_smul, Finsupp.smul_apply, smul_eq_mul,
    torusElt_apply]
  by_cases hD : F.D R α k (Finsupp.single b 1) a = 0
  · rw [hD]
    ring
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [F.D_zero, Module.End.one_apply] at hD ⊢
    obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 hD
    ring
  · have hw : labelWt τ a = labelWt τ b + k • α.1 := F.mapsLabelWt_D α hk a b hD
    have hsum : ∑ j, τ.cartan i j * labelWt τ a j =
        ∑ j, τ.cartan i j * labelWt τ b j + (∑ j, τ.cartan i j * α.1 j) * k := by
      rw [hw, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      ring
    rw [hsum, zpow_add, zpow_mul, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
    ring

theorem torusElt_mul_elt (i : Fin τ.rank) (t : Rˣ) (α : Root τ) (c : R) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) * F.elt R α c =
      F.elt R α (((t ^ (∑ j, τ.cartan i j * α.1 j) : Rˣ) : R) * c) *
        (torusElt τ R i t : Module.End R (RootModule τ R)) := by
  simp only [elt, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    F.torusElt_mul_D, smul_smul, mul_pow]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem torusElt_mul_elt_mul_inv (i : Fin τ.rank) (t : Rˣ) (α : Root τ) (c : R) :
    (torusElt τ R i t : Module.End R (RootModule τ R)) * F.elt R α c *
        (((torusElt τ R i t)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      F.elt R α (((t ^ (∑ j, τ.cartan i j * α.1 j) : Rˣ) : R) * c) := by
  rw [F.torusElt_mul_elt, Units.mul_inv_cancel_right]

theorem torusElt_mul_eltUnit_mul_inv (i : Fin τ.rank) (t : Rˣ) (α : Root τ) (c : R) :
    torusElt τ R i t * F.eltUnit R α c * (torusElt τ R i t)⁻¹ =
      F.eltUnit R α (((t ^ (∑ j, τ.cartan i j * α.1 j) : Rˣ) : R) * c) :=
  Units.ext (F.torusElt_mul_elt_mul_inv i t α c)

end Ring

section Field

variable {K : Type} [Field K]

theorem eltUnit_mem_adjointGroup (α : Root τ) (c : K) : F.eltUnit K α c ∈ adjointGroup τ K := by
  obtain ⟨j, ε, m, -, hm, h⟩ := F.exists_eltUnit_eq_conj K α
  have hm' : m ∈ adjointGroup τ K :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => weylElt_mem_adjointGroup i 1) hm
  rw [h c]
  exact mul_mem (mul_mem hm' (xUnit_mem_adjointGroup j _)) (inv_mem hm')

@[expose] noncomputable def eltElement (α : Root τ) (c : K) : adjointGroup τ K :=
  ⟨F.eltUnit K α c, F.eltUnit_mem_adjointGroup α c⟩

@[simp] theorem coe_eltElement (α : Root τ) (c : K) :
    ((F.eltElement α c : adjointGroup τ K) : ModGL τ K) = F.eltUnit K α c :=
  rfl

theorem eltElement_add (α : Root τ) (c d : K) :
    F.eltElement α (c + d) = F.eltElement α c * F.eltElement α d :=
  Subtype.ext (F.eltUnit_add α c d)

theorem eltElement_zero (α : Root τ) : F.eltElement α (0 : K) = 1 :=
  Subtype.ext (F.eltUnit_zero α)

variable (K) in
@[expose] noncomputable def rootHom (α : Root τ) : Multiplicative K →* adjointGroup τ K where
  toFun c := F.eltElement α c.toAdd
  map_one' := F.eltElement_zero α
  map_mul' c d := F.eltElement_add α c.toAdd d.toAdd

@[simp] theorem rootHom_apply (α : Root τ) (c : Multiplicative K) :
    F.rootHom K α c = F.eltElement α c.toAdd :=
  rfl

variable (K) in
@[expose] noncomputable def rootSubgroup (α : Root τ) : Subgroup (adjointGroup τ K) :=
  (F.rootHom K α).range

theorem mem_rootSubgroup {α : Root τ} {g : adjointGroup τ K} :
    g ∈ F.rootSubgroup K α ↔ ∃ c : K, F.eltElement α c = g :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem eltElement_mem_rootSubgroup (α : Root τ) (c : K) :
    F.eltElement α c ∈ F.rootSubgroup K α :=
  F.mem_rootSubgroup.2 ⟨c, rfl⟩

theorem mem_rootSubgroup_simple (i : Fin τ.rank) (g : adjointGroup τ K) :
    g ∈ F.rootSubgroup K (simpleRoot τ i) ↔ ∃ c : K, (g : ModGL τ K) = xUnit τ K i c := by
  rw [F.mem_rootSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, F.eltUnit_simple i c⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext ((F.eltUnit_simple i c).trans hc.symm)⟩

theorem mem_rootSubgroup_neg_simple (i : Fin τ.rank) (g : adjointGroup τ K) :
    g ∈ F.rootSubgroup K (-simpleRoot τ i) ↔ ∃ c : K, (g : ModGL τ K) = yUnit τ K i c := by
  rw [F.mem_rootSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, F.eltUnit_neg_simple i c⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext ((F.eltUnit_neg_simple i c).trans hc.symm)⟩

theorem rootSubgroup_weight_shift (α : Root τ) (g : adjointGroup τ K)
    (hg : g ∈ F.rootSubgroup K α) (a b : Label τ)
    (h : ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a -
      (Finsupp.single b 1 : RootModule τ K) a ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • α.1 := by
  obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hg
  exact F.elt_weight_shift α c a b h

theorem map_conj_rootSubgroup {α β : Root τ} (g : adjointGroup τ K) {u : K → K}
    (hu : Function.Surjective u) (h : ∀ c, g * F.eltElement α c * g⁻¹ = F.eltElement β (u c)) :
    (F.rootSubgroup K α).map (MulAut.conj g).toMonoidHom = F.rootSubgroup K β := by
  ext x
  simp only [Subgroup.mem_map, F.mem_rootSubgroup, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨u c, (h c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨c', rfl⟩ := hu c
    exact ⟨_, ⟨c', rfl⟩, h c'⟩

theorem weylElement_mul_eltElement_mul_inv (i : Fin τ.rank) (α : Root τ) (c : K) :
    weylElement τ K i * F.eltElement α c * (weylElement τ K i)⁻¹ =
      F.eltElement (simple τ i • α) ((F.sign i α : K) * c) :=
  Subtype.ext (F.weylElt_mul_eltUnit_mul_inv i α c)

theorem map_conj_weylElement (i : Fin τ.rank) (α : Root τ) :
    (F.rootSubgroup K α).map (MulAut.conj (weylElement τ K i)).toMonoidHom =
      F.rootSubgroup K (simple τ i • α) :=
  F.map_conj_rootSubgroup _ (u := fun c => (F.sign i α : K) * c)
    (fun c => ⟨(F.sign i α : K) * c, by
      beta_reduce
      rw [← mul_assoc, F.sign_cast_mul_self, one_mul]⟩)
    (F.weylElement_mul_eltElement_mul_inv i α)

theorem torusElement_mul_eltElement_mul_inv (i : Fin τ.rank) (t : Kˣ) (α : Root τ) (c : K) :
    torusElement τ K i t * F.eltElement α c * (torusElement τ K i t)⁻¹ =
      F.eltElement α (((t ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K) * c) :=
  Subtype.ext (F.torusElt_mul_eltUnit_mul_inv i t α c)

theorem map_conj_torusElement (i : Fin τ.rank) (t : Kˣ) (α : Root τ) :
    (F.rootSubgroup K α).map (MulAut.conj (torusElement τ K i t)).toMonoidHom =
      F.rootSubgroup K α :=
  F.map_conj_rootSubgroup _
    (u := fun c => ((t ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K) * c)
    (fun c => ⟨(((t ^ (∑ j, τ.cartan i j * α.1 j))⁻¹ : Kˣ) : K) * c, by
      beta_reduce
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]⟩)
    (F.torusElement_mul_eltElement_mul_inv i t α)

variable (K) in
@[expose] def CommContained (α β : Root τ) : Prop :=
  ∀ x ∈ F.rootSubgroup K α, ∀ y ∈ F.rootSubgroup K β, x * y * x⁻¹ * y⁻¹ ∈
    ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
      F.rootSubgroup K γ

theorem commContained_iff {α β : Root τ} :
    F.CommContained K α β ↔ ∀ c d : K,
      F.eltElement α c * F.eltElement β d * (F.eltElement α c)⁻¹ * (F.eltElement β d)⁻¹ ∈
        ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
          F.rootSubgroup K γ := by
  constructor
  · exact fun h c d =>
      h _ (F.eltElement_mem_rootSubgroup α c) _ (F.eltElement_mem_rootSubgroup β d)
  · intro h x hx y hy
    obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := F.mem_rootSubgroup.1 hy
    exact h c d

theorem CommContained.symm {α β : Root τ} (h : F.CommContained K α β) :
    F.CommContained K β α := by
  intro y hy x hx
  have hmem := inv_mem (h x hx y hy)
  rw [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at hmem
  have hle : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
      F.rootSubgroup K γ) ≤
      ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • β.1 + b • α.1),
        F.rootSubgroup K γ :=
    biSup_mono fun γ ⟨a, b, ha, hb, hγ⟩ => ⟨b, a, hb, ha, by rw [hγ, add_comm]⟩
  exact hle hmem

theorem map_conj_weylElement_iSup (i : Fin τ.rank) (P : Root τ → Prop) :
    (⨆ (γ : Root τ) (_ : P γ), F.rootSubgroup K γ).map
        (MulAut.conj (weylElement τ K i)).toMonoidHom =
      ⨆ (γ : Root τ) (_ : P ((simple τ i)⁻¹ • γ)), F.rootSubgroup K γ := by
  simp only [Subgroup.map_iSup, F.map_conj_weylElement]
  apply le_antisymm
  · exact iSup₂_le fun γ hγ =>
      le_iSup₂_of_le (simple τ i • γ) (by rwa [inv_smul_smul]) le_rfl
  · refine iSup₂_le fun γ hγ => le_iSup₂_of_le ((simple τ i)⁻¹ • γ) hγ ?_
    rw [smul_inv_smul]

theorem comm_transport (i : Fin τ.rank) {α β : Root τ} (h : F.CommContained K α β) :
    F.CommContained K (simple τ i • α) (simple τ i • β) := by
  intro x hx y hy
  rw [← F.map_conj_weylElement] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj (weylElement τ K i)).toMonoidHom
    (h x hx y hy)
  rw [F.map_conj_weylElement_iSup, map_mul, map_mul, map_mul, map_inv, map_inv] at hmem
  have hle : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      ((simple τ i)⁻¹ • γ).1 = a • α.1 + b • β.1), F.rootSubgroup K γ) ≤
      ⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
        γ.1 = a • (simple τ i • α).1 + b • (simple τ i • β).1), F.rootSubgroup K γ := by
    refine biSup_mono fun γ ⟨a, b, ha, hb, hγ⟩ => ⟨a, b, ha, hb, ?_⟩
    rw [coe_smul_root] at hγ
    rw [coe_smul_root, coe_smul_root, ← smul_inv_smul (simple τ i) γ.1, hγ, smul_add,
      smul_comm (simple τ i) a, smul_comm (simple τ i) b]
  exact hle hmem

theorem comm_transport_list (l : List (Fin τ.rank)) {α β : Root τ}
    (h : F.CommContained K α β) :
    F.CommContained K ((l.map (simple τ)).prod • α) ((l.map (simple τ)).prod • β) := by
  induction l with
  | nil => simpa using h
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, mul_smul]
    exact F.comm_transport i ih

theorem comm_transport_weyl (w : WeylGroup τ) {α β : Root τ} (h : F.CommContained K α β) :
    F.CommContained K (w • α) (w • β) := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => simpa using h
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul]
    exact F.comm_transport i ih

theorem commContained_smul_iff (w : WeylGroup τ) {α β : Root τ} :
    F.CommContained K (w • α) (w • β) ↔ F.CommContained K α β := by
  refine ⟨fun h => ?_, F.comm_transport_weyl w⟩
  simpa using F.comm_transport_weyl w⁻¹ h

end Field

variable (K : Type) [Field K]

@[expose] noncomputable def toRootSubgroups
    (hcomm : ∀ (i : Fin τ.rank) (β : Root τ), 0 < height β.1 → β ≠ simpleRoot τ i →
      F.CommContained K (simpleRoot τ i) β) :
    RootSubgroups τ K where
  X := F.rootSubgroup K
  mem_simple := F.mem_rootSubgroup_simple
  mem_neg_simple := F.mem_rootSubgroup_neg_simple
  weight_shift := F.rootSubgroup_weight_shift
  conj_weyl := F.map_conj_weylElement
  conj_torus := F.map_conj_torusElement
  comm := hcomm

@[simp] theorem toRootSubgroups_X
    (hcomm : ∀ (i : Fin τ.rank) (β : Root τ), 0 < height β.1 → β ≠ simpleRoot τ i →
      F.CommContained K (simpleRoot τ i) β) :
    (F.toRootSubgroups K hcomm).X = F.rootSubgroup K :=
  rfl

open CFSG.LieType.BorelTits in
theorem holds_adjointGroup_of_family [Finite K]
    (hcomm : ∀ (i : Fin τ.rank) (β : Root τ), 0 < height β.1 → β ≠ simpleRoot τ i →
      F.CommContained K (simpleRoot τ i) β)
    (p : ℕ) [Fact p.Prime] [CharP K p] : Holds (adjointGroup τ K) p :=
  holds_adjointGroup (F.toRootSubgroups K hcomm) p

end RootOperatorFamily

end CFSG.LieType.Chevalley
