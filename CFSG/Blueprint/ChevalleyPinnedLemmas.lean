module

public import CFSG.Blueprint.ChevalleyPinned
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.Blueprint.Chevalley

open scoped Nat

variable {τ : Tag} {R : Type*} [CommRing R]

theorem single_eq_single_iff {i j : Fin τ.rank} :
    (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_contra hij
  have := congrFun h i
  simp [Pi.single_eq_of_ne hij] at this

theorem single_ne_neg_single' (i j : Fin τ.rank) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single j 1 := by
  intro h
  have := congrFun h i
  by_cases hij : i = j
  · subst hij; simp at this
  · simp [Pi.single_eq_of_ne hij] at this

theorem pinnedData_single (i : Fin τ.rank) :
    pinnedData τ (Pi.single i 1) = (i, [], 1) := by
  have h : ∃ j, (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 := ⟨i, rfl⟩
  rw [pinnedData, dite_eq_left_of_eq_true (eq_true h), (single_eq_single_iff.1 h.choose_spec).symm]

theorem pinnedData_neg_single (i : Fin τ.rank) :
    pinnedData τ (-Pi.single i 1) = (i, [(i : ℕ)], -1) := by
  have h : ¬ ∃ j, (-Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single j 1 :=
    fun ⟨j, hj⟩ => single_ne_neg_single' j i hj.symm
  have h' : ∃ j, (-Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single j 1 := ⟨i, rfl⟩
  have hj : h'.choose = i := (single_eq_single_iff.1 (neg_injective h'.choose_spec)).symm
  rw [pinnedData, dite_eq_right_of_eq_false (eq_false h), dite_eq_left_of_eq_true (eq_true h'), hj]

theorem xUnit_add (i : Fin τ.rank) (c d : R) :
    xUnit τ R i (c + d) = xUnit τ R i c * xUnit τ R i d :=
  Units.ext (xOp_mul_xOp (upTransport τ) i c d).symm

theorem xUnit_zero (i : Fin τ.rank) : xUnit τ R i 0 = 1 :=
  Units.ext (xOp_zero i)

variable (τ R)

theorem pinnedX_add (α : Fin τ.rank → ℤ) (c d : R) :
    pinnedX τ R α (c + d) = pinnedX τ R α c * pinnedX τ R α d := by
  simp only [pinnedX, smul_add, xUnit_add]
  group

theorem pinnedX_zero (α : Fin τ.rank → ℤ) : pinnedX τ R α 0 = 1 := by
  simp [pinnedX, xUnit_zero]

theorem pinnedX_neg (α : Fin τ.rank → ℤ) (c : R) : (pinnedX τ R α c)⁻¹ = pinnedX τ R α (-c) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pinnedX_add, neg_add_cancel, pinnedX_zero]

theorem pinnedSign_eq (α : Fin τ.rank → ℤ) :
    (pinnedData τ α).2.2 = 1 ∨ (pinnedData τ α).2.2 = -1 := by
  unfold pinnedData
  split_ifs <;> simp

theorem pinnedX_injective (α : Fin τ.rank → ℤ) : Function.Injective (pinnedX τ R α) := by
  intro c d h
  have h' : xUnit τ R (pinnedData τ α).1 ((pinnedData τ α).2.2 • c) =
      xUnit τ R (pinnedData τ α).1 ((pinnedData τ α).2.2 • d) := by
    simpa [pinnedX] using h
  have h'' := xOp_injective (τ := τ) (R := R) _ (congrArg Units.val h')
  rcases pinnedSign_eq τ α with hε | hε <;> rw [hε] at h'' <;> simpa using h''

theorem pinnedX_single (i : Fin τ.rank) (c : R) : pinnedX τ R (Pi.single i 1) c = xUnit τ R i c := by
  simp [pinnedX, pinnedWeyl, pinnedData_single]

theorem pinnedX_neg_single (i : Fin τ.rank) (c : R) :
    pinnedX τ R (-Pi.single i 1) c = yUnit τ R i c := by
  have hidx : τ.idx (i : ℕ) = i := Fin.ext (Nat.mod_eq_of_lt i.2)
  refine Units.ext ?_
  simp only [pinnedX, pinnedWeyl, pinnedData_neg_single, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one,
    hidx, Units.val_mul, neg_smul, one_smul]
  rw [coe_xUnit, weylElt_mul_xOp_mul_inv]
  simp [coe_yUnit]

theorem conj_smul_pinnedE (α : Fin τ.rank → ℤ) (e : R) :
    ((pinnedWeyl τ R α)⁻¹ : (Module.End R (RootModule τ R))ˣ).val * (e • pinnedE τ R α) *
        (pinnedWeyl τ R α).val = (e * (pinnedData τ α).2.2) • infE τ R (pinnedData τ α).1 := by
  simp only [pinnedE, smul_smul]
  rw [mul_smul_comm, smul_mul_assoc]
  simp [mul_assoc]

theorem smul_pinnedE_injective (α : Fin τ.rank → ℤ) :
    Function.Injective fun c : R => c • pinnedE τ R α := by
  intro c d h
  have h2 : (c * (pinnedData τ α).2.2) • infE τ R (pinnedData τ α).1 =
      (d * (pinnedData τ α).2.2) • infE τ R (pinnedData τ α).1 := by
    rw [← conj_smul_pinnedE, ← conj_smul_pinnedE]
    exact congrArg (fun A => ((pinnedWeyl τ R α)⁻¹ : (Module.End R (RootModule τ R))ˣ).val * A *
      (pinnedWeyl τ R α).val) h
  have h3 := congrArg (fun A : Module.End R (RootModule τ R) =>
    A (rootVec τ R (-Pi.single (pinnedData τ α).1 1)) (Sum.inl (pinnedData τ α).1)) h2
  simp [infE_rootVec_neg_single, hVec] at h3
  rcases pinnedSign_eq τ α with hε | hε <;> rw [hε] at h3 <;> simpa using h3

@[expose] def pinnedCoeff (α : Fin τ.rank → ℤ) (k : ℕ) : Module.End R (RootModule τ R) :=
  (((pinnedData τ α).2.2 ^ k : ℤ) : R) •
    ((pinnedWeyl τ R α : Module.End R (RootModule τ R)) * xCoeff τ R (pinnedData τ α).1 k *
      ((pinnedWeyl τ R α)⁻¹ : (Module.End R (RootModule τ R))ˣ))

theorem pinnedX_eq_sum (α : Fin τ.rank → ℤ) (c : R) :
    (pinnedX τ R α c : Module.End R (RootModule τ R)) =
      ∑ k ∈ Finset.range 4, c ^ k • pinnedCoeff τ R α k := by
  simp only [pinnedX, Units.val_mul, coe_xUnit, xOp_eq_sum_xCoeff, Finset.mul_sum,
    Finset.sum_mul, pinnedCoeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, mul_smul_comm, smul_mul_assoc, zsmul_eq_mul, mul_pow]
  push_cast
  ring_nf

theorem pinnedE_pow (α : Fin τ.rank → ℤ) (k : ℕ) :
    pinnedE τ R α ^ k = (k ! : R) • pinnedCoeff τ R α k := by
  simp only [pinnedE, pinnedCoeff, smul_pow, Units.conj_pow, infE_pow, mul_smul_comm,
    smul_mul_assoc, smul_smul]
  push_cast
  ring_nf

theorem pinnedE_pow_four (α : Fin τ.rank → ℤ) : pinnedE τ R α ^ 4 = 0 := by
  rw [pinnedE_pow, pinnedCoeff, xCoeff_eq_zero _ (le_refl 4)]
  simp

theorem pinnedCoeff_zero (α : Fin τ.rank → ℤ) : pinnedCoeff τ R α 0 = 1 := by
  simp [pinnedCoeff, xCoeff_zero]

theorem pinnedCoeff_one (α : Fin τ.rank → ℤ) : pinnedCoeff τ R α 1 = pinnedE τ R α := by
  simp [pinnedCoeff, pinnedE, xCoeff_one]

theorem pinnedX_eq_sum_pow {R : Type*} [CommRing R] [Algebra ℚ R] (α : Fin τ.rank → ℤ) (c : R) :
    (pinnedX τ R α c : Module.End R (RootModule τ R)) =
      ∑ k ∈ Finset.range 4, ((k ! : ℚ)⁻¹ • c ^ k) • pinnedE τ R α ^ k := by
  rw [pinnedX_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pinnedE_pow, smul_smul]
  congr 1
  have h1 : c ^ k * (k ! : R) = ((k ! : ℚ)) • c ^ k := by
    rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ]
  rw [smul_mul_assoc, h1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k),
    one_smul]

end CFSG.Blueprint.Chevalley
