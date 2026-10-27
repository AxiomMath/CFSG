module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Poly
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial Polynomial
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum



variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k] {τ : Tag}

theorem card_orbitField (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Nat.card (D.orbitField O) = D.q ^ orbitCard O := by
  rw [OrthogonalSemilinearFixedRootDatum.orbitField,
    card_frobeniusFixedField (Nat.mul_pos (by have := D.one_le_e; omega) (D.orbitCard_pos hO)),
    pow_mul]
  rfl

theorem commute_uSL_of_commute_orbitX (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hτ : τ ≠ .G2) (hq : 3 ≤ D.q) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hcard : orbitCard O = 1 ∨ orbitCard O = 2) {z : Module.End k (RootModule τ k)}
    (hz : ∀ c : D.orbitField O, z * (D.orbitX O c : Module.End k (RootModule τ k)) =
      (D.orbitX O c : Module.End k (RootModule τ k)) * z)
    {j : ℕ} (hj : j < orbitCard O) (t : k) :
    z * (rootSL2 τ k (D.orbitVec O j) (uSL t) : Module.End k (RootModule τ k)) =
      (rootSL2 τ k (D.orbitVec O j) (uSL t) : Module.End k (RootModule τ k)) * z := by
  classical
  have hcardO := card_orbitField D hO
  have : Finite (D.orbitField O) := Nat.finite_of_card_ne_zero (by
    rw [hcardO]
    exact pow_ne_zero _ (by omega))
  have : Fintype (D.orbitField O) := Fintype.ofFinite _
  have hfc : Fintype.card (D.orbitField O) = D.q ^ orbitCard O := by
    rw [← Nat.card_eq_fintype_card, hcardO]
  set A := rootUCoeff (k := k) (D.orbitVec O 0) with hA
  set B := rootUCoeff (k := k) (D.orbitVec O 1) with hB
  rw [rootSL2_uSL_eq_sum hτ, ← sub_eq_zero, commutator_sum_smul]
  refine Finset.sum_eq_zero fun a ha => ?_
  rcases hcard with h1 | h2
  · have hj0 : j = 0 := by omega
    subst hj0
    have hX : ∀ c : D.orbitField O, (D.orbitX O c : Module.End k (RootModule τ k)) =
        ∑ a ∈ Finset.range 3, (c : k) ^ a • A a := by
      intro c
      rw [OrthogonalSemilinearFixedRootDatum.orbitX, D.orbitMap_eq_prod, h1, List.range_one,
        List.map_singleton, List.prod_singleton, D.orbitFactor_uSL, pow_zero, pow_one,
        rootSL2_uSL_eq_sum hτ]
    have h0 := eq_zero_of_forall_sum_smul_eq_zero (f := fun c : D.orbitField O => (c : k))
      Subtype.val_injective (Finset.range 3) id (Set.injOn_id _) (D := 2)
      (fun x hx => by have := Finset.mem_range.1 hx; simp only [id]; omega)
      (by rw [hfc, h1, pow_one]; omega) (fun a => z * A a - A a * z)
      (fun c => by
        rw [← commutator_sum_smul]
        simp only [id]
        rw [← hX, hz c, sub_self]) ha
    rw [h0, smul_zero]
  · have hX : ∀ c : D.orbitField O, (D.orbitX O c : Module.End k (RootModule τ k)) =
        ∑ x ∈ Finset.range 3 ×ˢ Finset.range 3, (c : k) ^ (x.1 + D.q * x.2) • (A x.1 * B x.2) := by
      intro c
      rw [OrthogonalSemilinearFixedRootDatum.orbitX, D.orbitMap_eq_prod, h2]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.singleton_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [D.orbitFactor_uSL, D.orbitFactor_uSL, Units.val_mul, pow_zero, pow_one, pow_one,
        rootSL2_uSL_eq_sum hτ, rootSL2_uSL_eq_sum hτ, Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_smul_comm, pow_add, ← pow_mul]
    have hN : ∀ x ∈ Finset.range 3 ×ˢ Finset.range 3, z * (A x.1 * B x.2) - A x.1 * B x.2 * z = 0 :=
      fun x hx => eq_zero_of_forall_sum_smul_eq_zero (f := fun c : D.orbitField O => (c : k))
        Subtype.val_injective _ (fun x : ℕ × ℕ => x.1 + D.q * x.2) (injOn_add_mul hq)
        (D := 2 + 2 * D.q)
        (fun x hx => by
          simp only [Finset.mem_product, Finset.mem_range] at hx
          have := Nat.mul_le_mul_left D.q (show x.2 ≤ 2 by omega)
          omega)
        (by rw [hfc, h2]; nlinarith)
        (fun x => z * (A x.1 * B x.2) - A x.1 * B x.2 * z)
        (fun c => by
          rw [← commutator_sum_smul]
          rw [← hX, hz c, sub_self]) hx
    have ha3 := Finset.mem_range.1 ha
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have h1 := hN (a, 0) (Finset.mem_product.2 ⟨ha, by simp⟩)
      simp only [hB, rootUCoeff_zero, mul_one] at h1
      rw [h1, smul_zero]
    · have h1 := hN (0, a) (Finset.mem_product.2 ⟨by simp, ha⟩)
      simp only [hA, rootUCoeff_zero, one_mul] at h1
      rw [h1, smul_zero]

theorem commute_vSL_of_commute_orbitY (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hτ : τ ≠ .G2) (hq : 3 ≤ D.q) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hcard : orbitCard O = 1 ∨ orbitCard O = 2) {z : Module.End k (RootModule τ k)}
    (hz : ∀ c : D.orbitField O, z * (D.orbitY O c : Module.End k (RootModule τ k)) =
      (D.orbitY O c : Module.End k (RootModule τ k)) * z)
    {j : ℕ} (hj : j < orbitCard O) (t : k) :
    z * (rootSL2 τ k (D.orbitVec O j) (vSL t) : Module.End k (RootModule τ k)) =
      (rootSL2 τ k (D.orbitVec O j) (vSL t) : Module.End k (RootModule τ k)) * z := by
  classical
  have hcardO := card_orbitField D hO
  have : Finite (D.orbitField O) := Nat.finite_of_card_ne_zero (by
    rw [hcardO]
    exact pow_ne_zero _ (by omega))
  have : Fintype (D.orbitField O) := Fintype.ofFinite _
  have hfc : Fintype.card (D.orbitField O) = D.q ^ orbitCard O := by
    rw [← Nat.card_eq_fintype_card, hcardO]
  set A := rootVCoeff (k := k) (D.orbitVec O 0) with hA
  set B := rootVCoeff (k := k) (D.orbitVec O 1) with hB
  rw [rootSL2_vSL_eq_sum hτ, ← sub_eq_zero, commutator_sum_smul]
  refine Finset.sum_eq_zero fun a ha => ?_
  rcases hcard with h1 | h2
  · have hj0 : j = 0 := by omega
    subst hj0
    have hX : ∀ c : D.orbitField O, (D.orbitY O c : Module.End k (RootModule τ k)) =
        ∑ a ∈ Finset.range 3, (c : k) ^ a • A a := by
      intro c
      rw [OrthogonalSemilinearFixedRootDatum.orbitY, D.orbitMap_eq_prod, h1, List.range_one,
        List.map_singleton, List.prod_singleton, D.orbitFactor_vSL, pow_zero, pow_one,
        rootSL2_vSL_eq_sum hτ]
    have h0 := eq_zero_of_forall_sum_smul_eq_zero (f := fun c : D.orbitField O => (c : k))
      Subtype.val_injective (Finset.range 3) id (Set.injOn_id _) (D := 2)
      (fun x hx => by have := Finset.mem_range.1 hx; simp only [id]; omega)
      (by rw [hfc, h1, pow_one]; omega) (fun a => z * A a - A a * z)
      (fun c => by
        rw [← commutator_sum_smul]
        simp only [id]
        rw [← hX, hz c, sub_self]) ha
    rw [h0, smul_zero]
  · have hX : ∀ c : D.orbitField O, (D.orbitY O c : Module.End k (RootModule τ k)) =
        ∑ x ∈ Finset.range 3 ×ˢ Finset.range 3, (c : k) ^ (x.1 + D.q * x.2) • (A x.1 * B x.2) := by
      intro c
      rw [OrthogonalSemilinearFixedRootDatum.orbitY, D.orbitMap_eq_prod, h2]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.singleton_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [D.orbitFactor_vSL, D.orbitFactor_vSL, Units.val_mul, pow_zero, pow_one, pow_one,
        rootSL2_vSL_eq_sum hτ, rootSL2_vSL_eq_sum hτ, Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_smul_comm, pow_add, ← pow_mul]
    have hN : ∀ x ∈ Finset.range 3 ×ˢ Finset.range 3, z * (A x.1 * B x.2) - A x.1 * B x.2 * z = 0 :=
      fun x hx => eq_zero_of_forall_sum_smul_eq_zero (f := fun c : D.orbitField O => (c : k))
        Subtype.val_injective _ (fun x : ℕ × ℕ => x.1 + D.q * x.2) (injOn_add_mul hq)
        (D := 2 + 2 * D.q)
        (fun x hx => by
          simp only [Finset.mem_product, Finset.mem_range] at hx
          have := Nat.mul_le_mul_left D.q (show x.2 ≤ 2 by omega)
          omega)
        (by rw [hfc, h2]; nlinarith)
        (fun x => z * (A x.1 * B x.2) - A x.1 * B x.2 * z)
        (fun c => by
          rw [← commutator_sum_smul]
          rw [← hX, hz c, sub_self]) hx
    have ha3 := Finset.mem_range.1 ha
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have h1 := hN (a, 0) (Finset.mem_product.2 ⟨ha, by simp⟩)
      simp only [hB, rootVCoeff_zero, mul_one] at h1
      rw [h1, smul_zero]
    · have h1 := hN (0, a) (Finset.mem_product.2 ⟨by simp, ha⟩)
      simp only [hA, rootVCoeff_zero, one_mul] at h1
      rw [h1, smul_zero]

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
