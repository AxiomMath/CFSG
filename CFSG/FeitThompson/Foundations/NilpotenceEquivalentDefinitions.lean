module

public import CFSG.FeitThompson.Foundations.NormalSylowDirectProduct
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.PGroupNilpotent
import CFSG.FeitThompson.Foundations.NilpotentHomImageNilpotent
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem isNilpotent_iff_exists_normal_series_commutator_le (G : Type*) [Group G] :
    Group.IsNilpotent G ↔ ∃ (r : ℕ) (X : ℕ → Subgroup G), X 0 = ⊥ ∧ X r = ⊤ ∧
      (∀ i < r, X i ≤ X (i + 1)) ∧ (∀ i, (X i).Normal) ∧
      ∀ i, 1 ≤ i → i ≤ r → ⁅(⊤ : Subgroup G), X i⁆ ≤ X (i - 1) := by
  rw [isNilpotent_iff_exists_central_series]
  refine exists_congr fun r => exists_congr fun X => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [closure_setOf_inv_mul_inv_mul_mul]
  constructor
  · intro h i hi1 hi2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simpa using h j (by omega)
  · intro h i hi
    simpa using h (i + 1) (by omega) (by omega)

theorem upperCentralSeries_succ_eq_comap_center (G : Type*) [Group G] (i : ℕ) :
    Subgroup.upperCentralSeries G (i + 1) =
      Subgroup.comap (QuotientGroup.mk' (Subgroup.upperCentralSeries G i))
        (Subgroup.center (G ⧸ Subgroup.upperCentralSeries G i)) :=
  Subgroup.upperCentralSeriesStep_eq_comap_center (Subgroup.upperCentralSeries G i)

theorem eq_upperCentralSeries_of_comap_center {Z : ℕ → Subgroup G} (hn : ∀ i, (Z i).Normal)
    (h0 : Z 0 = ⊥)
    (hsucc : ∀ i, letI := hn i;
      Z (i + 1) = Subgroup.comap (QuotientGroup.mk' (Z i)) (Subgroup.center (G ⧸ Z i)))
    (i : ℕ) : Z i = Subgroup.upperCentralSeries G i := by
  induction i with
  | zero => rw [h0, Subgroup.upperCentralSeries_zero]
  | succ i ih =>
    have := hn i
    refine (hsucc i).trans ?_
    rw [← Subgroup.upperCentralSeriesStep_eq_comap_center]
    ext x
    simp only [Subgroup.mem_upperCentralSeriesStep, Subgroup.mem_upperCentralSeries_succ_iff, ih]

theorem isNilpotent_iff_exists_upperCenterSeries_eq_top (G : Type*) [Group G] :
    Group.IsNilpotent G ↔ ∃ (r : ℕ) (Z : ℕ → Subgroup G) (hn : ∀ i, (Z i).Normal), Z 0 = ⊥ ∧
      (∀ i, letI := hn i;
        Z (i + 1) = Subgroup.comap (QuotientGroup.mk' (Z i)) (Subgroup.center (G ⧸ Z i))) ∧
      Z r = ⊤ := by
  rw [Group.isNilpotent_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, Subgroup.upperCentralSeries G, fun _ => inferInstance,
      Subgroup.upperCentralSeries_zero G, upperCentralSeries_succ_eq_comap_center G, hr⟩
  · rintro ⟨r, Z, hn, h0, hsucc, hr⟩
    exact ⟨r, (eq_upperCentralSeries_of_comap_center hn h0 hsucc r).symm.trans hr⟩

theorem isNilpotent_iff_exists_normal_sylow_family (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent G ↔ ∃ (P : (Nat.card G).primeFactors → Subgroup G)
      (hcard : ∀ p, Nat.card (P p) = (p : ℕ) ^ (Nat.card G).factorization (p : ℕ))
      (hn : ∀ p, (P p).Normal), Function.Bijective (normalSylowPiHom P hcard hn) := by
  constructor
  · intro _
    have hne : ∀ p : (Nat.card G).primeFactors, Nonempty (Sylow (p : ℕ) G) := fun p =>
      have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      inferInstance
    refine ⟨fun p => ((hne p).some : Subgroup G),
      natCard_sylow_eq_pow_factorization fun p => (hne p).some, fun p => ?_,
      bijective_normalSylowPiHom _ _ _⟩
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact sylow_normal_of_isNilpotent (hne p).some
  · rintro ⟨P, hcard, hn, hbij⟩
    have : ∀ p : (Nat.card G).primeFactors, Group.IsNilpotent (P p) := fun p =>
      isNilpotent_of_natCard_eq_prime_pow (Nat.prime_of_mem_primeFactors p.2) (hcard p)
    exact (Group.isNilpotent_congr (MulEquiv.ofBijective _ hbij)).1 Group.isNilpotent_pi

theorem exists_mulEquiv_pi_normal_sylow (G : Type*) [Group G] [Finite G] [Group.IsNilpotent G] :
    ∃ (P : (Nat.card G).primeFactors → Subgroup G), (∀ p, (P p).Normal) ∧
      (∀ p, Nat.card (P p) = (p : ℕ) ^ (Nat.card G).factorization (p : ℕ)) ∧
      Nonempty ((∀ p : (Nat.card G).primeFactors, P p) ≃* G) := by
  obtain ⟨P, hcard, hn, hbij⟩ := (isNilpotent_iff_exists_normal_sylow_family G).1 ‹_›
  exact ⟨P, hn, hcard, ⟨MulEquiv.ofBijective _ hbij⟩⟩

theorem nilpotence_tfae (G : Type*) [Group G] [Finite G] :
    List.TFAE
      [ ∃ (r : ℕ) (X : ℕ → Subgroup G), X 0 = ⊥ ∧ X r = ⊤ ∧ (∀ i < r, X i ≤ X (i + 1)) ∧
          (∀ i, (X i).Normal) ∧ ∀ i, 1 ≤ i → i ≤ r → ⁅(⊤ : Subgroup G), X i⁆ ≤ X (i - 1),
        ∃ (r : ℕ) (Z : ℕ → Subgroup G) (hn : ∀ i, (Z i).Normal), Z 0 = ⊥ ∧
          (∀ i, letI := hn i;
            Z (i + 1) = Subgroup.comap (QuotientGroup.mk' (Z i)) (Subgroup.center (G ⧸ Z i))) ∧
          Z r = ⊤,
        ∃ (P : (Nat.card G).primeFactors → Subgroup G)
          (hcard : ∀ p, Nat.card (P p) = (p : ℕ) ^ (Nat.card G).factorization (p : ℕ))
          (hn : ∀ p, (P p).Normal), Function.Bijective (normalSylowPiHom P hcard hn),
        Group.IsNilpotent G ] := by
  tfae_have 1 ↔ 4 := (isNilpotent_iff_exists_normal_series_commutator_le G).symm
  tfae_have 2 ↔ 4 := (isNilpotent_iff_exists_upperCenterSeries_eq_top G).symm
  tfae_have 3 ↔ 4 := (isNilpotent_iff_exists_normal_sylow_family G).symm
  tfae_finish

end

end CFSG.FeitThompson
