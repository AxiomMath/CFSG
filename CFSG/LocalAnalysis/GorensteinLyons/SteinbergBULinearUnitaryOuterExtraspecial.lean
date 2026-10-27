module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OuterDerived Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace LinearUnitaryOuter

open LinearFlag in
theorem linear_outer_filtration {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    ∃ (N : Subgroup (Outer (projectiveSL n K))) (_ : N.Normal), IsCyclic N ∧
      Nat.card N ∣ Nat.gcd n (Nat.card K - 1) ∧
      (∀ x y : Outer (projectiveSL n K) ⧸ N, x * y = y * x) ∧
      ∃ a b : Outer (projectiveSL n K) ⧸ N,
        closure ({a, b} : Set (Outer (projectiveSL n K) ⧸ N)) = ⊤ := by
  set N := ((QuotientGroup.mk' (inner (projectiveSL n K))).comp (conjAut n K)).range with hN
  obtain ⟨hcyc, hcard⟩ := linear_diagonal_outer (K := K) (n := n) (by omega)
  have hcomm : ∀ a b : Outer (projectiveSL n K), a * b * a⁻¹ * b⁻¹ ∈ N := by
    intro a b
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp (commutator_mem_linearAutGroup hn α β)
    exact ⟨A, by rw [MonoidHom.comp_apply, hA]; rfl⟩
  obtain ⟨-, -, hNn, hab⟩ := derived_of_commutator_mem hcyc hcard hcomm
  obtain ⟨-, -, -, -, -, ⟨g, -, hgD⟩, ⟨g', -, hg'E⟩, -⟩ :=
    standard_outer_quotients (K := K) (n := n)
  have hR := (LinearFlag.automorphism_generation (K := K) hn).1
  refine ⟨N, hNn, hcyc, hcard, hab, QuotientGroup.mk (QuotientGroup.mk g),
    QuotientGroup.mk (QuotientGroup.mk g'), eq_top_iff.2 fun z _ => ?_⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨k', hk'⟩ := hg'E x (by rw [hR]; exact mem_top x)
  obtain ⟨k, hk⟩ := hgD _ hk'
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 hk
  have h0 : (QuotientGroup.mk (QuotientGroup.mk (g ^ k * (g' ^ k' * x) :
      MulAut (projectiveSL n K))) : Outer (projectiveSL n K) ⧸ N) = 1 := by
    rw [QuotientGroup.eq_one_iff, ← hA]
    exact ⟨A, rfl⟩
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h0
  rw [← mul_assoc] at h0
  rw [eq_inv_of_mul_eq_one_right h0]
  exact inv_mem (mul_mem (zpow_mem (subset_closure (Set.mem_insert _ _)) k)
    (zpow_mem (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k'))

open UnitaryHigher in
theorem unitary_outer_filtration {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    ∃ (N : Subgroup (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
      (_ : N.Normal), IsCyclic N ∧ Nat.card N ∣ Nat.gcd n (p ^ f + 1) ∧
      IsCyclic (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⧸ N) := by
  have : Finite K := h.finite
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨-, -, -, -, -, -, -, hFker, -, hinner, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hq
  set F := primeFormFieldFactor h (isPrimeFormGram_one (n := n) (K := K)) hn hq
  have hI : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≤ F.ker := by
    rw [hFker]
    intro α hα
    obtain ⟨s, rfl⟩ := (hinner α).1 hα
    exact ⟨_, rfl⟩
  set ψ := QuotientGroup.lift _ F hI
  obtain ⟨-, hcyc, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  obtain ⟨hNcyc, hNcard⟩ := isCyclic_map_mk_and_card_dvd _ _ hcyc
  have hker : ψ.ker = (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map
      (QuotientGroup.mk' _) := by
    rw [QuotientGroup.ker_lift, hFker]
  refine ⟨ψ.ker, inferInstance, by rw [hker]; exact hNcyc,
    by rw [hker]; exact hNcard.trans (dvd_of_eq hcard),
    isCyclic_of_injective (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ)⟩

end LinearUnitaryOuter

open LinearUnitaryOuter

end CFSG.LocalAnalysis.GorensteinLyons
