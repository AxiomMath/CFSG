module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteFaithfulInvariantSubspace
public import CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedRepresentationFaithful
public import CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel
public import CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeAbelianNormalizerCentralizes

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension

open CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary

theorem centralizes {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (r : ℕ) [Fact r.Prime] (D : Subgroup G) (hDcard : Nat.card D = r)
    (hD : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule F V))
    (E : Subgroup G) [hE : IsMulCommutative E] (hDE : D ≤ Subgroup.normalizer (E : Set G))
    (hEF : (Nat.card E : F) ≠ 0) (hrF : (r : F) ≠ 0) :
    D ≤ Subgroup.centralizer (E : Set G) := by
  classical
  haveI : IsCyclic D := isCyclic_of_prime_card hDcard
  obtain ⟨⟨d, hdD⟩, hgen⟩ := IsCyclic.exists_generator (α := D)
  have hzp : D = Subgroup.zpowers d := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        (show (⟨x, hx⟩ : D) ∈ Subgroup.zpowers (⟨d, hdD⟩ : D) from hgen _)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    · rw [Subgroup.zpowers_le]; exact hdD
  have hker : LinearMap.ker (ρ d - LinearMap.id) = ⊥ := by
    rw [eq_bot_iff, ← hD]
    intro v hv
    have hv' : ρ d v = v := by simpa [sub_eq_zero] using hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    intro x hx
    rw [hzp] at hx
    have hS : ∀ n : ℤ, ρ (d ^ n) v = v := by
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ m ih => rw [zpow_add_one, map_mul, Module.End.mul_apply, hv', ih]
      | pred m ih =>
        have : ρ (d ^ (-(m : ℤ))) v = v := ih
        have h2 : ρ (d ^ (-(m : ℤ) - 1)) v = v := by
          rw [zpow_sub_one, map_mul, Module.End.mul_apply]
          have : ρ d⁻¹ v = v := by
            calc ρ d⁻¹ v = ρ d⁻¹ (ρ d v) := by rw [hv']
              _ = v := by rw [← Module.End.mul_apply, ← map_mul]; simp
          rw [this, ih]
        exact h2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn, hS, sub_self]
  obtain ⟨W, hW, hWfin, hWinj⟩ := FiniteFaithfulInvariantSubspace.exists_submodule ρ hρ
  let ρW := Representation.subrepresentation ρ W hW
  have hkerW : LinearMap.ker (ρW d - LinearMap.id) = ⊥ :=
    FiniteFaithfulInvariantSubspace.fixed_kernel_eq_bot ρ W hW d hker
  have hDW : (⨅ e ∈ D, LinearMap.ker (ρW e - LinearMap.id)) = ⊥ := by
    rw [CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel.cyclic_invariants_eq_ker ρW D d hzp]
    exact hkerW
  let K := AlgebraicClosure F
  have hDK : (⨅ e ∈ D, LinearMap.ker (extend (K := K) ρW e - LinearMap.id)) = ⊥ :=
    CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel.cyclic_invariants_eq_bot ρW D d hzp hDW
  have hinj := CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedRepresentationFaithful.faithful (K := K) ρW hWinj
  have hEK : (Nat.card E : K) ≠ 0 := by
    have : (Nat.card E : K) = algebraMap F K (Nat.card E : F) := by simp
    rw [this]
    exact (map_ne_zero _).mpr hEF
  have hrK : (r : K) ≠ 0 := by
    have : (r : K) = algebraMap F K (r : F) := by simp
    rw [this]
    exact (map_ne_zero _).mpr hrF
  exact CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeAbelianNormalizerCentralizes.centralizes
    (extend (K := K) ρW) hinj r D hDcard hDK E hDE hEK hrK

end CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension
