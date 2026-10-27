module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore)
open CFSG.EvenSmallLie (StandardSetting)

theorem apply_eq_self_of_mem_zpowers {F : Type*} [Field F] {σ τ : F ≃+* F} {y : F}
    (hy : σ y = y) (hτ : τ ∈ zpowers σ) : τ y = y := by
  have hle : zpowers σ ≤ MulAction.stabilizer (F ≃+* F) y :=
    (Subgroup.zpowers_le).mpr (by rw [MulAction.mem_stabilizer_iff]; exact hy)
  exact (MulAction.mem_stabilizer_iff.mp (hle hτ) : τ • y = y)

theorem exists_subfield_involution {K F : Type*} [Field K] [Field F] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = 2 ^ (2 * f)) :
    ∃ (ι : K →+* F) (σ : F ≃+* F), σ ≠ 1 ∧ σ * σ = 1 ∧
      ∀ x : F, σ x = x ↔ x ∈ Set.range ι := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hrK : Module.finrank (ZMod 2) K = f := by
    have h := FiniteField.pow_finrank_eq_natCard 2 K
    rw [hK] at h
    exact Nat.pow_right_injective le_rfl h
  have hrF : Module.finrank (ZMod 2) F = 2 * f := by
    have h := FiniteField.pow_finrank_eq_natCard 2 F
    rw [hF] at h
    exact Nat.pow_right_injective le_rfl h
  obtain ⟨ι₀⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := K) (L := F)
    (by rw [hrK, hrF]; exact Dvd.intro_left 2 rfl)
  set ι : K →+* F := ι₀.toRingHom with hι
  obtain ⟨φ, hφ, hord, -, -, hsub⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * f) hF
  have hσa : ∀ a, (φ ^ f) a = a ^ 2 ^ f := LinearFlag.pow_apply_of_sq hφ f
  have hσ1 : φ ^ f ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  have hσσ : φ ^ f * φ ^ f = 1 := by
    rw [← pow_add, ← two_mul, ← hord, pow_orderOf_eq_one]
  have hfixι : ∀ c : K, (φ ^ f) (ι c) = ι c := fun c => by
    have := Fintype.ofFinite K
    rw [hσa, ← map_pow]
    congr 1
    have h := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, hK] at h
  have hordσ : orderOf (φ ^ f) = 2 :=
    orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  obtain ⟨-, S, hS, hScard⟩ := hsub (zpowers (φ ^ f))
  rw [Nat.card_zpowers, hordσ, show 2 * f / 2 = f by omega] at hScard
  have hSset : (S : Set F) = Set.range ι := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨c, rfl⟩
      rw [hS]
      exact fun τ hτ => apply_eq_self_of_mem_zpowers (hfixι c) hτ
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_range_of_injective
        ι.injective, hK]
      exact (le_of_eq hScard)
    · exact Set.toFinite _
  refine ⟨ι, φ ^ f, hσ1, hσσ, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [← hSset, hS]
    exact fun τ hτ => apply_eq_self_of_mem_zpowers hx hτ
  · rintro ⟨c, rfl⟩
    exact hfixι c

end CFSG.SeitzReduction.LinearPilot
