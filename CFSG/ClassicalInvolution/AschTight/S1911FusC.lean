module

public import CFSG.ClassicalInvolution.AschTight.S1911FusB
public import CFSG.ClassicalInvolution.AschTight.S1911FusA

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]

variable (K) in
noncomputable abbrev slProj (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) :
    ↥K →* SL(2, F) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore K))

theorem slAut_slProj (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (n : Subgroup.normalizer (K : Set G)) (k : K) :
    slAut K e n (slProj K e k) = slProj K e (normalizerConj K n k) :=
  congr_oddCoreQuotientAut_apply e n k

theorem slProj_eq_one_iff (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (k : K) :
    slProj K e k = 1 ↔ (k : G) ∈ oddCoreOf K := by
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oddCoreOf_iff]
  exact ⟨fun h => ⟨k.2, h⟩, fun ⟨_, h⟩ => h⟩

theorem slProj_surjective (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) :
    Function.Surjective (slProj K e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

variable [Finite G]

theorem exists_mem_centralizer_of_slAut_eq (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    {a : G} (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1) {b : SL(2, F)}
    (hb : slAut K e ⟨a, haN⟩ b = b) :
    ∃ c : K, (c : G) ∈ Subgroup.centralizer ({a} : Set G) ∧ slProj K e c = b := by
  obtain ⟨k, rfl⟩ := slProj_surjective e b
  rw [slAut_slProj] at hb
  have h1 : slProj K e (k⁻¹ * normalizerConj K ⟨a, haN⟩ k) = 1 := by
    rw [map_mul, map_inv, hb, inv_mul_cancel]
  rw [slProj_eq_one_iff] at h1
  have h2 : (k : G)⁻¹ * (a * k * a⁻¹) ∈ oddCoreOf K := by
    simpa [normalizerConj_apply_coe] using h1
  obtain ⟨o, ho, hko⟩ := exists_mul_mem_centralizer_of_odd (oddCoreOf_odd_natCard K) ha2
    (mem_normalizer_oddCoreOf_of_mem_normalizer haN) h2
  have hoK : o ∈ K := oddCoreOf_le_self K ho
  refine ⟨k * ⟨o, hoK⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : ((k * ⟨o, hoK⟩ : K) : G) = (k : G) * o := rfl
    rw [e1]
    calc (k : G) * o * a = a * ((k : G) * o) * a⁻¹ * a := by rw [hko]
      _ = a * ((k : G) * o) := by group
  · have ho1 : slProj K e ⟨o, hoK⟩ = 1 := (slProj_eq_one_iff e _).mpr ho
    rw [map_mul, ho1, mul_one]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
