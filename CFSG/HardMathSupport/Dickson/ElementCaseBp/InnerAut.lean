module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

private theorem conj_eq_one_iff_mem_center {K : Type*} [Group K] (k : K) :
    MulAut.conj k = 1 ↔ k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg : k * g * k⁻¹ = g := by
      have h' := congrArg (fun φ : MulAut K => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h'
      exact h'
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  · intro h
    ext y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h y, mul_inv_cancel_right]

theorem exists_centerQuotient_mulAut (K : Type*) [Group K] :
    ∃ ι : K ⧸ Subgroup.center K →* MulAut K, Function.Injective ι ∧
      ι.range = (MulAut.conj : K →* MulAut K).range ∧
      ∀ k : K, ι (k : K ⧸ Subgroup.center K) = MulAut.conj k := by
  have hker : Subgroup.center K ≤ (MulAut.conj : K →* MulAut K).ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    exact (conj_eq_one_iff_mem_center k).mpr hk
  refine ⟨QuotientGroup.lift (Subgroup.center K) MulAut.conj hker, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hx' : MulAut.conj k = 1 := hx
    exact (QuotientGroup.eq_one_iff k).mpr ((conj_eq_one_iff_mem_center k).mp hx')
  · ext φ
    simp only [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k : K ⧸ Subgroup.center K), rfl⟩
  · intro k
    rfl

theorem mul_conj_mul_inv {K : Type*} [Group K] (φ : MulAut K) (k : K) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

variable {G : Type*} [Group G] {K : Subgroup G}

theorem normalizerMonoidHom_apply_coe (n : Subgroup.normalizer (K : Set G)) (k : K) :
    ((Subgroup.normalizerMonoidHom K n k : K) : G) = (n : G) * (k : G) * (n : G)⁻¹ := by
  rfl

theorem normalizerMonoidHom_of_mem {k : G} (hk : k ∈ K) (hkN : k ∈ Subgroup.normalizer (K : Set G)) :
    Subgroup.normalizerMonoidHom K ⟨k, hkN⟩ = MulAut.conj (⟨k, hk⟩ : K) := by
  ext y
  exact normalizerMonoidHom_apply_coe ⟨k, hkN⟩ y

theorem normalizerMonoidHom_eq_one_iff (n : Subgroup.normalizer (K : Set G)) :
    Subgroup.normalizerMonoidHom K n = 1 ↔ (n : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : G)) h
    simp only [normalizerMonoidHom_apply_coe, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro h
    ext x
    rw [normalizerMonoidHom_apply_coe, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (h x.1 x.2).symm

end CFSG.HardMathSupport.Dickson.ElementCaseBp
