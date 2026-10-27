module

public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
import all CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeWard

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GroupTheory CFSG.RankThree

section


theorem small_Ree_odd_prime_field_descent (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut (ReeTag.G2.reeGamma K a)) (hα : α ^ p = 1)
    (hαout : α ∉ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) :
    p ∣ 2 * a + 1 ∧
    ∃ (δ : MulAut (ReeTag.G2.reeGamma K a)) (σ : K ≃+* K), orderOf σ = p ∧
      δ * α * δ⁻¹ = ReeTag.G2.reeGammaFieldAut K a σ ∧
      Nat.card (fixSubfield σ) = 3 ^ ((2 * a + 1) / p) ∧
      ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma K a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) (((2 * a + 1) / p - 1) / 2)).map
          (baseChangeGL (fixSubfield σ).subtype) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨σ₁, hσ₁, hσ₁ord, hσ₁top, hcardAut, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_three (by omega) hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₁, hσ₁top⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨-, -, -, ⟨R, χ, hker, hsec, -, hR3, -⟩, -, -⟩ :=
    small_Ree_outer_three_kernel_field_complement a ha K hK
  obtain ⟨x, σ, hβ₁⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.smallReeOuterIsField a ha K hK α
  set σh := ReeTag.G2.reeGammaFieldAut K a σ with hσh
  have hα1 : α ≠ 1 := fun h1 => hαout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hαp : orderOf α = p := orderOf_eq_prime hα hα1
  have hχα : χ (QuotientGroup.mk (s := OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) α) =
      σ := by
    have hmk : (QuotientGroup.mk (s := OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a)) α) =
        QuotientGroup.mk σh := by
      rw [hβ₁, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (N := OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a))
          (MulAut.conj x)).2 ⟨x, rfl⟩, one_mul]
    rw [hmk]
    exact hsec σ
  have hσp : orderOf σ = p := by
    have hσpow : σ ^ p = 1 := by
      rw [← hχα, ← map_pow, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one, map_one]
    refine orderOf_eq_prime hσpow fun h1 => hαout ⟨x, ?_⟩
    have : σh = 1 := by
      rw [hσh, h1, ← ReeTag.reeGammaFieldAutHom_apply, map_one]
    rw [hβ₁, this, mul_one]
  have hpf : p ∣ 2 * a + 1 := by
    rw [← hσp, ← hcardAut]
    exact orderOf_dvd_natCard σ
  refine ⟨hpf, ?_⟩
  have hβ₁p : (MulAut.conj x * σh) ^ p = 1 := by
    rw [← hβ₁]
    exact hα
  obtain ⟨δ₂, hfin, hk, hfixed⟩ :=
    CFSG.RankThree.small_Ree_coset_descent_data ha hK hp hp2 σ hσp x hβ₁p
  refine ⟨δ₂, σ, hσp, ?_, hk, hfixed⟩
  rw [hβ₁]
  exact hfin

end

end CFSG.HardMathSupport.Lang.Coordinator
