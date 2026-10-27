module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LieType.BorelExponent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem hasBorelExponent_graphFixedRootGroup {t : TwistTag} {K : Type} [Field K] [Finite K]
    [CharP K 2] {σ : K →+* K} (hσ : Function.Surjective σ) :
    HasBorelExponent ↥(graphFixedRootGroup t K σ) (Nat.card K - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := t.tag) (K := K)
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf
      ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)) ⊤ := by
    refine ⟨le_top, isPGroup_graphFixedPosUnipotent_subgroupOf 2, ?_⟩
    rw [show (((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)).subgroupOf
        ⊤).index = ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)).index
      from Subgroup.relIndex_top_right _]
    exact not_dvd_index_graphFixedPosUnipotent 2 hσ
  refine hasBorelExponent_of_isSylowTwoOf hU fun x hx => ?_
  rw [Subgroup.mem_subgroupOf]
  have hxB : (x : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨x.2, mem_normalizer_of_mem_normalizer_subgroupOf hUC hx⟩
  rw [Subgroup.coe_pow]
  exact pow_card_sub_one_mem_graphFixedPosUnipotent hσ hxB

theorem borelExponentAt_twistedE6 : BorelExponentAt .twistedE6 := by
  intro X _ _ m f _ hLie
  obtain ⟨-, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .twistedE6) (by decide)).1 hLie
  obtain ⟨K, hK, hfin, σ, hcard, -, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have hcard' : Nat.card K = 2 ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard'])
  have := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  have h := hasBorelExponent_graphFixedRootGroup (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom) σ.surjective
  rw [hcard'] at h
  exact h.of_mulEquiv e.symm

end CFSG.LieType.BorelExponent

end
