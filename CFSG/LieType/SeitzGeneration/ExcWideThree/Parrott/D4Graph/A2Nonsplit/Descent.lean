module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Twist

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K]

theorem mem_adjointGroup_of_rootDiagUnit_mul {b : Fin Tag.D4.rank → Kˣ} {j : ModGL Tag.D4 K}
    (hj : j ∈ adjointGroup Tag.D4 K) {k : ℕ} (h3 : (rootDiagUnit Tag.D4 b * j) ^ 3 ^ k = 1) :
    rootDiagUnit Tag.D4 b * j ∈ adjointGroup Tag.D4 K := by
  have hsq : rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K := by
    rw [← rootDiagUnit_mul]
    convert rootDiagUnit_sq_mem_adjointGroup_D4 (K := K) b using 2
    congr 1
    funext j
    rw [Pi.mul_apply, pow_two]
  have hconj : (rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K := by
    have h := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) b⁻¹ hj
    rwa [← rootDiagUnit_inv, inv_inv] at h
  have h2 : (rootDiagUnit Tag.D4 b * j) ^ 2 ∈ adjointGroup Tag.D4 K := by
    have e : (rootDiagUnit Tag.D4 b * j) ^ 2 = (rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b) *
        ((rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b) * j := by
      rw [pow_two]
      group
    rw [e]
    exact mul_mem (mul_mem hsq hconj) hj
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have e : rootDiagUnit Tag.D4 b * j = ((rootDiagUnit Tag.D4 b * j) ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, h3, one_mul]
  rw [e]
  exact pow_mem h2 _

theorem units_map_entrywiseHom_eq_baseChangeGL (σ : K →+* K) (g : ModGL Tag.D4 K) :
    Units.map (entrywiseHom σ) g = baseChangeGL σ g :=
  Units.ext rfl

theorem mem_range_ιTw_of_fixed [Finite K] {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K K₂]
    (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K) {Q : SL2 K₂} {c : K₂ˣ}
    (hQc : Matrix.SpecialLinearGroup.map σ Q = Q * nSL c) {h : ↥(adjointGroup Tag.D4 K₂)}
    (hfix : gTw (nSL c) * bcAd σ h * (gTw (nSL c))⁻¹ = h) {k : ℕ} (hk : h ^ 3 ^ k = 1) :
    h ∈ (ιTw K Q).range := by
  have hσg : bcAd σ (gTw Q) = gTw Q * gTw (nSL c) := by rw [bcAd_gTw, hQc, gTw_mul]
  have hrF : bcAd σ (gTw Q * h * (gTw Q)⁻¹) = gTw Q * h * (gTw Q)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hσg, mul_inv_rev]
    conv_rhs => rw [← hfix]
    group
  have hrF' : Units.map (entrywiseHom σ) ((gTw Q * h * (gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = ((gTw Q * h * (gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) :
        ModGL Tag.D4 K₂) := by
    have e := congrArg Subtype.val hrF
    rw [coe_bcAd] at e
    exact (units_map_entrywiseHom_eq_baseChangeGL σ _).trans e
  obtain ⟨a, u, ⟨u₀, hu₀, rfl⟩, hru⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.D4 σ hσ
    (gTw Q * h * (gTw Q)⁻¹).2 hrF'
  have hbw : baseChangeGL (algebraMap K K₂) (rootDiagUnit Tag.D4 a * u₀) =
      ((gTw Q * h * (gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) := by
    rw [map_mul, hru]
  have hw3 : (rootDiagUnit Tag.D4 a * u₀) ^ 3 ^ k = 1 := by
    apply baseChangeGL_injective (algebraMap K K₂)
    rw [map_pow, hbw, map_one, ← Subgroup.coe_pow, conj_pow, hk, mul_one, mul_inv_cancel,
      Subgroup.coe_one]
  have hwG := mem_adjointGroup_of_rootDiagUnit_mul hu₀ hw3
  refine ⟨⟨_, hwG⟩, ?_⟩
  rw [ιTw_apply, show bcAd (algebraMap K K₂) ⟨_, hwG⟩ = gTw Q * h * (gTw Q)⁻¹ from
    Subtype.ext hbw]
  group

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
