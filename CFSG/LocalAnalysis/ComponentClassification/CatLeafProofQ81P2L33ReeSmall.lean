module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeTools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.Ree

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model

theorem WSL_mul_WSL_eq_neg_one {K : Type} [Field K] : (WSL : SL2 K) * WSL = -1 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_ne_one_ne_neg_one {K : Type} [Field K] :
    (WSL : SL2 K) ≠ 1 ∧ (WSL : SL2 K) ≠ -1 := by
  constructor <;>
  · intro h
    have h1 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [coe_WSL, Matrix.SpecialLinearGroup.coe_neg] at h1

theorem smallRee_not_isPGroup
    {m : ℕ} (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * m + 1))
    (α : MulAut ↥(ReeTag.G2.reeGamma K m)) (hα : orderOf α = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  have := finite_modGL (τ := ReeTag.G2.tag) (K := K)
  obtain ⟨x, ⟨hx, rfl⟩, -⟩ :=
    (CatalogueBSmallRee.small_Ree_automorphism_involutions_inner m hm K hK).2 α hα
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, hfus⟩ := small_Ree_prime_field_involution_fusion m K hK w₀ hw₀
  obtain ⟨ψ, hψC, -, -, -, hψ1, -, -, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure m K hK w₀ hw₀
  have hx' : orderOf (x : ModGL ReeTag.G2.tag K) = 2 := by rw [Subgroup.orderOf_coe, hx]
  obtain ⟨y, hy, hyx⟩ := hfus _ x.2 hx'
  rw [fixedPoints_conj]
  intro hP
  have hP' := isPGroup_centralizer_conj x ⟨y, hy⟩ hP
  set x' : ReeTag.G2.reeGamma K m := ⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹ with hx'
  have hx'v : (x' : ModGL ReeTag.G2.tag K) = smallReeH m K (-1) := by
    rw [hx', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hyx
  have hle : ψ.range ≤ ReeTag.G2.reeGamma K m ⊓ centralizer {(x' : ModGL ReeTag.G2.tag K)} := by
    rw [hx'v]
    rintro _ ⟨g, rfl⟩
    exact hψC g
  have h27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : Nat.card K ≠ 2 := by omega
  have h3 : Nat.card K ≠ 3 := by omega
  have hord : orderOf (⟨ψ WSL, WSL, rfl⟩ : ψ.range) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      show ψ WSL ^ 2 = 1
      rw [sq, ← map_mul, WSL_mul_WSL_eq_neg_one]
      exact (hψ1 (-1)).mpr (Or.inr rfl)
    · intro h
      rcases (hψ1 WSL).mp (congrArg Subtype.val h) with h1 | h1
      · exact WSL_ne_one_ne_neg_one.1 h1
      · exact WSL_ne_one_ne_neg_one.2 h1
  have heven : 2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    have h1 := orderOf_dvd_natCard (⟨ψ WSL, WSL, rfl⟩ : ψ.range)
    rw [hord] at h1
    rwa [Nat.card_congr e.toEquiv]
  exact not_isPGroup_centralizer x' hle e.symm
    (commutator_eq_top_of_simple
      (CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr h2) (Or.inr h3))
      (CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K h2 h3)) heven hP'

theorem smallRee_not_isPGroup_of_model
    (Y : Type) [Group Y] [Finite Y] {p f : ℕ} (hY : Blueprint.ReeTitsModel Y .twistedG2 p f)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  obtain ⟨-, -, hp, -, hiso⟩ := small_Ree_model_Schreier Y p f hY
  obtain ⟨hadm, m, hfm, K, _, _, hK, ⟨e⟩⟩ := hY
  subst hp
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso m K hfm hK ⟨e⟩
  exact not_isPGroup_of_mulEquiv E
    (smallRee_not_isPGroup (by omega) K (by rw [hK, hfm])) a ha

end CFSG.ComponentClassification.HarrisLit.L33.Ree
