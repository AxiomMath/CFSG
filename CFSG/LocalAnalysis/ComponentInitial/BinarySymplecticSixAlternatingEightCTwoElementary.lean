module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightKSubgroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

theorem orderSeven_orbit : ∀ v : Fin 3 → ZMod 2, v ≠ 0 → ∃ k : Fin 7,
    orderSeven ^ (k : ℕ) * altMat (Pi.single 2 1) * (orderSeven ^ (k : ℕ))ᵀ = altMat v := by
  decide +kernel

theorem jMat_eq_altMat : jMat 0 1 0 = altMat (Pi.single 2 1) := by
  decide

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf

include hzC hsup hinf hz hb hnd hV he halt in
theorem isElementaryAbelian_C₂ {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟)
    (hC₂ab : ∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜)
    {k : G} (hk : k ∈ C₂)
    (hkc : z⁻¹ * k⁻¹ * z * k = tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0)))
    (hk2 : k * k = 1) : IsElementaryAbelian 2 C₂ := by
  have hAe := (pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf).1
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hker : ∀ c ∈ C₂, z⁻¹ * c⁻¹ * z * c = 1 → c ∈ 𝒜 := by
    intro c hc h
    rw [← hC₂z c hc]
    have h1 : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = z * (z⁻¹ * c⁻¹ * z * c) := by group
        _ = z := by rw [h, mul_one]
    calc c * z = c * (c⁻¹ * z * c) := by rw [h1]
      _ = z * c := by group
  obtain ⟨σ, hσs, -, -, hσ⟩ := exists_sigma hzC hsup hinf hb hnd hV φ he
  have hconj : ∀ (n : 𝒮) (B : binarySymMatrices 3),
      (n : G) * tauHom φ he (Multiplicative.ofAdd B) * (n : G)⁻¹ =
        tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ n) B)) := by
    intro n B
    have h := RadicalLabels.conj_radHom_of_sigma φ he hzC hz (fun _ hx => (mem_inf.1 hx).2) σ hσ
      n B 0
    rwa [RadicalLabels.radHom_apply, RadicalLabels.radHom_apply, RadicalLabels.zPow_zero, mul_one,
      mul_one] at h
  set T : Set (binarySymMatrices 3) :=
    {B | ∀ c ∈ C₂, z⁻¹ * c⁻¹ * z * c = tauHom φ he (Multiplicative.ofAdd B) → c * c = 1} with hT
  have hT0 : (0 : binarySymMatrices 3) ∈ T := by
    intro c hc h
    rw [ofAdd_zero, map_one] at h
    exact mul_self_of_isElementaryAbelian hAe (hker c hc h)
  have hcomm_mul : ∀ {c c' : G}, c ∈ C₂ → c' ∈ C₂ →
      z⁻¹ * (c * c')⁻¹ * z * (c * c') = (z⁻¹ * c⁻¹ * z * c) * (z⁻¹ * c'⁻¹ * z * c') :=
    fun hc hc' => comm_mul_of_mem_D₂ hzC hsup hinf hz hb hnd hV φ he halt (hC₂D hc) (hC₂D hc')
  have hT1 : jSym 0 1 0 ∈ T := by
    intro c hc h
    have hkinv : k⁻¹ ∈ C₂ := inv_mem hk
    have h2 := hcomm_mul hk hkinv
    simp only [mul_inv_cancel, inv_one, mul_one, inv_mul_cancel] at h2
    have h1 : z⁻¹ * (c * k⁻¹)⁻¹ * z * (c * k⁻¹) = 1 := by
      rw [hcomm_mul hc hkinv, h, ← hkc]
      exact h2.symm
    have ha := hker _ (mul_mem hc hkinv) h1
    have hc' : c = (c * k⁻¹) * k := by group
    rw [hc', show c * k⁻¹ * k * (c * k⁻¹ * k) = (c * k⁻¹) * (c * k⁻¹) * (k * k) by
      rw [show c * k⁻¹ * k * (c * k⁻¹ * k) = c * k⁻¹ * (k * (c * k⁻¹)) * k by group,
        hC₂ab k hk _ (mul_mem hc hkinv)]
      group, mul_self_of_isElementaryAbelian hAe ha, hk2, mul_one]
  have hTinv : ∀ (n : 𝒮) (B : binarySymMatrices 3), B ∈ T → symThreeCongr (σ n) B ∈ T := by
    intro n B hB c hc h
    have hn : (n : G)⁻¹ ∈ 𝒩 := inv_mem (mem_inf.1 n.2).1
    have hc' : (n : G)⁻¹ * c * (n : G)⁻¹⁻¹ ∈ C₂ := hC₂N _ hn c hc
    rw [inv_inv] at hc'
    have hnz : (n : G) * z = z * n := mem_centralizer_singleton_iff.1 (mem_inf.1 n.2).2
    have h1 : z⁻¹ * ((n : G)⁻¹ * c * n)⁻¹ * z * ((n : G)⁻¹ * c * n) =
        tauHom φ he (Multiplicative.ofAdd B) := by
      have h2 : z⁻¹ * ((n : G)⁻¹ * c * n)⁻¹ * z * ((n : G)⁻¹ * c * n) =
          (n : G)⁻¹ * (z⁻¹ * c⁻¹ * z * c) * n := by
        have hzi : z⁻¹ * (n : G)⁻¹ = (n : G)⁻¹ * z⁻¹ := by
          have h3 := congrArg Inv.inv hnz
          simpa only [_root_.mul_inv_rev] using h3
        calc z⁻¹ * ((n : G)⁻¹ * c * n)⁻¹ * z * ((n : G)⁻¹ * c * n) =
            z⁻¹ * (n : G)⁻¹ * c⁻¹ * (n * z * (n : G)⁻¹) * c * n := by group
          _ = z⁻¹ * (n : G)⁻¹ * c⁻¹ * z * c * n := by rw [hnz, mul_inv_cancel_right]
          _ = (n : G)⁻¹ * z⁻¹ * c⁻¹ * z * c * n := by rw [hzi]
          _ = (n : G)⁻¹ * (z⁻¹ * c⁻¹ * z * c) * n := by group
      rw [h2, h, ← hconj n B]
      group
    have h3 := hB _ hc' h1
    calc c * c = (n : G) * (((n : G)⁻¹ * c * n) * ((n : G)⁻¹ * c * n)) * (n : G)⁻¹ := by group
      _ = 1 := by rw [h3, mul_one, mul_inv_cancel]
  obtain ⟨n₇, hn₇⟩ := hσs (glOfDet orderSeven orderSeven_det)
  have hTall : ∀ c ∈ C₂, c * c = 1 := by
    intro c hc
    obtain ⟨B, hB, hBc⟩ := (BinarySymThreeOrbit.mem_layerSub θ₂).1
      (comm_mem_radI hzC hsup hinf hz hb hnd hV φ he halt (hC₂D hc))
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one] at hBc
    by_cases hB0 : B = 0
    · subst hB0
      exact hT0 c hc hBc
    · have hBa := eq_altLabel_of_diag_eq_zero (BinarySymThreeOrbit.mem_altSym_iff.1 hB)
      have hv : symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0 := by
        intro h
        rw [h, DegreeEight.altLabel_zero] at hBa
        exact hB0 hBa
      obtain ⟨j, hj⟩ := orderSeven_orbit _ hv
      have hBj : B = symThreeCongr (σ (n₇ ^ (j : ℕ))) (jSym 0 1 0) := by
        apply Subtype.ext
        rw [coe_symThreeCongr, map_pow, hn₇, Units.val_pow_eq_pow_val, coe_glOfDet]
        change (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _ * jMat 0 1 0 * _
        rw [jMat_eq_altMat, hj]
        conv_lhs => rw [hBa]
        rfl
      rw [hBj] at hBc
      exact hTinv _ _ hT1 c hc hBc
  exact isElementaryAbelian_of_forall hC₂ab hTall

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
