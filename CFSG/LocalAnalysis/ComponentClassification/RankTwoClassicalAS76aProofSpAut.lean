module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviNoInv
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj upperUnipotentSp
  coe_upperUnipotentSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp fieldAut coe_fieldSp
  fieldAut_proj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spInner spInner_eq_conj
  spInner_mul_fieldAut_proj exceptionalAut exceptionalAut_proj exceptionalSpAut
  exceptionalSpAut_upperUnipotent displacementInLine_conj displacementInLine_upperUnipotent
  not_displacementInLine_upperUnipotent_swap transpose_single_zero_zero transpose_single_swap)
open scoped MatrixGroups

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem fieldSp_longBlock_upper (φ : K ≃+* K) (k : Fin n) (a : K) :
    fieldSp n K φ (longBlock K n k (sl2Upper a)) = longBlock K n k (sl2Upper (φ a)) := by
  apply mat_injective
  change (mat n K (longBlock K n k (sl2Upper a))).map φ = mat n K (longBlock K n k (sl2Upper (φ a)))
  rw [longBlock_sl2Upper, longBlock_sl2Upper, mat_elt_positiveLong, mat_elt_positiveLong,
    transvection, transvection]
  ext r t
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp

theorem fieldSp_longBlock_lower (φ : K ≃+* K) (k : Fin n) (a : K) :
    fieldSp n K φ (longBlock K n k (sl2Lower a)) = longBlock K n k (sl2Lower (φ a)) := by
  apply mat_injective
  change (mat n K (longBlock K n k (sl2Lower a))).map φ = mat n K (longBlock K n k (sl2Lower (φ a)))
  rw [longBlock_sl2Lower, longBlock_sl2Lower, mat_elt_negativeLong, mat_elt_negativeLong,
    transvection, transvection]
  ext r t
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp

theorem fieldAut_sp_eq_one {φ : K ≃+* K} (hφ : ∀ a, φ a = a) : fieldAut n K φ = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change fieldAut n K φ (proj n K g) = proj n K g
  rw [fieldAut_proj]
  congr 1
  apply mat_injective
  change (mat n K g).map φ = mat n K g
  ext r t
  exact hφ _

theorem sl2Upper_injective : Function.Injective (sl2Upper : K → SL(2, K)) := fun a b h => by
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  simpa [sl2Upper] using this

end Field

section Fix

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

theorem fix_spBarW (s : StatedSp (m + 1) K) (φ : K ≃+* K)
    (hW : ∀ w ∈ spBarW K m, (spInner (m + 1) K s * fieldAut (m + 1) K φ) w = w) :
    (∀ a, φ a = a) ∧ s ∈ (spL K m).range := by
  have key : ∀ X : SL(2, K), s * fieldSp (m + 1) K φ (spW K m X) * s⁻¹ = spW K m X := by
    intro X
    have h := hW _ ⟨X, rfl⟩
    simp only [MonoidHom.comp_apply] at h
    rw [spInner_mul_fieldAut_proj] at h
    exact proj_sp_injective h
  have hcomm : ∀ X : SL(2, K), fieldSp (m + 1) K φ (spW K m X) = spW K m X →
      s * spW K m X = spW K m X * s := by
    intro X hX
    have h := key X
    rw [hX] at h
    calc s * spW K m X = s * spW K m X * s⁻¹ * s := by group
      _ = spW K m X * s := by rw [h]
  have hU : fieldSp (m + 1) K φ (spW K m (sl2Upper 1)) = spW K m (sl2Upper 1) := by
    rw [spW, fieldSp_longBlock_upper, map_one]
  have hL : fieldSp (m + 1) K φ (spW K m (sl2Lower 1)) = spW K m (sl2Lower 1) := by
    rw [spW, fieldSp_longBlock_lower, map_one]
  have hs := mem_range_spL_of_commute (hcomm _ hU) (hcomm _ hL)
  refine ⟨fun a => ?_, hs⟩
  obtain ⟨t, rfl⟩ := hs
  have h := key (sl2Upper a)
  rw [spW, fieldSp_longBlock_upper, ← spW, ← spW_commute_spL, mul_inv_cancel_right] at h
  exact sl2Upper_injective (longBlock_injective _ h)

theorem eq_one_of_fix_spInner (hm : 1 ≤ m) {s : StatedSp (m + 1) K} (hs : s ∈ (spL K m).range)
    (hL : ∀ l ∈ spBarL K m, spInner (m + 1) K s l = l) : s = 1 := by
  obtain ⟨t, rfl⟩ := hs
  have ht : t ∈ center (StatedSp m K) := by
    rw [mem_center_iff]
    intro S
    have h := hL _ ⟨S, rfl⟩
    simp only [MonoidHom.comp_apply] at h
    rw [spInner_eq_conj, conj_proj_sp] at h
    have h2 := proj_sp_injective h
    rw [← map_inv, ← map_mul, ← map_mul] at h2
    have h3 := spEmbed_injective _ h2
    calc S * t = t * S * t⁻¹ * t := by rw [h3]
      _ = t * S := by group
  rw [center_statedSp_eq_bot hm, mem_bot] at ht
  rw [ht, map_one]

theorem eq_one_of_fixes_sp_of_two_le [Finite K] (hm : 2 ≤ m)
    (α : MulAut (StatedProj (StatedSp (m + 1) K)))
    (hW : ∀ w ∈ spBarW K m, α w = w) (hL : ∀ l ∈ spBarL K m, α l = l) : α = 1 := by
  obtain ⟨hE, -⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.automorphism_generation
    (K := K) (r := m + 1) (by omega)
  obtain ⟨s, φ, rfl⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exists_eq_spInner_mul_fieldAut
      (hE ▸ Subgroup.mem_top α)
  obtain ⟨hφ, hs⟩ := fix_spBarW s φ hW
  rw [fieldAut_sp_eq_one hφ, mul_one] at hL ⊢
  rw [eq_one_of_fix_spInner (by omega) hs hL, map_one]

omit [CharP K 2] in
theorem longBlock_zero_upper_eq :
    longBlock K (1 + 1) 0 (sl2Upper 1) =
      upperUnipotentSp 2 K (transpose_single_zero_zero (K := K)) := by
  apply mat_injective
  have h := coe_upperUnipotentSp (r := 2) (K := K) (transpose_single_zero_zero (K := K))
  change _ = (upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))).val.val
  rw [h, longBlock_sl2Upper, mat_elt_positiveLong]
  ext r t
  rcases r with r | r <;> rcases t with t | t <;> fin_cases r <;> fin_cases t <;>
    simp [transvection]

theorem eq_one_of_fixes_sp_one [Finite K] (α : MulAut (StatedProj (StatedSp (1 + 1) K)))
    (h2 : α * α = 1) (hW : ∀ w ∈ spBarW K 1, α w = w) (hL : ∀ l ∈ spBarL K 1, α l = l) :
    α = 1 := by
  classical
  by_contra hne
  have hord : orderOf α = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact h2) hne
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hKf' : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  obtain ⟨Fr, hFr, hFrord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two f.pos hKf'
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure f.pos hFr
      hFrord hzp
  obtain ⟨g, j, hj, hαeq⟩ := hinv α hord
  have hγ2 := CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_sq
    (K := K) hFr
  have hE : ∀ φ : K ≃+* K, α = spInner 2 K g * fieldAut 2 K φ → False := by
    intro φ hαφ
    obtain ⟨hφ, hs⟩ := fix_spBarW (m := 1) g φ (fun w hw => by rw [← hαφ]; exact hW w hw)
    apply hne
    rw [hαφ, fieldAut_sp_eq_one hφ, mul_one]
    rw [hαφ, fieldAut_sp_eq_one hφ, mul_one] at hL
    rw [eq_one_of_fix_spInner le_rfl hs hL, map_one]
  rcases hj with rfl | rfl
  · exact hE 1 (by rw [hαeq, pow_zero, mul_one, map_one, mul_one])
  · rcases Nat.even_or_odd (f : ℕ) with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine hE (Fr ^ k) ?_
      rw [hαeq, show (f : ℕ) = 2 * k by omega, pow_mul, hγ2, ← map_pow]
    ·
      set t₀ : StatedSp (1 + 1) K := longBlock K (1 + 1) 0 (sl2Upper 1) with ht₀
      have hfix : α (proj (1 + 1) K t₀) = proj (1 + 1) K t₀ :=
        hL _ ((longBlock_zero_mem_range_spL le_rfl (sl2Upper 1)).elim fun S hS =>
          ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]; rfl⟩)
      have hpow : exceptionalAut K ^ (f : ℕ) = exceptionalAut K * fieldAut 2 K (Fr ^ k) := by
        rw [show (f : ℕ) = 1 + 2 * k by omega, pow_add, pow_one, pow_mul, hγ2, ← map_pow]
      rw [hαeq, hpow, ← mul_assoc, MulAut.mul_apply, MulAut.mul_apply] at hfix
      have h1 : fieldAut 2 K (Fr ^ k) (proj (1 + 1) K t₀) = proj (1 + 1) K t₀ := by
        change fieldAut 2 K (Fr ^ k) (proj 2 K t₀) = proj 2 K t₀
        rw [fieldAut_proj, ht₀, fieldSp_longBlock_upper, map_one]
      rw [h1, ht₀, longBlock_zero_upper_eq] at hfix
      change spInner 2 K g (exceptionalAut K (proj 2 K _)) = proj 2 K _ at hfix
      rw [exceptionalAut_proj, exceptionalSpAut_upperUnipotent, spInner_eq_conj,
        conj_proj_sp (m := 1)] at hfix
      have h2 := proj_sp_injective (m := 1) hfix
      have h3 := displacementInLine_conj g⁻¹ (upperUnipotentSp 2 K
        (transpose_single_zero_zero (K := K))) (RingEquiv.refl K)
        displacementInLine_upperUnipotent
      have h4 : fieldSp 2 K (RingEquiv.refl K)
          (upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))) =
          upperUnipotentSp 2 K (transpose_single_zero_zero (K := K)) := by
        rw [← longBlock_zero_upper_eq]
        exact (fieldSp_longBlock_upper _ _ _).trans (by rfl)
      rw [h4, ← h2] at h3
      have h5 : g⁻¹ * (g * upperUnipotentSp 2 K (transpose_single_swap (K := K)) * g⁻¹) * g⁻¹⁻¹ =
          upperUnipotentSp 2 K (transpose_single_swap (K := K)) := by group
      rw [h5] at h3
      exact not_displacementInLine_upperUnipotent_swap h3

end Fix

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {A : Subgroup G}

theorem noInv_sp {m : ℕ} {θ : ↥A →* StatedProj (StatedSp (m + 1) K)} (hA : commutator ↥A = ⊤)
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4)
    (hm : 1 ≤ m) : NoInvolutoryCentralizing A (spLeviW θ ⊔ spLeviL θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hW := inducedAut_fix_of_levLift hθ (commutator_spBarW h4) le_sup_left hfix hα
  have hL := inducedAut_fix_of_levLift hθ (commutator_spBarL h4) le_sup_right hfix hα
  have h1 : α = 1 := by
    rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact eq_one_of_fixes_sp_one α (inducedAut_sq hθ hσ hα) hW hL
    · exact eq_one_of_fixes_sp_of_two_le hm2 α hW hL
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end Lift

end CFSG.ComponentClassification.RankTwoClassical
