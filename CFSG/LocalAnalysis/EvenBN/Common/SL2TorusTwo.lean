module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix Subgroup CFSG.SL2MinimalFaithful
open scoped MatrixGroups

variable {k : Type*} [Field k]

theorem transvection_eq_unipotent_or_lowerUnipotent {i j : Fin 2} (h : i ≠ j) (c : k) :
    SpecialLinearGroup.transvection h c = unipotent c ∨
      SpecialLinearGroup.transvection h c = lowerUnipotent c := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · left
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [SpecialLinearGroup.transvection_coe, coe_unipotent]
  · right
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [SpecialLinearGroup.transvection_coe, coe_lowerUnipotent]
  · exact absurd rfl h

theorem hom_ext_upperSL_lowerSL {G : Type*} [Group G] {f g : SL(2, k) →* G}
    (hu : ∀ c, f (unipotent c) = g (unipotent c))
    (hl : ∀ c, f (lowerUnipotent c) = g (lowerUnipotent c)) : f = g := by
  ext A
  induction A using Matrix.SL2.transvection_induction with
  | htransvec i j h c =>
    rcases transvection_eq_unipotent_or_lowerUnipotent h c with e | e <;> rw [e]
    exacts [hu c, hl c]
  | hmul A B hA hB => rw [map_mul, map_mul, hA, hB]

theorem map_mem_normalizer_map {G : Type*} [Group G] (σ : G ≃* G) {H : Subgroup G} {y : G}
    (hy : y ∈ normalizer (H : Set G)) :
    σ y ∈ normalizer ((H.map σ.toMonoidHom : Subgroup G) : Set G) := by
  rw [← map_equiv_normalizer_eq]
  exact ⟨y, hy, rfl⟩

section CharTwo

variable [CharP k 2]

theorem exists_units_sq_eq [Finite k] (ν : kˣ) : ∃ ρ : kˣ, ρ ^ 2 = ν := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (R := k) 2) (ν : k)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [sq, hr])⟩

theorem map_upperSL_ne_lowerSL [Finite k] (hk : 8 ≤ Nat.card k) (σ : SL(2, k) ≃* SL(2, k))
    (hσ : ∀ ρ : kˣ, σ (diagSL ρ) = diagSL ρ) : (upperSL k).map σ.toMonoidHom ≠ lowerSL k := by
  intro hswap
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hmem : ∀ c : k, ∃ c' : k, lowerUnipotent c' = σ (unipotent c) := by
    intro c
    have : σ (unipotent c) ∈ (upperSL k).map σ.toMonoidHom :=
      ⟨unipotent c, unipotent_mem_upperSL c, rfl⟩
    rw [hswap] at this
    exact mem_lowerSL_iff.1 this
  choose φ hφ using hmem
  have hadd : ∀ c c', φ (c + c') = φ c + φ c' := by
    intro c c'
    apply lowerUnipotent_injective
    rw [hφ, unipotent_add, map_mul, ← hφ, ← hφ, lowerUnipotent_add]
  have hequi : ∀ (ρ : kˣ) (c : k), φ ((ρ : k) ^ 2 * c) = (ρ : k)⁻¹ ^ 2 * φ c := by
    intro ρ c
    apply lowerUnipotent_injective
    rw [hφ, ← diagSL_conj_unipotent, map_mul, map_mul, map_inv, hσ, ← hφ,
      diagSL_conj_lowerUnipotent]
  have h1 : φ 1 ≠ 0 := by
    intro h
    have e : σ (unipotent 1) = σ (unipotent 0) := by
      rw [← hφ, h, lowerUnipotent_zero, unipotent_zero, map_one]
    exact one_ne_zero (unipotent_injective (σ.injective e))
  have hinv : ∀ s : k, s ≠ 0 → φ s = s⁻¹ * φ 1 := by
    intro s hs
    obtain ⟨ρ, hρ⟩ := exists_units_sq_eq (Units.mk0 s hs)
    have hρs : (ρ : k) ^ 2 = s := by rw [← Units.val_pow_eq_pow_val, hρ, Units.val_mk0]
    have := hequi ρ 1
    rwa [mul_one, inv_pow, hρs] at this
  have hroot : ∀ s : k, s ≠ 0 → s ≠ 1 → s ^ 2 + s + 1 = 0 := by
    intro s hs0 hs1
    have hs1' : s + 1 ≠ 0 := fun h => hs1 (by linear_combination h - h2)
    have e := hadd s 1
    rw [hinv s hs0, hinv (s + 1) hs1'] at e
    have hu : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    have hv : (s + 1) * (s + 1)⁻¹ = 1 := mul_inv_cancel₀ hs1'
    have : φ 1 * (s ^ 2 + s + 1) = 0 := by
      linear_combination (-(s * (s + 1))) * e - ((s + 1) * φ 1) * hu + (s * φ 1) * hv
    exact (mul_eq_zero.1 this).resolve_left h1
  classical
  have : Fintype k := Fintype.ofFinite k
  have hcard : 2 < ((Finset.univ.erase (0 : k)).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨one_ne_zero, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha hb hc
  have hsum : ∀ x y : k, x ≠ y → x ^ 2 + x + 1 = 0 → y ^ 2 + y + 1 = 0 → x + y + 1 = 0 := by
    intro x y hxy hx hy
    have : (x - y) * (x + y + 1) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hxy)
  have e1 := hsum a b hab (hroot a ha.2 ha.1) (hroot b hb.2 hb.1)
  have e2 := hsum a c hac (hroot a ha.2 ha.1) (hroot c hc.2 hc.1)
  exact hbc (by linear_combination e1 - e2)

theorem exists_eq_conj_of_forall_torusSL [Finite k] (hk : 8 ≤ Nat.card k)
    (σ : SL(2, k) ≃* SL(2, k)) (hσ : ∀ x ∈ torusSL k, σ x = x) :
    ∃ τ ∈ torusSL k, ∀ x, σ x = τ * x * τ⁻¹ := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hσd : ∀ ρ : kˣ, σ (diagSL ρ) = diagSL ρ := fun ρ => hσ _ (diagSL_mem_torusSL ρ)
  have : Nontrivial kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
    omega
  obtain ⟨μ₀, hμ₀⟩ := exists_ne (1 : kˣ)
  have himage : ∀ H : Subgroup SL(2, k), Nat.card H = Nat.card k →
      torusSL k ≤ normalizer (H : Set SL(2, k)) →
      H.map σ.toMonoidHom = upperSL k ∨ H.map σ.toMonoidHom = lowerSL k := by
    intro H hH hT
    refine eq_upperSL_or_eq_lowerSL ?_ hμ₀ ?_
    · rw [Subgroup.card_map_of_injective σ.injective, hH]
    · rw [← hσd μ₀]
      exact map_mem_normalizer_map σ (hT (diagSL_mem_torusSL μ₀))
  have hUU : (upperSL k).map σ.toMonoidHom = upperSL k :=
    (himage _ card_upperSL torusSL_le_normalizer_upperSL).resolve_right
      (map_upperSL_ne_lowerSL hk σ hσd)
  have hLL : (lowerSL k).map σ.toMonoidHom = lowerSL k :=
    (himage _ card_lowerSL torusSL_le_normalizer_lowerSL).resolve_left fun h =>
      upperSL_ne_lowerSL (Subgroup.map_injective σ.injective (hUU.trans h.symm))
  obtain ⟨α, hα⟩ : ∃ α : kˣ, ∀ c, σ (unipotent c) = unipotent (α * c) := by
    have hmem : ∀ c : k, ∃ c' : k, unipotent c' = σ (unipotent c) := by
      intro c
      have : σ (unipotent c) ∈ (upperSL k).map σ.toMonoidHom :=
        ⟨unipotent c, unipotent_mem_upperSL c, rfl⟩
      rw [hUU] at this
      exact mem_upperSL_iff.1 this
    choose φ hφ using hmem
    have hequi : ∀ (ρ : kˣ) (c : k), φ ((ρ : k) ^ 2 * c) = (ρ : k) ^ 2 * φ c := by
      intro ρ c
      apply unipotent_injective
      rw [hφ, ← diagSL_conj_unipotent, map_mul, map_mul, map_inv, hσd, ← hφ,
        diagSL_conj_unipotent]
    have h0 : φ 0 = 0 := unipotent_injective (by rw [hφ, unipotent_zero, map_one])
    have h1 : φ 1 ≠ 0 := by
      intro h
      have e : σ (unipotent 1) = σ (unipotent 0) := by rw [← hφ, h, ← hφ, h0]
      exact one_ne_zero (unipotent_injective (σ.injective e))
    refine ⟨Units.mk0 (φ 1) h1, fun c => ?_⟩
    rw [← hφ, Units.val_mk0]
    congr 1
    by_cases hc : c = 0
    · rw [hc, h0, mul_zero]
    · obtain ⟨ρ, hρ⟩ := exists_units_sq_eq (Units.mk0 c hc)
      have hρc : (ρ : k) ^ 2 = c := by rw [← Units.val_pow_eq_pow_val, hρ, Units.val_mk0]
      have := hequi ρ 1
      rw [mul_one, hρc] at this
      rw [this, mul_comm]
  obtain ⟨β, hβ⟩ : ∃ β : kˣ, ∀ c, σ (lowerUnipotent c) = lowerUnipotent (β * c) := by
    have hmem : ∀ c : k, ∃ c' : k, lowerUnipotent c' = σ (lowerUnipotent c) := by
      intro c
      have : σ (lowerUnipotent c) ∈ (lowerSL k).map σ.toMonoidHom :=
        ⟨lowerUnipotent c, lowerUnipotent_mem_lowerSL c, rfl⟩
      rw [hLL] at this
      exact mem_lowerSL_iff.1 this
    choose φ hφ using hmem
    have hequi : ∀ (ρ : kˣ) (c : k), φ ((ρ : k)⁻¹ ^ 2 * c) = (ρ : k)⁻¹ ^ 2 * φ c := by
      intro ρ c
      apply lowerUnipotent_injective
      rw [hφ, ← diagSL_conj_lowerUnipotent, map_mul, map_mul, map_inv, hσd, ← hφ,
        diagSL_conj_lowerUnipotent]
    have h0 : φ 0 = 0 := lowerUnipotent_injective (by rw [hφ, lowerUnipotent_zero, map_one])
    have h1 : φ 1 ≠ 0 := by
      intro h
      have e : σ (lowerUnipotent 1) = σ (lowerUnipotent 0) := by rw [← hφ, h, ← hφ, h0]
      exact one_ne_zero (lowerUnipotent_injective (σ.injective e))
    refine ⟨Units.mk0 (φ 1) h1, fun c => ?_⟩
    rw [← hφ, Units.val_mk0]
    congr 1
    by_cases hc : c = 0
    · rw [hc, h0, mul_zero]
    · obtain ⟨ρ, hρ⟩ := exists_units_sq_eq (Units.mk0 c hc)⁻¹
      have hρc : (ρ : k)⁻¹ ^ 2 = c := by
        rw [inv_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_inv_eq_inv_val, Units.val_mk0,
          inv_inv]
      have := hequi ρ 1
      rw [mul_one, hρc] at this
      rw [this, mul_comm]
  have hαβ : (α : k) * β = 1 := by
    have hw : σ (weylSL k) * diagSL μ₀ * (σ (weylSL k))⁻¹ = diagSL μ₀⁻¹ := by
      rw [← hσd μ₀, ← map_inv, ← map_mul, ← map_mul, weylSL_conj_diagSL, hσd]
    rw [weylSL_eq, map_mul, map_mul, hα, hβ] at hw
    have hw' := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0)
      (mul_inv_eq_iff_eq_mul.1 hw)
    simp [coe_unipotent, coe_lowerUnipotent, coe_diagSL, Matrix.mul_apply,
      Fin.sum_univ_two] at hw'
    have hne : (μ₀ : k) - (μ₀ : k)⁻¹ ≠ 0 := sub_ne_zero.2 (units_inv_ne_self hμ₀).symm
    have : (1 + (α : k) * β) * ((μ₀ : k) - (μ₀ : k)⁻¹) = 0 := by linear_combination hw'
    have := (mul_eq_zero.1 this).resolve_right hne
    linear_combination this - h2
  obtain ⟨ρ, hρ⟩ := exists_units_sq_eq α
  have hρα : (ρ : k) ^ 2 = α := by rw [← Units.val_pow_eq_pow_val, hρ]
  refine ⟨diagSL ρ, diagSL_mem_torusSL ρ, fun x => ?_⟩
  have hext : σ.toMonoidHom = (MulAut.conj (diagSL ρ)).toMonoidHom := by
    refine hom_ext_upperSL_lowerSL (fun c => ?_) (fun c => ?_)
    · show σ (unipotent c) = diagSL ρ * unipotent c * (diagSL ρ)⁻¹
      rw [hα, diagSL_conj_unipotent, hρα]
    · show σ (lowerUnipotent c) = diagSL ρ * lowerUnipotent c * (diagSL ρ)⁻¹
      rw [hβ, diagSL_conj_lowerUnipotent, inv_pow, hρα, ← eq_inv_of_mul_eq_one_right hαβ]
  exact DFunLike.congr_fun hext x

end CharTwo

end CFSG.LocalAnalysis.EvenBN.Common
