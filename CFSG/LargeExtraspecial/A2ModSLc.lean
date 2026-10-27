module

public import CFSG.LargeExtraspecial.A2ModSLb
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix

variable {n : ℕ}

local notation "SL2" => SpecialLinearGroup (Fin n) (ZMod 2)

theorem exists_dotProduct_eq_one {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    ∃ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v = 1 := by
  obtain ⟨i, hi⟩ := exists_apply_eq_one_of_ne_zero hv
  exact ⟨Pi.single i 1, by rw [single_dotProduct, one_mul, hi]⟩

theorem exists_dotProduct_eq_one_two {v w : Fin n → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v = 1 ∧ ψ ⬝ᵥ w = 1 := by
  obtain ⟨ψ₁, h₁⟩ := exists_dotProduct_eq_one hv
  rcases zmodTwo_eq_zero_or_one (ψ₁ ⬝ᵥ w) with h₁w | h₁w
  · obtain ⟨ψ₂, h₂⟩ := exists_dotProduct_eq_one hw
    rcases zmodTwo_eq_zero_or_one (ψ₂ ⬝ᵥ v) with h₂v | h₂v
    · exact ⟨ψ₁ + ψ₂, by rw [add_dotProduct, h₁, h₂v, add_zero],
        by rw [add_dotProduct, h₁w, h₂, zero_add]⟩
    · exact ⟨ψ₂, h₂v, h₂⟩
  · exact ⟨ψ₁, h₁, h₁w⟩

theorem exists_dotProduct_eq_zero_eq_one {v w : Fin n → ZMod 2} (hw : w ≠ 0) (hwv : w ≠ v) :
    ∃ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v = 0 ∧ ψ ⬝ᵥ w = 1 := by
  obtain ⟨χ₁, h₁⟩ := exists_dotProduct_eq_one hw
  rcases zmodTwo_eq_zero_or_one (χ₁ ⬝ᵥ v) with h₁v | h₁v
  · exact ⟨χ₁, h₁v, h₁⟩
  have hvw : v + w ≠ 0 := fun h => hwv (by
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h
    exact h.symm)
  obtain ⟨χ₂, h₂⟩ := exists_dotProduct_eq_one hvw
  rw [dotProduct_add] at h₂
  rcases zmodTwo_eq_zero_or_one (χ₂ ⬝ᵥ v) with h₂v | h₂v
  · rw [h₂v, zero_add] at h₂
    exact ⟨χ₂, h₂v, h₂⟩
  · rw [h₂v, add_eq_left] at h₂
    exact ⟨χ₁ + χ₂, by rw [add_dotProduct, h₁v, h₂v]; rfl,
      by rw [add_dotProduct, h₁, h₂, add_zero]⟩

theorem exists_dotProduct_eq_zero_eq_one_eq_one {v w w' : Fin n → ZMod 2} (hw : w ≠ 0)
    (hwv : w ≠ v) (hw' : w' ≠ 0) (hw'v : w' ≠ v) :
    ∃ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v = 0 ∧ ψ ⬝ᵥ w = 1 ∧ ψ ⬝ᵥ w' = 1 := by
  obtain ⟨ψ₁, h₁v, h₁w⟩ := exists_dotProduct_eq_zero_eq_one hw hwv
  rcases zmodTwo_eq_zero_or_one (ψ₁ ⬝ᵥ w') with h₁w' | h₁w'
  · obtain ⟨ψ₂, h₂v, h₂w'⟩ := exists_dotProduct_eq_zero_eq_one hw' hw'v
    rcases zmodTwo_eq_zero_or_one (ψ₂ ⬝ᵥ w) with h₂w | h₂w
    · exact ⟨ψ₁ + ψ₂, by rw [add_dotProduct, h₁v, h₂v, add_zero],
        by rw [add_dotProduct, h₁w, h₂w, add_zero], by rw [add_dotProduct, h₁w', h₂w', zero_add]⟩
    · exact ⟨ψ₂, h₂v, h₂w, h₂w'⟩
  · exact ⟨ψ₁, h₁v, h₁w, h₁w'⟩

theorem sl_mulVec_injective (g : SL2) :
    Function.Injective fun x : Fin n → ZMod 2 => (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x :=
  fun x y h => by
    have := congrArg (fun z => ((g⁻¹ : SL2) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h
    simpa only [sl_inv_mulVec_mulVec] using this

theorem exists_mulVec_eq {v w : Fin n → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL2, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = w := by
  by_cases hvw : v = w
  · exact ⟨1, by rw [SpecialLinearGroup.coe_one, one_mulVec, hvw]⟩
  obtain ⟨ψ, h₁, h₂⟩ := exists_dotProduct_eq_one_two hv hw
  have h : ψ ⬝ᵥ (v + w) = 0 := by rw [dotProduct_add, h₁, h₂]; rfl
  exact ⟨tv (v + w) ψ, by rw [tv_mulVec h, h₁, one_smul, ← add_assoc, ZModModule.add_self,
    zero_add]⟩

theorem exists_contra_eq {φ ψ : Fin n → ZMod 2} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ∃ g : SL2, contra g φ = ψ := by
  by_cases hφψ : φ = ψ
  · exact ⟨1, by rw [contra_one, hφψ]⟩
  obtain ⟨x, h₁, h₂⟩ := exists_dotProduct_eq_one_two hφ hψ
  rw [dotProduct_comm] at h₁ h₂
  have h : (φ + ψ) ⬝ᵥ x = 0 := by rw [add_dotProduct, h₁, h₂]; rfl
  exact ⟨tv x (φ + ψ), by rw [contra_tv h, h₁, one_smul, sub_add_cancel_left,
    ZModModule.neg_eq_self]⟩

theorem exists_mulVec_eq_of_mulVec_eq {v w w' : Fin n → ZMod 2} (hw : w ≠ 0) (hwv : w ≠ v)
    (hw' : w' ≠ 0) (hw'v : w' ≠ v) :
    ∃ g : SL2, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v ∧
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
  by_cases hww : w = w'
  · exact ⟨1, by rw [SpecialLinearGroup.coe_one, one_mulVec],
      by rw [SpecialLinearGroup.coe_one, one_mulVec, hww]⟩
  obtain ⟨ψ, h₀, h₁, h₂⟩ := exists_dotProduct_eq_zero_eq_one_eq_one hw hwv hw' hw'v
  have h : ψ ⬝ᵥ (w + w') = 0 := by rw [dotProduct_add, h₁, h₂]; rfl
  exact ⟨tv (w + w') ψ, by rw [tv_mulVec h, h₀, zero_smul, add_zero],
    by rw [tv_mulVec h, h₁, one_smul, ← add_assoc, ZModModule.add_self, zero_add]⟩

theorem exists_contra_eq_of_contra_eq {φ ψ ψ' : Fin n → ZMod 2} (hψ : ψ ≠ 0) (hψφ : ψ ≠ φ)
    (hψ' : ψ' ≠ 0) (hψ'φ : ψ' ≠ φ) :
    ∃ g : SL2, contra g φ = φ ∧ contra g ψ = ψ' := by
  by_cases h : ψ = ψ'
  · exact ⟨1, contra_one φ, by rw [contra_one, h]⟩
  obtain ⟨x, h₀, h₁, h₂⟩ := exists_dotProduct_eq_zero_eq_one_eq_one hψ hψφ hψ' hψ'φ
  rw [dotProduct_comm] at h₀ h₁ h₂
  have hx : (ψ + ψ') ⬝ᵥ x = 0 := by rw [add_dotProduct, h₁, h₂]; rfl
  exact ⟨tv x (ψ + ψ'), by rw [contra_tv hx, h₀, zero_smul, sub_zero],
    by rw [contra_tv hx, h₁, one_smul, sub_add_cancel_left, ZModModule.neg_eq_self]⟩

theorem exists_mulVec_eq_pair {v w v' w' : Fin n → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0)
    (hwv : w ≠ v) (hv' : v' ≠ 0) (hw' : w' ≠ 0) (hwv' : w' ≠ v') :
    ∃ g : SL2, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v' ∧
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_eq hv hv'
  have h1 : (g₁ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w ≠ 0 :=
    fun h => hw ((sl_mulVec_eq_zero_iff g₁).mp h)
  have h2 : (g₁ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w ≠ v' :=
    fun h => hwv (sl_mulVec_injective g₁ (h.trans hg₁.symm))
  obtain ⟨g₂, hg₂v, hg₂w⟩ := exists_mulVec_eq_of_mulVec_eq h1 h2 hw' hwv'
  exact ⟨g₂ * g₁, by rw [sl_mulVec_mul, hg₁, hg₂v], by rw [sl_mulVec_mul, hg₂w]⟩

theorem exists_mulVec_eq_contra_eq {v φ w ψ : Fin n → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (h : φ ⬝ᵥ v = 0) (hw : w ≠ 0) (hψ : ψ ≠ 0) (h' : ψ ⬝ᵥ w = 0) :
    ∃ g : SL2, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = w ∧ contra g φ = ψ := by
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_eq hv hw
  have hφ₁ : contra g₁ φ ≠ 0 := fun h0 => hφ ((contra_eq_zero_iff g₁).mp h0)
  have hφ₁w : contra g₁ φ ⬝ᵥ w = 0 := by rw [← hg₁, contra_dotProduct_mulVec, h]
  by_cases he : contra g₁ φ = ψ
  · exact ⟨g₁, hg₁, he⟩
  obtain ⟨x, h₁, h₂⟩ := exists_dotProduct_eq_one_two hφ₁ hψ
  rw [dotProduct_comm] at h₁ h₂
  have hx : (contra g₁ φ + ψ) ⬝ᵥ x = 0 := by rw [add_dotProduct, h₁, h₂]; rfl
  refine ⟨tv x (contra g₁ φ + ψ) * g₁, ?_, ?_⟩
  · rw [sl_mulVec_mul, hg₁,
      tv_mulVec_of_dotProduct_eq_zero (by rw [add_dotProduct, hφ₁w, h', add_zero])]
  · rw [contra_mul, contra_tv hx, h₁, one_smul, sub_add_cancel_left, ZModModule.neg_eq_self]

theorem isConj_tv {v φ w ψ : Fin n → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (hw : w ≠ 0) (hψ : ψ ≠ 0) (h' : ψ ⬝ᵥ w = 0) : IsConj (tv v φ) (tv w ψ) := by
  obtain ⟨g, hgv, hgφ⟩ := exists_mulVec_eq_contra_eq hv hφ h hw hψ h'
  exact isConj_iff.mpr ⟨g, by rw [conj_tv, hgv, hgφ]⟩

theorem conjugatesOf_transvection {i j : Fin n} (hij : i ≠ j) :
    conjugatesOf (SpecialLinearGroup.transvection hij (1 : ZMod 2)) =
      transvectionSet n (ZMod 2) := by
  have hmem := transvection_mem_transvectionSet hij (one_ne_zero (α := ZMod 2))
  ext g
  constructor
  · intro hc
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    exact conj_mem_transvectionSet c hmem
  · intro hg
    obtain ⟨w, ψ, hw, hψ, h', rfl⟩ := mem_transvectionSet.mp hg
    obtain ⟨v, φ, hv, hφ, h, hvφ⟩ := mem_transvectionSet.mp hmem
    change IsConj _ _
    rw [← hvφ]
    exact isConj_tv hv hφ h hw hψ h'

theorem eq_bot_or_eq_top_of_invariant (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hW : ∀ g : SL2, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact .inl hbot
  refine .inr (eq_top_iff.mpr fun v _ => ?_)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  by_cases hv : v = 0
  · rw [hv]
    exact W.zero_mem
  obtain ⟨g, hg⟩ := exists_mulVec_eq hw0 hv
  rw [← hg]
  exact hW g w hwW

theorem eq_zero_of_equivariant (hn : 3 ≤ n) {f : (Fin n → ZMod 2) → (Fin n → ZMod 2)}
    (hf : ∀ (g : SL2) (x : Fin n → ZMod 2),
      f ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = contra g (f x))
    (x : Fin n → ZMod 2) : f x = 0 := by
  have hu : ∀ u : Fin n → ZMod 2, f x ⬝ᵥ u = 0 := by
    intro u
    obtain ⟨χ, hχ, hχx, hχu⟩ := exists_ne_zero_dotProduct_eq_zero_two hn x u
    have hfix := hf (tv u χ) x
    rw [tv_mulVec_of_dotProduct_eq_zero hχx, contra_tv hχu] at hfix
    exact (smul_eq_zero.mp (sub_eq_self.mp hfix.symm)).resolve_right hχ
  funext j
  simpa only [dotProduct_single, mul_one, Pi.zero_apply] using hu (Pi.single j 1)

theorem orderOf_tv_mul_tv {v φ w ψ : Fin n → ZMod 2} (h : φ ⬝ᵥ v = 0) (h' : ψ ⬝ᵥ w = 0)
    (hφw : φ ⬝ᵥ w = 1) (hψv : ψ ⬝ᵥ v = 1) : orderOf (tv v φ * tv w ψ) = 3 := by
  have hb : tv v φ * tv w ψ * (tv v φ)⁻¹ = tv w ψ * tv v φ * (tv w ψ)⁻¹ := by
    rw [conj_tv, conj_tv, tv_mulVec h, tv_mulVec h', contra_tv h, contra_tv h', hφw, hψv]
    simp only [one_smul, sub_eq_add_neg, ZModModule.neg_eq_self]
    rw [add_comm w v, add_comm ψ φ]
  rw [tv_inv_eq_self, tv_inv_eq_self] at hb
  refine orderOf_eq_prime ?_ ?_
  · calc (tv v φ * tv w ψ) ^ 3
        = (tv v φ * tv w ψ * tv v φ) * (tv w ψ * tv v φ * tv w ψ) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (tv w ψ * tv v φ * tv w ψ) * (tv w ψ * tv v φ * tv w ψ) := by rw [hb]
      _ = 1 := by simp only [mul_assoc, tv_mul_tv_mul_cancel, tv_mul_self]
  · intro h1
    have hyx : tv w ψ = tv v φ := by
      have := congrArg (tv v φ * ·) h1
      simp only [← mul_assoc, tv_mul_self, one_mul, mul_one] at this
      exact this
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [dotProduct_zero] at hψv
      exact zero_ne_one hψv
    have hφ0 : φ ≠ 0 := by
      rintro rfl
      rw [zero_dotProduct] at hφw
      exact zero_ne_one hφw
    obtain ⟨rfl, rfl⟩ := (tv_eq_tv_iff hv0 hφ0 h h').mp hyx.symm
    rw [h] at hφw
    exact zero_ne_one hφw

theorem exists_orderOf_eq_three (hn : 2 ≤ n) : ∃ g : SL2, orderOf g = 3 := by
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by simp [Fin.ext_iff] at h
  have h01 : (Pi.single (⟨1, by omega⟩ : Fin n) (1 : ZMod 2)) ⬝ᵥ Pi.single ⟨0, by omega⟩ 1 = 0 :=
    by rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm]
  have h10 : (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ZMod 2)) ⬝ᵥ Pi.single ⟨1, by omega⟩ 1 = 0 :=
    by rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij]
  exact ⟨_, orderOf_tv_mul_tv h01 h10 (by simp) (by simp)⟩

theorem not_isPGroup_two (hn : 2 ≤ n) : ¬ IsPGroup 2 SL2 := by
  intro h
  obtain ⟨g, hg⟩ := exists_orderOf_eq_three hn
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h g
  rw [hg] at hk
  rcases k with _ | k
  · norm_num at hk
  · rw [pow_succ] at hk
    omega

end CFSG.LargeExtraspecial.A2Mod
