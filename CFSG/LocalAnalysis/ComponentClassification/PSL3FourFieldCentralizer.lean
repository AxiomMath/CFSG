module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUType
public import TauCeti.Algebra.Group.Conj

public section

namespace CFSG.ComponentClassification.PSL3Four

open Subgroup CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.TBLit

theorem card_centralizer_r₂_inf_R :
    Nat.card ↥(centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 672 := by
  have h1 := ConjClasses.card_carrier_mk r₂R
  rw [conjClass₂.2] at h1
  have h2 := (centralizer ({r₂R} : Set R)).card_mul_index
  rw [← h1, card_R] at h2
  have h3 : (centralizer ({r₂R} : Set R)).map R.subtype =
      centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    ext x
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨congrArg Subtype.val hy, y.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨x, hxR⟩, Subtype.ext hx, rfl⟩
  rw [← h3, card_map_of_injective R.subtype_injective]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h2.trans (by norm_num))

theorem exists_mem_C₂_of_commute_r₂ {r : Equiv.Perm (Fin 42)}
    (hr : r ∈ R) (hc : r * r₂ = r₂ * r) :
    ∃ c ∈ C₂, r = c ∨ r = c * r₂ ∨ r = c * r₃ ∨ r = c * r₄ := by
  set u : Fin 4 → Equiv.Perm (Fin 42) := ![1, r₂, r₃, r₄] with hu
  have huR : ∀ i, u i ∈ R := by
    intro i
    fin_cases i
    · exact R.one_mem
    · exact r₂_mem_R
    · exact r₃_mem_R
    · exact r₄_mem_R
  have huc : ∀ i, u i * r₂ = r₂ * u i := by
    intro i
    fin_cases i
    · show 1 * r₂ = r₂ * 1
      group
    · rfl
    · exact L34FU.r₂_mul_r₃.symm
    · exact L34FU.r₂_mul_r₄.symm
  have h2 : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right r₂_mul_self
  have h3 : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right r₃_mul_self
  have h4 : r₄⁻¹ = r₄ := inv_eq_of_mul_eq_one_right r₄_mul_self
  have h23 : r₂ * r₃ = r₄ := rfl
  have h32 : r₃ * r₂ = r₄ := L34FU.r₂_mul_r₃.symm
  have h24 : r₂ * r₄ = r₃ := by
    show g₅ * (g₅ * g₆) = g₆
    rw [← mul_assoc, show g₅ * g₅ = 1 from r₂_mul_self, one_mul]
  have h34 : r₃ * r₄ = r₂ := by
    have hc56 : g₅ * g₆ = g₆ * g₅ := L34FU.r₂_mul_r₃
    show g₆ * (g₅ * g₆) = g₅
    rw [hc56, ← mul_assoc, show g₆ * g₆ = 1 from r₃_mul_self, one_mul]
  have h42 : r₄ * r₂ = r₃ := by rw [← L34FU.r₂_mul_r₄, h24]
  have h43 : r₄ * r₃ = r₂ := by rw [← L34FU.r₃_mul_r₄, h34]
  have hS2 : r₂ ∉ S := not_mem_S_r₂
  have hS3 : r₃ ∉ S := not_mem_S_r₃
  have hS4 : r₄ ∉ S := not_mem_S_r₄
  have hdist : ∀ i j, u i * (u j)⁻¹ ∈ S → i = j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hu, h2, h3, h4, h23, h32, h24, h34, h42, h43] at hij ⊢ <;>
      first | exact absurd hij hS2 | exact absurd hij hS3 | exact absurd hij hS4
  set T : Subgroup (Equiv.Perm (Fin 42)) := centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ R
    with hT
  have hmemT : ∀ (c : ↥C₂) (i : Fin 4), (c : Equiv.Perm (Fin 42)) * u i ∈ T := by
    intro c i
    have hcC := mem_inf.mp c.2
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      R.mul_mem (S_le_R hcC.2) (huR i)⟩
    have hc2 := mem_centralizer_singleton_iff.mp hcC.1
    rw [mul_assoc, huc i, ← mul_assoc, hc2, mul_assoc]
  let f : ↥C₂ × Fin 4 → ↥T := fun p => ⟨(p.1 : Equiv.Perm (Fin 42)) * u p.2, hmemT p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    have h1 : (c : Equiv.Perm (Fin 42)) * u i = c' * u j := congrArg Subtype.val h
    have h2 : u i * (u j)⁻¹ ∈ S := by
      have : u i * (u j)⁻¹ = (c : Equiv.Perm (Fin 42))⁻¹ * c' := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h1, mul_inv_cancel_right]
      rw [this]
      exact S.mul_mem (S.inv_mem (mem_inf.mp c.2).2) (mem_inf.mp c'.2).2
    obtain rfl := hdist i j h2
    have h3 : c = c' := Subtype.ext (mul_right_cancel h1)
    rw [h3]
  have hcard : Nat.card ↥T ≤ Nat.card (↥C₂ × Fin 4) := by
    rw [hT, card_centralizer_r₂_inf_R, Nat.card_prod, card_C₂, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨⟨c, i⟩, hci⟩ := (hf.bijective_of_nat_card_le hcard).2
    ⟨r, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc, hr⟩⟩
  have hr' : (c : Equiv.Perm (Fin 42)) * u i = r := congrArg Subtype.val hci
  refine ⟨c, c.2, ?_⟩
  fin_cases i
  · exact Or.inl (by rw [← hr']; exact mul_one _)
  · exact Or.inr (Or.inl hr'.symm)
  · exact Or.inr (Or.inr (Or.inl hr'.symm))
  · exact Or.inr (Or.inr (Or.inr hr'.symm))

theorem isConj_r₄_of_mem_S_mul_r₄
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ S) (h2 : c * r₄ * (c * r₄) = 1) :
    IsConj (⟨c * r₄, R.mul_mem (S_le_R hc) r₄_mem_R⟩ : R) r₄R := by
  set x : R := ⟨c * r₄, R.mul_mem (S_le_R hc) r₄_mem_R⟩ with hx
  have hr₄S : ∀ y : Equiv.Perm (Fin 42), y ∈ S → c * r₄ = y → False := by
    intro y hy hcy
    apply not_mem_S_r₄
    have : r₄ = c⁻¹ * y := by rw [← hcy, inv_mul_cancel_left]
    rw [this]
    exact S.mul_mem (S.inv_mem hc) hy
  have hx1 : x ≠ 1 := fun h => hr₄S 1 S.one_mem (congrArg Subtype.val h)
  have hord : orderOf x = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact h2)) hx1
  rcases (orderOf_eq_two_iff x).1 hord with h | h | h | h
  · exact (hr₄S _ (mem_S_of_isConj₁ h) rfl).elim
  · obtain ⟨d, hdR, hd⟩ := eq_conj_of_isConj h
    apply (L34FU.conj_r₂_mul_r₄_not_mem_S hdR).elim
    have hd' : c * r₄ = d * r₂ * d⁻¹ := hd
    rw [← hd', mul_assoc, r₄_mul_self, mul_one]
    exact hc
  · obtain ⟨d, hdR, hd⟩ := eq_conj_of_isConj h
    have hd' : c * r₄ = d * r₃ * d⁻¹ := hd
    have hσ := L34FU.conj_r₄_mul_mem_S hdR
    exfalso
    apply not_mem_S_r₂
    apply conj_mem_S' hdR
    have e1 : d * r₂ * d⁻¹ = c * (d * r₄ * d⁻¹ * r₄⁻¹)⁻¹ := by
      have e2 : d * r₃ * d⁻¹ = d * r₂ * d⁻¹ * (d * r₄ * d⁻¹) := by
        have h24 : r₂ * r₄ = r₃ := by
          show g₅ * (g₅ * g₆) = g₆
          rw [← mul_assoc, show g₅ * g₅ = 1 from r₂_mul_self, one_mul]
        rw [← h24]
        group
      have e3 : c * r₄ = d * r₂ * d⁻¹ * (d * r₄ * d⁻¹) := by rw [hd', e2]
      rw [mul_inv_rev, inv_inv, ← mul_assoc, e3]
      group
    rw [e1]
    exact S.mul_mem hc (S.inv_mem hσ)
  · exact h

end CFSG.ComponentClassification.PSL3Four
