module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenU
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB

@[expose] def s123 : Perm (Fin 6) := swap 1 2 * swap 2 3

@[expose] def s450 : Perm (Fin 6) := swap 4 5 * swap 5 0

theorem s123_isThreeCycle : s123.IsThreeCycle := card_support_eq_three_iff.mp (by decide)

theorem eq_of_commute_s123 {a : Perm (Fin 6)} (hs : sign a = 1) (hc : a * s123 = s123 * a) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ a = s123 ^ i * s450 ^ j := by
  have hp : ∀ (b : Perm (Fin 6)), b * s123 = s123 * b → ∀ x, b (s123 x) = s123 (b x) :=
    fun b hb x => by
      have := congrArg (fun f : Perm (Fin 6) => f x) hb
      simpa only [Perm.mul_apply] using this
  have hfix : ∀ y : Fin 6, y ≠ 1 → y ≠ 2 → y ≠ 3 → s123 y = y := by decide
  have h1 : a 1 = 1 ∨ a 1 = 2 ∨ a 1 = 3 := by
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨n1, n2, n3⟩ := hne
    have e : a 2 = a 1 := by
      rw [show (2 : Fin 6) = s123 1 by decide, hp a hc, hfix _ n1 n2 n3]
    exact absurd (a.injective e) (by decide)
  obtain ⟨i, hi3, hi⟩ : ∃ i : ℕ, i < 3 ∧ (s123 ^ i) 1 = a 1 := by
    rcases h1 with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; rfl⟩
    · exact ⟨1, by norm_num, by rw [h]; decide⟩
    · exact ⟨2, by norm_num, by rw [h]; decide⟩
  set a' := (s123 ^ i)⁻¹ * a with ha'
  have hci : (s123 ^ i)⁻¹ * s123 = s123 * (s123 ^ i)⁻¹ :=
    ((Commute.refl s123).pow_left i).inv_left.eq
  have hc' : a' * s123 = s123 * a' := by
    rw [ha', mul_assoc, hc, ← mul_assoc, hci, mul_assoc]
  have ha'1 : a' 1 = 1 := by rw [ha', Perm.mul_apply, ← hi]; simp
  have ha'2 : a' 2 = 2 := by
    rw [show (2 : Fin 6) = s123 1 by decide, hp a' hc', ha'1]
  have ha'3 : a' 3 = 3 := by
    rw [show (3 : Fin 6) = s123 2 by decide, hp a' hc', ha'2]
  set κ : Perm (Fin 6) := swap 1 4 * swap 2 5 with hκ
  have hκi : κ⁻¹ = κ := by decide
  set a'' := κ * a' * κ⁻¹ with ha''
  have hfix'' : ∀ x : Fin 6, 4 ≤ (x : ℕ) → a'' x = x := by
    intro x hx
    have hx' : x = 4 ∨ x = 5 := by
      rcases (by omega : (x : ℕ) = 4 ∨ (x : ℕ) = 5) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hx' with rfl | rfl
    · rw [ha'', Perm.mul_apply, Perm.mul_apply, hκi, show κ 4 = 1 by decide, ha'1]
      decide
    · rw [ha'', Perm.mul_apply, Perm.mul_apply, hκi, show κ 5 = 2 by decide, ha'2]
      decide
  obtain ⟨π', hπ'⟩ := exists_perm_four_of_fix (by norm_num : 4 ≤ 6) hfix''
  have h3 : π' 3 = 3 := by
    have e : a'' 3 = 3 := by
      rw [ha'', Perm.mul_apply, Perm.mul_apply, hκi, show κ 3 = 3 by decide, ha'3]
      decide
    have e2 := viaEmbeddingHom_apply_image (fourEmb (by norm_num : 4 ≤ 6)) π' 3
    rw [hπ', show fourEmb (by norm_num : 4 ≤ 6) 3 = (3 : Fin 6) from rfl, e] at e2
    exact (fourEmb (by norm_num : 4 ≤ 6)).injective e2.symm
  have hsg : sign π' = 1 := by
    have hs123 : sign s123 = 1 := by decide
    have e : sign (viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) π') = 1 := by
      rw [hπ', ha'', ha']
      simp [hs, hs123]
    rwa [sign_viaEmbeddingHom] at e
  have key : ∀ π : Perm (Fin 4), π 3 = 3 → sign π = 1 →
      π = 1 ∨ π = swap 0 1 * swap 1 2 ∨ π = (swap 0 1 * swap 1 2)⁻¹ := by decide
  have hback : a' = κ⁻¹ * viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) π' * κ := by
    rw [hπ', ha'']
    group
  have hv : viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 6)) (swap 0 1 * swap 1 2) =
      swap 0 1 * swap 1 2 := by
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl
  have ha : a = s123 ^ i * a' := by rw [ha']; group
  have hk1 : κ * (swap 0 1 * swap 1 2) * κ = s450 ^ 1 := by rw [hκ]; decide
  have hk2 : κ * (swap 0 1 * swap 1 2)⁻¹ * κ = s450 ^ 2 := by rw [hκ]; decide
  rcases key π' h3 hsg with h | h | h
  · refine ⟨i, 0, hi3, by norm_num, ?_⟩
    rw [ha, hback, h]
    simp
  · refine ⟨i, 1, hi3, by norm_num, ?_⟩
    rw [ha, hback, h, hv, hκi, hk1]
  · refine ⟨i, 2, hi3, by norm_num, ?_⟩
    rw [ha, hback, h, map_inv, hv, hκi, hk2]

theorem card_centralizer_s123 :
    Nat.card (centralizer ({s123} : Set (Perm (Fin 6)))) = 18 := by
  rw [nat_card_centralizer, show s123.cycleType = {3} from s123_isThreeCycle]
  decide

@[expose] def e123 : alternatingGroup (Fin 6) := ⟨s123, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def e450 : alternatingGroup (Fin 6) := ⟨s450, mem_alternatingGroup.mpr (by decide)⟩

theorem exists_perm_of_fix_e123 (θ : MulAut (alternatingGroup (Fin 6))) (hθ : θ e123 = e123) :
    ∃ σ : Perm (Fin 6), θ = conjPerm 6 σ ∧ σ * s123 = s123 * σ := by
  set κ : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 with hκ
  have hκc : conjPerm 6 κ a6c012 = e123 := Subtype.ext (by
    rw [conjPerm_apply, hκ]
    decide)
  have hκc' : (conjPerm 6 κ)⁻¹ e123 = a6c012 := by
    rw [← hκc]
    simp
  set θ' := (conjPerm 6 κ)⁻¹ * θ * conjPerm 6 κ with hθ'
  have h' : θ' a6c012 = a6c012 := by
    show (conjPerm 6 κ)⁻¹ (θ (conjPerm 6 κ a6c012)) = a6c012
    rw [hκc, hθ, hκc']
  obtain ⟨σ', hσ'⟩ := exists_perm_of_isThreeCycle θ'
    (by rw [h']; exact card_support_eq_three_iff.mp (by decide))
  have hθ'eq : θ' = conjPerm 6 σ' :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hσ' g, conjPerm_apply])
  have hθeq : θ = conjPerm 6 (κ * σ' * κ⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← hθ'eq, hθ']
    group
  refine ⟨κ * σ' * κ⁻¹, hθeq, ?_⟩
  have h2 := congrArg Subtype.val hθ
  rw [hθeq, conjPerm_apply] at h2
  have h3 : (κ * σ' * κ⁻¹) * s123 * (κ * σ' * κ⁻¹)⁻¹ = s123 := h2
  calc (κ * σ' * κ⁻¹) * s123 = (κ * σ' * κ⁻¹) * s123 * (κ * σ' * κ⁻¹)⁻¹ * (κ * σ' * κ⁻¹) := by
        group
    _ = s123 * (κ * σ' * κ⁻¹) := by rw [h3]

end CFSG.ComponentClassification.RankTwoAlt
