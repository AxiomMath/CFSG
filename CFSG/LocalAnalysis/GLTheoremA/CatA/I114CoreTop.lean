module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114CoreMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Core2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Main6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem x_cube_identities' {x : Y} (hx3 : x ^ 3 = 1) : (x * x) * x = 1 := by
  calc (x * x) * x = x ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    _ = 1 := hx3

theorem core_T_eq_bot [Finite Y] {B K T : Subgroup Y} (hB : IsElemAbelian 3 B)
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3)
    (hcomm : ∀ b ∈ B, b ∉ Subgroup.normalizer (K : Set Y) → ElemCommute K (cj b K))
    (hmax : ∀ F : Subgroup Y, IsElemAbelian 3 F →
      (∃ W : Subgroup Y, W ≠ ⊥ ∧ IsPGroup 2 W ∧ F ≤ Subgroup.normalizer (W : Set Y)) →
      Nat.card F ≤ Nat.card B)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (hA : ∃ y : ↥K, (∃ z : ↥K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
      ∃ U : Subgroup ↥K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ y ∈ Subgroup.normalizer (U : Set ↥K))
    (hBF : ∀ (H : Subgroup (MulAut ↥K)) (S : Subgroup ↥K), IsElemAbelian 3 H →
      Nat.card H = 9 → S ≠ ⊥ → IsPGroup 2 S →
      (∀ h ∈ H, S.map (MulEquiv.toMonoidHom h) = S) →
      ∃ U : Subgroup ↥K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ h ∈ H, U.map (MulEquiv.toMonoidHom h) = U) ∧
        ∃ y : ↥K, (∃ z : ↥K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
          y ∈ Subgroup.normalizer (U : Set ↥K) ∧ (∀ h ∈ H, h y = y) ∧
          ∃ α ∈ H, orderOf α = 3 ∧ ¬ ∃ k : ↥K, ∀ z : ↥K, α z = k * z * k⁻¹)
    (hHr : ∀ H : Subgroup (MulAut ↥K), IsElemAbelian 3 H → Nat.card H ≤ 9)
    (hT : T ≤ ⨆ b ∈ B, cj b K) (hTp : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set Y)) : T = ⊥ := by
  classical
  obtain ⟨x, hxB, hxN⟩ := exists_mem_not_normalizer hrel
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hKK₂ : ElemCommute K (cj x K) := hcomm x hxB hxN
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hxxN : x * x ∉ Subgroup.normalizer (K : Set Y) := by
    intro h
    apply hxN
    have hxx : x = (x * x) * (x * x) := (x_cube_identities hx3).2.symm
    rw [hxx]
    exact (Subgroup.normalizer (K : Set Y)).mul_mem h h
  have hKK₃ : ElemCommute K (cj (x * x) K) := hcomm (x * x) hxxB hxxN
  have hHk := H9_bound hB hxB hrel hKK₂ hKK₃ hmax hA
  have hHel : IsElemAbelian 3 (HK K B) := isElemAbelian_HK hB
  have hH9 : Nat.card (HK K B) = 9 := le_antisymm (hHr _ hHel) hHk
  have hTK : T ≤ K ⊔ (cj x K ⊔ cj (x * x) K) := by
    rw [← sup_assoc]
    exact hT.trans (closure_le_three hB hxB hxN hrel)
  have hTx : cj x T = T := mem_normalizer_iff_cj.1 (hBT hxB)
  have hTxx : cj (x * x) T = T := mem_normalizer_iff_cj.1 (hBT hxxB)
  have hTn : ∀ b ∈ B, cj b T = T := fun b hb => mem_normalizer_iff_cj.1 (hBT hb)
  by_cases hA' : T ≤ cj x K ⊔ cj (x * x) K
  ·
    obtain ⟨hxxx, hxxxx⟩ := x_cube_identities hx3
    have hxxx' := x_cube_identities' hx3
    have hK₂K₃ : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
    have hZ₂ : Nat.card (Subgroup.center ↥(cj x K)) = 3 := by
      rw [card_center_cj]
      exact hZ
    have hZ₃ : Nat.card (Subgroup.center ↥(cj (x * x) K)) = 3 := by
      rw [card_center_cj]
      exact hZ
    have h1 : cj x (cj (x * x) K) = K := by
      rw [← cj_mul, hxxx, cj_one]
    have h2 : cj (x * x) (cj x K) = K := by
      rw [← cj_mul, hxxx', cj_one]
    have h3 : cj (x * x) (cj (x * x) K) = cj x K := by
      rw [← cj_mul, hxxxx]
    have hT₂ : T ≤ cj (x * x) K ⊔ K := by
      have h := cj_mono x hA'
      rw [hTx, cj_sup, cj_xx_of_cj_x, h1] at h
      exact h
    have hT₃ : T ≤ K ⊔ cj x K := by
      have h := cj_mono (x * x) hA'
      rw [hTxx, cj_sup, h2, h3] at h
      exact h
    exact two_group_le_pair_trivial hKK₂ hKK₃ hK₂K₃ hZ₂ hZ₃ hA' hT₂ hT₃ hTp
  ·
    obtain ⟨t, htT, htP⟩ := SetLike.not_le_iff_exists.1 hA'
    have hPn : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Y) →
        cj b (cj x K ⊔ cj (x * x) K) = cj x K ⊔ cj (x * x) K := by
      intro b hb hbN
      have hbK : cj b K = K := mem_normalizer_iff_cj.1 hbN
      have hbx : b * x = x * b := isElemAbelian_commute hB hb hxB
      have hbxx : b * (x * x) = (x * x) * b := by
        rw [← mul_assoc, hbx, mul_assoc, hbx, ← mul_assoc]
      rw [cj_sup, cj_fix_of_comm hbx hbK, cj_fix_of_comm hbxx hbK]
    have hKP : ElemCommute K (cj x K ⊔ cj (x * x) K) := commutes_sup_right hKK₂ hKK₃
    obtain ⟨P₀, hP₀K, hP₀ne, hP₀p, hP₀n⟩ :=
      exists_normal_two_subgroup hKP hZ hPn hTn hTK hTp htT htP
    exact (contra_final hB hxB hrel hKK₂ hKK₃ hmax hBF hH9 hP₀K hP₀ne hP₀p hP₀n).elim

end CFSG.LocalAnalysis.GLTheoremA.I114
