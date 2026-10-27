module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Q11

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem dvd_card_of_transitive_nonzero (R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)))
    (h : ∀ w : Fin 2 → ZMod 11, w ≠ 0 → ∃ g ∈ R, g • (![1, 0] : Fin 2 → ZMod 11) = w) :
    120 ∣ Nat.card R := by
  set e₁ : Fin 2 → ZMod 11 := ![1, 0] with he₁
  have he₁0 : e₁ ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp only [he₁] at this
    exact absurd this (by decide)
  have horb : MulAction.orbit R e₁ = {v | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩ h0
      apply he₁0
      have h1 : ((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11))
          *ᵥ e₁ = 0 := h0
      have h2 : e₁ = (((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11))⁻¹ :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) *ᵥ
          (((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
            Matrix (Fin 2) (Fin 2) (ZMod 11)) *ᵥ e₁) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [h2, h1, Matrix.mulVec_zero]
    · intro hv
      obtain ⟨g, hg, hgv⟩ := h v hv
      exact ⟨⟨g, hg⟩, hgv⟩
  have hcard : Nat.card (MulAction.orbit R e₁) = 120 := by
    rw [horb]
    have : Nat.card {v : Fin 2 → ZMod 11 // v ≠ 0} = 120 := card_nonzero_eleven
    exact this
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer R e₁)
  have hcard' : (MulAction.orbit R e₁).ncard = 120 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  rw [MulAction.index_stabilizer, hcard'] at h1
  exact Dvd.intro_left _ h1

theorem actMat_of_conj
    (n : Subgroup.normalizer (Q11 : Set J)) (a b c d e f : ℕ)
    (hx : (n : J) * qx * (n : J)⁻¹ = qx ^ a * qy ^ b * qz ^ c)
    (hy : (n : J) * qy * (n : J)⁻¹ = qx ^ d * qy ^ e * qz ^ f) :
    heisData.actMat n = !![(a : ZMod 11), (d : ZMod 11); (b : ZMod 11), (e : ZMod 11)] := by
  have hπx : heisData.π ⟨qx, qx_mem⟩ = Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod 11) := by
    rw [← heisData_x]; exact heisData.π_x
  have hπy : heisData.π ⟨qy, qy_mem⟩ = Multiplicative.ofAdd (![0, 1] : Fin 2 → ZMod 11) := by
    rw [← heisData_y]; exact heisData.π_y
  have hcx : Q11.normalizerMonoidHom n ⟨qx, qx_mem⟩ =
      ⟨qx, qx_mem⟩ ^ a * ⟨qy, qy_mem⟩ ^ b * ⟨qz, qz_mem⟩ ^ c := by
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    simpa using hx
  have hcy : Q11.normalizerMonoidHom n ⟨qy, qy_mem⟩ =
      ⟨qx, qx_mem⟩ ^ d * ⟨qy, qy_mem⟩ ^ e * ⟨qz, qz_mem⟩ ^ f := by
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    simpa using hy
  have hcol0 : Multiplicative.toAdd (heisData.π (Q11.normalizerMonoidHom n heisData.x)) =
      ![(a : ZMod 11), (b : ZMod 11)] := by
    have hπ : heisData.π (⟨qx, qx_mem⟩ ^ a * ⟨qy, qy_mem⟩ ^ b * ⟨qz, qz_mem⟩ ^ c) =
        heisData.π ⟨qx, qx_mem⟩ ^ a * heisData.π ⟨qy, qy_mem⟩ ^ b *
          heisData.π ⟨qz, qz_mem⟩ ^ c := by simp only [map_mul, map_pow]
    rw [heisData_x, hcx, hπ, hπx, hπy, π_qz]
    ext k; fin_cases k <;> simp
  have hcol1 : Multiplicative.toAdd (heisData.π (Q11.normalizerMonoidHom n heisData.y)) =
      ![(d : ZMod 11), (e : ZMod 11)] := by
    have hπ : heisData.π (⟨qx, qx_mem⟩ ^ d * ⟨qy, qy_mem⟩ ^ e * ⟨qz, qz_mem⟩ ^ f) =
        heisData.π ⟨qx, qx_mem⟩ ^ d * heisData.π ⟨qy, qy_mem⟩ ^ e *
          heisData.π ⟨qz, qz_mem⟩ ^ f := by simp only [map_mul, map_pow]
    rw [heisData_y, hcy, hπ, hπx, hπy, π_qz]
    ext k; fin_cases k <;> simp
  ext i j
  fin_cases j
  · have := congrFun hcol0 i
    fin_cases i <;> simpa [HeisCoordData.actMat, HeisCoordData.gen2] using this
  · have := congrFun hcol1 i
    fin_cases i <;> simpa [HeisCoordData.actMat, HeisCoordData.gen2] using this

theorem actMat_nrm₁ :
    heisData.actMat ⟨nrm₁, nrm₁_mem_normalizer⟩ = !![7, 3; 3, 3] := by
  have := actMat_of_conj ⟨nrm₁, nrm₁_mem_normalizer⟩ 7 3 2 3 3 9 nrm₁_qx nrm₁_qy
  simpa using this

theorem range_actHom_transitive :
    ∀ w : Fin 2 → ZMod 11, w ≠ 0 →
      ∃ g ∈ heisData.actHom.range, g • (![1, 0] : Fin 2 → ZMod 11) = w := by
  intro w hw
  have he : (![1, 0] : Fin 2 → ZMod 11) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
    exact absurd this (by decide)
  obtain ⟨g, hg, hgw⟩ := matAB_transitive _ w he hw
  have key : ∀ m ∈ Submonoid.closure ({CFSG.Sporadic.J4Schreier.matA, CFSG.Sporadic.J4Schreier.matB} : Set (Matrix (Fin 2) (Fin 2) (ZMod 11))),
      ∃ γ ∈ heisData.actHom.range, ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
        Matrix (Fin 2) (Fin 2) (ZMod 11)) = m := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨heisData.actHom ⟨nrm₁, nrm₁_mem_normalizer⟩, ⟨_, rfl⟩, by
          rw [heisData.coe_actHom, actMat_nrm₁]; rfl⟩
      · exact ⟨heisData.actHom ⟨nrm₂, nrm₂_mem_normalizer⟩, ⟨_, rfl⟩, by
          rw [heisData.coe_actHom, actMat_nrm₂]; rfl⟩
    | one => exact ⟨1, one_mem _, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨γ₁, h₁, e₁⟩ := hx
      obtain ⟨γ₂, h₂, e₂⟩ := hy
      exact ⟨γ₁ * γ₂, mul_mem h₁ h₂, by rw [Units.val_mul, e₁, e₂]⟩
  obtain ⟨γ, hγ, hγg⟩ := key g hg
  exact ⟨γ, hγ, by rw [← hgw, ← hγg]; rfl⟩

theorem card_range_actHom_Q11 :
    Nat.card heisData.actHom.range = 240 := by
  have hN := card_normalizer_eq heisData actMat_eq_one_mem
  rw [card_Q11] at hN
  have h240 : Nat.card heisData.actHom.range ∣ 240 := by
    have h1 := Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (Q11 : Set J))
    rw [hN, card_J_eq] at h1
    have h2 : Nat.card heisData.actHom.range ∣
        2 ^ 21 * 3 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43 := by
      have : 11 ^ 3 * Nat.card heisData.actHom.range ∣
          11 ^ 3 * (2 ^ 21 * 3 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43) := by
        convert h1 using 1
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
    have h3 := Nat.dvd_gcd h2 (card_range_actHom_dvd heisData)
    exact h3.trans (by norm_num)
  have h16 : 16 ∣ Nat.card heisData.actHom.range := by
    have h := sixteen_dvd_card_normalizer
    rw [hN] at h
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h)
  have h120 : 120 ∣ Nat.card heisData.actHom.range :=
    dvd_card_of_transitive_nonzero _ range_actHom_transitive
  have h240' : 240 ∣ Nat.card heisData.actHom.range := by
    have h := Nat.lcm_dvd h16 h120
    rwa [show Nat.lcm 16 120 = 240 by norm_num] at h
  exact Nat.dvd_antisymm h240 h240'

theorem card_normalizer_Q11 :
    Nat.card (Subgroup.normalizer (Q11 : Set J)) = 11 ^ 3 * 240 := by
  rw [card_normalizer_eq heisData actMat_eq_one_mem, card_Q11, card_range_actHom_Q11]

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
