module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Wrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Inv
public import CFSG.Sporadic.J4.QTRankWitProof

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
  CFSG.QuasithinUnique.Setup.X1.J4Inv

section MovedJ

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem index_conj_J (σ : J →* MulAut W) {s t : J} (h : IsConj s t) :
    (fixV (Subgroup.zpowers (σ t))).index = (fixV (Subgroup.zpowers (σ s))).index := by
  obtain ⟨k, hk⟩ := isConj_iff.1 h
  rw [← hk, map_mul, map_mul, map_inv]
  exact index_fixV_conj (σ k) (σ s)

theorem moved_rank_J
    (hW : ∀ w : W, w * w = 1) (σ : J →* MulAut W) (hσ : Function.Injective σ)
    (t : J) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    2 ^ 18 ≤ (fixV (Subgroup.zpowers (σ t))).index := by
  have hF := j4Facts
  rcases inv_conj_root hF ht2 ht1 with h | h
  ·
    rw [index_conj_J σ h]
    have hord : orderOf (σ (eta uJ 11 1) * (σ gW⁻¹ * σ (eta uJ 11 1) * (σ gW⁻¹)⁻¹)) = 37 := by
      have h1 : σ (c37) = σ (eta uJ 11 1) * (σ gW⁻¹ * σ (eta uJ 11 1) * (σ gW⁻¹)⁻¹) := by
        rw [c37, map_mul, map_mul, map_mul, map_inv, inv_inv]
      rw [← h1, orderOf_injective σ hσ, orderOf_c37 hF]
    exact two_pow_eighteen_le_index_of_dihedral_37 hW hord
  ·
    have hconj : IsConj a t := (isConj_eta_three_a hF).symm.trans h
    rw [index_conj_J σ hconj]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := witness11 hF
    have hsq := a_mul_a hF.mat
    have hE := two_pow_hundred_le_index_sq hW (X := σ xE) (Y := σ yE) (Zm := σ zE) (T := σ a)
      (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
      (fun h => h3 (hσ (by rw [h, map_one])))
      (by rw [← map_mul, ← map_mul, h4]) (by rw [← map_mul, ← map_mul, h5])
      (by have := congrArg σ h6; simpa [map_mul, map_inv] using this)
      (by rw [← map_mul, hsq, map_one])
      (by have := congrArg σ h7; simpa [map_mul, map_inv] using this)
      (by rw [← map_mul, ← map_mul, h8])
    by_contra hlt
    push Not at hlt
    have : (fixV (Subgroup.zpowers (σ a))).index ^ 2 < (2 ^ 18) ^ 2 :=
      Nat.pow_lt_pow_left hlt (by norm_num)
    have h100 : (2 : ℕ) ^ 100 ≥ (2 ^ 18) ^ 2 := by norm_num
    omega

end MovedJ

theorem moved_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : Y →* MulAut W, Function.Injective σ → ∀ t : Y, t ≠ 1 → t * t = 1 →
        2 ^ 18 ≤ (fixV (Subgroup.zpowers (σ t))).index)
    (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (σ : X →* MulAut W)
    (hσ : Function.Injective σ) (t : X) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    2 ^ 18 ≤ (fixV (Subgroup.zpowers (σ t))).index := by
  have hinj : Function.Injective (σ.comp e.symm.toMonoidHom) := by
    intro x y hxy
    exact e.symm.injective (hσ hxy)
  have h := hY W hW (σ.comp e.symm.toMonoidHom) hinj (e t)
    (fun h => ht1 (e.injective (by rw [h, map_one])))
    (by rw [← map_mul, ht2, map_one])
  simpa using h

theorem j4MovedRank_aux
    : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ σ : NativeSporadic.J4 →* MulAut W, Function.Injective σ → ∀ t : NativeSporadic.J4,
      t ≠ 1 → t * t = 1 → 2 ^ 18 ≤ (fixV (Subgroup.zpowers (σ t))).index := by
  intro W _ _ hW σ hσ t ht1 ht2
  have e : NativeSporadic.J4 ≃* CFSG.Sporadic.J4.J :=
    CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat
  exact @moved_of_mulEquiv NativeSporadic.J4 CFSG.Sporadic.J4.J inferInstance inferInstance e
    (fun W _ _ hW σ hσ t ht1 ht2 => moved_rank_J hW σ hσ t ht1 ht2) W _ _ hW σ hσ t ht1 ht2

theorem j4MovedRank
    : J4MovedRankProp := j4MovedRank_aux

end CFSG.QuasithinUnique.Setup.X1
