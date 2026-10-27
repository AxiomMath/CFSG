module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEigen
public import CFSG.GH74.Generic.Front.InvolutionLA
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix
open CFSG.ComponentClassification.Burgoyne.O (gramMat gramMat_det_ne_zero famOf famOf_gram)

variable {K : Type} [Field K] {d : ℕ}

abbrev negE (u : Matrix (Fin d) (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.ker (Matrix.toLin' u + LinearMap.id)

abbrev posE (u : Matrix (Fin d) (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.ker (Matrix.toLin' u - LinearMap.id)

theorem mem_negE {u : Matrix (Fin d) (Fin d) K} {v : Fin d → K} : v ∈ negE u ↔ u *ᵥ v = -v := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, Matrix.toLin'_apply]
  exact ⟨fun h => eq_neg_of_add_eq_zero_left h, fun h => by rw [h, neg_add_cancel]⟩

theorem mem_posE {u : Matrix (Fin d) (Fin d) K} {v : Fin d → K} : v ∈ posE u ↔ u *ᵥ v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, Matrix.toLin'_apply]
  exact sub_eq_zero

theorem finrank_split (h2 : (2 : K) ≠ 0) {g : Matrix (Fin d) (Fin d) K} (hg : g * g = 1)
    {W : Submodule K (Fin d → K)} (hW : ∀ w ∈ W, g *ᵥ w ∈ W) :
    finrank K W = finrank K ↥(W ⊓ posE g) + finrank K ↥(W ⊓ negE g) := by
  have hgg : ∀ v, g *ᵥ (g *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hg, one_mulVec]
  have hinf : (W ⊓ posE g) ⊓ (W ⊓ negE g) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨⟨-, hv1⟩, -, hv2⟩ := hv
    rw [SetLike.mem_coe, mem_posE] at hv1
    rw [SetLike.mem_coe, mem_negE] at hv2
    rw [Submodule.mem_bot]
    have h : (2 : K) • v = 0 := by rw [two_smul]; nth_rw 1 [← hv1]; rw [hv2, neg_add_cancel]
    exact (smul_eq_zero.mp h).resolve_left h2
  have hsup : (W ⊓ posE g) ⊔ (W ⊓ negE g) = W := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    have : Invertible (2 : K) := invertibleOfNonzero h2
    have hw' : w = ⅟(2 : K) • (w + g *ᵥ w) + ⅟(2 : K) • (w - g *ᵥ w) := by
      rw [← smul_add, show w + g *ᵥ w + (w - g *ᵥ w) = (2 : K) • w by rw [two_smul]; abel,
        smul_smul, invOf_mul_self, one_smul]
    rw [hw']
    refine Submodule.add_mem_sup ⟨W.smul_mem _ (W.add_mem hw (hW w hw)), ?_⟩
      ⟨W.smul_mem _ (W.sub_mem hw (hW w hw)), ?_⟩
    · rw [SetLike.mem_coe, mem_posE, mulVec_smul, mulVec_add, hgg, add_comm]
    · rw [SetLike.mem_coe, mem_negE, mulVec_smul, mulVec_sub, hgg, ← smul_neg, neg_sub]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ posE g) (W ⊓ negE g)
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h

theorem klein_dims (h2 : (2 : K) ≠ 0) {u₁ u₂ : Matrix (Fin d) (Fin d) K}
    (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁) :
    finrank K (negE u₁) = finrank K ↥(negE u₁ ⊓ posE u₂) + finrank K ↥(negE u₁ ⊓ negE u₂) ∧
    finrank K (negE u₂) = finrank K ↥(negE u₂ ⊓ posE u₁) + finrank K ↥(negE u₁ ⊓ negE u₂) ∧
    finrank K (negE (u₁ * u₂)) =
      finrank K ↥(negE u₂ ⊓ posE u₁) + finrank K ↥(negE u₁ ⊓ posE u₂) := by
  have hc : ∀ v, u₁ *ᵥ (u₂ *ᵥ v) = u₂ *ᵥ (u₁ *ᵥ v) := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, h12]
  have hu₁ : ∀ v, u₁ *ᵥ (u₁ *ᵥ v) = v := fun v => by rw [mulVec_mulVec, h₁, one_mulVec]
  have s₁ := finrank_split h2 h₂ (W := negE u₁) fun w hw => by
    rw [mem_negE] at hw ⊢
    rw [hc, hw, mulVec_neg]
  have s₂ := finrank_split h2 h₁ (W := negE u₂) fun w hw => by
    rw [mem_negE] at hw ⊢
    rw [← hc, hw, mulVec_neg]
  have s₃ := finrank_split h2 h₁ (W := negE (u₁ * u₂)) fun w hw => by
    rw [mem_negE, ← mulVec_mulVec] at hw ⊢
    rw [← hc, hu₁]
    have e := congrArg (fun z => u₁ *ᵥ z) hw
    rw [hu₁, mulVec_neg] at e
    exact e
  have e₁ : negE (u₁ * u₂) ⊓ posE u₁ = negE u₂ ⊓ posE u₁ := by
    ext v
    simp only [Submodule.mem_inf, mem_negE, mem_posE, ← mulVec_mulVec]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨?_, h'⟩
      rw [hc, h'] at h
      exact h
    · rintro ⟨h, h'⟩
      exact ⟨by rw [h, mulVec_neg, h'], h'⟩
  have e₂ : negE (u₁ * u₂) ⊓ negE u₁ = negE u₁ ⊓ posE u₂ := by
    ext v
    simp only [Submodule.mem_inf, mem_negE, mem_posE, ← mulVec_mulVec]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h', ?_⟩
      rw [hc, h', mulVec_neg, neg_inj] at h
      exact h
    · rintro ⟨h, h'⟩
      exact ⟨by rw [h', h], h⟩
  rw [e₁, e₂] at s₃
  rw [inf_comm (negE u₂) (negE u₁)] at s₂
  exact ⟨s₁, s₂, s₃⟩

theorem odd_finrank_joint (h2 : (2 : K) ≠ 0) {u₁ u₂ : Matrix (Fin d) (Fin d) K}
    (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁)
    (hk₁ : finrank K (negE u₁) % 4 = 2) (hk₂ : finrank K (negE u₂) % 4 = 2)
    (hk₃ : finrank K (negE (u₁ * u₂)) % 4 = 2) :
    Odd (finrank K ↥(negE u₁ ⊓ posE u₂)) := by
  obtain ⟨s₁, s₂, s₃⟩ := klein_dims h2 h₁ h₂ h12
  have : finrank K ↥(negE u₁ ⊓ posE u₂) % 2 = 1 := by omega
  exact Nat.odd_iff.mpr this

theorem exists_two_of_klein (h2 : (2 : K) ≠ 0) (hd : d ≤ 8) {u₁ u₂ : Matrix (Fin d) (Fin d) K}
    (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁)
    (hk₁ : finrank K (negE u₁) % 4 = 2) (hk₂ : finrank K (negE u₂) % 4 = 2)
    (hk₃ : finrank K (negE (u₁ * u₂)) % 4 = 2) :
    finrank K (negE u₁) = 2 ∨ finrank K (negE u₂) = 2 ∨ finrank K (negE (u₁ * u₂)) = 2 := by
  obtain ⟨s₁, s₂, s₃⟩ := klein_dims h2 h₁ h₂ h12
  have hu₁ : ∀ v, Matrix.toLin' u₁ (Matrix.toLin' u₁ v) = v := fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, h₁, one_mulVec]
  have hsum : finrank K (negE u₁) + finrank K (posE u₁) = d := by
    have h := CFSG.GH74.Generic.involution_finrank_add h2 (Matrix.toLin' u₁) hu₁
    rw [Module.finrank_fin_fun] at h
    exact h
  have hle : finrank K ↥(negE u₂ ⊓ posE u₁) ≤ finrank K (posE u₁) :=
    Submodule.finrank_mono inf_le_right
  omega

theorem dot_iso {R u : Matrix (Fin d) (Fin d) K} (hu : uᵀ * R * u = R) (a b : Fin d → K) :
    (u *ᵥ a) ⬝ᵥ R *ᵥ (u *ᵥ b) = a ⬝ᵥ R *ᵥ b := by
  have e : ∀ y, (u *ᵥ a) ⬝ᵥ y = a ⬝ᵥ (uᵀ *ᵥ y) := fun y => by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [e, mulVec_mulVec, mulVec_mulVec, hu]

theorem nondeg_joint (h2 : (2 : K) ≠ 0) {R : Matrix (Fin d) (Fin d) K} (hRdet : R.det ≠ 0)
    {u₁ u₂ : Matrix (Fin d) (Fin d) K} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h12 : u₁ * u₂ = u₂ * u₁) (hR₁ : u₁ᵀ * R * u₁ = R) (hR₂ : u₂ᵀ * R * u₂ = R) :
    ∀ v ∈ negE u₁ ⊓ posE u₂, (∀ w ∈ negE u₁ ⊓ posE u₂, v ⬝ᵥ R *ᵥ w = 0) → v = 0 := by
  intro v hv h0
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.1 hv
  rw [mem_negE] at hv₁
  rw [mem_posE] at hv₂
  have hu₁ : ∀ x, u₁ *ᵥ (u₁ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h₁, one_mulVec]
  have hu₂ : ∀ x, u₂ *ᵥ (u₂ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h₂, one_mulVec]
  have hc : ∀ x, u₂ *ᵥ (u₁ *ᵥ x) = u₁ *ᵥ (u₂ *ᵥ x) := fun x => by
    rw [mulVec_mulVec, mulVec_mulVec, h12]
  have hφ₁ : ∀ b, v ⬝ᵥ R *ᵥ (u₁ *ᵥ b) = -(v ⬝ᵥ R *ᵥ b) := by
    intro b
    have e := dot_iso hR₁ v (u₁ *ᵥ b)
    rw [hv₁, hu₁, neg_dotProduct] at e
    exact e.symm
  have hφ₂ : ∀ b, v ⬝ᵥ R *ᵥ (u₂ *ᵥ b) = v ⬝ᵥ R *ᵥ b := by
    intro b
    have e := dot_iso hR₂ v (u₂ *ᵥ b)
    rw [hv₂, hu₂] at e
    exact e.symm
  have hall : ∀ x, v ⬝ᵥ R *ᵥ x = 0 := by
    intro x
    set w := (4 : K)⁻¹ • (x - u₁ *ᵥ x + u₂ *ᵥ x - u₁ *ᵥ (u₂ *ᵥ x)) with hw
    have hwW : w ∈ negE u₁ ⊓ posE u₂ := by
      refine Submodule.mem_inf.2 ⟨mem_negE.2 ?_, mem_posE.2 ?_⟩
      · rw [hw, mulVec_smul, mulVec_sub, mulVec_add, mulVec_sub, hu₁, hu₁, ← smul_neg]
        congr 1
        abel
      · rw [hw, mulVec_smul, mulVec_sub, mulVec_add, mulVec_sub]
        simp only [hu₂, hc]
        congr 1
        abel
    have h1 := h0 w hwW
    rw [hw, mulVec_smul, dotProduct_smul, smul_eq_mul, mulVec_sub, mulVec_add, mulVec_sub,
      dotProduct_sub, dotProduct_add, dotProduct_sub, hφ₁, hφ₂, hφ₁, hφ₂] at h1
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have h1' : (4 : K)⁻¹ * (4 * (v ⬝ᵥ R *ᵥ x)) = 0 := by linear_combination h1
    rwa [← mul_assoc, inv_mul_cancel₀ h4, one_mul] at h1'
  have hvR : v ᵥ* R = 0 := by
    funext i
    have e := hall (Pi.single i 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at e
    exact e
  by_contra hv0
  exact hRdet (exists_vecMul_eq_zero_iff.1 ⟨v, hv0, hvR⟩)

theorem similitude_pow_eq {R T : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R)
    {W : Submodule K (Fin d → K)} (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0)
    (hTW : ∀ w ∈ W, T *ᵥ w ∈ W) {l μ : K} (hT2 : ∀ w ∈ W, T *ᵥ (T *ᵥ w) = l • w)
    (hTR : ∀ v ∈ W, ∀ w ∈ W, (T *ᵥ v) ⬝ᵥ R *ᵥ (T *ᵥ w) = μ * (v ⬝ᵥ R *ᵥ w)) :
    μ ^ finrank K W = l ^ finrank K W ∧ IsSquare (l ^ finrank K W) := by
  set u : Module.Basis (Fin (finrank K W)) K W := Module.finBasisOfFinrankEq K W rfl with hu
  have hTW' : ∀ w ∈ W, Matrix.toLin' T w ∈ W := fun w hw => by
    rw [Matrix.toLin'_apply]
    exact hTW w hw
  set f : W →ₗ[K] W := (Matrix.toLin' T).restrict hTW' with hf
  set A := LinearMap.toMatrix u u f with hA
  have hfu : ∀ j, T *ᵥ (u j : Fin d → K) = famOf u A j := by
    intro j
    have e := congrArg Subtype.val (u.sum_repr (f (u j)))
    rw [Submodule.coe_sum] at e
    have e' : (f (u j) : Fin d → K) = T *ᵥ (u j : Fin d → K) := rfl
    calc T *ᵥ (u j : Fin d → K) = (f (u j) : Fin d → K) := e'.symm
      _ = ∑ i, ((u.repr (f (u j)) i • u i : W) : Fin d → K) := e.symm
      _ = famOf u A j := by
        simp only [famOf, Submodule.coe_smul, hA, LinearMap.toMatrix_apply]
  have hG := gramMat_det_ne_zero hR hW u
  have hAGA : Aᵀ * gramMat R u * A = μ • gramMat R u := by
    ext j k
    rw [← famOf_gram, ← hfu j, ← hfu k, hTR _ (u j).2 _ (u k).2, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hff : f * f = l • LinearMap.id := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change Matrix.toLin' T (Matrix.toLin' T (w : Fin d → K)) = l • (w : Fin d → K)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hT2 _ w.2
  have hA2 : A * A = l • (1 : Matrix (Fin (finrank K W)) (Fin (finrank K W)) K) := by
    rw [hA, ← LinearMap.toMatrix_mul, hff, map_smul, LinearMap.toMatrix_id]
  have e1 := congrArg Matrix.det hAGA
  rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin] at e1
  have e2 := congrArg Matrix.det hA2
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at e2
  refine ⟨?_, ⟨A.det, e2.symm⟩⟩
  have e3 : (A.det * A.det) * (gramMat R u).det = μ ^ finrank K W * (gramMat R u).det := by
    linear_combination e1
  rw [e2] at e3
  exact (mul_right_cancel₀ hG e3).symm

end CFSG.ComponentClassification.Burgoyne.DX
