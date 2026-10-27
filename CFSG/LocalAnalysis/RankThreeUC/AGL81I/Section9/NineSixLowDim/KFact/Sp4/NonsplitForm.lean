module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Defs
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic
import CFSG.LieType.SeitzGeneration.ExcHigh.Product
import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private def spPos (i k : Fin 2) : Fin 2 ⊕ Fin 2 := ![Sum.inl i, Sum.inr i] k

private def spBlk (i : Fin 2) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun k l => M (spPos i k) (spPos i l)

private theorem spBlk_zero_spPair (s t : Matrix (Fin 2) (Fin 2) F) :
    spBlk 0 (spPairMatrix s t) = s := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spBlk, spPos, spPairMatrix, spIdx]

private theorem spBlk_one_spPair (s t : Matrix (Fin 2) (Fin 2) F) :
    spBlk 1 (spPairMatrix s t) = t := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spBlk, spPos, spPairMatrix, spIdx]

private theorem spPair_mul (s t s' t' : Matrix (Fin 2) (Fin 2) F) :
    spPairMatrix s t * spPairMatrix s' t' = spPairMatrix (s * s') (t * t') := by
  ext (x|x) (y|y) <;> fin_cases x <;> fin_cases y <;>
    simp [spPairMatrix, spIdx, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

private theorem spPair_one : spPairMatrix (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext (x|x) (y|y) <;> fin_cases x <;> fin_cases y <;>
    simp [spPairMatrix, spIdx]

private theorem spPair_pow (s t : Matrix (Fin 2) (Fin 2) F) (n : ℕ) :
    spPairMatrix s t ^ n = spPairMatrix (s ^ n) (t ^ n) := by
  induction n with
  | zero => simp [spPair_one]
  | succ n ih => rw [pow_succ, ih, spPair_mul, ← pow_succ, ← pow_succ]

private theorem eq_spPair_of_block {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ x y, (spIdx x).1 ≠ (spIdx y).1 → M x y = 0) :
    M = spPairMatrix (spBlk 0 M) (spBlk 1 M) := by
  ext (x|x) (y|y) <;> fin_cases x <;> fin_cases y <;>
    simp [spPairMatrix, spIdx, spBlk, spPos] <;> exact h _ _ (by simp [spIdx])

private theorem spPair_sp {s t : Matrix (Fin 2) (Fin 2) F} (hs : s.det = 1) (ht : t.det = 1) :
    (spPairMatrix s t)ᵀ * fromBlocks 0 1 (-1) 0 * spPairMatrix s t = fromBlocks 0 1 (-1) 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, s = !![a, b; c, d] := ⟨_, _, _, _, s.eta_fin_two⟩
  obtain ⟨a', b', c', d', rfl⟩ : ∃ a b c d, t = !![a, b; c, d] := ⟨_, _, _, _, t.eta_fin_two⟩
  rw [det_fin_two_of] at hs ht
  ext (x|x) (y|y) <;> fin_cases x <;> fin_cases y <;>
    simp [spPairMatrix, spIdx, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      fromBlocks, Matrix.one_apply] <;>
    first
      | ring1
      | linear_combination (norm := ring1) hs
      | linear_combination (norm := ring1) -hs
      | linear_combination (norm := ring1) ht
      | linear_combination (norm := ring1) -ht

open CFSG.ClassicalGroups.Symplectic in
private theorem exists_fixed_of_isElemSp {p : ℕ} (hp : p.Prime)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)} (hE : IsElemSp p E) :
    ∃ g ∈ E, g ≠ 1 ∧ ∃ v : Fin 2 ⊕ Fin 2 → F, v ≠ 0 ∧ (g : Matrix _ _ F) *ᵥ v = v := by
  by_contra hcon
  push Not at hcon
  have : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hE.card_eq]; exact pow_ne_zero 2 hp.ne_zero)
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hE.comm a a.2 b b.2)⟩⟩
  let ρ : Representation F E (Fin 2 ⊕ Fin 2 → F) :=
    (Matrix.toLinAlgEquiv' : 𝕄 ≃ₐ[F] _).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp E.subtype)
  have hcyc := CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic.isCyclic_of_fixedFree
    ρ (fun a ha v hv => by
      by_contra hv0
      exact hcon a a.2 (fun h => ha (Subtype.ext h)) v hv0 hv)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.pow_eq_one g g.2))
  rw [hg, hE.card_eq] at h1
  have := Nat.le_of_dvd hp.pos h1
  nlinarith [hp.two_le]

section Avg

open CFSG.ClassicalGroups.Symplectic

variable {p : ℕ} {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}

private noncomputable def spAvg (p : ℕ) (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  (p : F)⁻¹ • ∑ k ∈ Finset.range p, Matrix.toLin' (G ^ k)

private theorem spAvg_apply (y : Fin 2 ⊕ Fin 2 → F) :
    spAvg p G y = (p : F)⁻¹ • ∑ k ∈ Finset.range p, (G ^ k) *ᵥ y := by
  rw [spAvg, LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [Matrix.toLin'_apply]

private theorem mulVec_spAvg (hG : G ^ p = 1) (y : Fin 2 ⊕ Fin 2 → F) :
    G *ᵥ spAvg p G y = spAvg p G y := by
  rw [spAvg_apply, Matrix.mulVec_smul, Matrix.mulVec_sum]
  congr 1
  simp_rw [Matrix.mulVec_mulVec, ← pow_succ']
  have h1 := Finset.sum_range_succ' (fun k => (G ^ k) *ᵥ y) p
  have h2 := Finset.sum_range_succ (fun k => (G ^ k) *ᵥ y) p
  rw [hG] at h2
  rw [pow_zero] at h1
  exact add_right_cancel (h1.symm.trans h2)

private theorem pow_mulVec_of_fixed {c : Fin 2 ⊕ Fin 2 → F} (hc : G *ᵥ c = c) (k : ℕ) :
    (G ^ k) *ᵥ c = c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hc, ih]

private theorem spAvg_of_fixed (hp0 : (p : F) ≠ 0) {c : Fin 2 ⊕ Fin 2 → F} (hc : G *ᵥ c = c) :
    spAvg p G c = c := by
  rw [spAvg_apply]
  simp_rw [pow_mulVec_of_fixed hc]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul F, smul_smul,
    inv_mul_cancel₀ hp0, one_smul]

private theorem spAvg_sub_self (hp0 : (p : F) ≠ 0) (hG : G ^ p = 1) (y : Fin 2 ⊕ Fin 2 → F) :
    spAvg p G (y - spAvg p G y) = 0 := by
  rw [map_sub, spAvg_of_fixed hp0 (mulVec_spAvg hG y), sub_self]

private theorem mulVec_spAvg_comm {H : 𝕄} (hHG : H * G = G * H)
    (y : Fin 2 ⊕ Fin 2 → F) : H *ᵥ spAvg p G y = spAvg p G (H *ᵥ y) := by
  rw [spAvg_apply, spAvg_apply, Matrix.mulVec_smul, Matrix.mulVec_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ((Commute.pow_right hHG k)).eq]

private theorem spForm_pow_mulVec (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y)
    (k : ℕ) (x y : Fin 2 ⊕ Fin 2 → F) :
    spForm 2 F ((G ^ k) *ᵥ x) ((G ^ k) *ᵥ y) = spForm 2 F x y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGsp, ih]

private theorem spForm_fixed_avg (hp0 : (p : F) ≠ 0)
    (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y)
    {c w : Fin 2 ⊕ Fin 2 → F} (hc : G *ᵥ c = c) (hw : spAvg p G w = 0) :
    spForm 2 F c w = 0 := by
  have h : spForm 2 F c (spAvg p G w) = spForm 2 F c w := by
    rw [spAvg_apply, map_smul, map_sum]
    have : ∀ k ∈ Finset.range p, spForm 2 F c ((G ^ k) *ᵥ w) = spForm 2 F c w := fun k _ => by
      conv_lhs => rw [← pow_mulVec_of_fixed hc k]
      exact spForm_pow_mulVec hGsp k c w
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Nat.cast_smul_eq_nsmul F, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
  rw [← h, hw, map_zero]

private theorem spForm_avg_fixed (hp0 : (p : F) ≠ 0)
    (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y)
    {c w : Fin 2 ⊕ Fin 2 → F} (hc : G *ᵥ c = c) (hw : spAvg p G w = 0) :
    spForm 2 F w c = 0 := by
  rw [← spForm_isAlt.neg_eq, spForm_fixed_avg hp0 hGsp hc hw, neg_zero]

private theorem exists_fixed_partner (hp0 : (p : F) ≠ 0) (hG : G ^ p = 1)
    (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y)
    {e : Fin 2 ⊕ Fin 2 → F} (he0 : e ≠ 0) (he : G *ᵥ e = e) :
    ∃ f, G *ᵥ f = f ∧ spForm 2 F e f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, spForm 2 F e y ≠ 0 := by
    by_contra h
    push Not at h
    exact he0 ((spForm_nondegenerate (m := 2) (K := F)).1 e h)
  have hc : spForm 2 F e (spAvg p G y) ≠ 0 := by
    have h1 := spForm_fixed_avg hp0 hGsp he (spAvg_sub_self hp0 hG y)
    rw [map_sub, sub_eq_zero] at h1
    rwa [← h1]
  refine ⟨(spForm 2 F e (spAvg p G y))⁻¹ • spAvg p G y, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, mulVec_spAvg hG]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]

private theorem exists_avg_partner (hp0 : (p : F) ≠ 0) (hG : G ^ p = 1)
    (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y)
    {e : Fin 2 ⊕ Fin 2 → F} (he0 : e ≠ 0) (he : spAvg p G e = 0) :
    ∃ f, spAvg p G f = 0 ∧ spForm 2 F e f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, spForm 2 F e y ≠ 0 := by
    by_contra h
    push Not at h
    exact he0 ((spForm_nondegenerate (m := 2) (K := F)).1 e h)
  have hc : spForm 2 F e (y - spAvg p G y) ≠ 0 := by
    rwa [map_sub, spForm_avg_fixed hp0 hGsp (mulVec_spAvg hG y) he, sub_zero]
  refine ⟨(spForm 2 F e (y - spAvg p G y))⁻¹ • (y - spAvg p G y), ?_, ?_⟩
  · rw [map_smul, spAvg_sub_self hp0 hG, smul_zero]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]

private theorem exists_avg_ne_zero (hp0 : (p : F) ≠ 0) (hG : G ^ p = 1) (hG1 : G ≠ 1) :
    ∃ w, w ≠ 0 ∧ spAvg p G w = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, G *ᵥ x ≠ x := by
    by_contra h
    push Not at h
    exact hG1 (Matrix.toLin'.injective (by rw [Matrix.toLin'_one]; exact LinearMap.ext h))
  refine ⟨x - spAvg p G x, fun h => hx ?_, spAvg_sub_self hp0 hG x⟩
  rw [sub_eq_zero] at h
  have := mulVec_spAvg hG x
  rwa [← h] at this

private def spPlane (p : ℕ) (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Fin 2 → (Fin 2 ⊕ Fin 2 → F) → Prop :=
  ![fun u => G *ᵥ u = u, fun u => spAvg p G u = 0]

private theorem spPlane_orth (hp0 : (p : F) ≠ 0)
    (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y) {i j : Fin 2} (hij : i ≠ j)
    {u u' : Fin 2 ⊕ Fin 2 → F} (hu : spPlane p G i u) (hu' : spPlane p G j u') :
    spForm 2 F u u' = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spPlane] at hij hu hu'
  · exact spForm_fixed_avg hp0 hGsp hu hu'
  · exact spForm_avg_fixed hp0 hGsp hu' hu

private theorem spPlane_mulVec {H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hHG : H * G = G * H)
    {i : Fin 2} {u : Fin 2 ⊕ Fin 2 → F} (hu : spPlane p G i u) : spPlane p G i (H *ᵥ u) := by
  fin_cases i <;> simp [spPlane] at hu ⊢
  · rw [← hHG, ← Matrix.mulVec_mulVec, hu]
  · rw [← mulVec_spAvg_comm hHG, hu, Matrix.mulVec_zero]

end Avg

section Frame

open CFSG.ClassicalGroups.Symplectic

private theorem frame_gram_apply (b : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → F)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (x y : Fin 2 ⊕ Fin 2) :
    ((of fun i x => b x i)ᵀ * M * of fun i x => b x i) x y = b x ⬝ᵥ (M *ᵥ b y) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc,
    transpose_apply, of_apply]
  exact Finset.sum_comm

private theorem exists_sp_of_frame {b : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → F}
    (hb : ∀ x y, spForm 2 F (b x) (b y) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) x y) :
    ∃ Q ∈ CFSG.Open.StatedSp 2 F, (Q : Matrix _ _ F) = of fun i x => b x i := by
  have hQ : (of fun i x => b x i)ᵀ * fromBlocks 0 1 (-1) 0 * (of fun i x => b x i) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    ext x y
    rw [frame_gram_apply, ← hb x y, spForm_apply]
    rfl
  have hdet : (of fun i x => b x i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hQ
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at this
    exact spJ_det_ne_zero (m := 2) (K := F) this.symm
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, rfl⟩
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  exact hQ

private theorem frame_conj_apply {Q : GL (Fin 2 ⊕ Fin 2) F} (hQ : Q ∈ CFSG.Open.StatedSp 2 F)
    {b : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → F} (hQb : (Q : Matrix _ _ F) = of fun i x => b x i)
    (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (i : Fin 2) (y : Fin 2 ⊕ Fin 2) :
    (((Q⁻¹ : GL _ F) : 𝕄) * H * (Q : 𝕄)) (Sum.inr i) y =
        spForm 2 F (b (Sum.inl i)) (H *ᵥ b y) ∧
      (((Q⁻¹ : GL _ F) : 𝕄) * H * (Q : 𝕄)) (Sum.inl i) y =
        -spForm 2 F (b (Sum.inr i)) (H *ᵥ b y) := by
  have hsp := CFSG.Open.StatedAPI.mem_statedSp_iff.1 hQ
  set N : 𝕄 := ((Q⁻¹ : GL _ F) : 𝕄) * H * (Q : 𝕄)
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((Q⁻¹ : GL _ F) : Matrix _ _ F) = (Q : Matrix _ _ F)ᵀ * fromBlocks 0 1 (-1) 0 := by
    calc _ = (Q : Matrix _ _ F)ᵀ * fromBlocks 0 1 (-1) 0 * (Q : Matrix _ _ F) *
          ((Q⁻¹ : GL _ F) : Matrix _ _ F) := by rw [hsp]
      _ = _ := by
        rw [Matrix.mul_assoc ((Q : 𝕄)ᵀ * fromBlocks 0 1 (-1) 0), Units.mul_inv, Matrix.mul_one]
  have key : ∀ z, ((fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * N) z y =
      spForm 2 F (b z) (H *ᵥ b y) := by
    intro z
    have : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * N =
        (Q : Matrix _ _ F)ᵀ * (fromBlocks 0 1 (-1) 0 * H) * (Q : Matrix _ _ F) := by
      simp only [N, ← Matrix.mul_assoc, hJ]
    rw [this, hQb, frame_gram_apply, spForm_apply, ← Matrix.mulVec_mulVec]
    rfl
  constructor
  · rw [← key]
    simp [fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · rw [← key]
    simp [fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

end Frame

section Core

open CFSG.ClassicalGroups.Symplectic

private theorem spGram_of {p : ℕ} {G : 𝕄} (hp0 : (p : F) ≠ 0)
    (hGsp : ∀ x y, spForm 2 F (G *ᵥ x) (G *ᵥ y) = spForm 2 F x y)
    {e₀ f₀ e₁ f₁ : Fin 2 ⊕ Fin 2 → F} (he₀ : G *ᵥ e₀ = e₀) (hf₀ : G *ᵥ f₀ = f₀)
    (he₁ : spAvg p G e₁ = 0) (hf₁ : spAvg p G f₁ = 0) (h₀ : spForm 2 F e₀ f₀ = 1)
    (h₁ : spForm 2 F e₁ f₁ = 1) (x y : Fin 2 ⊕ Fin 2) :
    spForm 2 F (Sum.elim ![e₀, e₁] ![f₀, f₁] x) (Sum.elim ![e₀, e₁] ![f₀, f₁] y) =
      (fromBlocks 0 1 (-1) 0 : 𝕄) x y := by
  have skew : ∀ u w, spForm 2 F w u = -spForm 2 F u w :=
    fun u w => (spForm_isAlt.neg_eq u w).symm
  have h₀' : spForm 2 F f₀ e₀ = -1 := by rw [skew, h₀]
  have h₁' : spForm 2 F f₁ e₁ = -1 := by rw [skew, h₁]
  rcases x with x|x <;> rcases y with y|y <;> fin_cases x <;> fin_cases y <;>
    simp [fromBlocks, spForm_self, h₀, h₁, h₀', h₁', spForm_fixed_avg hp0 hGsp he₀ he₁,
      spForm_fixed_avg hp0 hGsp he₀ hf₁, spForm_fixed_avg hp0 hGsp hf₀ he₁,
      spForm_fixed_avg hp0 hGsp hf₀ hf₁, spForm_avg_fixed hp0 hGsp he₀ he₁,
      spForm_avg_fixed hp0 hGsp he₀ hf₁, spForm_avg_fixed hp0 hGsp hf₀ he₁,
      spForm_avg_fixed hp0 hGsp hf₀ hf₁]

private theorem exists_conj_block {p : ℕ} (hp : p.Prime) (hp0 : (p : F) ≠ 0)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)} (hE : IsElemSp p E) :
    ∃ P ∈ CFSG.Open.StatedSp 2 F, ∃ g ∈ E, g ≠ 1 ∧
      (∀ h ∈ E, ((P * h * P⁻¹ : GL _ F) : 𝕄) =
        spPairMatrix (spBlk 0 ((P * h * P⁻¹ : GL _ F) : 𝕄))
          (spBlk 1 ((P * h * P⁻¹ : GL _ F) : 𝕄))) ∧
      spBlk 0 ((P * g * P⁻¹ : GL _ F) : 𝕄) = 1 := by
  obtain ⟨g, hgE, hg1, v, hv0, hv⟩ := exists_fixed_of_isElemSp hp hE
  have hG : (g : 𝕄) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hE.pow_eq_one g hgE, Units.val_one]
  have hGsp := (mem_statedSp_iff_forall g).1 (hE.le_sp hgE)
  have hG1 : (g : 𝕄) ≠ 1 := fun h => hg1 (Units.ext h)
  obtain ⟨f₀, hf₀, h₀⟩ := exists_fixed_partner hp0 hG hGsp hv0 hv
  obtain ⟨e₁, he₁0, he₁⟩ := exists_avg_ne_zero hp0 hG hG1
  obtain ⟨f₁, hf₁, h₁⟩ := exists_avg_partner hp0 hG hGsp he₁0 he₁
  obtain ⟨Q, hQ, hQb⟩ := exists_sp_of_frame (spGram_of hp0 hGsp hv hf₀ he₁ hf₁ h₀ h₁)
  have hbP : ∀ x, spPlane p (g : 𝕄) (spIdx x).1 (Sum.elim ![v, e₁] ![f₀, f₁] x) := by
    rintro (x|x) <;> fin_cases x <;> simp [spPlane, spIdx, hv, hf₀, he₁, hf₁]
  have hconj : ∀ h : GL (Fin 2 ⊕ Fin 2) F,
      ((Q⁻¹ * h * Q⁻¹⁻¹ : GL _ F) : 𝕄) = ((Q⁻¹ : GL _ F) : 𝕄) * h * Q := by
    intro h
    rw [inv_inv, Units.val_mul, Units.val_mul]
  refine ⟨Q⁻¹, inv_mem hQ, g, hgE, hg1, fun h hh => ?_, ?_⟩
  · rw [hconj]
    apply eq_spPair_of_block
    have hhG : (h : 𝕄) * g = g * h := by
      rw [← Units.val_mul, ← Units.val_mul, hE.comm h hh g hgE]
    rintro (i|i) y hxy
    · rw [(frame_conj_apply hQ hQb _ i y).2,
        spPlane_orth hp0 hGsp hxy (hbP (Sum.inr i)) (spPlane_mulVec hhG (hbP y)), neg_zero]
    · rw [(frame_conj_apply hQ hQb _ i y).1,
        spPlane_orth hp0 hGsp hxy (hbP (Sum.inl i)) (spPlane_mulVec hhG (hbP y))]
  · rw [hconj]
    have hb := spGram_of hp0 hGsp hv hf₀ he₁ hf₁ h₀ h₁
    have hrow : ∀ x y, (spIdx y).1 = 0 →
        (((Q⁻¹ : GL _ F) : 𝕄) * (g : 𝕄) * (Q : 𝕄)) x y = (1 : 𝕄) x y := by
      intro x y hy
      have hgy : (g : 𝕄) *ᵥ Sum.elim ![v, e₁] ![f₀, f₁] y = Sum.elim ![v, e₁] ![f₀, f₁] y := by
        have := hbP y
        rw [hy] at this
        simpa [spPlane] using this
      rcases x with i|i
      · rw [(frame_conj_apply hQ hQb _ i y).2, hgy, hb]
        rcases y with j|j <;> simp [fromBlocks, Matrix.one_apply]
      · rw [(frame_conj_apply hQ hQb _ i y).1, hgy, hb]
        rcases y with j|j <;> simp [fromBlocks, Matrix.one_apply]
    ext k l
    simp only [spBlk, of_apply]
    rw [hrow _ _ (by fin_cases l <;> rfl)]
    fin_cases k <;> fin_cases l <;> simp [spPos, Matrix.one_apply]

end Core

section Finish

open CFSG.ClassicalGroups.Symplectic
open scoped MatrixGroups

private theorem natCast_ne_zero_zmod {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) :
    (p : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h).symm

private theorem eq_one_of_pow_eq_one_zmod {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ q - 1) {x : ZMod q} (hx : x ^ p = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hx
    exact zero_ne_one hx
  have hcop : p.Coprime (q - 1) := (Nat.coprime_or_dvd_of_prime hp _).resolve_right h
  have := pow_gcd_eq_one.2 ⟨hx, ZMod.pow_card_sub_one_eq_one hx0⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

private theorem conj_pow_eq_one {E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)} {p : ℕ} (hE : IsElemSp p E)
    (P : GL (Fin 2 ⊕ Fin 2) F) {g : GL (Fin 2 ⊕ Fin 2) F} (hg : g ∈ E) :
    ((P * g * P⁻¹ : GL _ F) : 𝕄) ^ p = 1 := by
  rw [← Units.val_pow_eq_pow_val, conj_pow, hE.pow_eq_one g hg, mul_one, mul_inv_cancel,
    Units.val_one]

private theorem spPair_pow_eq_one {s t : Matrix (Fin 2) (Fin 2) F} {p : ℕ}
    (h : spPairMatrix s t ^ p = 1) : s ^ p = 1 ∧ t ^ p = 1 := by
  rw [spPair_pow, ← spPair_one] at h
  exact ⟨by simpa [spBlk_zero_spPair] using congrArg (spBlk 0) h,
    by simpa [spBlk_one_spPair] using congrArg (spBlk 1) h⟩

private theorem ne_one_of_conj_ne_one {P g : GL (Fin 2 ⊕ Fin 2) F} (hg : g ≠ 1) :
    ((P * g * P⁻¹ : GL _ F) : 𝕄) ≠ 1 := by
  intro h
  apply hg
  have h' : P * g * P⁻¹ = 1 := Units.ext h
  rwa [mul_inv_eq_one, mul_eq_left] at h'

private theorem dvd_of_mem_GL_two {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {β : Matrix (Fin 2) (Fin 2) (ZMod q)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    p ∣ q - 1 ∨ p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : q.Prime := Fact.out
  let u : GL (Fin 2) (ZMod q) := Units.ofPowEqOne β p hβ hp.ne_zero
  have hu : orderOf u = p :=
    orderOf_eq_prime (Units.pow_ofPowEqOne hβ hp.ne_zero) (fun h => hβ1 (by
      simpa [u] using congrArg Units.val h))
  have hdvd := orderOf_dvd_natCard u
  rw [hu, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at hdvd
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hdvd
  rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1, sq,
    ← Nat.mul_sub_one] at hdvd
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact absurd h hpq'
    · exact Or.inl h

section SLConj

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

private theorem mem_zpowers_of_commute_SL (hpK : (p : K) ≠ 0) {a z : SL(2, K)} (ha : a ^ p = 1)
    (hz : z ^ p = 1) (hz1 : z ≠ 1) (hc : Commute a z) : a ∈ Subgroup.zpowers z := by
  have hpair : ({a, z} : Set SL(2, K)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    exacts [Commute.refl _, hc, hc.symm, Commute.refl _]
  have hcomm := Subgroup.isMulCommutative_closure hpair
  have hexp : ∀ x ∈ Subgroup.closure ({a, z} : Set SL(2, K)), x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> assumption
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      have : Commute x y := by
        have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [this.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hle := CFSG.LieType.SeitzGeneration.ExcHigh.card_le_of_isElemAbelian_specialLinear_two
    hpK (F := Subgroup.closure ({a, z} : Set SL(2, K))) ⟨hcomm, hexp⟩
  have hzH : Subgroup.zpowers z ≤ Subgroup.closure ({a, z} : Set SL(2, K)) :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hcz : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hz hz1]
  rw [Subgroup.eq_of_le_of_card_ge hzH (by rw [hcz]; exact hle)]
  exact Subgroup.subset_closure (by simp)

omit [Finite K] in
private theorem isPGroup_zpowers_SL {a : SL(2, K)} (ha : a ^ p = 1) (ha1 : a ≠ 1) :
    IsPGroup p (Subgroup.zpowers a) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ha ha1, pow_one])

private theorem exists_central_of_sylow_SL (S : Sylow p SL(2, K)) {a : SL(2, K)} (haS : a ∈ S)
    (ha1 : a ≠ 1) : ∃ z : SL(2, K), z ^ p = 1 ∧ z ≠ 1 ∧ ∀ y ∈ S, Commute y z := by
  have : Nontrivial S := ⟨⟨⟨a, haS⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
  have hpS : IsPGroup p S := S.isPGroup'
  have := hpS.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := ((hpS.to_subgroup (Subgroup.center S)).nontrivial_iff_card).1 ‹_›
  have : Fintype (Subgroup.center S) := Fintype.ofFinite _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card (G := Subgroup.center S) p (by
    rw [Fintype.card_eq_nat_card, hcard]; exact dvd_pow_self p hn.ne')
  have hz : orderOf ((w : S) : SL(2, K)) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  refine ⟨((w : S) : SL(2, K)), ?_, fun h => ?_, fun y hy => ?_⟩
  · have := pow_orderOf_eq_one ((w : S) : SL(2, K))
    rwa [hz] at this
  · rw [h, orderOf_one] at hz
    exact (Fact.out : p.Prime).one_lt.ne hz
  · have := Subgroup.mem_center_iff.1 w.2 ⟨y, hy⟩
    exact congrArg Subtype.val this

private theorem exists_conj_pow_SL (hpK : (p : K) ≠ 0) {a b : SL(2, K)} (ha : a ^ p = 1)
    (ha1 : a ≠ 1)
    (hb : b ^ p = 1) (hb1 : b ≠ 1) : ∃ s : SL(2, K), ∃ m : ℕ, s * b ^ m * s⁻¹ = a := by
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_SL ha ha1).exists_le_sylow
  obtain ⟨T, hT⟩ := (isPGroup_zpowers_SL hb hb1).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq SL(2, K) T S
  have hb' : x * b * x⁻¹ ∈ S := by
    have := Subgroup.smul_mem_pointwise_smul b (MulAut.conj x) (T : Subgroup SL(2, K))
      (hT (Subgroup.mem_zpowers b))
    rwa [← Sylow.coe_subgroup_smul, hx, MulAut.smul_def, MulAut.conj_apply] at this
  have haS : a ∈ S := hS (Subgroup.mem_zpowers a)
  obtain ⟨z, hz, hz1, hcz⟩ := exists_central_of_sylow_SL S haS ha1
  have hb'p : (x * b * x⁻¹) ^ p = 1 := by rw [conj_pow, hb, mul_one, mul_inv_cancel]
  have hb'1 : x * b * x⁻¹ ≠ 1 := by
    rwa [Ne, mul_inv_eq_one, mul_eq_left]
  have hbz := mem_zpowers_of_commute_SL hpK hb'p hz hz1 (hcz _ hb')
  have haz := mem_zpowers_of_commute_SL hpK ha hz hz1 (hcz _ haS)
  have heq : Subgroup.zpowers (x * b * x⁻¹) = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hbz) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hz hz1,
        orderOf_eq_prime hb'p hb'1])
  rw [← heq, ← mem_powers_iff_mem_zpowers] at haz
  obtain ⟨m, hm⟩ := haz
  exact ⟨x, m, by rw [← conj_pow]; exact hm⟩

end SLConj

private theorem exists_conj_pow_mat {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hpK : (p : K) ≠ 0) {α β : Matrix (Fin 2) (Fin 2) K} (hαp : α ^ p = 1) (hdetα : α.det = 1)
    (hα1 : α ≠ 1) (hβp : β ^ p = 1) (hdetβ : β.det = 1) (hβ1 : β ≠ 1) :
    ∃ s : SL(2, K), ∃ m : ℕ,
      (s : Matrix (Fin 2) (Fin 2) K) * β ^ m * ((s⁻¹ : SL(2, K)) : Matrix _ _ K) = α := by
  obtain ⟨s, m, hsm⟩ := exists_conj_pow_SL hpK (a := ⟨α, hdetα⟩) (b := ⟨β, hdetβ⟩)
    (Subtype.ext ((Matrix.SpecialLinearGroup.coe_pow ⟨α, hdetα⟩ p).trans hαp))
    (fun e => hα1 (congrArg Subtype.val e))
    (Subtype.ext ((Matrix.SpecialLinearGroup.coe_pow ⟨β, hdetβ⟩ p).trans hβp))
    (fun e => hβ1 (congrArg Subtype.val e))
  refine ⟨s, m, ?_⟩
  have := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K)) hsm
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  exact this

private theorem spBlk_spPair (i : Fin 2) (s t : Matrix (Fin 2) (Fin 2) F) :
    spBlk i (spPairMatrix s t) = ![s, t] i := by
  fin_cases i
  · exact spBlk_zero_spPair s t
  · exact spBlk_one_spPair s t

private noncomputable def spBlkHom (i : Fin 2) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (P : GL (Fin 2 ⊕ Fin 2) F)
    (hblock : ∀ h ∈ E, ((P * h * P⁻¹ : GL _ F) : 𝕄) =
      spPairMatrix (spBlk 0 ((P * h * P⁻¹ : GL _ F) : 𝕄)) (spBlk 1 ((P * h * P⁻¹ : GL _ F) : 𝕄))) :
    E →* Matrix (Fin 2) (Fin 2) F where
  toFun h := spBlk i ((P * (h : GL _ F) * P⁻¹ : GL _ F) : 𝕄)
  map_one' := by
    rw [OneMemClass.coe_one, mul_one, mul_inv_cancel, Units.val_one, ← spPair_one, spBlk_spPair]
    fin_cases i <;> rfl
  map_mul' a b := by
    have hab : P * ((a * b : E) : GL _ F) * P⁻¹ =
        (P * (a : GL _ F) * P⁻¹) * (P * (b : GL _ F) * P⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    rw [hab, Units.val_mul, hblock a a.2, hblock b b.2, spPair_mul, spBlk_spPair, spBlk_spPair,
      spBlk_spPair]
    fin_cases i <;> rfl

private theorem det_spBlkHom {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (h₁ : ¬ p ∣ q - 1)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E) (i : Fin 2)
    (P : GL (Fin 2 ⊕ Fin 2) (ZMod q))
    (hblock : ∀ h ∈ E, ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) =
      spPairMatrix (spBlk 0 ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)))
        (spBlk 1 ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)))) (h : E) :
    (spBlkHom i P hblock h).det = 1 := by
  refine eq_one_of_pow_eq_one_zmod hp h₁ ?_
  have hh : h ^ p = 1 := Subtype.ext (by simpa using hE.pow_eq_one h h.2)
  rw [← det_pow, ← map_pow, hh, map_one, det_one]

private noncomputable def spBlkSL {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (h₁ : ¬ p ∣ q - 1)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E)
    (P : GL (Fin 2 ⊕ Fin 2) (ZMod q))
    (hblock : ∀ h ∈ E, ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) =
      spPairMatrix (spBlk 0 ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)))
        (spBlk 1 ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)))) :
    E →* SL(2, ZMod q) where
  toFun h := ⟨spBlkHom 1 P hblock h, det_spBlkHom hp h₁ hE 1 P hblock h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

private theorem exists_ker_spBlkSL {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    (h₁ : ¬ p ∣ q - 1) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E)
    (P : GL (Fin 2 ⊕ Fin 2) (ZMod q))
    (hblock : ∀ h ∈ E, ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) =
      spPairMatrix (spBlk 0 ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)))
        (spBlk 1 ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)))) :
    ∃ h : E, h ≠ 1 ∧
      spBlk 1 ((P * (h : GL _ (ZMod q)) * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set ρ := spBlkSL hp h₁ hE P hblock
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hE.comm a a.2 b b.2)
  have hel : CFSG.Open.IsElemAbelian p ρ.range := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hcomm]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hE.pow_eq_one a a.2),
        map_one]
  have hle := CFSG.LieType.SeitzGeneration.ExcHigh.card_le_of_isElemAbelian_specialLinear_two
    (natCast_ne_zero_zmod hp hpq) hel
  have hni : ¬ Function.Injective ρ := fun hinj => by
    have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [hE.card_eq] at h1
    rw [← h1] at hle
    nlinarith [hp.two_le]
  rw [injective_iff_map_eq_one] at hni
  push Not at hni
  obtain ⟨h, hρ, hne⟩ := hni
  exact ⟨h, hne, congrArg Subtype.val hρ⟩

private noncomputable def spPairGL (s : SL(2, F)) : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨spPairMatrix 1 (s : Matrix (Fin 2) (Fin 2) F),
    spPairMatrix 1 ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F),
    by rw [spPair_mul, Matrix.one_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, spPair_one],
    by rw [spPair_mul, Matrix.one_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, spPair_one]⟩

private theorem spPairGL_mem (s : SL(2, F)) : spPairGL s ∈ CFSG.Open.StatedSp 2 F := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  exact spPair_sp det_one s.2

private theorem conj_spPairGL (s : SL(2, F)) {x : GL (Fin 2 ⊕ Fin 2) F}
    {a b : Matrix (Fin 2) (Fin 2) F}
    (hx : (x : 𝕄) = spPairMatrix a b) :
    ((spPairGL s * x * (spPairGL s)⁻¹ : GL _ F) : 𝕄) =
      spPairMatrix a ((s : Matrix (Fin 2) (Fin 2) F) * b * ((s⁻¹ : SL(2, F)) : Matrix _ _ F)) := by
  rw [Units.val_mul, Units.val_mul, hx]
  change spPairMatrix 1 (s : Matrix (Fin 2) (Fin 2) F) * spPairMatrix a b *
    spPairMatrix 1 ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _
  rw [spPair_mul, spPair_mul, Matrix.one_mul, Matrix.mul_one]

private theorem conj_mul_apply (D P x : GL (Fin 2 ⊕ Fin 2) F) :
    (MulAut.conj (D * P)).toMonoidHom x = D * (P * x * P⁻¹) * D⁻¹ := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem not_dvd_sub_one_of_dvd_add_one {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ q + 1) : ¬ p ∣ q - 1 := by
  intro h
  have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hdvd h
  rw [show q + 1 - (q - 1) = 2 by have := hq.two_le; omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

private theorem spBlk_conj_props {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (h₁ : ¬ p ∣ q - 1)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E)
    (P : GL (Fin 2 ⊕ Fin 2) (ZMod q)) {h : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hh : h ∈ E)
    {α β : Matrix (Fin 2) (Fin 2) (ZMod q)}
    (hN : ((P * h * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) = spPairMatrix α β) :
    α ^ p = 1 ∧ α.det = 1 ∧ β ^ p = 1 ∧ β.det = 1 := by
  have h1 := spPair_pow_eq_one (hN ▸ conj_pow_eq_one hE P hh)
  refine ⟨h1.1, eq_one_of_pow_eq_one_zmod hp h₁ ?_, h1.2, eq_one_of_pow_eq_one_zmod hp h₁ ?_⟩
  · rw [← det_pow, h1.1, det_one]
  · rw [← det_pow, h1.2, det_one]

end Finish

theorem exists_conj_spPair {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E)
    (hdvd : p ∣ q + 1) :
    ∃ P ∈ CFSG.Open.StatedSp 2 (ZMod q), ∃ s₀ : GL (Fin 2) (ZMod q),
      (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 ∧ orderOf s₀ = p ∧
      (∃ g ∈ E.map (MulAut.conj P).toMonoidHom,
        (g : Matrix _ _ (ZMod q)) = spPairMatrix (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q)) 1) ∧
      ∃ g ∈ E.map (MulAut.conj P).toMonoidHom,
        (g : Matrix _ _ (ZMod q)) = spPairMatrix 1 (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h₁ := not_dvd_sub_one_of_dvd_add_one Fact.out hp hp2 hdvd
  have hp0 := natCast_ne_zero_zmod (q := q) hp hpq
  obtain ⟨P, hP, g, hgE, hg1, hblock, hblk0⟩ := exists_conj_block hp hp0 hE
  obtain ⟨h, hne, hh1⟩ := exists_ker_spBlkSL hp hpq h₁ hE P hblock
  have hNh := hblock h h.2
  rw [hh1] at hNh
  have hNg := hblock g hgE
  rw [hblk0] at hNg
  obtain ⟨hαp, hdetα, -, -⟩ := spBlk_conj_props hp h₁ hE P h.2 hNh
  obtain ⟨-, -, hβp, hdetβ⟩ := spBlk_conj_props hp h₁ hE P hgE hNg
  set α := spBlk 0 ((P * (h : GL _ (ZMod q)) * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q))
  set β := spBlk 1 ((P * g * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q))
  have hα1 : α ≠ 1 := by
    intro e
    rw [e, spPair_one] at hNh
    exact ne_one_of_conj_ne_one (fun e' => hne (Subtype.ext e')) hNh
  have hβ1 : β ≠ 1 := by
    intro e
    rw [e, spPair_one] at hNg
    exact ne_one_of_conj_ne_one hg1 hNg
  obtain ⟨s, m, hsm'⟩ := exists_conj_pow_mat hp0 hαp hdetα hα1 hβp hdetβ hβ1
  refine ⟨spPairGL s * P, mul_mem (spPairGL_mem s) hP, Units.ofPowEqOne α p hαp hp.ne_zero,
    by rw [Units.val_ofPowEqOne]; exact hdetα,
    orderOf_eq_prime (Units.pow_ofPowEqOne _ _) (fun e => hα1 (by
      simpa using congrArg Units.val e)),
    ⟨_, Subgroup.mem_map_of_mem _ h.2, ?_⟩, ⟨_, Subgroup.mem_map_of_mem _ (pow_mem hgE m), ?_⟩⟩
  · rw [Units.val_ofPowEqOne, conj_mul_apply, conj_spPairGL s hNh, Matrix.mul_one,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · have hNm : ((P * g ^ m * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) =
        spPairMatrix 1 (β ^ m) := by
      rw [← conj_pow, Units.val_pow_eq_pow_val, hNg, spPair_pow, one_pow]
    rw [Units.val_ofPowEqOne, conj_mul_apply, conj_spPairGL s hNm, hsm']

theorem false_of_isElemSp {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hE : IsElemSp p E)
    (h₁ : ¬ p ∣ q - 1) (h₂ : ¬ p ∣ q + 1) : False := by
  have _ := hp2
  obtain ⟨P, -, g, hgE, hg1, hblock, hblk0⟩ :=
    exists_conj_block hp (natCast_ne_zero_zmod hp hpq) hE
  have hN := hblock g hgE
  rw [hblk0] at hN
  have hβ := (spPair_pow_eq_one (hN ▸ conj_pow_eq_one hE P hgE)).2
  have hβ1 : spBlk 1 ((P * g * P⁻¹ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) ≠ 1 := by
    intro h
    rw [h, spPair_one] at hN
    exact ne_one_of_conj_ne_one hg1 hN
  rcases dvd_of_mem_GL_two hp hpq hβ hβ1 with h | h
  · exact h₁ h
  · exact h₂ h

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
