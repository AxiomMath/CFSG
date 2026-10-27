module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCen

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Def

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

abbrev vU (v : ι → K) : ι₂ → K := fun a => v (ou oe a)

@[expose] noncomputable def qAlpha (u : Fin 2 → ι₂ → K) (c : K) (v : ι → K) (s : Fin 2) : K :=
  Q₂.polarBilin (vU oe v) (u s) + Q₂ (u s) * v (oy oe s) +
    if s = 1 then c * v (oy oe 0) else (c + Q₂.polarBilin (u 0) (u 1)) * v (oy oe 1)

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem qAlpha_add (u : Fin 2 → ι₂ → K) (c : K) (v w : ι → K) (s : Fin 2) :
    qAlpha oe Q₂ u c (v + w) s = qAlpha oe Q₂ u c v s + qAlpha oe Q₂ u c w s := by
  have h : vU oe (v + w) = vU oe v + vU oe w := rfl
  simp only [qAlpha, h, map_add, LinearMap.add_apply, Pi.add_apply]
  split_ifs <;> ring

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem qAlpha_smul (u : Fin 2 → ι₂ → K) (c : K) (a : K) (v : ι → K) (s : Fin 2) :
    qAlpha oe Q₂ u c (a • v) s = a * qAlpha oe Q₂ u c v s := by
  have h : vU oe (a • v) = a • vU oe v := rfl
  simp only [qAlpha, h, map_smul, LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply]
  split_ifs <;> ring

@[expose] noncomputable def qEL (u : Fin 2 → ι₂ → K) (c : K) : (ι → K) →ₗ[K] (ι → K) where
  toFun v := oVec oe (vU oe v + ∑ t, v (oy oe t) • u t)
    (Sum.elim (fun s => v (ox oe s) + qAlpha oe Q₂ u c v s) (fun s => v (oy oe s)))
  map_add' v w := by
    refine oVec_ext oe (fun a => ?_) (fun b => ?_)
    · simp only [oVec_apply_inl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [vU, add_mul, Finset.sum_add_distrib]
      ring
    · rcases b with s | s
      · simp only [oVec_apply_inr, Sum.elim_inl, Pi.add_apply, qAlpha_add]
        ring
      · simp only [oVec_apply_inr, Sum.elim_inr, Pi.add_apply]
  map_smul' a v := by
    refine oVec_ext oe (fun b => ?_) (fun b => ?_)
    · simp only [oVec_apply_inl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      simp only [vU, mul_add, Finset.mul_sum, mul_assoc]
    · rcases b with s | s
      · simp only [oVec_apply_inr, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, qAlpha_smul,
          RingHom.id_apply]
        ring
      · simp only [oVec_apply_inr, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]

@[expose] noncomputable def qE (u : Fin 2 → ι₂ → K) (c : K) : Matrix ι ι K :=
  LinearMap.toMatrix' (qEL oe Q₂ u c)

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_mulVec (u : Fin 2 → ι₂ → K) (c : K) (v : ι → K) :
    qE oe Q₂ u c *ᵥ v = oVec oe (vU oe v + ∑ t, v (oy oe t) • u t)
      (Sum.elim (fun s => v (ox oe s) + qAlpha oe Q₂ u c v s) (fun s => v (oy oe s))) := by
  rw [qE, LinearMap.toMatrix'_mulVec]
  rfl

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_mulVec_ou (u : Fin 2 → ι₂ → K) (c : K) (v : ι → K) (a : ι₂) :
    (qE oe Q₂ u c *ᵥ v) (ou oe a) = v (ou oe a) + ∑ t, v (oy oe t) * u t a := by
  rw [qE_mulVec, oVec_apply_inl]
  simp

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_mulVec_ox (u : Fin 2 → ι₂ → K) (c : K) (v : ι → K) (s : Fin 2) :
    (qE oe Q₂ u c *ᵥ v) (ox oe s) = v (ox oe s) + qAlpha oe Q₂ u c v s := by
  rw [qE_mulVec, oVec_apply_inr, Sum.elim_inl]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_mulVec_oy (u : Fin 2 → ι₂ → K) (c : K) (v : ι → K) (s : Fin 2) :
    (qE oe Q₂ u c *ᵥ v) (oy oe s) = v (oy oe s) := by
  rw [qE_mulVec, oVec_apply_inr, Sum.elim_inr]

end Def

section Mul

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι] [DecidableEq ι]
  (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

omit [CharP K 2] in
theorem qE_zero : qE oe Q₂ 0 0 = 1 := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [one_mulVec]
  funext i
  obtain ⟨d, rfl⟩ := oe.surjective i
  rcases d with a | s | s
  · rw [qE_mulVec_ou]
    simp
  · rw [qE_mulVec_ox]
    simp [qAlpha]
  · rw [qE_mulVec_oy]

theorem qE_mul (u u' : Fin 2 → ι₂ → K) (c c' : K) :
    qE oe Q₂ u c * qE oe Q₂ u' c' =
      qE oe Q₂ (u + u') (c + c' + Q₂.polarBilin (u' 0) (u 1)) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec]
  funext i
  obtain ⟨d, rfl⟩ := oe.surjective i
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsym := polarBilin_comm Q₂
  rcases d with a | s | s
  · simp only [qE_mulVec_ou, qE_mulVec_oy, Fin.sum_univ_two, Pi.add_apply]
    ring
  · rw [qE_mulVec_ox, qE_mulVec_ox, qE_mulVec_ox]
    have hU : vU oe (qE oe Q₂ u' c' *ᵥ v) = vU oe v + ∑ t, v (oy oe t) • u' t := by
      funext a
      simp only [vU]
      rw [qE_mulVec_ou]
      simp
    have hy : ∀ t, (qE oe Q₂ u' c' *ᵥ v) (oy oe t) = v (oy oe t) := qE_mulVec_oy oe Q₂ u' c' v
    simp only [qAlpha, hU, hy, Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, Pi.add_apply, quad_add]
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, ↓reduceIte]
      linear_combination (-(v (oy oe 1) * Q₂.polarBilin (u' 0) (u 1))) * h2 +
        v (oy oe 1) * hsym (u' 1) (u 0) + v (oy oe 0) * hsym (u' 0) (u 0)
    · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte]
      linear_combination v (oy oe 1) * hsym (u' 1) (u 1)
  · simp only [qE_mulVec_oy]

end Mul

section Forms

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem quad_oVec (w : ι₂ → K) (z : Fin 2 ⊕ Fin 2 → K) :
    Q (oVec oe w z) = Q₂ w + StatedQuadPlus 2 K z := by
  rw [hQ, oVec_inl, oVec_inr]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_oVec (w w' : ι₂ → K) (z z' : Fin 2 ⊕ Fin 2 → K) :
    Q.polarBilin (oVec oe w z) (oVec oe w' z') =
      Q₂.polarBilin w w' + (quadPlus 2 K).polarBilin z z' := by
  rw [polarBilin_oe hQ, oVec_inl, oVec_inl, oVec_inr, oVec_inr]

omit hQ [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_quadPlus_two (z z' : Fin 2 ⊕ Fin 2 → K) :
    (quadPlus 2 K).polarBilin z z' = z (.inl 0) * z' (.inr 0) + z (.inr 0) * z' (.inl 0) +
      (z (.inl 1) * z' (.inr 1) + z (.inr 1) * z' (.inl 1)) := by
  rw [polarBilin_apply_apply, polar, coe_quadPlus]
  simp only [StatedQuadPlus, Fin.sum_univ_two, Pi.add_apply]
  ring

variable [CharP K 2]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_isometry (u : Fin 2 → ι₂ → K) (c : K) (v : ι → K) :
    Q (qE oe Q₂ u c *ᵥ v) = Q v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [qE_mulVec, quad_oVec hQ, hQ v]
  simp only [StatedQuadPlus, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, quad_add,
    QuadraticMap.map_smul, map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, qAlpha,
    Fin.isValue, zero_ne_one, ↓reduceIte]
  linear_combination (v (oy oe 0) * Q₂.polarBilin (vU oe v) (u 0) +
    v (oy oe 1) * Q₂.polarBilin (vU oe v) (u 1) + v (oy oe 0) * v (oy oe 0) * Q₂ (u 0) +
    v (oy oe 1) * v (oy oe 1) * Q₂ (u 1) + c * v (oy oe 0) * v (oy oe 1) +
    v (oy oe 0) * v (oy oe 1) * Q₂.polarBilin (u 0) (u 1)) * h2

end Forms

section Commute

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι] [DecidableEq ι]
  (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

omit [CharP K 2] in
theorem oN₀_mulVec (v : ι → K) :
    oN₀ K oe *ᵥ v = Pi.single (ox oe 1) (v (oy oe 0)) + Pi.single (ox oe 0) (v (oy oe 1)) := by
  rw [oN₀, add_mulVec, single_mulVec, single_mulVec, one_mul, one_mul]
  rfl

omit [CharP K 2] in
theorem qE_mulVec_single_ox (u : Fin 2 → ι₂ → K) (c a : K) (s : Fin 2) :
    qE oe Q₂ u c *ᵥ Pi.single (ox oe s) a = Pi.single (ox oe s) a := by
  funext i
  obtain ⟨d, rfl⟩ := oe.surjective i
  rcases d with b | r | r
  · rw [qE_mulVec_ou]
    simp
  · rw [qE_mulVec_ox]
    have hU : vU oe (Pi.single (ox oe s) a) = 0 := by
      funext b
      simp [vU]
    simp [qAlpha, hU, Pi.single_apply]
  · rw [qE_mulVec_oy]

omit [CharP K 2] in
theorem qE_commute (u : Fin 2 → ι₂ → K) (c : K) :
    qE oe Q₂ u c * oN₀ K oe = oN₀ K oe * qE oe Q₂ u c := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, oN₀_mulVec, oN₀_mulVec, mulVec_add,
    qE_mulVec_single_ox, qE_mulVec_single_ox, qE_mulVec_oy, qE_mulVec_oy]

theorem qE_mul_inv (u : Fin 2 → ι₂ → K) (c : K) :
    qE oe Q₂ u c * qE oe Q₂ u (c + Q₂.polarBilin (u 0) (u 1)) = 1 := by
  rw [qE_mul, ← qE_zero oe Q₂]
  congr 1
  · funext t a
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · rw [show c + (c + Q₂.polarBilin (u 0) (u 1)) + Q₂.polarBilin (u 0) (u 1) =
      (c + c) + (Q₂.polarBilin (u 0) (u 1) + Q₂.polarBilin (u 0) (u 1)) by ring,
      CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

@[expose] noncomputable def qEGL (u : Fin 2 → ι₂ → K) (c : K) : GL ι K where
  val := qE oe Q₂ u c
  inv := qE oe Q₂ u (c + Q₂.polarBilin (u 0) (u 1))
  val_inv := qE_mul_inv oe Q₂ u c
  inv_val := by
    have h := qE_mul_inv oe Q₂ u (c + Q₂.polarBilin (u 0) (u 1))
    rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h

theorem coe_qEGL (u : Fin 2 → ι₂ → K) (c : K) :
    ((qEGL oe Q₂ u c : GL ι K) : Matrix ι ι K) = qE oe Q₂ u c := rfl

end Commute

section Char

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem polarBilin_col (g : Matrix ι ι K) (j k : ι) :
    Q.polarBilin (g *ᵥ Pi.single j 1) (g *ᵥ Pi.single k 1) =
      Q₂.polarBilin (fun a => g (ou oe a) j) (fun a => g (ou oe a) k) +
        (g (ox oe 0) j * g (oy oe 0) k + g (oy oe 0) j * g (ox oe 0) k +
          (g (ox oe 1) j * g (oy oe 1) k + g (oy oe 1) j * g (ox oe 1) k)) := by
  rw [mulVec_single_one, mulVec_single_one, polarBilin_oe hQ, polarBilin_quadPlus_two]
  rfl

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem quad_col (g : Matrix ι ι K) (j : ι) :
    Q (g *ᵥ Pi.single j 1) = Q₂ (fun a => g (ou oe a) j) +
      (g (ox oe 0) j * g (oy oe 0) j + g (ox oe 1) j * g (oy oe 1) j) := by
  rw [mulVec_single_one, hQ]
  simp only [StatedQuadPlus, Fin.sum_univ_two]
  rfl

end Char

end CFSG.ComponentClassification.RankTwoClassical.ORigid
