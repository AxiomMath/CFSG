module

public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Subgroup CFSG.Open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

theorem coe_suConj_mul_suField_apply {K : Type} [Field K] {p f : ℕ}
    {h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K}
    (B : unitaryIsom3 h) (δ : K ≃+* K) (b : unitarySU p f K 3) :
    ((((suConj h B * suField h δ) b : unitarySU p f K 3)) : GL (Fin 3) K) =
      (B : GL (Fin 3) K) * glAut δ (b : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹ := by
  rw [MulAut.mul_apply, coe_suConj, coe_suField]
  rfl

theorem exists_smul_of_suConj_mul_suField_fixes_torus {K : Type} [Field K] {p f : ℕ}
    {h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K}
    {T : Subgroup (unitarySU p f K 3)} {v : Fin 3 → K} (hvne : v ≠ 0)
    (hvfix : ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    (hspan : ∀ w : Fin 3 → K,
      (∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) →
        ∃ c : K, w = c • v)
    {B : unitaryIsom3 h} {δ : K ≃+* K}
    (hβ : ∀ b ∈ T, (suConj h B * suField h δ) b = b) :
    ∃ c : K, c ≠ 0 ∧
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (δ ∘ v) = c • v := by
  let Bm : GL (Fin 3) K := (B : GL (Fin 3) K)
  let vδ : Fin 3 → K := δ ∘ v
  have hβcoe : ∀ b : unitarySU p f K 3,
      ((((suConj h B * suField h δ) b : unitarySU p f K 3)) : GL (Fin 3) K) =
        Bm * glAut δ (b : GL (Fin 3) K) * Bm⁻¹ :=
    fun b => coe_suConj_mul_suField_apply B δ b
  have hfixB : ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
      (((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vδ) =
        ((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vδ := by
    intro b hb
    have hbB : (b : GL (Fin 3) K) * Bm = Bm * glAut δ (b : GL (Fin 3) K) := by
      have h1 : (b : GL (Fin 3) K) = Bm * glAut δ (b : GL (Fin 3) K) * Bm⁻¹ := by
        rw [← hβcoe b, hβ b hb]
      calc (b : GL (Fin 3) K) * Bm = (Bm * glAut δ (b : GL (Fin 3) K) * Bm⁻¹) * Bm := by
            conv_lhs => rw [h1]
        _ = Bm * glAut δ (b : GL (Fin 3) K) := by group
    have hgl : ((glAut δ (b : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ vδ = vδ := by
      funext i
      rw [coe_glAut]
      have hmv := RingHom.map_mulVec (δ : K →+* K) ((b : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) v i
      rw [hvfix b hb] at hmv
      exact hmv.symm
    have hbBmat : ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((glAut δ (b : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hbB
    rw [Matrix.mulVec_mulVec, hbBmat, ← Matrix.mulVec_mulVec, hgl]
  obtain ⟨c, hc⟩ := hspan (((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vδ)
    hfixB
  have hvδ : vδ ≠ 0 := by
    intro h0
    apply hvne
    funext i
    exact δ.injective (by simpa [vδ] using congrFun h0 i)
  have hBvδ : ((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vδ ≠ 0 := by
    intro h0
    apply hvδ
    have h1 : ((Bm⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((Bm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vδ) = vδ := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h1, h0, Matrix.mulVec_zero]
  exact ⟨c, fun hc0 => hBvδ (by rw [hc, hc0]; simp), hc⟩

theorem suConj_mul_suField_map_stabilizer_eq {K : Type} [Field K] [Finite K] {p f : ℕ}
    {h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K}
    {T : Subgroup (unitarySU p f K 3)} {v : Fin 3 → K}
    (hvfix : ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {L : Subgroup (unitarySU p f K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {B : unitaryIsom3 h} {δ : K ≃+* K} {c : K} (hcne : c ≠ 0)
    (hc : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (δ ∘ v) = c • v)
    (hβ : ∀ b ∈ T, (suConj h B * suField h δ) b = b) :
    L.map (suConj h B * suField h δ).toMonoidHom = L := by
  let Bm : GL (Fin 3) K := (B : GL (Fin 3) K)
  let vδ : Fin 3 → K := δ ∘ v
  have hc' : (Bm : Matrix (Fin 3) (Fin 3) K) *ᵥ vδ = c • v := hc
  have hβcoe : ∀ b : unitarySU p f K 3,
      ((((suConj h B * suField h δ) b : unitarySU p f K 3)) : GL (Fin 3) K) =
        Bm * glAut δ (b : GL (Fin 3) K) * Bm⁻¹ :=
    fun b => coe_suConj_mul_suField_apply B δ b
  have hBinv_v : (Bm : Matrix (Fin 3) (Fin 3) K)⁻¹ *ᵥ v = (c⁻¹ : K) • vδ := by
    have hmul : (Bm : Matrix (Fin 3) (Fin 3) K)⁻¹ * (Bm : Matrix (Fin 3) (Fin 3) K) = 1 := by
      simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
        (inv_mul_cancel Bm)
    have h1 : (Bm : Matrix (Fin 3) (Fin 3) K)⁻¹ *ᵥ (Bm *ᵥ vδ) = vδ := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    have h2 : vδ = c • ((Bm : Matrix (Fin 3) (Fin 3) K)⁻¹ *ᵥ v) := by
      rw [← h1, hc', Matrix.mulVec_smul]
    rw [h2, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hglv : ∀ g ∈ L, ((glAut δ (g : GL (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ vδ = vδ := by
    intro g hg
    have hgv := (hL g).1 hg
    funext i
    rw [coe_glAut]
    have hmv := RingHom.map_mulVec (δ : K →+* K) ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) v i
    rw [hgv] at hmv
    exact hmv.symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨g, hg, rfl⟩
    refine (hL ((suConj h B * suField h δ) g)).2 ?_
    rw [hβcoe g]
    have hBM : ((Bm * glAut δ (g : GL (Fin 3) K) * Bm⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (Bm : Matrix (Fin 3) (Fin 3) K) *
          (glAut δ (g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (Bm⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
      simp [Units.val_mul]
    rw [hBM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBinv_v, Matrix.mulVec_smul,
      hglv g hg, Matrix.mulVec_smul, hc', smul_smul, inv_mul_cancel₀ hcne, one_smul]
  · rw [Subgroup.card_map_of_injective (suConj h B * suField h δ).injective]

theorem map_stabilizer_eq_of_forall_mem_eq {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hq : 2 < 2 ^ n)
    {T : Subgroup (StatedSU 3 (2 ^ n) K)} {v : Fin 3 → K} (hvne : v ≠ 0)
    (hvfix : ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    (hspan : ∀ w : Fin 3 → K,
      (∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) →
        ∃ c : K, w = c • v)
    {L : Subgroup (StatedSU 3 (2 ^ n) K)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    (β : MulAut (StatedSU 3 (2 ^ n) K)) (hβ : ∀ b ∈ T, β b = b) :
    L.map β.toMonoidHom = L := by
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K := unitaryFieldDataOfCard hK
  obtain ⟨B, δ, hBδ⟩ := exists_suConj_mul_suField h hq β
  rw [hBδ] at hβ ⊢
  obtain ⟨c, hcne, hc⟩ := exists_smul_of_suConj_mul_suField_fixes_torus hvne hvfix hspan hβ
  exact suConj_mul_suField_map_stabilizer_eq hvfix hL hcne hc hβ

end CFSG.ClassicalGroups.UnitaryFlag

end
