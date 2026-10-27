module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis

public noncomputable section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

structure IsFixedLine (p : ℕ) (u : SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) : Prop where
  odd : Odd p
  ne_zero : (p : K) ≠ 0
  pow_eq_one : u ^ p = 1
  ne : x ≠ 0
  fixed : (u : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x
  le : ∀ v : Fin 3 → K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v ∈ K ∙ x

namespace IsFixedLine

variable {p : ℕ} {u : SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K}

theorem eq_zero_of_mem (h : IsFixedLine p u x) {v : Fin 3 → K} (hv : v ∈ K ∙ x)
    (hr : v ∈ LinearMap.range (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1))) : v = 0 := by
  obtain ⟨y, rfl⟩ := hr
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  refine sub_one_mulVec_eq_zero h.ne_zero (coe_pow_eq_one h.pow_eq_one) y ?_
  rw [mulVecLin_apply] at hc
  rw [← hc, Matrix.mulVec_smul, h.fixed]

theorem finrank_range (h : IsFixedLine p u x) :
    Module.finrank K (LinearMap.range (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1))) = 2 := by
  have hker : LinearMap.ker (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1)) = K ∙ x := by
    ext v
    rw [LinearMap.mem_ker, mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    refine ⟨h.le v, fun hv => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [Matrix.mulVec_smul, h.fixed]
  have := LinearMap.finrank_range_add_finrank_ker
    (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1))
  rw [hker, finrank_span_singleton h.ne, Module.finrank_fin_fun] at this
  omega

theorem mulVec_mem_range {U : Matrix (Fin 3) (Fin 3) K} {w : Fin 3 → K}
    (hw : w ∈ LinearMap.range (mulVecLin (U - 1))) :
    U *ᵥ w ∈ LinearMap.range (mulVecLin (U - 1)) := by
  obtain ⟨y, rfl⟩ := hw
  refine ⟨U *ᵥ y, ?_⟩
  simp only [mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one]

theorem not_scalar (h : IsFixedLine p u x) {w₁ w₂ : Fin 3 → K}
    (hli : LinearIndependent K ![x, w₁, w₂]) (a : K)
    (h₁ : (u : Matrix (Fin 3) (Fin 3) K) *ᵥ w₁ = a • w₁)
    (h₂ : (u : Matrix (Fin 3) (Fin 3) K) *ᵥ w₂ = a • w₂) : False := by
  have hdet : (u : Matrix (Fin 3) (Fin 3) K).det = !![1, 0, 0; 0, a, 0; 0, 0, a].det := by
    refine det_eq_of_mulVec_eq_sum hli fun j => ?_
    fin_cases j <;> simp [Fin.sum_univ_three, h.fixed, h₁, h₂]
  rw [u.prop, Matrix.det_fin_three] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const] at hdet
  have hw₁ : w₁ ≠ 0 := hli.ne_zero 1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_smul] at h₁
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h.le w₁ h₁)
    have := Fintype.linearIndependent_iff.mp hli ![c, -1, 0]
      (by simp [Fin.sum_univ_three, hc]) 1
    simp at this
  have hap : a ^ p = 1 := by
    have e := pow_mulVec_of_mulVec_eq_smul h₁ p
    rw [coe_pow_eq_one h.pow_eq_one, Matrix.one_mulVec] at e
    exact smul_left_injective K hw₁ (by simpa using e.symm)
  have ha : a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) ha1
    · exact eq_neg_of_add_eq_zero_left h0
  rw [ha, h.odd.neg_one_pow] at hap
  exact ha1 (ha.trans hap)

theorem eigen_or_linearIndependent {U : Matrix (Fin 3) (Fin 3) K} {w : Fin 3 → K} (hw : w ≠ 0) :
    (∃ a : K, U *ᵥ w = a • w) ∨ LinearIndependent K ![w, U *ᵥ w] := by
  by_contra hno
  push Not at hno
  obtain ⟨hno, hli⟩ := hno
  apply hli
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hw, rfl⟩
  · refine absurd ?_ (hno (-(t⁻¹ * s)))
    have h2 : t • (U *ᵥ w) = -(s • w) := eq_neg_of_add_eq_zero_right hst
    calc U *ᵥ w = t⁻¹ • (t • (U *ᵥ w)) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = -(t⁻¹ * s) • w := by rw [h2, smul_neg, smul_smul, neg_smul]

theorem exists_normalBasis (h : IsFixedLine p u x) : ∃ w : Fin 3 → K,
    w ∈ LinearMap.range (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1)) ∧
    LinearIndependent K ![x, w, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ w] ∧
    (u : Matrix (Fin 3) (Fin 3) K) *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
      (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ w)
        - w ∧
    Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1 ≠ 2 := by
  classical
  set U : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K) with hUdef
  set R := LinearMap.range (mulVecLin (U - 1)) with hR
  have hxR : ∀ c : K, ∀ v ∈ R, c • x = v → c = 0 := fun c v hv hcv =>
    (smul_eq_zero.mp (h.eq_zero_of_mem (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self x)) (hcv ▸ hv))).resolve_right h.ne
  have hli3 : ∀ {w₁ w₂ : Fin 3 → K}, w₁ ∈ R → w₂ ∈ R → LinearIndependent K ![w₁, w₂] →
      LinearIndependent K ![x, w₁, w₂] := by
    intro w₁ w₂ h₁ h₂ hli
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have hc0 : c 0 = 0 := by
      refine hxR _ _ (R.neg_mem (R.add_mem (R.smul_mem (c 1) h₁) (R.smul_mem (c 2) h₂))) ?_
      rw [add_assoc] at hc
      exact eq_neg_of_add_eq_zero_left hc
    rw [hc0, zero_smul, zero_add] at hc
    obtain ⟨hc1, hc2⟩ := LinearIndependent.pair_iff.mp hli _ _ hc
    intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  obtain ⟨w, hwR, hwli⟩ : ∃ w ∈ R, LinearIndependent K ![w, U *ᵥ w] := by
    let bR := Module.finBasisOfFinrankEq K R h.finrank_range
    have hw12 : LinearIndependent K ![(bR 0 : Fin 3 → K), bR 1] := by
      have := bR.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
      convert this using 1
      ext i : 1
      fin_cases i <;> rfl
    have hs0 : ((bR 0 : Fin 3 → K) + bR 1) ≠ 0 := by
      intro h0
      have := LinearIndependent.pair_iff.mp hw12 1 1 (by simpa using h0)
      simp at this
    have h0 : (bR 0 : Fin 3 → K) ≠ 0 := by simpa using hw12.ne_zero 0
    have h1 : (bR 1 : Fin 3 → K) ≠ 0 := by simpa using hw12.ne_zero 1
    rcases eigen_or_linearIndependent (U := U) h0 with ⟨a, ha⟩ | hl
    · rcases eigen_or_linearIndependent (U := U) h1 with ⟨b, hb⟩ | hl
      · rcases eigen_or_linearIndependent (U := U) hs0 with ⟨c, hc⟩ | hl
        · exfalso
          rw [Matrix.mulVec_add, ha, hb] at hc
          have h' := LinearIndependent.pair_iff.mp hw12 (a - c) (b - c) (by
            rw [sub_smul, sub_smul, smul_add] at *; rw [← sub_eq_zero] at hc
            rw [← hc]; abel)
          have hab : b = a := by linear_combination h'.2 - h'.1
          exact h.not_scalar (hli3 (bR 0).2 (bR 1).2 hw12) a ha (by rw [hb, hab])
        · exact ⟨_, R.add_mem (bR 0).2 (bR 1).2, hl⟩
      · exact ⟨_, (bR 1).2, hl⟩
    · exact ⟨_, (bR 0).2, hl⟩
  have hfx : U *ᵥ x = x := h.fixed
  have hUw : U *ᵥ w ∈ R := mulVec_mem_range hwR
  have hli := hli3 hwR hUw hwli
  obtain ⟨c, hc⟩ := exists_sum_smul_eq hli (U *ᵥ (U *ᵥ w))
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  have hc0 : c 0 = 0 := hxR _ _ (R.sub_mem (mulVec_mem_range hUw)
    (R.add_mem (R.smul_mem (c 1) hwR) (R.smul_mem (c 2) hUw))) (by rw [← hc]; abel)
  rw [hc0, zero_smul, zero_add] at hc
  have hM : ∀ j, U *ᵥ ![x, w, U *ᵥ w] j =
      ∑ i, !![1, 0, 0; 0, 0, c 1; 0, 1, c 2] i j • ![x, w, U *ᵥ w] i := by
    intro j
    fin_cases j <;> simp [Fin.sum_univ_three, hfx, ← hc]
  have hdet := det_eq_of_mulVec_eq_sum hli hM
  rw [u.prop, Matrix.det_fin_three] at hdet
  simp at hdet
  have htr : U.trace = 1 + c 2 := by
    rw [trace_eq_of_mulVec_eq_sum hli hM, Matrix.trace_fin_three]
    simp
  refine ⟨w, hwR, hli, ?_, fun ht => ?_⟩
  · rw [← hc, htr, show c 1 = -1 by linear_combination hdet]
    module
  ·
    have h2 : c 2 = 2 := by rw [← ht, htr]; ring
    have hfix : U *ᵥ ((U - 1) *ᵥ w) = (U - 1) *ᵥ w := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, ← hc, h2,
        show c 1 = -1 by linear_combination hdet]
      module
    have h0 := sub_one_mulVec_eq_zero h.ne_zero (coe_pow_eq_one h.pow_eq_one) w hfix
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    have := LinearIndependent.pair_iff.mp hwli 1 (-1) (by rw [h0]; simp)
    simp at this

theorem mulVec_eq_of_commute (h : IsFixedLine p u x) {w : Fin 3 → K}
    (hwR : w ∈ LinearMap.range (mulVecLin ((u : Matrix (Fin 3) (Fin 3) K) - 1)))
    (hli : LinearIndependent K ![x, w, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ w])
    {G : Matrix (Fin 3) (Fin 3) K} (hG : (u : Matrix (Fin 3) (Fin 3) K) * G = G * u) :
    (∃ l : K, G *ᵥ x = l • x) ∧
      ∃ α β : K, G *ᵥ w = α • w + β • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  set U : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K) with hUdef
  set R := LinearMap.range (mulVecLin (U - 1)) with hR
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp
      (h.le _ (mulVec_fixed_of_commute hG h.fixed))
    exact ⟨l, hl.symm⟩
  · have hGw : G *ᵥ w ∈ R := by
      obtain ⟨y, rfl⟩ := hwR
      refine ⟨G *ᵥ y, ?_⟩
      simp only [mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hG]
    obtain ⟨c, hc⟩ := exists_sum_smul_eq hli (G *ᵥ w)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have hc0 : c 0 • x = 0 := by
      refine h.eq_zero_of_mem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) ?_
      have : c 0 • x = G *ᵥ w - (c 1 • w + c 2 • (U *ᵥ w)) := by rw [← hc]; abel
      rw [this]
      exact R.sub_mem hGw (R.add_mem (R.smul_mem _ hwR) (R.smul_mem _ (mulVec_mem_range hwR)))
    exact ⟨c 1, c 2, by rw [← hc, hc0, zero_add]⟩

end IsFixedLine

end CFSG.AGLEmbedding.LinearThreeKit
