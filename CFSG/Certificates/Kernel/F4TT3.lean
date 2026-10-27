module

import all CFSG.Fischer.F4
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

public section

namespace CFSG.KC.F4T

open CFSG.Fischer CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

@[expose] def Fix (M : Matrix (Fin 3) (Fin 3) F4) (v : Fin 3 → F4) : Prop :=
  ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec M v = c • v

theorem frame_scalar {M B : Matrix (Fin 3) (Fin 3) F4} (hB : IsUnit B.det) {a : Fin 3 → F4}
    (ha : ∀ i, a i ≠ 0) (hcol : ∀ i : Fin 3, Fix M (fun r => B r i))
    (h4 : Fix M (Matrix.mulVec B a)) : ∃ d : F4, M = d • 1 := by
  choose c _ hc using hcol
  obtain ⟨d, _, hd⟩ := h4
  have hMB : M * B = B * Matrix.diagonal c := by
    ext r i
    rw [Matrix.mul_diagonal]
    have := congrFun (hc i) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, this, mul_comm]
  have hinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det B).2 hB)
  have e1 : Matrix.mulVec M (Matrix.mulVec B a) = Matrix.mulVec B (Matrix.mulVec (Matrix.diagonal c) a) := by
    rw [Matrix.mulVec_mulVec, hMB, ← Matrix.mulVec_mulVec]
  have e2 : Matrix.mulVec (Matrix.diagonal c) a = d • a :=
    hinj (e1.symm.trans (hd.trans (Matrix.mulVec_smul B d a).symm))
  have hci : ∀ i, c i = d := by
    intro i
    have := congrFun e2 i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ (ha i) this
  have hc' : c = fun _ => d := funext hci
  have hMB' : M * B = d • B := by
    rw [hMB, hc']
    ext r i
    simp [Matrix.mul_diagonal, mul_comm]
  refine ⟨d, ?_⟩
  calc M = M * B * B⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv B hB, mul_one]
    _ = d • 1 := by rw [hMB', Matrix.smul_mul, Matrix.mul_nonsing_inv B hB]

theorem cube_roots : ∀ d : F4, d * d * d = 1 → d = 1 ∨ d = F4.ω ∨ d = F4.ω * F4.ω := by decide

theorem InM_scalar {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} (hZ : InM H Zs)
    {d : F4} (hd : (d • (1 : Matrix (Fin 3) (Fin 3) F4)).det = 1) :
    InM H (d • (1 : Matrix (Fin 3) (Fin 3) F4)) := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_three, ← mul_assoc] at hd
  rcases cube_roots d hd with rfl | rfl | rfl
  · rw [one_smul]
    exact InM_one H
  · exact hZ
  · have h := InM_mul hZ hZ
    rw [Zs, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at h
    exact h

theorem inv_mulVec_of {r : Matrix.GeneralLinearGroup (Fin 3) F4} {v w : Fin 3 → F4} {b : F4}
    (hb : b ≠ 0) (h : Matrix.mulVec (r : Matrix (Fin 3) (Fin 3) F4) v = b • w) :
    Matrix.mulVec ((r⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) w =
      b⁻¹ • v := by
  have h1 : Matrix.mulVec ((r⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
      (Matrix.mulVec (r : Matrix (Fin 3) (Fin 3) F4) v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem P_le_of_chain (k : Fin 6) (pts : Nat → Fin 3 → F4)
    (hΩ : ∀ v ∈ Omega k, ∃ q < 6, v = pts q) (hmem : ∀ q < 6, pts q ∈ Omega k)
    (hdist : ∀ i < 6, ∀ j < 6, i ≠ j → ∀ c : F4, pts i ≠ c • pts j)
    {B : Matrix (Fin 3) (Fin 3) F4} (hB : IsUnit B.det) (hBc : ∀ i : Fin 3, (fun r => B r i) = pts i)
    {a : Fin 3 → F4} (ha : ∀ i, a i ≠ 0) (h3 : Matrix.mulVec B a = pts 3)
    {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} (hZ : InM H Zs)
    (hch : ∀ l < 4, ∀ p, l < p → p < 6 → ∃ r ∈ P k, r ∈ H ∧
      (∀ i < l, Fix (r : Matrix (Fin 3) (Fin 3) F4) (pts i)) ∧
      ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec (r : Matrix (Fin 3) (Fin 3) F4) (pts l) = c • pts p) :
    P k ≤ H := by
  have key : ∀ n l, l + n = 4 → ∀ g ∈ P k,
      (∀ i < l, Fix (g : Matrix (Fin 3) (Fin 3) F4) (pts i)) → g ∈ H := by
    intro n
    induction n with
    | zero =>
      intro l hl g hg hfix
      have hl4 : l = 4 := by omega
      subst hl4
      obtain ⟨d, hd⟩ := frame_scalar hB ha (fun i => by rw [hBc i]; exact hfix i (by omega))
        (by rw [h3]; exact hfix 3 (by omega))
      have hdet : (d • (1 : Matrix (Fin 3) (Fin 3) F4)).det = 1 := by rw [← hd]; exact hg.1
      obtain ⟨g', hg', he⟩ := InM_scalar hZ hdet
      rw [← hd] at he
      rw [← Units.ext he]
      exact hg'
    | succ n ih =>
      intro l hl g hg hfix
      have hl6 : l < 6 := by omega
      obtain ⟨u, hu, c, hc, hgl⟩ := hg.2 (pts l) (hmem l hl6)
      obtain ⟨q, hq, rfl⟩ := hΩ u hu
      rcases lt_trichotomy q l with hql | rfl | hlq
      · exfalso
        obtain ⟨c', hc', hgq⟩ := hfix q hql
        have e1 := inv_mulVec_of hc hgl
        have e2 := inv_mulVec_of hc' hgq
        rw [e1] at e2
        apply hdist l hl6 q hq (by omega) (c * c'⁻¹)
        have := congrArg (fun x => c • x) e2
        simp only [smul_smul, mul_inv_cancel₀ hc, one_smul] at this
        exact this
      · refine ih (q + 1) (by omega) g hg fun i hi => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hfix i hi
        · exact ⟨c, hc, hgl⟩
      · obtain ⟨r, hrP, hrH, hrfix, e, he, hrl⟩ := hch l (by omega) q hlq hq
        have hg' : r⁻¹ * g ∈ P k := (P k).mul_mem ((P k).inv_mem hrP) hg
        have hfix' : ∀ i < l + 1, Fix ((r⁻¹ * g : Matrix.GeneralLinearGroup (Fin 3) F4) :
            Matrix (Fin 3) (Fin 3) F4) (pts i) := by
          intro i hi
          unfold Fix
          rw [Units.val_mul, ← Matrix.mulVec_mulVec]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · obtain ⟨a', ha', hga⟩ := hfix i hi
            obtain ⟨b, hb, hrb⟩ := hrfix i hi
            refine ⟨a' * b⁻¹, mul_ne_zero ha' (inv_ne_zero hb), ?_⟩
            rw [hga, Matrix.mulVec_smul, inv_mulVec_of hb hrb, smul_smul]
          · refine ⟨c * e⁻¹, mul_ne_zero hc (inv_ne_zero he), ?_⟩
            rw [hgl, Matrix.mulVec_smul, inv_mulVec_of he hrl, smul_smul]
        have := ih (l + 1) (by omega) _ hg' hfix'
        have hgr : g = r * (r⁻¹ * g) := by group
        rw [hgr]
        exact H.mul_mem hrH this
  intro g hg
  exact key 4 0 rfl g hg fun i hi => absurd hi (Nat.not_lt_zero i)

end CFSG.KC.F4T

end
