module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRModel
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModel
public import Certificates.Certificate15118

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.GMS78RuS
open CFSG.ComponentClassification.GMS78.RuSimCode CFSG.ComponentClassification.GMS78.RuSModel

theorem nCo_eq_cOf (m : Nat) : nCo m = cOf m := rfl

theorem gamN_zero_left (c' n : Nat) : gamN 0 c' n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gamN, ih]

theorem gam_zero_left (c' : Nat) : gam 0 c' = 0 := gamN_zero_left c' 8

theorem dPartN_fst_lt' (d : Fin 8) (c n : Nat) : (dPartN d c n).1 < 256 := by
  induction n with
  | zero => simp [dPartN]
  | succ n ih =>
    simp only [dPartN]
    split_ifs
    · have h : 2 ^ (dMul d (fin8Of n)).val < 256 := by
        have := (dMul d (fin8Of n)).isLt
        calc 2 ^ (dMul d (fin8Of n)).val < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) this
          _ = 256 := by norm_num
      exact xor_lt ih h
    · exact ih

theorem dPart_fst_lt (d : Fin 8) (c : Nat) : (dPart d c).1 < 256 := dPartN_fst_lt' d c 8

theorem dMul_zero_zero : dMul 0 0 = 0 := by decide

theorem dMul_zero_left : ∀ d : Fin 8, dMul 0 d = d := by decide

theorem dCode_zero_linId : dCode 0 = linId := rfl

section Cert


theorem gam_eq_nBeta {c c' : Nat} (hc : c < 256) (hc' : c' < 256) :
    gam c c' = nBeta (sMask c) (sMask c') := by
  have h := Certificates.certificate15118.1
  simp only [gamColCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [nBeta, nCo_eq_cOf, nCo_eq_cOf, cOf_sMask hc, cOf_sMask hc']
  have hj : ∀ j < 8, xs8 c' (nBT j) = bC (sBasis.getD j 0) (sMaskN c' j) := fun j hj =>
    h j hj c' hc'
  rw [xs8_congr c hj]
  simp only [gam, gamN, xs8, fin8_zero_xor]

theorem dPart_eq_nAut (d : Fin 8) {c : Nat} (hc : c < 256) :
    (dPart d c).1 = cOf (nAd (dCode d) (sMask c)) ∧ (dPart d c).2 = nTau (dCode d) (sMask c) := by
  have h := Certificates.certificate15118.2
  simp only [dPartCheck, List.all_eq_true, List.mem_finRange, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, forall_const] at h
  obtain ⟨h1, h2⟩ := h d c hc
  refine ⟨?_, h2⟩
  rw [← h1, cOf_sMask (dPart_fst_lt d c)]

theorem dPart_zero_left {c : Nat} (hc : c < 256) : dPart 0 c = (c, 0) := by
  obtain ⟨h1, h2⟩ := dPart_eq_nAut 0 hc
  have hm : sMask c < 256 := sMaskN_lt c 8
  have hid := (nIdCheck_parts.1 (sMask c) hm)
  rw [dCode_zero_linId, hid.1, cOf_sMask hc] at h1
  rw [dCode_zero_linId, hid.2.1] at h2
  exact Prod.ext h1 h2

theorem sMul_R {m n : Nat} (hm : m < 256) (hn : n < 256) (t s : Fin 8) :
    sMul false (cOf m, t, 0) (cOf n, s, 0) = (cOf (m ^^^ n), t ^^^ s ^^^ nBeta m n, 0) := by
  have hdp := dPart_zero_left (cOf_lt n)
  simp only [sMul, hdp, dCode_zero_linId, linApply_linId, dMul_zero_zero, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, fin8_xor_zero]
  rw [gam_eq_nBeta (cOf_lt m) (cOf_lt n), sMask_cOf hm, sMask_cOf hn,
    show cOf (m ^^^ n) = cOf m ^^^ cOf n from maskApply_xor _ _ _]

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

theorem sModel_one_eq (hS : Sec3.SzR.SModel L T R μ ν false Φ) : Φ (0, 0, 0) = 1 := by
  have h := hS.mul (0, 0, 0) (0, 0, 0)
  have e : sMul false (0, 0, 0) (0, 0, 0) = (0, 0, 0) := by decide
  rw [e] at h
  exact left_eq_mul.mp h

@[expose] noncomputable def thetaR (hS : Sec3.SzR.SModel L T R μ ν false Φ) : RuR →* G where
  toFun x := Φ (cOf x.m.val, x.t, 0)
  map_one' := by
    change Φ (cOf 0, 0, 0) = 1
    exact sModel_one_eq hS
  map_mul' x y := by
    rw [← hS.mul, sMul_R x.m.isLt y.m.isLt]
    rw [show (x * y).m.val = x.m.val ^^^ y.m.val from fin256_val_xor _ _]
    rfl

theorem thetaR_apply (hS : Sec3.SzR.SModel L T R μ ν false Φ) (x : RuR) :
    thetaR hS x = Φ (cOf x.m.val, x.t, 0) := rfl

theorem thetaR_injective (hS : Sec3.SzR.SModel L T R μ ν false Φ) :
    Function.Injective (thetaR hS) := by
  intro x y h
  have := hS.inj _ _ (cOf_lt _) (cOf_lt _) h
  simp only [Prod.mk.injEq, and_true] at this
  refine RuR.ext (Fin.ext ?_) this.2
  rw [← sMask_cOf x.m.isLt, ← sMask_cOf y.m.isLt, this.1]

theorem range_thetaR (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) : (thetaR hS).range = R := by
  refine le_antisymm ?_ fun r hr => ?_
  · rintro _ ⟨x, rfl⟩
    exact hS.mem_R _ _
  · have hrN : r ∈ normalizer (R : Set G) := le_normalizer hr
    have hcode : ∀ b ∈ gmsA L T, ν (r * b * r⁻¹) = linApply (dCode 0) (ν b) := by
      intro b hb
      rw [hM.central r hr b hb, mul_inv_cancel_right, dCode_zero_linId, linApply_linId]
    obtain ⟨p, hp, hp0, hpr⟩ := hS.surj r hrN 0 hcode
    refine ⟨⟨⟨sMask p.1, sMaskN_lt _ 8⟩, p.2.1⟩, ?_⟩
    rw [thetaR_apply, ← hpr]
    change Φ (cOf (sMask p.1), p.2.1, 0) = Φ p
    rw [cOf_sMask hp, ← hp0]

theorem thetaR_mem (hS : Sec3.SzR.SModel L T R μ ν false Φ) (x : RuR) : thetaR hS x ∈ R :=
  hS.mem_R _ _

theorem μ_thetaR (hS : Sec3.SzR.SModel L T R μ ν false Φ) (x : RuR) :
    μ (thetaR hS x) = x.m.val := by
  rw [thetaR_apply, hS.μ_eq, sMask_cOf x.m.isLt]

theorem thetaR_A1 (hS : Sec3.SzR.SModel L T R μ ν false Φ) (t : Fin 8) :
    thetaR hS ⟨0, t⟩ ∈ gmsA L T ∧ ν (thetaR hS ⟨0, t⟩) = t := by
  have e : cOf (⟨0, t⟩ : RuR).m.val = 0 := maskApply_zero _
  rw [thetaR_apply, e]
  exact ⟨hS.mem_A t, hS.ν_eq t⟩


theorem conj_thetaR_D (hS : Sec3.SzR.SModel L T R μ ν false Φ) (d : Fin 8) (x : RuR) :
    Φ (0, 0, d) * thetaR hS x * (Φ (0, 0, d))⁻¹ = thetaR hS (nAut (dCode d) x) := by
  rw [mul_inv_eq_iff_eq_mul, thetaR_apply, thetaR_apply, ← hS.mul, ← hS.mul]
  obtain ⟨h1, h2⟩ := dPart_eq_nAut d (cOf_lt x.m.val)
  rw [sMask_cOf x.m.isLt] at h1 h2
  have hz := dPart_zero 0
  simp only [sMul, h1, h2, hz, gam_zero_left, gam_zero_right, dMul_zero_right, dMul_zero_left,
    dCode_zero_linId, linApply_zero, Bool.false_and, Bool.false_eq_true, ↓reduceIte, fin8_xor_zero,
    fin8_zero_xor, Nat.zero_xor, Nat.xor_zero, nAut_m, nAut_t]

@[expose] noncomputable def thetaE (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) : RuR ≃* R :=
  (MonoidHom.ofInjective (thetaR_injective hS)).trans
    (MulEquiv.subgroupCongr (range_thetaR hM hS))

theorem thetaE_apply (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (x : RuR) :
    (thetaE hM hS x : G) = thetaR hS x := rfl

theorem conj_mem_R {n : G} (hn : n ∈ normalizer (R : Set G)) {x : G} (hx : x ∈ R) :
    n * x * n⁻¹ ∈ R :=
  (mem_normalizer_iff.mp hn x).mp hx

theorem conj_inv_mem_R {n : G} (hn : n ∈ normalizer (R : Set G)) {x : G} (hx : x ∈ R) :
    n⁻¹ * x * n ∈ R := by
  have := conj_mem_R (inv_mem hn) hx
  rwa [inv_inv] at this

theorem thetaR_thetaE_symm (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (r : R) :
    thetaR hS ((thetaE hM hS).symm r) = r := by
  rw [← thetaE_apply hM hS, MulEquiv.apply_symm_apply]

@[expose] noncomputable def conjR (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {n : G} (hn : n ∈ normalizer (R : Set G)) :
    MulAut RuR where
  toFun x := (thetaE hM hS).symm ⟨n * thetaR hS x * n⁻¹, conj_mem_R hn (thetaR_mem hS x)⟩
  invFun x := (thetaE hM hS).symm ⟨n⁻¹ * thetaR hS x * n, conj_inv_mem_R hn (thetaR_mem hS x)⟩
  left_inv x := thetaR_injective hS (by
    simp only [thetaR_thetaE_symm]
    group)
  right_inv x := thetaR_injective hS (by
    simp only [thetaR_thetaE_symm]
    group)
  map_mul' x y := thetaR_injective hS (by
    simp only [map_mul, thetaR_thetaE_symm]
    group)

theorem thetaR_conjR (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {n : G} (hn : n ∈ normalizer (R : Set G))
    (x : RuR) : thetaR hS (conjR hM hS hn x) = n * thetaR hS x * n⁻¹ :=
  thetaR_thetaE_symm hM hS _

theorem conjR_eq_iff (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {n : G} (hn : n ∈ normalizer (R : Set G))
    (x y : RuR) : conjR hM hS hn x = y ↔ n * thetaR hS x * n⁻¹ = thetaR hS y := by
  rw [← thetaR_conjR hM hS hn]
  exact (thetaR_injective hS).eq_iff.symm

theorem conjR_mul (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {n n' : G} (hn : n ∈ normalizer (R : Set G))
    (hn' : n' ∈ normalizer (R : Set G)) :
    conjR hM hS (mul_mem hn hn') = conjR hM hS hn * conjR hM hS hn' := by
  refine MulEquiv.ext fun x => (conjR_eq_iff hM hS _ _ _).mpr ?_
  rw [MulAut.mul_apply, thetaR_conjR, thetaR_conjR]
  group

theorem conjR_thetaR (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (y : RuR) :
    conjR hM hS (le_normalizer (thetaR_mem hS y)) = MulAut.conj y := by
  refine MulEquiv.ext fun x => (conjR_eq_iff hM hS _ _ _).mpr ?_
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem conjR_D (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (d : Fin 8) (x : RuR) :
    conjR hM hS (hS.mem (0, 0, d)) x = nAut (dCode d) x :=
  (conjR_eq_iff hM hS _ _ _).mpr (conj_thetaR_D hS d x)

theorem conjR_code (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {n : G} (hn : n ∈ normalizer (R : Set G)) {r : Lin8}
    (hA : ∀ b ∈ gmsA L T, ν (n * b * n⁻¹) = linApply r (ν b))
    (hR : ∀ x ∈ R, μ (n * x * n⁻¹) = maskApply (adMat r) (μ x)) :
    (∀ x, (conjR hM hS hn x).m = (nAut r x).m) ∧
      ∀ t, conjR hM hS hn ⟨0, t⟩ = ⟨0, linApply r t⟩ := by
  refine ⟨fun x => Fin.ext ?_, fun t => ?_⟩
  · rw [← μ_thetaR hS, thetaR_conjR, hR _ (thetaR_mem hS x), μ_thetaR hS, nAut_m]
    rfl
  · rw [conjR_eq_iff]
    have h1 := thetaR_A1 hS t
    have h2 := thetaR_A1 hS (linApply r t)
    refine hM.eq_of_ν_eq (hM.normA n hn _ h1.1) h2.1 ?_
    rw [hA _ h1.1, h1.2, h2.2]

end Cert

end CFSG.ComponentClassification.GMS78.RuN
