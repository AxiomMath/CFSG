module

public import Certificates.Certificate5167
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieTorus

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open Certificates.L34DC
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.QuasithinUnique.Fin257 CFSG.QuasithinUnique.Fin257.L3
open CFSG.GH74.KGroups (GF4)
open CFSG.Quasithin.H13.F431.L3.P3

abbrev KF : Type := GaloisField 2 2

abbrev YF : Type := projectiveSL 3 KF

theorem card_GF4 : Nat.card GF4 = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card]; rfl

@[expose] noncomputable def psi : GF4 ≃+* KF :=
  CFSG.ClassicalModels.finiteFieldEquivGaloisField GF4 2 2 (by norm_num) card_GF4

theorem tk_ne : ∀ k : Fin 3, tk k ≠ 0 := by decide

theorem tk_mul : ∀ k k' : Fin 3, tk k * tk k' = tk (k + k') := by decide

theorem sk_eq : ∀ k : Fin 3, sk k = tk k * tk k := by decide

theorem tk_inj : ∀ k k' : Fin 3, tk k = tk k' → k = k' := by decide

theorem tk_sub : ∀ j₁ j₂ : Fin 3, tk j₁ = tk j₂ * tk (j₁ - j₂) := by decide

theorem tk_surj : ∀ z : GF4, z ≠ 0 → ∃ j : Fin 3, z = tk j := by decide

theorem tk_zero : tk 0 = 1 := by decide

theorem tk_cube : ∀ k : Fin 3, tk k * tk k * tk k = 1 := by decide

theorem gf4_zero_eq : (⟨0⟩ : GF4) = 0 := by decide

@[expose] noncomputable def Tk (k : Fin 3) : KF := psi (tk k)

theorem Tk_ne (k : Fin 3) : Tk k ≠ 0 := by
  intro h
  apply tk_ne k
  exact psi.injective (by rw [Tk] at h; rw [h, map_zero])

theorem Tk_mul (k k' : Fin 3) : Tk k * Tk k' = Tk (k + k') := by
  rw [Tk, Tk, Tk, ← map_mul, tk_mul]

theorem Tk_cube (k : Fin 3) : Tk k * Tk k * Tk k = 1 := by
  rw [Tk, ← map_mul, ← map_mul, tk_cube k, map_one]

theorem Tk_sub (j₁ j₂ : Fin 3) : Tk j₁ = Tk j₂ * Tk (j₁ - j₂) := by
  rw [Tk, Tk, Tk, ← map_mul, ← tk_sub j₁ j₂]

theorem Tk_inj {k k' : Fin 3} (h : Tk k = Tk k') : k = k' :=
  tk_inj k k' (psi.injective h)

theorem Tk_zero : Tk 0 = 1 := by rw [Tk, tk_zero, map_one]

@[expose] noncomputable def tU (k : Fin 3) : Units KF := Units.mk0 (Tk k) (Tk_ne k)

theorem tU_val (k : Fin 3) : ((tU k : Units KF) : KF) = Tk k := Units.val_mk0 _

theorem tU_mul (k k' : Fin 3) : tU k * tU k' = tU (k + k') := by
  apply Units.ext
  rw [Units.val_mul, tU_val, tU_val, tU_val, Tk_mul]

theorem tU_zero : tU 0 = 1 := by
  apply Units.ext
  rw [tU_val, Tk_zero, Units.val_one]

@[expose] noncomputable def dd (k : Fin 3) : YF := proj 3 KF (dMat (tU k) 1)

theorem dd_mul (k k' : Fin 3) : dd k * dd k' = dd (k + k') := by
  unfold dd
  rw [← map_mul, dMat_mul, tU_mul, mul_one]

theorem dd_zero : dd 0 = 1 := by
  unfold dd
  rw [tU_zero, dMat_one, map_one]

@[expose] noncomputable def nfY (x : Elt) : YF :=
  wP (psi x.2.2.1) * xP (psi x.1) * yP (psi x.2.1) * dd x.2.2.2

theorem mat_entries (c a b : KF) (t : Units KF) :
    ((wMat c * xMat a * yMat b * dMat t 1 : Matrix.SpecialLinearGroup (Fin 3) KF) :
      Matrix (Fin 3) (Fin 3) KF) =
    !![(t : KF), a, (a * b + c) * (t : KF)⁻¹; 0, 1, b * (t : KF)⁻¹; 0, 0, (t : KF)⁻¹] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, xMat, yMat, xM, yM, wM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;>
    ring

theorem nfY_eq_proj (x : Elt) : nfY x =
    proj 3 KF (wMat (psi x.2.2.1) * xMat (psi x.1) * yMat (psi x.2.1) * dMat (tU x.2.2.2) 1) := by
  simp only [nfY, dd, wP, xP, yP, map_mul]

theorem elt_idx (x : Elt) : elt (idx x) = x := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩, k⟩ := x
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hk := k.isLt
  simp only [elt, idx, idxN, Prod.mk.injEq, GF4.mk.injEq, Fin.ext_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp only [Fin.val_mk]) <;> omega

theorem idx_elt (i : Fin 192) : idx (elt i) = i := by
  have := i.isLt
  apply Fin.ext
  simp only [idx, idxN, elt]
  omega

theorem dd_nf (k : Fin 3) (c a b : KF) :
    dd k * (wP c * xP a * yP b) = (wP (Tk k * Tk k * c) * xP (Tk k * a) * yP (Tk k * b)) * dd k := by
  have h := dP_conj_nf (tU k) 1 c a b
  simp only [tU_val, Units.val_one, mul_one, one_mul, inv_one] at h
  unfold dd
  rw [← h]
  group

theorem NF_mul (c a b c' a' b' : KF) :
    (wP c * xP a * yP b) * (wP c' * xP a' * yP b') =
      wP (c + c' + a' * b) * xP (a + a') * yP (b + b') := by
  calc (wP c * xP a * yP b) * (wP c' * xP a' * yP b')
      = wP c * xP a * (yP b * wP c') * xP a' * yP b' := by group
    _ = wP c * xP a * (wP c' * yP b) * xP a' * yP b' := by rw [← wP_mul_yP c' b]
    _ = wP c * (xP a * wP c') * yP b * xP a' * yP b' := by group
    _ = wP c * (wP c' * xP a) * yP b * xP a' * yP b' := by rw [wP_mul_xP c' a]
    _ = wP c * wP c' * xP a * yP b * xP a' * yP b' := by simp only [mul_assoc]
    _ = wP c * wP c' * xP a * (yP b * xP a') * yP b' := by group
    _ = wP c * wP c' * xP a * (wP (a' * b) * xP a' * yP b) * yP b' := by rw [yP_mul_xP a' b]
    _ = wP c * wP c' * (xP a * wP (a' * b)) * xP a' * yP b * yP b' := by group
    _ = wP c * wP c' * (wP (a' * b) * xP a) * xP a' * yP b * yP b' := by rw [wP_mul_xP (a' * b) a]
    _ = (wP c * wP c' * wP (a' * b)) * (xP a * xP a') * (yP b * yP b') := by simp only [mul_assoc]
    _ = wP (c + c' + a' * b) * xP (a + a') * yP (b + b') := by
      rw [wP_add, wP_add, xP_add, yP_add]

theorem nfY_mul (x y : Elt) : nfY (mulE x y) = nfY x * nfY y := by
  obtain ⟨a, b, c, k⟩ := x
  obtain ⟨a', b', c', k'⟩ := y
  have hs : psi (sk k) = psi (tk k) * psi (tk k) := by rw [sk_eq, map_mul]
  have hR : nfY (mulE (a, b, c, k) (a', b', c', k')) =
      ((wP (psi c) * xP (psi a) * yP (psi b)) *
        (wP (Tk k * Tk k * psi c') * xP (Tk k * psi a') * yP (Tk k * psi b'))) * dd (k + k') := by
    rw [NF_mul]
    simp only [nfY, mulE, map_add, map_mul, hs, Tk]
  have hD := dd_nf k (psi c') (psi a') (psi b')
  rw [hR, ← dd_mul]
  unfold nfY
  calc (wP (psi c) * xP (psi a) * yP (psi b)) *
          (wP (Tk k * Tk k * psi c') * xP (Tk k * psi a') * yP (Tk k * psi b')) * (dd k * dd k')
      = wP (psi c) * xP (psi a) * yP (psi b) *
          ((wP (Tk k * Tk k * psi c') * xP (Tk k * psi a') * yP (Tk k * psi b')) * dd k) * dd k' := by
        simp only [mul_assoc]
    _ = wP (psi c) * xP (psi a) * yP (psi b) * (dd k * (wP (psi c') * xP (psi a') * yP (psi b'))) *
          dd k' := by rw [hD]
    _ = _ := by simp only [mul_assoc]

theorem nfY_one : nfY one = 1 := by
  simp only [nfY, one, gf4_zero_eq, map_zero, xP_zero, wP_zero, yP_zero, dd_zero, one_mul, mul_one]

theorem nfY_inj : Function.Injective nfY := by
  rintro ⟨a, b, c, k⟩ ⟨a', b', c', k'⟩ h
  rw [nfY_eq_proj, nfY_eq_proj] at h
  obtain ⟨s, -, hs⟩ := exists_smul_of_proj_eq h
  rw [mat_entries, mat_entries] at hs
  have e11 := congrFun (congrFun hs 1) 1
  have e00 := congrFun (congrFun hs 0) 0
  have e01 := congrFun (congrFun hs 0) 1
  have e02 := congrFun (congrFun hs 0) 2
  have e12 := congrFun (congrFun hs 1) 2
  simp at e11 e00 e01 e02 e12
  subst e11
  simp only [one_mul, tU_val] at e00 e01 e02 e12
  have hk : k = k' := Tk_inj e00.symm
  subst hk
  have hTi : (Tk k)⁻¹ ≠ 0 := inv_ne_zero (Tk_ne k)
  have hb : psi b' = psi b := mul_right_cancel₀ hTi e12
  have ha : psi a' = psi a := e01
  have hc : psi c' = psi c := by
    rw [hb, ha] at e02
    exact add_left_cancel (mul_right_cancel₀ hTi e02)
  have ha' := psi.injective ha
  have hb' := psi.injective hb
  have hc' := psi.injective hc
  subst ha' hb' hc'
  rfl

noncomputable abbrev V1' : Subgroup YF := CFSG.QuasithinUnique.Fin257.L3.V1
noncomputable abbrev V2' : Subgroup YF := CFSG.QuasithinUnique.Fin257.L3.V2

@[expose] noncomputable def B0 : Subgroup YF :=
  Subgroup.normalizer ((V2' : Subgroup YF) : Set YF) ⊓ Subgroup.normalizer ((V1' : Subgroup YF) : Set YF)

theorem wP_mem_U (c : KF) : wP c ∈ projUnitriangular 3 KF := by
  refine mem_Ubar.mpr ⟨c, 0, 0, ?_⟩
  rw [xP_zero, yP_zero, mul_one, mul_one]

theorem xP_mem_U (a : KF) : xP a ∈ projUnitriangular 3 KF := by
  refine mem_Ubar.mpr ⟨0, a, 0, ?_⟩
  rw [wP_zero, yP_zero, one_mul, mul_one]

theorem yP_mem_U (b : KF) : yP b ∈ projUnitriangular 3 KF := by
  refine mem_Ubar.mpr ⟨0, 0, b, ?_⟩
  rw [wP_zero, xP_zero, one_mul, one_mul]

theorem U_le_B0 {g : YF} (hg : g ∈ projUnitriangular 3 KF) : g ∈ B0 :=
  Subgroup.mem_inf.mpr ⟨U_le_normalizer_V2 hg, U_le_normalizer_V1 hg⟩

theorem dd_mem_B0 (k : Fin 3) : dd k ∈ B0 := by
  unfold dd
  exact Subgroup.mem_inf.mpr ⟨proj_diag_mem_normalizer_V2 (isDiag_dMat _ _),
    proj_diag_mem_normalizer_V1 (isDiag_dMat _ _)⟩

theorem nfY_mem_B0 (x : Elt) : nfY x ∈ B0 := by
  unfold nfY
  exact mul_mem (mul_mem (mul_mem (U_le_B0 (wP_mem_U _)) (U_le_B0 (xP_mem_U _)))
    (U_le_B0 (yP_mem_U _))) (dd_mem_B0 _)

theorem nfY_mem_V2_iff (x : Elt) : nfY x ∈ (V2' : Subgroup YF) ↔ x.1 = 0 ∧ x.2.2.2 = 0 := by
  constructor
  · intro h
    obtain ⟨b', c', hbc⟩ := mem_V2.mp h
    have h0 : nfY (0, psi.symm b', psi.symm c', 0) = yP b' * wP c' := by
      simp only [nfY, map_zero, xP_zero, dd_zero, mul_one, one_mul, RingEquiv.apply_symm_apply]
      exact wP_mul_yP c' b'
    have h1 := nfY_inj (h0.trans hbc.symm)
    subst h1
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine mem_V2.mpr ⟨psi x.2.1, psi x.2.2.1, ?_⟩
    simp only [nfY, h1, h2, map_zero, xP_zero, dd_zero, mul_one, one_mul]
    exact wP_mul_yP _ _

theorem tk_of_ne (u : KF) (hu : u ≠ 0) : ∃ j : Fin 3, u = Tk j := by
  obtain ⟨j, hj⟩ := tk_surj (psi.symm u) (by
    intro h
    apply hu
    have := congrArg psi h
    simpa using this)
  exact ⟨j, by rw [Tk, ← hj, RingEquiv.apply_symm_apply]⟩

theorem proj_dMat_scalar (c : Units KF) (hc : c ^ 3 = 1) : proj 3 KF (dMat c c) = 1 := by
  rw [proj_eq_one_iff, mem_scalars]
  refine ⟨c, hc, ?_⟩
  have hc3 : c * c * c = 1 := by rw [← hc, pow_three, mul_assoc]
  have h2 : (c * c)⁻¹ = c := inv_eq_of_mul_eq_one_right hc3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dMat, Matrix.scalar_apply, Matrix.diagonal, h2]

theorem torus_eq_dd (t₁ t₂ : Units KF) : ∃ k : Fin 3, proj 3 KF (dMat t₁ t₂) = dd k := by
  obtain ⟨j₁, e₁⟩ := tk_of_ne (t₁ : KF) t₁.ne_zero
  obtain ⟨j₂, e₂⟩ := tk_of_ne (t₂ : KF) t₂.ne_zero
  refine ⟨j₁ - j₂, ?_⟩
  have ht1 : (t₁ : KF) = (t₂ : KF) * Tk (j₁ - j₂) := by
    rw [e₁, Tk_sub j₁ j₂, ← e₂]
  have hc3 : (t₂⁻¹ : Units KF) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_one, e₂, inv_pow,
      show Tk j₂ ^ 3 = 1 from by rw [pow_three, ← mul_assoc, Tk_cube j₂]]
    simp
  have hu : t₁⁻¹ * tU (j₁ - j₂) = t₂⁻¹ * 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      tU_val, Units.val_one, mul_one, ht1]
    have h2 : (t₂ : KF) ≠ 0 := t₂.ne_zero
    have h3 : Tk (j₁ - j₂) ≠ 0 := Tk_ne _
    field_simp
  have key : (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) KF)⁻¹ * dMat (tU (j₁ - j₂)) 1 =
      dMat t₂⁻¹ t₂⁻¹ := by
    rw [dMat_inv, dMat_mul, hu, mul_one]
  unfold dd
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, key, proj_dMat_scalar _ hc3]

theorem B0_le_normalizer_U :
    B0 ≤ Subgroup.normalizer ((projUnitriangular 3 KF : Subgroup YF) : Set YF) := by
  rw [← U_eq_sup]
  intro a ha
  have hN1 : a ∈ Subgroup.normalizer ((V1' : Subgroup YF) : Set YF) := (Subgroup.mem_inf.mp ha).2
  have hN2 : a ∈ Subgroup.normalizer ((V2' : Subgroup YF) : Set YF) := (Subgroup.mem_inf.mp ha).1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hN1, Subgroup.mem_normalizer_iff_map_conj_eq.mp hN2]

theorem nfY_surj (g : YF) (hg : g ∈ B0) : ∃ x : Elt, nfY x = g := by
  have hN : g ∈ Subgroup.normalizer ((projUnitriangular 3 KF : Subgroup YF) : Set YF) :=
    B0_le_normalizer_U hg
  obtain ⟨u, hu, b, hb, rfl⟩ := torus3_mul hN
  obtain ⟨c, a, b', rfl⟩ := mem_Ubar.mp hu
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hb
  obtain ⟨k, hk⟩ := torus_eq_dd t₁ t₂
  refine ⟨(psi.symm a, psi.symm b', psi.symm c, k), ?_⟩
  simp only [nfY, RingEquiv.apply_symm_apply, hk]

@[expose] noncomputable def eBx (x : Elt) : B0 := ⟨nfY x, nfY_mem_B0 x⟩

@[expose] noncomputable def eB (i : Fin 192) : B0 := eBx (elt i)

@[expose] noncomputable def dB : B0 := eB 64

@[expose] noncomputable def gY : Fin 3 → B0 := ![eB 64, eB 16, eB 4]

theorem eBx_mul (x y : Elt) : eBx (mulE x y) = eBx x * eBx y := Subtype.ext (nfY_mul x y)

theorem nfY_gStd (l : Fin 3) : nfY (gStd () l) = (gY l).1 := by
  fin_cases l <;> rfl

theorem nfY_elt_ιB_exists (g : B0) : ∃ i : Fin 192, nfY (elt i) = g.1 :=
  ⟨idx (Classical.choose (nfY_surj g.1 g.2)), by
    rw [elt_idx]; exact Classical.choose_spec (nfY_surj g.1 g.2)⟩

@[expose] noncomputable def ιB (g : B0) : Fin 192 := Classical.choose (nfY_elt_ιB_exists g)

theorem nfY_elt_ιB (g : B0) : nfY (elt (ιB g)) = g.1 := Classical.choose_spec (nfY_elt_ιB_exists g)

@[expose] noncomputable def evalB (w : List (Fin 3)) (h : Fin 3 → B0) : B0 := w.foldl (fun acc l => acc * h l) 1

theorem nfY_fold (G : Fin 3 → Elt) (h : Fin 3 → B0) (hG : ∀ l, nfY (G l) = (h l).1)
    (w : List (Fin 3)) :
    ∀ (x : Elt) (y : B0), nfY x = y.1 →
      nfY (w.foldl (fun acc l => mulE acc (G l)) x) = (w.foldl (fun acc l => acc * h l) y).1 := by
  induction w with
  | nil => intro x y hxy; exact hxy
  | cons l w ih =>
    intro x y hxy
    simp only [List.foldl_cons]
    apply ih
    rw [nfY_mul, hG, hxy]
    exact (Subgroup.coe_mul _ _ _).symm

theorem nfY_evalW (G : Fin 3 → Elt) (h : Fin 3 → B0) (hG : ∀ l, nfY (G l) = (h l).1)
    (w : List (Fin 3)) : nfY (evalW w G) = (evalB w h).1 := by
  unfold evalW evalB
  exact nfY_fold G h hG w one 1 (by rw [nfY_one]; rfl)

theorem elt_16 : elt 16 = (1, 0, 0, 0) := by decide

theorem elt_4 : elt 4 = (0, 1, 0, 0) := by decide

@[expose] noncomputable def phiN (n : MulAut ↥B0) (x : Elt) : Elt := elt (ιB (n (eBx x)))

theorem nfY_phiN (n : MulAut ↥B0) (x : Elt) : nfY (phiN n x) = (n (eBx x)).1 := nfY_elt_ιB _

theorem nstab_of_cert (n : MulAut ↥B0)
    (hV : ∀ b : ↥B0, b.1 ∈ (V2' : Subgroup YF) → (n b).1 ∈ (V2' : Subgroup YF)) :
    ∃ y z : Elt, (n (eB 16)).1 = nfY y ∧ (n (eB 4)).1 = nfY z ∧
      y.2.1 = 0 ∧ y.2.2.2 = 0 ∧ y.1 ≠ 0 ∧ z.1 = 0 ∧ z.2.2.2 = 0 ∧ z.2.1 ≠ 0 := by
  have hm : ∀ x y, phiN n (mulE x y) = mulE (phiN n x) (phiN n y) := by
    intro x y
    apply nfY_inj
    rw [nfY_mul, nfY_phiN, nfY_phiN, nfY_phiN, eBx_mul, map_mul]
    rfl
  have hi : Function.Injective (phiN n) := by
    intro x y h
    have h1 : (n (eBx x)).1 = (n (eBx y)).1 := by rw [← nfY_phiN, ← nfY_phiN, h]
    have h2 : eBx x = eBx y := n.injective (Subtype.ext h1)
    exact nfY_inj (congrArg Subtype.val h2)
  have hV' : ∀ x : Elt, x.1 = 0 → x.2.2.2 = 0 → (phiN n x).1 = 0 ∧ (phiN n x).2.2.2 = 0 := by
    intro x h1 h2
    have h3 : (n (eBx x)).1 ∈ (V2' : Subgroup YF) := hV (eBx x) ((nfY_mem_V2_iff x).mpr ⟨h1, h2⟩)
    rw [← nfY_phiN] at h3
    exact (nfY_mem_V2_iff _).mp h3
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Certificates.certificate5167.2 (phiN n) hm hi hV'
  exact ⟨phiN n (elt 16), phiN n (elt 4), (nfY_phiN n _).symm, (nfY_phiN n _).symm,
    a1, a2, a3, a4, a5, a6⟩

end CFSG.GH74.QTGen4.DSGen4.L34
