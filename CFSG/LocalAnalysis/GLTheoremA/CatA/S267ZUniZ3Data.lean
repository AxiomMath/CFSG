module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Trans
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniZ1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Phan
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3 (blk mem_blk)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem commute_of_isDiag {x y : SG h} (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← hx.diagonal_diag,
    ← hy.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem isDiag_diagU (d : Fin 3 → K) (hn : ∀ i, h.bar (d i) * d i = 1) (hd : ∏ i, d i = 1) :
    (((diagU h d hn hd : SG h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  rw [coe_diagU]
  exact isDiag_diagonal d

theorem fixSubgroup_conj_eq (x : SG h) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set (SG h)) := by
  ext a
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro e
    calc a * x = (x * a * x⁻¹) * x := by rw [e]
      _ = x * a := by group
  · intro e
    calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [e]
      _ = a := by group

theorem exists_eq_tOne_pow_of_isDiag {lam : K} (hlamn : h.bar lam * lam = 1)
    (hlam : IsPrimitiveRoot lam 9) {s : SG h}
    (hsd : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) (hs9 : s ^ 9 = 1)
    (h12 : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 =
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2) :
    ∃ j : ℕ, s = tOne h hlamn ^ j := by
  have hdet : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_gramSU.1 s.2).2
  rw [← hsd.diagonal_diag, det_diagonal, Fin.prod_univ_three] at hdet
  simp only [Matrix.diag] at hdet
  have hy9 : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 9 = 1 := by
    have e := congrArg (fun g : SG h => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hs9
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one] at e
    rw [← hsd.diagonal_diag, diagonal_pow] at e
    have e11 := congrFun (congrFun e 1) 1
    rw [diagonal_apply_eq, one_apply_eq] at e11
    simpa [Matrix.diag] using e11
  obtain ⟨j, -, hj⟩ := hlam.eq_pow_of_pow_eq_one hy9
  have hy0 : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := by
    rintro h0
    rw [h0, zero_pow (by norm_num)] at hy9
    exact zero_ne_one hy9
  have h00 : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 2)⁻¹ := by
    rw [← h12] at hdet
    field_simp
    linear_combination hdet
  refine ⟨j, Subtype.ext (Units.ext ?_)⟩
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, tOne, coe_diagU, diagonal_pow,
    ← hsd.diagonal_diag]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.diag, Pi.pow_apply, dOne, Matrix.cons_val_zero]
    rw [h00, ← hj, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  · simp only [Fin.mk_one, Matrix.diag, Pi.pow_apply, dOne, Matrix.cons_val_one,
      Matrix.head_cons]
    exact hj.symm
  · simp only [Fin.reduceFinMk, Matrix.diag, Pi.pow_apply, dOne, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [← h12]
    exact hj.symm

theorem uU_ne_one (h2 : (2 : K) ≠ 0) : uU h ≠ 1 := by
  intro h1
  have e := congrArg (fun g : SG h => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) h1
  simp only [uU, coe_diagU, diagonal_apply_eq, Subgroup.coe_one, Units.val_one,
    one_apply_eq, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at e
  apply h2
  linear_combination -e

theorem uU_sq : uU h ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, uU, coe_diagU, diagonal_pow]
  have hpow : (![1, -1, -1] : Fin 3 → K) ^ 2 = 1 := by
    funext k
    fin_cases k <;> simp
  rw [hpow]
  rfl

theorem fieldUHom_uU (τ : K ≃+* K) : fieldUHom h τ (uU h) = uU h := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [fieldUHom_apply_entry, uU, coe_diagU]
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp
  · rw [diagonal_apply_ne _ hij, map_zero]

section Fix

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ] {σ : K ≃+* K} {f₀ : ℕ}
  (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀))
include hbar

theorem blockU_inf_fixSubgroup_eq :
    blockU h blk ⊓ fixSubgroup (fieldUHom h σ) = blockZ h hbar := by
  apply le_antisymm
  · rintro g ⟨hg, hfix⟩
    refine mem_blockZ_of_fixed hbar hg fun i j => ?_
    have e := congrArg (fun x : SG h => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j)
      (mem_fixSubgroup.1 hfix)
    exact e
  · intro g hg
    refine ⟨blockZ_le_blockU hbar hg, mem_fixSubgroup.2 ?_⟩
    exact primeFormFieldSU_eq_of_mem_blockZ hbar hg

theorem glaPLayer_blockZ_ne_bot (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2)
    (hq0 : 5 ≤ ℓ ^ f₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hζn : h.bar ζ * ζ = 1) (hζσ : σ ζ = ζ) : GLAPLayer p (blockZ h hbar) ≠ ⊥ := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hx : diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk hζ0) ∈ blockZ h hbar :=
    mem_blockZ_of_fixed hbar (diagU_blk_mem_blockU hζn hζ0) fun i j => by
      rw [coe_diagU]
      by_cases hij : i = j
      · subst hij
        fin_cases i <;> simp [hζσ, map_inv₀]
      · rw [diagonal_apply_ne _ hij, map_zero]
  have hy : swapBlk h ∈ blockZ h hbar :=
    mem_blockZ_of_fixed hbar swapBlk_mem_blockU fun i j => by
      rw [coe_swapBlk]
      fin_cases i <;> fin_cases j <;> simp [swapMat]
  have hdvd : p ∣ Nat.card (↥(blockZ h hbar) ⧸ Subgroup.center ↥(blockZ h hbar)) :=
    CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp hx hy
      (diagU_blk_pow hp hp2 hζ hζn) (diagU_blk_mul_swapBlk_ne hp hp2 hζ hζn)
  have hN : ((blockZ h hbar).subgroupOf (blockZ h hbar)).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp le_rfl hN
    (isQuasisimple_blockZ hbar hK0 hq0) hdvd

end Fix

section Data

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem z3Data_std (hℓ : ℓ ≠ 2) (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {f₀ : ℕ} (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) (hpQ : 3 ∣ ℓ ^ f₀ + 1)
    (hq : ℓ ^ f = (ℓ ^ f₀) ^ 3) (hq0 : 5 ≤ ℓ ^ f₀) {lam : K} (hlamn : h.bar lam * lam = 1)
    (hlam : IsPrimitiveRoot lam 9) {E : Subgroup (MulAut (SG h))}
    (hβE : MulAut.conj (tOne h hlamn) ∈ E) (hσE : fieldUHom h σ ∈ E)
    (hdec : ∀ γ ∈ E, ∃ k : ℤ, ∃ s : SG h,
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧ s ^ 9 = 1 ∧
        γ = fieldUHom h σ ^ k * MulAut.conj s) :
    Z3Data 3 (SG h) E := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp3⟩
  have hq5 : 5 ≤ ℓ ^ f := hq0.trans (by rw [hq]; exact Nat.le_self_pow (by norm_num) _)
  set t := tOne h hlamn with htdef
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  have hlam3 : lam ^ 3 ≠ 1 := fun h3 => by
    have := hlam.dvd_of_pow_eq_one 3 h3
    omega
  have hζ : IsPrimitiveRoot (lam ^ 3) 3 := hlam.pow (by norm_num) (by norm_num)
  have hζn : h.bar (lam ^ 3) * lam ^ 3 = 1 := by rw [map_pow, ← mul_pow, hlamn, one_pow]
  have htd : t = diagU h (dOne lam) (norm_dOne hlamn) (prod_dOne hlam0) := rfl
  have h12 : dOne lam 1 = dOne lam 2 := dOne_one_eq_two lam
  have hd01 : dOne lam 0 ≠ dOne lam 1 := dOne_zero_ne_one hlam0 hlam3
  have htD : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := isDiag_diagU _ _ _
  have hcomp : GLAPComponent 3 (Subgroup.centralizer ({t} : Set (SG h))) (blockU h blk) := by
    rw [htd]
    exact glaPComponent_cent_diagU (d := dOne lam) (hn := norm_dOne hlamn) (hd := prod_dOne hlam0)
      hK hq5 hp3 (by norm_num) hζ hζn h12 hd01
  have hJ : GLAPLayer 3 (fixSubgroup (MulAut.conj t)) = blockU h blk := by
    rw [fixSubgroup_conj_eq]
    refine CFSG.LocalAnalysis.GLTheoremA.H81.layer_eq_of_unique hcomp fun L hL => ?_
    rw [htd] at hL
    exact eq_of_glaPComponent_cent_diagU hK hq5 h12 hd01 hL
  obtain ⟨a, han, haσ⟩ := exists_norm_one_not_fixed h (le_refl 3) hK0 hq
    (le_trans (by norm_num) hq0)
  have ha0 : a ≠ 0 := ne_zero_of_norm han
  set j₁ := diagU h ![1, a, a⁻¹] (norm_diagBlk han) (prod_diagBlk ha0) with hj₁
  have hj₁J : j₁ ∈ blockU h blk := diagU_blk_mem_blockU han ha0
  have hj₁D : ((j₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := isDiag_diagU _ _ _
  have hfix_a : ∀ τ : K ≃+* K, fieldUHom h τ j₁ = j₁ → τ a = a := by
    intro τ e
    have e11 := congrArg (fun x : SG h => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) e
    simp only [fieldUHom_apply_entry, hj₁, coe_diagU, diagonal_apply_eq] at e11
    simpa using e11
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_char h hℓ
  have huD : ((uU h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := isDiag_diagU _ _ _
  refine ⟨MulAut.conj t, hβE, ?_, ?_, ?_, ⟨fieldUHom h σ, hσE, ?_, ?_⟩,
    ⟨Subgroup.zpowers (uU h), ?_, ?_, ?_⟩, uU h, uU_ne_one h2, uU_sq, ?_, ?_⟩
  ·
    intro h1
    have htc : t ∈ Subgroup.center (SG h) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have e : t * g * t⁻¹ = g := by
        have := congrArg (fun φ : MulAut (SG h) => φ g) h1
        simpa [MulAut.conj_apply] using this
      calc g * t = t * g * t⁻¹ * t := by rw [e]
        _ = t * g := by group
    rw [center_SG h hℓ] at htc
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 htc
    have h00 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    have h11 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 1 1) hc
    simp only [htd, coe_diagU, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq] at h00 h11
    exact hd01 (h00.trans h11.symm)
  · rw [hJ, fixSubgroup_conj_eq]
    exact hcomp
  ·
    intro γ hγ hcent
    rw [hJ] at hcent
    obtain ⟨k, s, hsd, hs9, rfl⟩ := hdec γ hγ
    have hJq : CFSG.Open.IsQuasisimple ↥(blockU h blk) := isQuasisimple_blockU hK hq5 (by decide)
    have hpJ : 3 ∣ Nat.card ↥(blockU h blk) :=
      (dvd_card_blockU_blk hp3 (by norm_num) hζ hζn).trans (Subgroup.card_quotient_dvd_card _)
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp3
      hJq hpJ (fieldUHom h σ ^ k * MulAut.conj s).toMonoidHom hcent
    have hk1 : fieldUHom h σ ^ k = 1 := by
      have e : (fieldUHom h σ ^ k * MulAut.conj s) j₁ = j₁ := hfix j₁ hj₁J
      rw [MulAut.mul_apply, MulAut.conj_apply, commute_of_isDiag hsd hj₁D, mul_assoc,
        mul_inv_cancel, mul_one, ← map_zpow] at e
      obtain ⟨m, rfl⟩ := dvd_of_zpow_apply_eq hp3 hσ haσ (hfix_a _ e)
      have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
      rw [_root_.zpow_mul, zpow_natCast, ← map_pow, hσ3, map_one, _root_.one_zpow]
    rw [hk1, one_mul]
    have hsJ : ∀ j ∈ blockU h blk, s * j = j * s := by
      intro j hj
      have e : (fieldUHom h σ ^ k * MulAut.conj s) j = j := hfix j hj
      rw [hk1, one_mul, MulAut.conj_apply] at e
      calc s * j = s * j * s⁻¹ * s := by group
        _ = j * s := by rw [e]
    have hsw := hsJ (swapBlk h) swapBlk_mem_blockU
    have e12 := congrArg (fun x : SG h => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2) hsw
    simp only [Subgroup.coe_mul, Units.val_mul, coe_swapBlk] at e12
    rw [← hsd.diagonal_diag, diagonal_mul, mul_diagonal] at e12
    have h12s : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 =
        ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
      simpa [swapMat, Matrix.diag] using e12
    obtain ⟨j, rfl⟩ := exists_eq_tOne_pow_of_isDiag hlamn hlam hsd hs9 h12s
    exact Subgroup.mem_zpowers_iff.2 ⟨j, by rw [zpow_natCast, ← map_pow]⟩
  ·
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply haσ
    apply hfix_a
    have htj : Commute t j₁ := commute_of_isDiag htD hj₁D
    rw [← hm, ← map_zpow, MulAut.conj_apply, (htj.zpow_left m).eq, mul_assoc, mul_inv_cancel,
      mul_one]
  ·
    obtain ⟨ζ, hζσ, hζ3, hζn'⟩ := exists_primitiveRoot_fixed h hp3 hK0 hbar hpQ
    rw [hJ, blockU_inf_fixSubgroup_eq hbar]
    exact glaPLayer_blockZ_ne_bot hbar hK0 hq0 hp3 (by norm_num) hζ3 hζn' hζσ
  ·
    intro hb
    apply uU_ne_one h2
    have hmem : uU h ∈ Subgroup.zpowers (uU h) := Subgroup.mem_zpowers _
    rw [hb, Subgroup.mem_bot] at hmem
    exact hmem
  ·
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hdvd : orderOf (x : SG h) ∣ 2 :=
      (orderOf_dvd_of_mem_zpowers x.2).trans (orderOf_dvd_of_pow_eq_one uU_sq)
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  ·
    intro γ hγ
    obtain ⟨k, s, hsd, -, rfl⟩ := hdec γ hγ
    rw [MonoidHom.map_zpowers]
    congr 1
    change (fieldUHom h σ ^ k * MulAut.conj s) (uU h) = uU h
    rw [MulAut.mul_apply, MulAut.conj_apply, commute_of_isDiag hsd huD,
      mul_assoc, mul_inv_cancel, mul_one, ← map_zpow, fieldUHom_uU]
  ·
    rw [MulAut.conj_apply, commute_of_isDiag htD huD, mul_assoc, mul_inv_cancel, mul_one]
  ·
    rw [hJ]
    exact fun j hj => uU_comm_blockU hj

end Data

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
