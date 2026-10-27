module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineE3Core

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
  GenLocL3Nine GenLocL3NineR3 GenLocL3NineE3
open scoped MatrixGroups Classical

namespace GenLocL3NineE3

variable {K : Type} [Field K]

theorem reflection_not_mem_noDual [Finite K] {y : MulAut (LinearFlag.projectiveSL 3 K)} {v : Fin 3 → Kˣ}
    (h : y = LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.fieldAut 3 K 1 * LinearFlag.dualAut 3 K ^ 1) :
    y ∉ noDual K := by
  intro hy
  apply dualAut_not_mem_noDual (K := K)
  have hc : LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.fieldAut 3 K 1 ∈ noDual K :=
    ⟨diag3 v, 1, isDiag_diag3 v, rfl⟩
  have : LinearFlag.dualAut 3 K = (LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.fieldAut 3 K 1)⁻¹ * y := by
    rw [h, pow_one]; group
  rw [this]
  exact (noDual K).mul_mem ((noDual K).inv_mem hc) hy

theorem odd_coord_aux (w : Fin 3 → Kˣ) (j k r : Fin 3) (hcov : ∀ i, i = j ∨ i = k ∨ i = r)
    (hs : ∀ i i', (w i : K) * w i = w i' * w i') (hjk : w j = w k)
    (hne : LinearFlag.conjAut 3 K (diag3 w) ≠ 1) : (w r : K) = -(w j : K) := by
  have hsc : ∀ (c : Kˣ), (∀ i, w i = c) → LinearFlag.conjAut 3 K (diag3 w) = 1 := by
    intro c hw
    have : w = fun i => c * (fun _ => (1 : Kˣ)) i := by
      funext i; simp [hw i]
    rw [this, conjAut_diag3_smul]
    have h1 : diag3 (fun _ : Fin 3 => (1 : Kˣ)) = (1 : GL (Fin 3) K) := by
      apply Units.ext
      rw [coe_diag3]
      simp
    rw [h1, map_one]
  have : ((w r : K) - w j) * ((w r : K) + w j) = 0 := by linear_combination hs r j
  rcases mul_eq_zero.1 this with h | h
  · exfalso
    apply hne
    refine hsc (w j) fun i => ?_
    rcases hcov i with rfl | rfl | rfl
    · rfl
    · exact hjk.symm
    · exact Units.ext (by linear_combination h)
  · linear_combination h

theorem w_rel (t : Fin 3) {w : Fin 3 → Kˣ} (hs : ∀ i i', (w i : K) * w i = w i' * w i')
    (hwt : w (crd t 0) = w (crd t 1)) (hne : LinearFlag.conjAut 3 K (diag3 w) ≠ 1) :
    (w (crd (t + 1) 0) : K) = -(w (crd (t + 1) 1) : K) := by
  fin_cases t
  · have := odd_coord_aux w 1 2 0 (by decide) hs hwt hne
    simp [crd] at hwt this ⊢
    rw [this, ← hwt]
  · have := odd_coord_aux w 0 2 1 (by decide) hs hwt hne
    simp [crd] at hwt this ⊢
    linear_combination this
  · have := odd_coord_aux w 0 1 2 (by decide) hs hwt hne
    simp [crd] at hwt this ⊢
    have h10 : (w 1 : K) = w 0 := by rw [hwt]
    linear_combination this + h10

theorem pow_eight_eq_one [Finite K] (hK : Nat.card K = 9) {a : K} (ha : a ≠ 0) : a ^ 8 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 9 := by rw [Fintype.card_eq_nat_card]; exact hK
  have := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [hK'] at this

theorem isSquare_of_pow_four [Finite K] (hK : Nat.card K = 9) {a : K} (ha : a ≠ 0) (h : a ^ 4 = 1) :
    IsSquare a := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 9 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2 : ringChar K ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  rw [FiniteField.isSquare_iff h2 ha, hK']
  simpa using h

theorem isSquare_neg_one_nine [Finite K] (hK : Nat.card K = 9) : IsSquare (-1 : K) := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 9 := by rw [Fintype.card_eq_nat_card]; exact hK
  rw [FiniteField.isSquare_neg_one_iff, hK']
  norm_num

theorem isSquare_mul_of_pow_four_eq [Finite K] (hK : Nat.card K = 9) (a b : Kˣ)
    (h : (a : K) ^ 4 = (b : K) ^ 4) : IsSquare ((a : K) * b) := by
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hb : (b : K) ≠ 0 := b.ne_zero
  apply isSquare_of_pow_four hK (mul_ne_zero ha hb)
  rw [mul_pow, ← h, ← pow_add]
  exact pow_eight_eq_one hK ha

theorem excE3 [Finite K] (hK : Nat.card K = 9) : ExcE3 K := by
  intro D hfs hA h8 hshape
  obtain ⟨⟨yF, uF, σF, εF, hεF, hyF, hσF⟩, ⟨τ, hτ1, hτd⟩, huniq⟩ := hshape
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have : Fintype ↥D := Fintype.ofFinite _
  have hD := hA.1
  have hcardD : (Finset.univ : Finset ↥D).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h8]
  have hsq : ∀ z : D, z * z = 1 := fun z => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD z
  have hsqv : ∀ z : D, (z : MulAut (LinearFlag.projectiveSL 3 K)) * (z : MulAut (LinearFlag.projectiveSL 3 K)) = 1 :=
    fun z => congrArg Subtype.val (hsq z)
  have hT1 : (T1D D).card ≤ 2 := by
    have hsub : T1D D ⊆ {1, τ} := by
      intro z hz
      by_cases hz1 : z = 1
      · simp [hz1]
      · have := huniq z τ hz1 hτ1 ((mem_T1D D).1 hz) hτd
        simp [this]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hmul := card_le_mul_T1D D hK hfs hD
  rw [hcardD] at hmul
  have himg4 : ((Finset.univ : Finset ↥D).image (typ D hfs)).card ≤ 4 := by
    calc _ ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_le_univ _
      _ = 4 := by simp
  have himg : ((Finset.univ : Finset ↥D).image (typ D hfs)).card = 4 := by
    have : 4 ≤ ((Finset.univ : Finset ↥D).image (typ D hfs)).card := by
      by_contra h
      push Not at h
      have : (T1D D).card * ((Finset.univ : Finset ↥D).image (typ D hfs)).card ≤ 2 * 3 :=
        Nat.mul_le_mul hT1 (by omega)
      omega
    omega
  have himgU : (Finset.univ : Finset ↥D).image (typ D hfs) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [himg]; simp)
  obtain ⟨ya, -, hya⟩ := Finset.mem_image.1 (himgU ▸ Finset.mem_univ (false, true))
  obtain ⟨yr, -, hyr⟩ := Finset.mem_image.1 (himgU ▸ Finset.mem_univ (true, false))
  obtain ⟨u, σ, ε, hε, hyu, hty⟩ := typ_spec D hfs ya
  obtain ⟨v, σ', ε', hε', hyv, hty'⟩ := typ_spec D hfs yr
  rw [hya] at hty
  rw [hyr] at hty'
  obtain ⟨h1, h2⟩ := Prod.mk.inj hty
  obtain ⟨h1', h2'⟩ := Prod.mk.inj hty'
  have hσ1 : σ ≠ 1 := by intro h; simp [h] at h1
  have hε0 : ε = 0 := by by_contra h; simp [h] at h2
  have hσ'1 : σ' = 1 := by by_contra h; simp [h] at h1'
  have hε'1 : ε' = 1 := by
    by_contra h
    have : ε' = 0 := by omega
    simp [this] at h2'
  subst hε0 hσ'1 hε'1
  have hσσ : σ * σ = 1 := sigma_sq_one_of_involution (hsqv ya) (Nat.zero_le 1) hyu
  have hpow := sigma_eq_pow hK hσ1 hσσ
  have hcomm : (ya : MulAut (LinearFlag.projectiveSL 3 K)) * yr = yr * ya :=
    (WeakSigGen.forall_of_isElementaryAbelian hD).1 ya.1 ya.2 yr.1 yr.2
  have hx := comm_relation hcomm hpow hyu hyv
  have hu4 := quartic_equal hK (hsqv ya) hσ1 hyu
  obtain ⟨t, w, hw, hwt, hws⟩ := T1D_data D hD ((mem_T1D D).2 hτd)
  have hne_w : LinearFlag.conjAut 3 K (diag3 w) ≠ 1 := by
    intro h
    apply hτ1
    apply Subtype.ext
    rw [hw, h]; rfl
  have hni : ∀ m : Fin 3, ¬ (blkAct D hfs m).range ≤
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := fun m h =>
    rho_not_inner_of_field m (hfs yF.2) hεF hyF hσF (h ⟨yF, rfl⟩)
  have hgood : GoodBlk D hfs t :=
    goodBlk_of_ker_not_inner hK D hfs hA h8 t τ hτ1 (rho_eq_one_of_eq t (hfs τ.2) hw hwt) (hni t)
  have hbt : t + 1 ≠ t := by fin_cases t <;> decide
  have hwrel := w_rel t hws hwt hne_w
  have hvsq : IsSquare ((v (crd (t + 1) 0) : K) * v (crd (t + 1) 1)) := by
    apply isSquare_mul_of_pow_four_eq hK
    have e1 := hx (crd (t + 1) 0) (crd (t + 1) 1)
    have e2 := hu4 (crd (t + 1) 0) (crd (t + 1) 1)
    have e3 : (((u (crd (t + 1) 0) : Kˣ) : K) * (v (crd (t + 1) 0) : K)) ^ 4 =
        (((u (crd (t + 1) 1) : Kˣ) : K) * (v (crd (t + 1) 1) : K)) ^ 4 := by
      have := congrArg (fun z => z ^ 2) e1
      simp only [← pow_mul] at this
      exact this
    rw [mul_pow, mul_pow, e2] at e3
    exact mul_left_cancel₀ (pow_ne_zero 4 (u (crd (t + 1) 1)).ne_zero) e3
  have hya1 : ∀ (yf : D) (uf : Fin 3 → Kˣ), (yf : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 uf) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ 0 →
      yf ≠ 1 ∧ yf ≠ yr := by
    intro yf uf hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : LinearFlag.conjAut 3 K (diag3 uf) * LinearFlag.fieldAut 3 K σ = 1 := by
        rw [← mul_one (LinearFlag.conjAut 3 K (diag3 uf) * LinearFlag.fieldAut 3 K σ), ← pow_zero (LinearFlag.dualAut 3 K),
          ← hf, h]
        rfl
      exact hσ1 (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1).1
    · apply reflection_not_mem_noDual hyv
      rw [← h, hf, pow_zero, mul_one]
      exact ⟨diag3 uf, σ, isDiag_diag3 uf, rfl⟩
  have hyr1 : yr ≠ 1 := by
    intro h
    apply reflection_not_mem_noDual hyv
    rw [h]
    exact (noDual K).one_mem
  by_cases hxe : (v (crd (t + 1) 0) : K) * (u (crd (t + 1) 0) : K) =
      (v (crd (t + 1) 1) : K) * (u (crd (t + 1) 1) : K)
  · obtain ⟨hya1', hyar⟩ := hya1 ya u hyu
    exact e3_core D hfs hA h8 hbt hgood ya yr hya1' hyr1 hyar hpow hyu hyv hxe hvsq
  ·
    have hc : ((ya * τ : D) : MulAut (LinearFlag.projectiveSL 3 K)) =
        LinearFlag.conjAut 3 K (diag3 u * GeneralLinearGroup.map (σ : K →+* K) (diag3 w)) *
          LinearFlag.fieldAut 3 K σ := by
      have h1 : ((ya * τ : D) : MulAut (LinearFlag.projectiveSL 3 K)) =
          LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ *
            (LinearFlag.conjAut 3 K (diag3 w) * LinearFlag.fieldAut 3 K 1) := by
        show (ya : MulAut (LinearFlag.projectiveSL 3 K)) * τ = _
        rw [hyu, hw, pow_zero, mul_one, map_one, mul_one]
      rw [h1, LinearFlag.conjAut_mul_fieldAut_mul, mul_one]
    have hdiag : ((diag3 u * GeneralLinearGroup.map (σ : K →+* K) (diag3 w) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag := by
      rw [Units.val_mul]
      exact GenLocL3NFFrame.isDiag_mul' (isDiag_diag3 u)
        (GenLocL3NFFrame.isDiag_map_gl σ (isDiag_diag3 w))
    obtain ⟨u', hu'⟩ := exists_diag3 hdiag
    have hentry : ∀ i, ((u' i : Kˣ) : K) = (u i : K) * σ (w i : K) := by
      intro i
      have h0 : ((diag3 u * GeneralLinearGroup.map (σ : K →+* K) (diag3 w) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = ((diag3 u' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hu']
      have := congrFun (congrFun h0 i) i
      simp only [Units.val_mul, coe_diag3, coe_map_diag3, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_eq] at this
      exact this.symm
    have hf' : ((ya * τ : D) : MulAut (LinearFlag.projectiveSL 3 K)) =
        LinearFlag.conjAut 3 K (diag3 u') * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ 0 := by
      rw [hc, hu', pow_zero, mul_one]
    obtain ⟨hyf1, hyfr⟩ := hya1 (ya * τ) u' hf'
    have hneg : (v (crd (t + 1) 0) : K) * (u (crd (t + 1) 0) : K) =
        -((v (crd (t + 1) 1) : K) * (u (crd (t + 1) 1) : K)) := by
      have e1 := hx (crd (t + 1) 0) (crd (t + 1) 1)
      have : ((v (crd (t + 1) 0) : K) * u (crd (t + 1) 0) -
          (v (crd (t + 1) 1) : K) * u (crd (t + 1) 1)) *
          ((v (crd (t + 1) 0) : K) * u (crd (t + 1) 0) +
          (v (crd (t + 1) 1) : K) * u (crd (t + 1) 1)) = 0 := by
        linear_combination e1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linear_combination h) hxe
      · linear_combination h
    have hjk : (v (crd (t + 1) 0) : K) * (u' (crd (t + 1) 0) : K) =
        (v (crd (t + 1) 1) : K) * (u' (crd (t + 1) 1) : K) := by
      rw [hentry, hentry, hpow, hpow, hwrel]
      linear_combination (-((w (crd (t + 1) 1) : Kˣ) : K) ^ 3) * hneg
    exact e3_core D hfs hA h8 hbt hgood (ya * τ) yr hyf1 hyr1 hyfr hpow hf' hyv hjk hvsq

end GenLocL3NineE3

end CFSG.GH74.Generic.BProg.B2
