module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Uni
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUd

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def scalU {d : K} (hd0 : d ≠ 0) (hdN : h.bar d * d = 1)
    (hd4 : d ^ 4 = 1) : unitarySU p f K 4 :=
  ⟨GeneralLinearGroup.scalar (Fin 4) (Units.mk0 d hd0), by
    rw [mem_unitarySU_iff h, GeneralLinearGroup.coe_scalar, Units.val_mk0]
    refine ⟨by rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hd4], ?_⟩
    rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, hdN, Matrix.diagonal_one]⟩

theorem coe_scalU {d : K} (hd0 : d ≠ 0) (hdN : h.bar d * d = 1) (hd4 : d ^ 4 = 1) :
    (((scalU h hd0 hdN hd4 : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      d • 1 := by
  change ((GeneralLinearGroup.scalar (Fin 4) (Units.mk0 d hd0) : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K) = d • 1
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem mk_scalU {d : K} (hd0 : d ≠ 0) (hdN : h.bar d * d = 1) (hd4 : d ^ 4 = 1) :
    (QuotientGroup.mk (scalU h hd0 hdN hd4) : StatedProj (StatedSU 4 (p ^ f) K)) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact ⟨Units.mk0 d hd0, rfl⟩

theorem ne_smul_of_orderOf {X : unitarySU p f K 4}
    (hz : orderOf (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) = 2) (a : K) :
    ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ a • 1 := by
  intro ha
  apply (by norm_num : (2 : ℕ) ≠ 1)
  rw [← hz, orderOf_eq_one_iff, QuotientGroup.eq_one_iff]
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := (Matrix.isUnits_det_units (X : GL (Fin 4) K)).ne_zero
    rw [ha, zero_smul, det_zero] at this
    exact this rfl
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]
  exact ha.symm

theorem det_eq_l_four {A : hypSU h 2 0} {l : K} :
    ((∃ v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K,
        (∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) ∧
        ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
          Sum.elim (fun _ => l) (fun _ => -l) i • v i) ∨
      (∃ e g : Fin 2 → HypIndex 2 0 → K,
        (∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i =
          l • e i) ∧
        (∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i =
          (-l) • g i) ∧
        (∀ i j, hypForm h 2 0 (e i) (e j) = 0) ∧ (∀ i j, hypForm h 2 0 (g i) (g j) = 0) ∧
        ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0)) →
    ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = l ^ 4 := by
  rintro (⟨v, hv, hAv⟩ | ⟨e, g, hAe, hAg, hee, hgg, heg⟩)
  · rw [InvClassU.det_of_eigen h (by simp) (G := 1) (Gi := 1)
      (by ext i j; simp [hv, one_apply]) (Matrix.one_mul 1) hAv]
    simp [Fintype.prod_sum_type]
    ring
  · have hge : ∀ i j, hypForm h 2 0 (g i) (e j) = if i = j then 1 else 0 := fun i j => by
      rw [← (hypForm_isSymm h).eq (e j) (g i), heg]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    have hG : (Matrix.of fun i j => hypForm h 2 0 (Sum.elim e g i) (Sum.elim e g j)) =
        (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      ext (i | i) (j | j) <;> simp [hee, hgg, heg, hge, one_apply]
    have hGG : (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        fromBlocks 0 1 1 0 = 1 := by
      rw [fromBlocks_multiply]
      simp [fromBlocks_one]
    rw [InvClassU.det_of_eigen h (by simp) hG hGG (d := Sum.elim (fun _ => l) (fun _ => -l))
      (by rintro (i | i); exacts [hAe i, hAg i])]
    simp [Fintype.prod_sum_type]
    ring

include h in
theorem false_of_sq_eq_smul_of_sq (hp2 : p ≠ 2) (h8 : p ^ f % 8 ≠ 7) {X : unitarySU p f K 4}
    (hz : orderOf (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) = 2) {c : K}
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = c • 1)
    (hc2 : c ^ 2 = -1) : False := by
  classical
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  set A : hypSU h 2 0 := (hypTransport h hR₀).symm X with hAdef
  set M : Matrix (Fin (2 * 2 + 0)) (Fin (2 * 2 + 0)) K :=
    ((X : GL (Fin (2 * 2 + 0)) K) : Matrix (Fin (2 * 2 + 0)) (Fin (2 * 2 + 0)) K) with hMdef
  have hX' : M * M = c • 1 := hX
  have hAm : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      transportInv h R₀ * M * R₀ :=
    coe_hypTransport_symm hR₀ X
  have hAA : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : GL (HypIndex 2 0) K) = c • 1 := by
    rw [hAm]
    calc transportInv h R₀ * M * R₀ * (transportInv h R₀ * M * R₀) =
        transportInv h R₀ * (M * (R₀ * transportInv h R₀) * M) * R₀ := by
          simp only [Matrix.mul_assoc]
      _ = c • 1 := by
          rw [mul_transportInv hR₀, Matrix.mul_one, hX', Matrix.mul_smul, Matrix.mul_one,
            Matrix.smul_mul, transportInv_mul hR₀]
  have hzA : orderOf (hypProj h 2 0 A) = 2 := by
    have e1 := hypPSUEquivStatedProj_hypProj hR₀ (by norm_num : 1 ≤ 2 * 2 + 0) A
    have e2 : hypTransport h hR₀ A = X := by rw [hAdef, MulEquiv.apply_symm_apply]
    rw [e2] at e1
    rw [← MulEquiv.orderOf_eq (hypPSUEquivStatedProj h hR₀ (by norm_num : 1 ≤ 2 * 2 + 0)), e1]
    exact hz
  obtain ⟨l, -, hAl, hcases⟩ :=
    InvClassU.classify_inv_U4 h hp2 A.2.1 (L4U4.orderOf_mk_eq_two h hzA)
  have hlc : l ^ 2 = c := by
    have := congrFun (congrFun (hAl.symm.trans hAA) (Sum.inl 0)) (Sum.inl 0)
    simpa using this
  have hdetA := (mem_hypSU.mp A.2).2
  have hfin : ∀ {l' : K}, l' ^ 2 = c →
      ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = l' ^ 4 →
      False := fun {l'} hl' hd => by
    rw [hdetA, show l' ^ 4 = (l' ^ 2) ^ 2 by ring, hl', hc2] at hd
    exact h2K (by linear_combination hd)
  rcases hcases with ⟨-, ⟨v, hv, hAv⟩ | ⟨d, hd, v, hv, hAv⟩⟩ | ⟨-, e, g, hAe, hAg, hee, hgg, heg⟩
  · exact hfin hlc (det_eq_l_four h (Or.inl ⟨v, hv, hAv⟩))
  · exact L4U4.false_of_D1 h hp2 h8 hd hv hAv
  · exact hfin hlc (det_eq_l_four h (Or.inr ⟨e, g, hAe, hAg, hee, hgg, heg⟩))

include h in
theorem inv_split (hp2 : p ≠ 2) (h8 : p ^ f % 8 ≠ 7) {z : StatedProj (StatedSU 4 (p ^ f) K)}
    (hz : orderOf z = 2) :
    (∃ X : unitarySU p f K 4, (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) = z ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1 ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1 ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1) ∨
    (p ^ f % 4 = 1 ∧ ∃ X : unitarySU p f K 4,
      (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) = z ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = -1) := by
  classical
  have := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective z
  have hns := ne_smul_of_orderOf hz
  have hX2 : X * X ∈ scal p f K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← sq, ← hz, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := val_of_mem_scal hX2
  have hMM : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) =
      (c : K) • 1 := by
    rw [← hc, Subgroup.coe_mul, Units.val_mul]
  have hc4 : (c : K) ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hMM
    rw [det_mul, ((mem_unitarySU_iff h).1 X.2).1, one_mul, det_smul, det_one, mul_one,
      Fintype.card_fin] at h1
    exact h1.symm
  have hcN : h.bar (c : K) * c = 1 := by
    have hu := ((mem_unitarySU_iff h).1 (X * X).2).2
    rw [hc] at hu
    have h1 := congrFun (congrFun hu 0) 0
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four] using h1
  have hc22 : ((c : K) ^ 2 - 1) * ((c : K) ^ 2 + 1) = 0 := by linear_combination hc4
  have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  rcases mul_eq_zero.1 hc22 with hc2 | hc2
  · have hc1 : ((c : K) - 1) * ((c : K) + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.1 hc1 with hc1 | hcm
    · left
      have hc1' : (c : K) = 1 := sub_eq_zero.1 hc1
      refine ⟨X, rfl, by rw [hMM, hc1', one_smul], fun h1 => hns 1 (by rw [h1, one_smul]),
        fun h1 => hns (-1) (by rw [h1, neg_one_smul])⟩
    · have hcm' : (c : K) = -1 := by linear_combination hcm
      by_cases hq : p ^ f % 4 = 1
      · exact Or.inr ⟨hq, X, rfl, by rw [hMM, hcm', neg_one_smul]⟩
      · left
        have hq3 : p ^ f % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
        obtain ⟨i, hi2, hiN⟩ := InvClassU.exists_sqrt_neg_one_norm_one h hq3
        have hi0 : i ≠ 0 := by
          rintro rfl
          rw [zero_mul] at hi2
          exact h2K (by linear_combination 2 * hi2)
        have hiN' : h.bar i⁻¹ * i⁻¹ = 1 := by
          rw [map_inv₀, ← mul_inv, mul_comm]
          change (h.norm i)⁻¹ = 1
          rw [hiN, inv_one]
        have hi4 : i⁻¹ ^ 4 = 1 := by
          rw [inv_pow, show i ^ 4 = (i * i) * (i * i) by ring, hi2]
          norm_num
        set Y : unitarySU p f K 4 := scalU h (inv_ne_zero hi0) hiN' hi4 * X with hY
        have hYm : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
            i⁻¹ • ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [hY, Subgroup.coe_mul, Units.val_mul, coe_scalU, Matrix.smul_mul, Matrix.one_mul]
        refine ⟨Y, ?_, ?_, ?_, ?_⟩
        · rw [hY, QuotientGroup.mk_mul, mk_scalU, one_mul]
        · rw [hYm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMM, hcm', smul_smul]
          have : i⁻¹ * i⁻¹ * (-1 : K) = 1 := by
            rw [← mul_inv, hi2]
            norm_num
          rw [this, one_smul]
        · intro h1
          apply hns i
          rw [hYm] at h1
          calc ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              i • (i⁻¹ • ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
                rw [smul_smul, mul_inv_cancel₀ hi0, one_smul]
            _ = i • 1 := by rw [h1]
        · intro h1
          apply hns (-i)
          rw [hYm] at h1
          calc ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              i • (i⁻¹ • ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
                rw [smul_smul, mul_inv_cancel₀ hi0, one_smul]
            _ = (-i) • 1 := by rw [h1, smul_neg, neg_smul]
  · exfalso
    have hc2' : (c : K) ^ 2 = -1 := by linear_combination hc2
    by_cases hq : p ^ f % 4 = 1
    · have := UnitaryConj.norm_eq_neg_one_of_sq h hq hc2'
      rw [UnitaryFieldData.norm, mul_comm] at this
      rw [this] at hcN
      exact h2K (by linear_combination -hcN)
    · exact false_of_sq_eq_smul_of_sq h hp2 h8 hz hMM hc2'

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
