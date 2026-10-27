module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfSL

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace ConfP

variable {K : Type} [Field K]

theorem coe_eq_or_neg_of_mem {x y : StatedSp 2 K} (h : x⁻¹ * y ∈ spScalars 2 K) :
    ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hy : ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((x⁻¹ * y : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]
  rcases (mem_spScalars_iff _).mp h with h1 | h1
  · left
    rw [hy, h1, Matrix.mul_one]
  · right
    rw [hy, h1, Matrix.mul_neg, Matrix.mul_one]

theorem sq_eq_or_neg_of_proj {T : StatedSp 2 K}
    (hTT : proj 2 K T * proj 2 K T = 1) :
    ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 ∨
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  have h : T * T ∈ spScalars 2 K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul]
    exact hTT
  rw [mem_spScalars_iff, Subgroup.coe_mul, Units.val_mul] at h
  exact h

theorem comm_or_anticomm_of_fix (A : gsp 2 K) {T : StatedSp 2 K}
    (hT : conjAut 2 K A (proj 2 K T) = proj 2 K T) :
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -(((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  rw [conjAut_proj] at hT
  have h := coe_eq_or_neg_of_mem (QuotientGroup.eq.mp hT)
  have hc : ((conjSp 2 K A T : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (A : GL (Fin 2 ⊕ Fin 2) K) * T * (A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := coe_conjSp A T
  have hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((((conjSp 2 K A T : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hc, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rcases h with h | h
  · left
    rw [hA, h]
  · right
    rw [hA, h, Matrix.neg_mul, neg_neg]

theorem mul_transpose_formJ (A : gsp 2 K) {d : K}
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K)
    (T : StatedSp 2 K) :
    (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ * formJ 2 K *
      (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
      d • formJ 2 K := by
  set Am := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAm
  set Tm := ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hTm
  have hT : Tmᵀ * formJ 2 K * Tm = formJ 2 K := symplectic_of_mem T
  rw [transpose_mul]
  calc Tmᵀ * Amᵀ * formJ 2 K * (Am * Tm) = Tmᵀ * (Amᵀ * formJ 2 K * Am) * Tm := by
        simp only [Matrix.mul_assoc]
    _ = Tmᵀ * (d • formJ 2 K) * Tm := by rw [hμ]
    _ = d • (Tmᵀ * formJ 2 K * Tm) := by rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = d • formJ 2 K := by rw [hT]

theorem comm_of_mem_fixOf (A : gsp 2 K) {Z : StatedSp 2 K} (hZ : Z ∈ fixOf (conjSp 2 K A)) :
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have h : conjSp 2 K A Z = Z := hZ
  have h' := congrArg (fun x : StatedSp 2 K => ((x : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_conjSp, Units.val_mul] at h'
  calc ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [Matrix.mul_assoc (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2)
          (Fin 2 ⊕ Fin 2) K) * ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2)
          (Fin 2 ⊕ Fin 2) K)), Units.inv_mul, Matrix.mul_one]
    _ = _ := by rw [h']

theorem mem_fixOf_of_comm (A : gsp 2 K) {Z : StatedSp 2 K}
    (h : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    Z ∈ fixOf (conjSp 2 K A) := by
  show conjSp 2 K A Z = Z
  apply sp_ext
  rw [coe_conjSp, Units.val_mul, Units.val_mul, h, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one]

theorem anti_of_cases {R : Type*} [Ring R] {a t D : R} (hAA : a * a = D)
    (hts : t * t = 1 ∨ t * t = -1) (hc : a * t = t * a ∨ a * t = -(t * a))
    (htype : a * t * (a * t) ≠ -D) (hnot : a * t = t * a → t * t = 1 → False) :
    a * t = -(t * a) ∧ t * t = -1 := by
  rcases hc with hc | hc <;> rcases hts with hs | hs
  · exact (hnot hc hs).elim
  · exfalso
    apply htype
    calc a * t * (a * t) = a * (t * a) * t := by simp only [mul_assoc]
      _ = a * (a * t) * t := by rw [hc]
      _ = a * a * (t * t) := by simp only [mul_assoc]
      _ = -D := by rw [hAA, hs, mul_neg, mul_one]
  · exfalso
    apply htype
    calc a * t * (a * t) = a * (t * a) * t := by simp only [mul_assoc]
      _ = a * (-(a * t)) * t := by rw [show t * a = -(a * t) by rw [hc, neg_neg]]
      _ = -(a * a * (t * t)) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -D := by rw [hAA, hs, mul_one]
  · exact ⟨hc, hs⟩

theorem proj_eq_one_of {T : StatedSp 2 K} (h : T = 1 ∨ T = negS K) : proj 2 K T = 1 := by
  rcases h with rfl | rfl
  · exact map_one _
  · rw [← MonoidHom.mem_ker, ker_proj]
    exact (mem_spScalars_iff _).mpr (Or.inr (coe_negS (K := K)))

theorem type_model {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K)
    (T : StatedSp 2 K) (hTfix : conjAut 2 K A (proj 2 K T) = proj 2 K T)
    (hTT : proj 2 K T * proj 2 K T = 1) (hT1 : proj 2 K T ≠ 1)
    (hadm : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣
      Nat.card (fixOf (conjAut 2 K A * MulAut.conj (proj 2 K T)))) :
    proj 2 K T ∉ (fixOf (conjSp 2 K A)).map (proj 2 K) ∧
      ∀ Z ∈ fixOf (conjSp 2 K A), proj 2 K Z * proj 2 K Z = 1 → proj 2 K Z ≠ 1 →
        ∃ g : StatedProj (StatedSp 2 K), g⁻¹ * proj 2 K Z * g = proj 2 K T := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (odd_card_of_card_eq hp hp2 hK)
  have hYc : conjAut 2 K A * MulAut.conj (proj 2 K T) =
      conjAut 2 K (A * ⟨T, statedSp_le_gsp T.2⟩) := by
    rw [map_mul, conjAut_statedSp]
  have hYm : (((A * ⟨T, statedSp_le_gsp T.2⟩ : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [Subgroup.coe_mul, Units.val_mul]
  rw [hYc] at hadm
  have htype : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ≠
      -(d • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    intro h
    apply not_dvd_card_fixOf_typeI hp hp2 hf hK _ (d := -d) (neg_ne_zero.mpr hd0)
      (by rw [hYm, h, neg_smul]) (by rw [hYm, neg_neg]; exact mul_transpose_formJ A hμ T) hadm
  have hnot : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 → False := by
    intro hc hs
    have hTT' : T * T = 1 := sp_ext (by
      rw [Subgroup.coe_mul, Units.val_mul, hs, OneMemClass.coe_one, Units.val_one])
    exact hT1 (proj_eq_one_of (fixOf_eq_one_or_negS hp hp2 hf hK A hd0 hdsq hAA hμ
      (mem_fixOf_of_comm A hc) hTT'))
  obtain ⟨hanti, hTm1⟩ := anti_of_cases hAA (sq_eq_or_neg_of_proj hTT)
    (comm_or_anticomm_of_fix A hTfix) htype hnot
  refine ⟨?_, ?_⟩
  · rintro ⟨Z, hZ, hZT⟩
    have hZA := comm_of_mem_fixOf A hZ
    have hTA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rcases coe_eq_or_neg_of_mem (QuotientGroup.eq.mp hZT) with h | h
      · rw [h, hZA]
      · rw [h, Matrix.mul_neg, Matrix.neg_mul, hZA]
    have h0 : (2 : K) • (((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hTA]
      rw [hanti, neg_add_cancel]
    have h0' := (smul_eq_zero.mp h0).resolve_left h2
    have hT0 : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 0 := by
      have h3 := congrArg (· * (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h0'
      simp only [Matrix.zero_mul] at h3
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h3
      exact h3
    rw [hT0, Matrix.zero_mul] at hTm1
    have h4 := congrFun (congrFun hTm1 (Sum.inl 0)) (Sum.inl 0)
    simp at h4
  · intro Z hZ hZZ hZ1
    have hZm1 : ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((Z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
      rcases sq_eq_or_neg_of_proj hZZ with hs | hs
      · exfalso
        have hZZ' : Z * Z = 1 := sp_ext (by
          rw [Subgroup.coe_mul, Units.val_mul, hs, OneMemClass.coe_one, Units.val_one])
        exact hZ1 (proj_eq_one_of (fixOf_eq_one_or_negS hp hp2 hf hK A hd0 hdsq hAA hμ hZ
          hZZ'))
      · exact hs
    obtain ⟨g₁, hg₁⟩ := exists_conj_T2 h2 T hTm1
    obtain ⟨g₂, hg₂⟩ := exists_conj_T2 h2 Z hZm1
    refine ⟨proj 2 K (g₂ * g₁⁻¹), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc (g₂ * g₁⁻¹)⁻¹ * Z * (g₂ * g₁⁻¹) = g₁ * (g₂⁻¹ * Z * g₂) * g₁⁻¹ := by group
      _ = g₁ * (g₁⁻¹ * T * g₁) * g₁⁻¹ := by rw [hg₂, hg₁]
      _ = T := by group

end ConfP

end CFSG.ComponentClassification.GSThmB
