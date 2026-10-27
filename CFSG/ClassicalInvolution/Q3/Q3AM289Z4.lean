module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Shape

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

section SU3

theorem s3_exists_sq_neg_one_F9 : ∃ i : F9, i * i = -1 := by
  have := Fintype.ofFinite F9
  have h : IsSquare (-1 : F9) := FiniteField.isSquare_neg_one_iff.mpr (by
    rw [← Nat.card_eq_fintype_card, card_F9]; norm_num)
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.symm⟩

@[expose] noncomputable def jjMat (i : F9) : Matrix (Fin 2) (Fin 2) F9 := !![i, 0; 0, -i]

theorem jjMat_mul_jjMat_neg {i : F9} (hi : i * i = -1) : jjMat i * jjMat (-i) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [jjMat, Matrix.mul_apply, Fin.sum_univ_two, hi]

theorem jjMat_neg_mul_jjMat {i : F9} (hi : i * i = -1) : jjMat (-i) * jjMat i = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [jjMat, Matrix.mul_apply, Fin.sum_univ_two, hi]

theorem det_jjMat {i : F9} (hi : i * i = -1) : (jjMat i).det = 1 := by
  simp [jjMat, Matrix.det_fin_two, hi]

theorem conjTr_jjMat_mul {i : F9} (hi : i * i = -1) :
    conjTr (unitaryInvolution F9 3 1) (jjMat i) * jjMat i = 1 := by
  have hs : (frobenius F9 3) i = -i := by
    rw [frobenius_def]
    calc i ^ 3 = i * (i * i) := by ring
      _ = -i := by rw [hi]; ring
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [jjMat, conjTr, Matrix.mul_apply, Fin.sum_univ_two, hs, hi, Matrix.transpose_apply,
      Matrix.map_apply]

@[expose] noncomputable def jjSU {i : F9} (hi : i * i = -1) : Su F9 3 1 2 :=
  ⟨⟨jjMat i, jjMat (-i), jjMat_mul_jjMat_neg hi, jjMat_neg_mul_jjMat hi⟩, det_jjMat hi,
    conjTr_jjMat_mul hi⟩

theorem suMat_jjSU {i : F9} (hi : i * i = -1) : suMat (jjSU hi) = jjMat i := rfl

theorem jjSU_mul_self {i : F9} (hi : i * i = -1) : jjSU hi * jjSU hi = negOneSU F9 3 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_jjSU, suMat_negOneSU]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [jjMat, Matrix.mul_apply, Fin.sum_univ_two, hi]

theorem suMat_blockEmb_jj {i : F9} (hi : i * i = -1) :
    suMat (blockEmb F9 3 1 3 2 0 (by omega) (jjSU hi)) =
      (Matrix.diagonal ![i, -i, 1] : Matrix (Fin 3) (Fin 3) F9) := by
  rw [suMat_blockEmb, suMat_jjSU]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, jjMat]

theorem suMat_blockEmb_negOne :
    suMat (blockEmb F9 3 1 3 2 1 (by omega) (negOneSU F9 3 1)) =
      (Matrix.diagonal ![1, -1, -1] : Matrix (Fin 3) (Fin 3) F9) := by
  rw [suMat_blockEmb, suMat_negOneSU]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply]

theorem su3_orderFour_triple : ∃ j d : SU3, j ∈ rootSU2₃ ∧ orderOf j = 4 ∧ d * d = 1 ∧ d ≠ 1 ∧
    d ≠ rootInvSU₃ ∧ j * d = d * j := by
  obtain ⟨i, hi⟩ := s3_exists_sq_neg_one_F9
  have h2 : (2 : F9) ≠ 0 := two_ne_zero_F9
  have hneg : (-1 : F9) ≠ 1 := neg_one_ne_one_of_two_ne_zero h2
  set j : SU3 := blockEmb F9 3 1 3 2 0 (by omega) (jjSU hi) with hj
  set d : SU3 := blockEmb F9 3 1 3 2 1 (by omega) (negOneSU F9 3 1) with hd
  have hjj : j * j = rootInvSU₃ := by
    rw [hj, ← map_mul, jjSU_mul_self]
    rfl
  refine ⟨j, d, ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ¬ j ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, hjj]
      exact rootInvSU₃_ne_one
    have h2' : j ^ 2 ^ (1 + 1) = 1 := by
      have : j ^ 2 ^ (1 + 1) = (j * j) * (j * j) := by
        rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl]
        simp [pow_succ, mul_assoc]
      rw [this, hjj, rootInvSU₃_mul_self]
    exact orderOf_eq_prime_pow h1 h2'
  · rw [hd, ← map_mul, negOneSU_mul_self, map_one]
  · intro h
    have := congrFun (congrFun (congrArg suMat h) 1) 1
    rw [hd, suMat_blockEmb_negOne, suMat_one] at this
    simp at this
    exact hneg this
  · intro h
    have := congrFun (congrFun (congrArg suMat h) 0) 0
    rw [hd, suMat_blockEmb_negOne, suMat_rootInvSU₃] at this
    simp at this
    exact hneg this.symm
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, hj, hd, suMat_blockEmb_jj hi, suMat_blockEmb_negOne,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext a
    fin_cases a <;> simp [mul_comm]

end SU3

section Abstract

variable {Q Y : Type} [Group Q] [Group Y]

theorem exists_order4_of_triple (ψ : Q →* Y) (hψ : Function.Bijective ψ)
    (hconj : CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj Q)
    {R : Subgroup Q} {r j d : Q} (hr : IsUniqueInvolution R r) (hj : j ∈ R) (hj4 : orderOf j = 4)
    (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdr : d ≠ r) (hjd : j * d = d * j) {u : Y}
    (hu : IsUniqueInvolution (R.map ψ) u) :
    ∃ g : Y, conjSub g (R.map ψ) ≠ R.map ψ ∧ ∃ w ∈ conjSub g (R.map ψ), orderOf w = 4 ∧
      w * u = u * w := by
  obtain ⟨h₀, hh₀⟩ := hconj d r hd2 hr.sq hd1 hr.ne_one
  have hψr : u = ψ r := by
    rcases hu.unique (ψ r) (Subgroup.mem_map_of_mem ψ hr.mem) (by rw [← map_mul, hr.sq, map_one])
      with h | h
    · exact absurd (hψ.1 (h.trans (map_one ψ).symm)) hr.ne_one
    · exact h.symm
  refine ⟨ψ h₀, ?_, ψ (h₀ * j * h₀⁻¹), ?_, ?_, ?_⟩
  · intro hEq
    have hmap : conjSub h₀ R = R := by
      have e : conjSub (ψ h₀) (R.map ψ) = (conjSub h₀ R).map ψ := by
        show (R.map ψ).map (MulAut.conj (ψ h₀)).toMonoidHom =
          (R.map (MulAut.conj h₀).toMonoidHom).map ψ
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp
      rw [e] at hEq
      exact Subgroup.map_injective hψ.1 hEq
    have hrR : h₀⁻¹ * r * h₀ ∈ R := by
      have h1 : r ∈ conjSub h₀ R := by
        rw [hmap]
        exact hr.mem
      rw [mem_conjSub_iff] at h1
      exact h1
    have hsq : (h₀⁻¹ * r * h₀) * (h₀⁻¹ * r * h₀) = 1 := by
      calc (h₀⁻¹ * r * h₀) * (h₀⁻¹ * r * h₀) = h₀⁻¹ * (r * r) * h₀ := by group
        _ = 1 := by rw [hr.sq]; group
    have hdr' : d = h₀⁻¹ * r * h₀ := by
      rw [← hh₀]
      group
    rcases hr.unique _ hrR hsq with h | h
    · exact hd1 (hdr'.trans h)
    · exact hdr (hdr'.trans h)
  · exact ⟨ψ j, Subgroup.mem_map_of_mem ψ hj, by simp [MulAut.conj_apply]⟩
  · have e : ψ (h₀ * j * h₀⁻¹) = ψ h₀ * ψ j * (ψ h₀)⁻¹ := by simp
    have : orderOf (ψ (h₀ * j * h₀⁻¹)) = orderOf (h₀ * j * h₀⁻¹) :=
      orderOf_injective ψ hψ.1 _
    rw [this]
    have h2 := MulEquiv.orderOf_eq (MulAut.conj h₀) j
    rw [MulAut.conj_apply] at h2
    exact h2.trans hj4
  · rw [hψr, ← map_mul, ← map_mul]
    congr 1
    calc h₀ * j * h₀⁻¹ * r = h₀ * j * h₀⁻¹ * (h₀ * d * h₀⁻¹) := by rw [hh₀]
      _ = h₀ * (j * d) * h₀⁻¹ := by group
      _ = h₀ * (d * j) * h₀⁻¹ := by rw [hjd]
      _ = (h₀ * d * h₀⁻¹) * (h₀ * j * h₀⁻¹) := by group
      _ = r * (h₀ * j * h₀⁻¹) := by rw [hh₀]

end Abstract

section Rows

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

theorem S3Shape.exists_order4 (h : S3Shape Φ) {J' : Subgroup Y} (hJ' : J' ∈ Φ) {u : Y}
    (hu : IsUniqueInvolution J' u) :
    ∃ g : Y, conjSub g J' ≠ J' ∧ ∃ w ∈ conjSub g J', orderOf w = 4 ∧ w * u = u * w := by
  obtain ⟨c, ψ, hc, hbij, hfund⟩ := h.exists_bijective
  obtain ⟨R, hR, hJR⟩ := hfund J' hJ'
  rw [hJR] at hu ⊢
  rcases hc with rfl | rfl | rfl
  · obtain ⟨e', he'⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
      Q3PP.statedLieAdmissible_psu3
    obtain ⟨g₀, hg₀⟩ := (Models.mem_longRootSetU_iff (by norm_num)).mp ((he' R).mp hR)
    have hg₀' : R.map e'.toMonoidHom = conjSub g₀ Q3PP.rootSU2₃ := hg₀
    let ψ' : Q3PP.SU3 →* Y := ψ.comp e'.symm.toMonoidHom
    have hψ' : Function.Bijective ψ' :=
      ⟨hbij.1.comp e'.symm.injective, hbij.2.comp e'.symm.surjective⟩
    have hJψ : R.map ψ = (conjSub g₀ Q3PP.rootSU2₃).map ψ' := by
      rw [← hg₀', Subgroup.map_map]
      congr 1
      ext x
      simp [ψ']
    obtain ⟨j₀, d₀, hj₀, hj₀4, hd₀2, hd₀1, hd₀r, hj₀d₀⟩ := su3_orderFour_triple
    have hL : IsLongRootSU2 Q3PP.F9 3 1 (by norm_num : 2 ≤ 3) (conjSub g₀ Q3PP.rootSU2₃)
        (g₀ * Q3PP.rootInvSU₃ * g₀⁻¹) := ⟨g₀, rfl, rfl⟩
    have hK : Nat.card Q3PP.F9 = (3 ^ 1) ^ 2 := Q3PP.card_F9
    have huniq : IsUniqueInvolution (conjSub g₀ Q3PP.rootSU2₃) (g₀ * Q3PP.rootInvSU₃ * g₀⁻¹) := by
      refine ⟨hL.mem, ?_, hL.mul_self, ?_⟩
      · intro h1
        apply Q3PP.rootInvSU₃_ne_one
        calc Q3PP.rootInvSU₃ = g₀⁻¹ * (g₀ * Q3PP.rootInvSU₃ * g₀⁻¹) * g₀ := by group
          _ = 1 := by rw [h1]; group
      · intro y hy hy2
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr (hL.eq_of_orderOf_eq_two hK (by norm_num) hy
            (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1))
    rw [hJψ] at hu ⊢
    have hjmem : g₀ * j₀ * g₀⁻¹ ∈ conjSub g₀ Q3PP.rootSU2₃ :=
      Subgroup.mem_map.mpr ⟨j₀, hj₀, by simp [MulAut.conj_apply]⟩
    have hj4 : orderOf (g₀ * j₀ * g₀⁻¹) = 4 := by
      have h2 := MulEquiv.orderOf_eq (MulAut.conj g₀) j₀
      rw [MulAut.conj_apply] at h2
      exact h2.trans hj₀4
    exact exists_order4_of_triple ψ' hψ'
      (CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.involutionsConj_su3 (p := 3) (f := 1)
        hK Q3PP.two_ne_zero_F9) huniq hjmem hj4
      (d := g₀ * d₀ * g₀⁻¹)
      (by calc g₀ * d₀ * g₀⁻¹ * (g₀ * d₀ * g₀⁻¹) = g₀ * (d₀ * d₀) * g₀⁻¹ := by group
            _ = 1 := by rw [hd₀2]; group)
      (by intro h1
          apply hd₀1
          calc d₀ = g₀⁻¹ * (g₀ * d₀ * g₀⁻¹) * g₀ := by group
            _ = 1 := by rw [h1]; group)
      (by intro h1
          apply hd₀r
          calc d₀ = g₀⁻¹ * (g₀ * d₀ * g₀⁻¹) * g₀ := by group
            _ = g₀⁻¹ * (g₀ * Q3PP.rootInvSU₃ * g₀⁻¹) * g₀ := by rw [h1]
            _ = Q3PP.rootInvSU₃ := by group)
      (by calc g₀ * j₀ * g₀⁻¹ * (g₀ * d₀ * g₀⁻¹) = g₀ * (j₀ * d₀) * g₀⁻¹ := by group
            _ = g₀ * (d₀ * j₀) * g₀⁻¹ := by rw [hj₀d₀]
            _ = g₀ * d₀ * g₀⁻¹ * (g₀ * j₀ * g₀⁻¹) := by group) hu
  · obtain ⟨r, j, d, hr, hj, hj4, hd, hd1, hdr, hjd⟩ :=
      Asc77.MuTab.g2_exists_orderFour (p := 3) (e := 1) (by norm_num) le_rfl hR
    exact exists_order4_of_triple ψ hbij (involutionsConj_of_rows (Or.inr (Or.inl rfl))) hr hj hj4
      hd hd1 hdr hjd hu
  · obtain ⟨r, j, d, hr, hj, hj4, hd, hd1, hdr, hjd⟩ :=
      Asc77.MuTab.td4_exists_orderFour (p := 3) (e := 1) (by norm_num)
        (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 from
          ⟨Nat.prime_three, le_rfl, rfl⟩) hR
    exact exists_order4_of_triple ψ hbij (involutionsConj_of_rows (Or.inr (Or.inr rfl))) hr hj hj4
      hd hd1 hdr hjd hu

end Rows

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
