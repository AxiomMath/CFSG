module

public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValField

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

abbrev M5c : Type := Matrix (Fin 5) (Fin 5) F4c

abbrev su5M (g : SU f4Frob 5) : M5c := ((g : GL (Fin 5) F4c) : M5c)

theorem su5M_mul (g h : SU f4Frob 5) : su5M (g * h) = su5M g * su5M h := rfl

theorem su5M_one : su5M 1 = 1 := rfl

theorem su5M_unitary (g : SU f4Frob 5) :
    conjTr f4Frob (su5M g) * (antidiag 5 : M5c) * su5M g = antidiag 5 :=
  g.2.2

theorem su5M_det (g : SU f4Frob 5) : (su5M g).det = 1 :=
  g.2.1

theorem fin5_rev0 : Fin.rev (0 : Fin 5) = 4 := rfl
theorem fin5_rev1 : Fin.rev (1 : Fin 5) = 3 := rfl
theorem fin5_rev2 : Fin.rev (2 : Fin 5) = 2 := rfl
theorem fin5_rev3 : Fin.rev (3 : Fin 5) = 1 := rfl
theorem fin5_rev4 : Fin.rev (4 : Fin 5) = 0 := rfl
theorem fin3_rev0 : Fin.rev (0 : Fin 3) = 2 := rfl
theorem fin3_rev1 : Fin.rev (1 : Fin 3) = 1 := rfl
theorem fin3_rev2 : Fin.rev (2 : Fin 3) = 0 := rfl

theorem card_SU_f4Frob_three : Nat.card (SU f4Frob 3) = 216 := by
  have := charP_f4c
  have hF : Nat.card F4c = (2 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, CFSG.GH74.Uniqueness.SU.SU5.F4c.card_eq]
    norm_num
  have e : unitaryInvolution F4c 2 1 = f4Frob := by
    ext c
    rw [unitaryInvolution_apply, f4Frob_apply, pow_one, sq]
  have h : (Nat.card (SU (unitaryInvolution F4c 2 1) 3) : ℤ) =
      ((2 ^ 1 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [Nat.card_congr (CFSG.LieType.Universal.Unitary.equivStatedSU hF 3).toEquiv]
    exact CFSG.RankThree.PartOne.KFU.card_statedSU_eq
      (CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hF le_rfl) (by norm_num)
  rw [e] at h
  have h' : (Nat.card (SU f4Frob 3) : ℤ) = 216 := by
    rw [h]
    decide
  exact_mod_cast h'

@[expose] def su5TM : M5c :=
  !![1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem su5TM_det : su5TM.det = 1 := by
  rw [det_of_corners (m := 3) su5TM (by decide) (by decide)]
  have h : (Matrix.of fun a b : Fin 3 => su5TM a.castSucc.succ b.castSucc.succ) = 1 := by
    decide
  rw [h, det_one]
  decide

@[expose] noncomputable def su5T : SU f4Frob 5 :=
  suMk f4Frob su5TM su5TM_det (by decide)

theorem su5M_su5T : su5M su5T = su5TM := rfl

theorem su5_t_comm {g : SU f4Frob 5} (hg : g ∈ Subgroup.centralizer {su5T}) :
    su5M g * su5TM = su5TM * su5M g := by
  have := congrArg su5M (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rwa [su5M_mul, su5M_mul, su5M_su5T] at this

theorem su5_t_shape {g : SU f4Frob 5} (hg : g ∈ Subgroup.centralizer {su5T}) :
    su5M g 1 0 = 0 ∧ su5M g 2 0 = 0 ∧ su5M g 3 0 = 0 ∧ su5M g 4 0 = 0 ∧ su5M g 4 1 = 0 ∧
      su5M g 4 2 = 0 ∧ su5M g 4 3 = 0 ∧ su5M g 4 4 = su5M g 0 0 := by
  have hc := su5_t_comm hg
  have e : ∀ i j, (su5M g * su5TM) i j = (su5TM * su5M g) i j := fun i j => by rw [hc]
  have e14 := e 1 4
  have e24 := e 2 4
  have e34 := e 3 4
  have e44 := e 4 4
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  have e04 := e 0 4
  simp [su5TM, Matrix.mul_apply, Fin.sum_univ_five] at e14 e24 e34 e44 e01 e02 e03 e04
  refine ⟨e14, e24, e34, e44, e01, e02, e03, ?_⟩
  rw [add_comm (su5M g 0 0)] at e04
  exact (add_left_cancel e04).symm

@[expose] def su5Mid (g : M5c) : Matrix (Fin 3) (Fin 3) F4c :=
  Matrix.of fun a b => g a.castSucc.succ b.castSucc.succ

theorem su5Mid_mul {g h : M5c} (hg1 : g 1 0 = 0) (hg2 : g 2 0 = 0) (hg3 : g 3 0 = 0)
    (hh1 : h 4 1 = 0) (hh2 : h 4 2 = 0) (hh3 : h 4 3 = 0) :
    su5Mid (g * h) = su5Mid g * su5Mid h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [su5Mid, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, hg1, hg2, hg3, hh1,
      hh2, hh3]

theorem su5Mid_one : su5Mid 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su5Mid_mul_of_mem {g h : SU f4Frob 5} (hg : g ∈ Subgroup.centralizer {su5T})
    (hh : h ∈ Subgroup.centralizer {su5T}) :
    su5Mid (su5M g * su5M h) = su5Mid (su5M g) * su5Mid (su5M h) := by
  obtain ⟨g1, g2, g3, -, -, -, -, -⟩ := su5_t_shape hg
  obtain ⟨-, -, -, -, h1, h2, h3, -⟩ := su5_t_shape hh
  exact su5Mid_mul g1 g2 g3 h1 h2 h3

@[expose] noncomputable def su5RhoT : Subgroup.centralizer {su5T} →* GL (Fin 3) F4c where
  toFun g := ⟨su5Mid (su5M g), su5Mid (su5M ((g⁻¹ : Subgroup.centralizer {su5T}) :
      SU f4Frob 5)), by
    rw [← su5Mid_mul_of_mem g.2 (g⁻¹).2, ← su5M_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, su5M_one, su5Mid_one], by
    rw [← su5Mid_mul_of_mem (g⁻¹).2 g.2, ← su5M_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, su5M_one, su5Mid_one]⟩
  map_one' := Units.ext (by
    change su5Mid (su5M 1) = 1
    rw [su5M_one, su5Mid_one])
  map_mul' g h := Units.ext (by
    change su5Mid (su5M ((g : SU f4Frob 5) * (h : SU f4Frob 5))) =
      su5Mid (su5M g) * su5Mid (su5M h)
    rw [su5M_mul, su5Mid_mul_of_mem g.2 h.2])

theorem su5_mid_unitary {g : M5c} (hU : conjTr f4Frob g * (antidiag 5 : M5c) * g = antidiag 5)
    (h41 : g 4 1 = 0) (h42 : g 4 2 = 0) (h43 : g 4 3 = 0) :
    conjTr f4Frob (su5Mid g) * (antidiag 3 : Matrix (Fin 3) (Fin 3) F4c) * su5Mid g =
      antidiag 3 := by
  ext a b
  have e := congrFun (congrFun hU a.castSucc.succ) b.castSucc.succ
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_five] at e
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_three]
  simp only [fin5_rev0, fin5_rev1, fin5_rev2, fin5_rev3, fin5_rev4, fin3_rev0, fin3_rev1,
    fin3_rev2] at e ⊢
  fin_cases a <;> fin_cases b <;> simp_all [su5Mid, antidiag]

@[expose] def su5SecT (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c) : M5c :=
  !![d, 0, 0, 0, 0; 0, A 0 0, A 0 1, A 0 2, 0; 0, A 1 0, A 1 1, A 1 2, 0;
    0, A 2 0, A 2 1, A 2 2, 0; 0, 0, 0, 0, d]

theorem su5Mid_su5SecT (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c) : su5Mid (su5SecT d A) = A := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su5SecT_comm (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c) :
    su5SecT d A * su5TM = su5TM * su5SecT d A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su5SecT, su5TM, Matrix.mul_apply, Fin.sum_univ_five]

theorem su5SecT_det (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c) :
    (su5SecT d A).det = d * d * A.det := by
  rw [det_of_corners (m := 3) (su5SecT d A) (fun i => by fin_cases i <;> rfl)
    (fun j => by fin_cases j <;> rfl)]
  have hm : (Matrix.of fun a b : Fin 3 => su5SecT d A a.castSucc.succ b.castSucc.succ) = A :=
    su5Mid_su5SecT d A
  rw [hm]
  rfl

theorem su5SecT_unitary (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c)
    (hA : conjTr f4Frob A * (antidiag 3 : Matrix (Fin 3) (Fin 3) F4c) * A = antidiag 3)
    (hd : f4Frob d * d = 1) :
    conjTr f4Frob (su5SecT d A) * (antidiag 5 : M5c) * su5SecT d A = antidiag 5 := by
  have hA' : ∀ a b : Fin 3, ∑ k, f4Frob (A k a) * A (Fin.rev k) b =
      (antidiag 3 : Matrix (Fin 3) (Fin 3) F4c) a b := fun a b => by
    rw [← conjTr_mul_antidiag_mul_apply, hA]
  have h00 := hA' 0 0
  have h01 := hA' 0 1
  have h02 := hA' 0 2
  have h10 := hA' 1 0
  have h11 := hA' 1 1
  have h12 := hA' 1 2
  have h20 := hA' 2 0
  have h21 := hA' 2 1
  have h22 := hA' 2 2
  clear hA hA'
  simp only [Fin.sum_univ_three, fin3_rev0, fin3_rev1, fin3_rev2] at h00 h01 h02 h10 h11 h12
  simp only [Fin.sum_univ_three, fin3_rev0, fin3_rev1, fin3_rev2] at h20 h21 h22
  ext i j
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_five]
  simp only [fin5_rev0, fin5_rev1, fin5_rev2, fin5_rev3, fin5_rev4]
  fin_cases i <;> fin_cases j <;> simp_all [su5SecT, antidiag, mul_comm]

@[expose] noncomputable def su5SecTElt (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c)
    (hA : conjTr f4Frob A * (antidiag 3 : Matrix (Fin 3) (Fin 3) F4c) * A = antidiag 3)
    (hd : f4Frob d * d = 1) (hdet : d * d * A.det = 1) : Subgroup.centralizer {su5T} :=
  ⟨suMk f4Frob (su5SecT d A) (by rw [su5SecT_det, hdet]) (su5SecT_unitary d A hA hd), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su5SecT_comm d A))⟩

theorem su5RhoT_su5SecTElt (d : F4c) (A : Matrix (Fin 3) (Fin 3) F4c) (hA) (hd) (hdet) :
    ((su5RhoT (su5SecTElt d A hA hd hdet) : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c) =
      A :=
  su5Mid_su5SecT d A

@[expose] noncomputable def su5DetR : su5RhoT.range →* F4cˣ :=
  Matrix.GeneralLinearGroup.det.comp su5RhoT.range.subtype

theorem su5_range_unitary (B : su5RhoT.range) :
    conjTr f4Frob ((B : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c) *
      (antidiag 3 : Matrix (Fin 3) (Fin 3) F4c) * ((B : GL (Fin 3) F4c) : Matrix _ _ F4c) =
        antidiag 3 := by
  obtain ⟨_, g, rfl⟩ := B
  obtain ⟨-, -, -, -, h41, h42, h43, -⟩ := su5_t_shape g.2
  exact su5_mid_unitary (su5M_unitary g) h41 h42 h43

theorem su5_card_ker_detR : Nat.card su5DetR.ker = 216 := by
  rw [← card_SU_f4Frob_three]
  symm
  refine Nat.card_eq_of_bijective (fun A : SU f4Frob 3 =>
    (⟨⟨su5RhoT (su5SecTElt 1 ((A : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c) A.2.2
      (by rw [map_one, one_mul]) (by rw [one_mul, one_mul]; exact A.2.1)), ⟨_, rfl⟩⟩, by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change ((su5RhoT _ : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c).det = 1
      rw [su5RhoT_su5SecTElt]
      exact A.2.1⟩ : su5DetR.ker)) ⟨?_, ?_⟩
  · intro A A' h
    have h' := congrArg (fun x : su5DetR.ker =>
      (((x : su5RhoT.range) : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c)) h
    simp only [su5RhoT_su5SecTElt] at h'
    exact Subtype.ext (Units.ext h')
  · rintro ⟨B, hB⟩
    have hdet : ((B : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c).det = 1 := by
      have := congrArg (fun u : F4cˣ => (u : F4c)) (MonoidHom.mem_ker.1 hB)
      exact this
    refine ⟨⟨(B : GL (Fin 3) F4c), hdet, su5_range_unitary B⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact su5RhoT_su5SecTElt _ _ _ _ _

@[expose] def su5DiagX (x : F4c) : Matrix (Fin 3) (Fin 3) F4c :=
  Matrix.diagonal ![x * x, 1, x * x]

theorem su5DiagX_facts : ∀ x : F4c, x ≠ 0 →
    conjTr f4Frob (su5DiagX x) * (antidiag 3 : Matrix (Fin 3) (Fin 3) F4c) * su5DiagX x =
      antidiag 3 ∧ f4Frob x * x = 1 ∧ x * x * (x * x * 1 * (x * x)) = 1 ∧
        x * x * 1 * (x * x) = x := by
  decide +kernel

theorem det_su5DiagX (x : F4c) : (su5DiagX x).det = x * x * 1 * (x * x) := by
  rw [su5DiagX, Matrix.det_diagonal, Fin.prod_univ_three]
  rfl

theorem su5DetR_surjective : Function.Surjective su5DetR := by
  intro μ
  have hx := (su5DiagX_facts (μ : F4c) μ.ne_zero)
  refine ⟨⟨su5RhoT (su5SecTElt (μ : F4c) (su5DiagX μ) hx.1 hx.2.1
    (by rw [det_su5DiagX]; exact hx.2.2.1)), ⟨_, rfl⟩⟩, ?_⟩
  apply Units.ext
  change ((su5RhoT _ : GL (Fin 3) F4c) : Matrix (Fin 3) (Fin 3) F4c).det = (μ : F4c)
  rw [su5RhoT_su5SecTElt, det_su5DiagX]
  exact hx.2.2.2

theorem su5_card_range_rhoT : Nat.card su5RhoT.range = 648 := by
  rw [card_eq_card_ker_mul_card_range su5DetR, su5_card_ker_detR,
    MonoidHom.range_eq_top.2 su5DetR_surjective, Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_units, CFSG.GH74.Uniqueness.SU.SU5.F4c.card_eq]

@[expose] def su5KT (q : F4c × F4c × F4c × F4c) : M5c :=
  !![1, q.1, q.2.1, q.2.2.1, q.2.2.2; 0, 1, 0, 0, f4Frob q.2.2.1; 0, 0, 1, 0, f4Frob q.2.1;
    0, 0, 0, 1, f4Frob q.1; 0, 0, 0, 0, 1]

@[expose] def su5KTSet : Finset (F4c × F4c × F4c × F4c) :=
  Finset.univ.filter fun q => conjTr f4Frob (su5KT q) * (antidiag 5 : M5c) * su5KT q =
    antidiag 5

theorem card_su5KTSet : su5KTSet.card = 128 := by
  decide +kernel

theorem su5KT_det (q : F4c × F4c × F4c × F4c) : (su5KT q).det = 1 := by
  rw [det_of_corners (m := 3) (su5KT q) (fun i => by fin_cases i <;> rfl)
    (fun j => by fin_cases j <;> rfl)]
  have hm : (Matrix.of fun a b : Fin 3 => su5KT q a.castSucc.succ b.castSucc.succ) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [hm, det_one]
  exact mul_one _

theorem su5KT_comm (q : F4c × F4c × F4c × F4c) : su5KT q * su5TM = su5TM * su5KT q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su5KT, su5TM, Matrix.mul_apply, Fin.sum_univ_five,
    add_comm]

theorem su5Mid_su5KT (q : F4c × F4c × F4c × F4c) : su5Mid (su5KT q) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

@[expose] noncomputable def su5KTElt (q : F4c × F4c × F4c × F4c) (hq : q ∈ su5KTSet) :
    su5RhoT.ker :=
  ⟨⟨suMk f4Frob (su5KT q) (su5KT_det q) (Finset.mem_filter.1 hq).2, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su5KT_comm q))⟩, by
    rw [MonoidHom.mem_ker]
    exact Units.ext (su5Mid_su5KT q)⟩

theorem su5KTElt_injective :
    Function.Injective fun q : su5KTSet => su5KTElt q.1 q.2 := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  have h' := congrArg (fun x : su5RhoT.ker =>
    su5M ((x : Subgroup.centralizer {su5T}) : SU f4Frob 5)) h
  change su5KT q = su5KT q' at h'
  apply Subtype.ext
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨a', b', c', d'⟩ := q'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 0) 2
  have h3 := congrFun (congrFun h' 0) 3
  have h4 := congrFun (congrFun h' 0) 4
  simp only [su5KT] at h1 h2 h3 h4
  simp_all

theorem su5KTElt_surjective :
    Function.Surjective fun q : su5KTSet => su5KTElt q.1 q.2 := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hmid : su5Mid (su5M g) = 1 := by
    have := congrArg (fun x : GL (Fin 3) F4c => (x : Matrix (Fin 3) (Fin 3) F4c))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b11 : su5M g 1 1 = 1 := congrFun (congrFun hmid 0) 0
  have b12 : su5M g 1 2 = 0 := congrFun (congrFun hmid 0) 1
  have b13 : su5M g 1 3 = 0 := congrFun (congrFun hmid 0) 2
  have b21 : su5M g 2 1 = 0 := congrFun (congrFun hmid 1) 0
  have b22 : su5M g 2 2 = 1 := congrFun (congrFun hmid 1) 1
  have b23 : su5M g 2 3 = 0 := congrFun (congrFun hmid 1) 2
  have b31 : su5M g 3 1 = 0 := congrFun (congrFun hmid 2) 0
  have b32 : su5M g 3 2 = 0 := congrFun (congrFun hmid 2) 1
  have b33 : su5M g 3 3 = 1 := congrFun (congrFun hmid 2) 2
  obtain ⟨s10, s20, s30, s40, s41, s42, s43, s44⟩ := su5_t_shape hg
  have hdet := su5M_det g
  rw [det_of_corners (m := 3) (su5M g) (fun i => by fin_cases i <;> assumption)
    (fun j => by fin_cases j <;> assumption)] at hdet
  have hm : (Matrix.of fun a b : Fin 3 => su5M g a.castSucc.succ b.castSucc.succ) = 1 := hmid
  rw [hm, det_one, mul_one] at hdet
  have s00 : su5M g 0 0 = 1 := by
    refine f4c_eq_one_of_mul_self _ ?_
    have h4 : su5M g (Fin.last 4) (Fin.last 4) = su5M g 0 0 := s44
    rw [h4] at hdet
    exact hdet
  have s44' : su5M g 4 4 = 1 := s44.trans s00
  have hU := su5M_unitary g
  have ex : ∀ i : Fin 5, ∑ k, f4Frob (su5M g k i) * su5M g (Fin.rev k) 4 =
      (antidiag 5 : M5c) i 4 := fun i => by
    rw [← conjTr_mul_antidiag_mul_apply, hU]
  have e1 := ex 1
  have e2 := ex 2
  have e3 := ex 3
  simp only [Fin.sum_univ_five, fin5_rev0, fin5_rev1, fin5_rev2, fin5_rev3, fin5_rev4] at e1 e2 e3
  simp [antidiag, b11, b21, b31, s41, b12, b22, b32, s42, b13, b23, b33, s43, s44'] at e1 e2 e3
  have r34 := f4c_eq_of_add_eq_zero _ _ e1
  have r24 := f4c_eq_of_add_eq_zero _ _ e2
  have r14 := f4c_eq_of_add_eq_zero _ _ e3
  have key : su5KT (su5M g 0 1, su5M g 0 2, su5M g 0 3, su5M g 0 4) = su5M g := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su5KT, b11, b12, b13, b21, b22, b23, b31, b32, b33,
      s10, s20, s30, s40, s41, s42, s43, s44', s00, r34, r24, r14]
  have hq : (su5M g 0 1, su5M g 0 2, su5M g 0 3, su5M g 0 4) ∈ su5KTSet := by
    rw [su5KTSet, Finset.mem_filter, key]
    exact ⟨Finset.mem_univ _, su5M_unitary g⟩
  exact ⟨⟨_, hq⟩, Subtype.ext (Subtype.ext (Subtype.ext (Units.ext key)))⟩

theorem su5_card_ker_rhoT : Nat.card su5RhoT.ker = 128 := by
  rw [← card_su5KTSet]
  exact natCard_eq_of_bijective_finset su5KTSet _ ⟨su5KTElt_injective, su5KTElt_surjective⟩

theorem su5_card_centralizer_t : Nat.card (Subgroup.centralizer ({su5T} : Set (SU f4Frob 5))) =
    82944 := by
  rw [card_eq_card_ker_mul_card_range su5RhoT, su5_card_ker_rhoT, su5_card_range_rhoT]

end CFSG.SeitzReduction.F4Pilot
