module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValField

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

abbrev M4c : Type := Matrix (Fin 4) (Fin 4) F4c

abbrev su4M (g : SU f4Frob 4) : M4c := ((g : GL (Fin 4) F4c) : M4c)

theorem su4M_mul (g h : SU f4Frob 4) : su4M (g * h) = su4M g * su4M h := rfl

theorem su4M_one : su4M 1 = 1 := rfl

theorem su4M_unitary (g : SU f4Frob 4) :
    conjTr f4Frob (su4M g) * (antidiag 4 : M4c) * su4M g = antidiag 4 :=
  g.2.2

theorem su4M_det (g : SU f4Frob 4) : (su4M g).det = 1 :=
  g.2.1

@[expose] def su4TM : M4c := !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem su4TM_det : su4TM.det = 1 := by
  rw [det_of_corners (m := 2) su4TM (by decide) (by decide)]
  have h : (Matrix.of fun a b : Fin 2 => su4TM a.castSucc.succ b.castSucc.succ) = 1 := by
    decide
  rw [h, det_one]
  decide

@[expose] noncomputable def su4T : SU f4Frob 4 :=
  suMk f4Frob su4TM su4TM_det (by decide)

theorem su4M_su4T : su4M su4T = su4TM := rfl

theorem su4_t_comm {g : SU f4Frob 4} (hg : g ∈ Subgroup.centralizer {su4T}) :
    su4M g * su4TM = su4TM * su4M g := by
  have := congrArg su4M (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rwa [su4M_mul, su4M_mul, su4M_su4T] at this

theorem su4_t_shape {g : SU f4Frob 4} (hg : g ∈ Subgroup.centralizer {su4T}) :
    su4M g 1 0 = 0 ∧ su4M g 2 0 = 0 ∧ su4M g 3 0 = 0 ∧ su4M g 3 1 = 0 ∧ su4M g 3 2 = 0 ∧
      su4M g 3 3 = su4M g 0 0 := by
  have hc := su4_t_comm hg
  have e : ∀ i j, (su4M g * su4TM) i j = (su4TM * su4M g) i j := fun i j => by rw [hc]
  have e13 := e 1 3
  have e23 := e 2 3
  have e33 := e 3 3
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  simp [su4TM, Matrix.mul_apply, Fin.sum_univ_four] at e13 e23 e33 e01 e02 e03
  refine ⟨e13, e23, e33, e01, e02, ?_⟩
  rw [add_comm (su4M g 0 0)] at e03
  exact (add_left_cancel e03).symm

@[expose] def su4Mid (g : M4c) : Matrix (Fin 2) (Fin 2) F4c :=
  Matrix.of fun a b => g a.castSucc.succ b.castSucc.succ

theorem su4Mid_mul {g h : M4c} (hg1 : g 1 0 = 0) (hg2 : g 2 0 = 0) (hh1 : h 3 1 = 0)
    (hh2 : h 3 2 = 0) : su4Mid (g * h) = su4Mid g * su4Mid h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [su4Mid, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, hg1, hg2, hh1, hh2]

theorem su4Mid_one : su4Mid 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su4Mid_mul_of_mem {g h : SU f4Frob 4} (hg : g ∈ Subgroup.centralizer {su4T})
    (hh : h ∈ Subgroup.centralizer {su4T}) :
    su4Mid (su4M g * su4M h) = su4Mid (su4M g) * su4Mid (su4M h) := by
  obtain ⟨g1, g2, -, -, -, -⟩ := su4_t_shape hg
  obtain ⟨-, -, -, h1, h2, -⟩ := su4_t_shape hh
  exact su4Mid_mul g1 g2 h1 h2

@[expose] noncomputable def su4RhoT : Subgroup.centralizer {su4T} →* GL (Fin 2) F4c where
  toFun g := ⟨su4Mid (su4M g), su4Mid (su4M ((g⁻¹ : Subgroup.centralizer {su4T}) :
      SU f4Frob 4)), by
    rw [← su4Mid_mul_of_mem g.2 (g⁻¹).2, ← su4M_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, su4M_one, su4Mid_one], by
    rw [← su4Mid_mul_of_mem (g⁻¹).2 g.2, ← su4M_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, su4M_one, su4Mid_one]⟩
  map_one' := Units.ext (by
    change su4Mid (su4M 1) = 1
    rw [su4M_one, su4Mid_one])
  map_mul' g h := Units.ext (by
    change su4Mid (su4M ((g : SU f4Frob 4) * (h : SU f4Frob 4))) =
      su4Mid (su4M g) * su4Mid (su4M h)
    rw [su4M_mul, su4Mid_mul_of_mem g.2 h.2])

theorem coe_su4RhoT (g : Subgroup.centralizer {su4T}) :
    ((su4RhoT g : GL (Fin 2) F4c) : Matrix (Fin 2) (Fin 2) F4c) = su4Mid (su4M g) := rfl

theorem fin4_rev0 : Fin.rev (0 : Fin 4) = 3 := rfl
theorem fin4_rev1 : Fin.rev (1 : Fin 4) = 2 := rfl
theorem fin4_rev2 : Fin.rev (2 : Fin 4) = 1 := rfl
theorem fin4_rev3 : Fin.rev (3 : Fin 4) = 0 := rfl
theorem fin2_rev0 : Fin.rev (0 : Fin 2) = 1 := rfl
theorem fin2_rev1 : Fin.rev (1 : Fin 2) = 0 := rfl

@[expose] def mk2 (p : F4c × F4c × F4c × F4c) : Matrix (Fin 2) (Fin 2) F4c :=
  !![p.1, p.2.1; p.2.2.1, p.2.2.2]

@[expose] def gu2Set : Finset (F4c × F4c × F4c × F4c) :=
  Finset.univ.filter fun p => conjTr f4Frob (mk2 p) * (antidiag 2 : Matrix (Fin 2) (Fin 2) F4c) *
    mk2 p = antidiag 2

theorem card_gu2Set : gu2Set.card = 18 := by
  decide +kernel

@[expose] def det2 (p : F4c × F4c × F4c × F4c) : F4c := p.1 * p.2.2.2 - p.2.1 * p.2.2.1

@[expose] def su4SecT (p : F4c × F4c × F4c × F4c) : M4c :=
  !![det2 p, 0, 0, 0; 0, p.1, p.2.1, 0; 0, p.2.2.1, p.2.2.2, 0; 0, 0, 0, det2 p]

theorem su4SecT_facts : ∀ p ∈ gu2Set, conjTr f4Frob (su4SecT p) * (antidiag 4 : M4c) *
    su4SecT p = antidiag 4 ∧ det2 p * det2 p * det2 p = 1 := by
  decide +kernel

theorem su4SecT_comm (p : F4c × F4c × F4c × F4c) : su4SecT p * su4TM = su4TM * su4SecT p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su4SecT, su4TM, Matrix.mul_apply, Fin.sum_univ_four]

theorem su4Mid_su4SecT (p : F4c × F4c × F4c × F4c) : su4Mid (su4SecT p) = mk2 p := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su4SecT_det (p : F4c × F4c × F4c × F4c) (h : det2 p * det2 p * det2 p = 1) :
    (su4SecT p).det = 1 := by
  rw [det_of_corners (m := 2) (su4SecT p) (fun i => by fin_cases i <;> rfl)
    (fun j => by fin_cases j <;> rfl)]
  have hm : (Matrix.of fun a b : Fin 2 => su4SecT p a.castSucc.succ b.castSucc.succ) = mk2 p :=
    su4Mid_su4SecT p
  rw [hm, Matrix.det_fin_two]
  exact h

@[expose] noncomputable def su4SecTElt (p : F4c × F4c × F4c × F4c) (hp : p ∈ gu2Set) :
    Subgroup.centralizer {su4T} :=
  ⟨suMk f4Frob (su4SecT p) (su4SecT_det p (su4SecT_facts p hp).2) (su4SecT_facts p hp).1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su4SecT_comm p))⟩

theorem su4_mid_unitary {g : M4c} (hU : conjTr f4Frob g * (antidiag 4 : M4c) * g = antidiag 4)
    (h31 : g 3 1 = 0) (h32 : g 3 2 = 0) :
    conjTr f4Frob (su4Mid g) * (antidiag 2 : Matrix (Fin 2) (Fin 2) F4c) * su4Mid g =
      antidiag 2 := by
  ext a b
  have e := congrFun (congrFun hU a.castSucc.succ) b.castSucc.succ
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_four] at e
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_two]
  simp only [fin4_rev0, fin4_rev1, fin4_rev2, fin4_rev3, fin2_rev0, fin2_rev1] at e ⊢
  fin_cases a <;> fin_cases b <;> simp_all [su4Mid, antidiag]

@[expose] def par2 (A : Matrix (Fin 2) (Fin 2) F4c) : F4c × F4c × F4c × F4c :=
  (A 0 0, A 0 1, A 1 0, A 1 1)

theorem mk2_par2 (A : Matrix (Fin 2) (Fin 2) F4c) : mk2 (par2 A) = A := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su4_card_range_rhoT : Nat.card su4RhoT.range = 18 := by
  rw [← card_gu2Set]
  refine natCard_eq_of_bijective_finset gu2Set
    (fun p => ⟨su4RhoT (su4SecTElt p.1 p.2), ⟨_, rfl⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have h' := congrArg (fun A : su4RhoT.range =>
      ((A : GL (Fin 2) F4c) : Matrix (Fin 2) (Fin 2) F4c)) h
    simp only [coe_su4RhoT] at h'
    change su4Mid (su4SecT p) = su4Mid (su4SecT p') at h'
    rw [su4Mid_su4SecT, su4Mid_su4SecT] at h'
    apply Subtype.ext
    rw [← mk2_par2 (mk2 p), ← mk2_par2 (mk2 p')] at h'
    obtain ⟨a, b, c, d⟩ := p
    obtain ⟨a', b', c', d'⟩ := p'
    have := congrArg par2 h'
    simpa [par2, mk2] using this
  · rintro ⟨A, g, rfl⟩
    have hp : par2 (su4Mid (su4M g)) ∈ gu2Set := by
      rw [gu2Set, Finset.mem_filter, mk2_par2]
      obtain ⟨-, -, -, h31, h32, -⟩ := su4_t_shape g.2
      exact ⟨Finset.mem_univ _, su4_mid_unitary (su4M_unitary g) h31 h32⟩
    refine ⟨⟨_, hp⟩, Subtype.ext (Units.ext ?_)⟩
    change su4Mid (su4SecT _) = su4Mid (su4M g)
    rw [su4Mid_su4SecT, mk2_par2]

@[expose] def su4KT (q : F4c × F4c × F4c × F4c × F4c) : M4c :=
  !![1, q.1, q.2.1, q.2.2.1; 0, 1, 0, q.2.2.2.1; 0, 0, 1, q.2.2.2.2; 0, 0, 0, 1]

@[expose] def su4KTSet : Finset (F4c × F4c × F4c × F4c × F4c) :=
  Finset.univ.filter fun q => conjTr f4Frob (su4KT q) * (antidiag 4 : M4c) * su4KT q =
    antidiag 4

theorem card_su4KTSet : su4KTSet.card = 32 := by
  decide +kernel

theorem su4KT_det (q : F4c × F4c × F4c × F4c × F4c) : (su4KT q).det = 1 := by
  rw [det_of_corners (m := 2) (su4KT q) (fun i => by fin_cases i <;> rfl)
    (fun j => by fin_cases j <;> rfl)]
  have hm : (Matrix.of fun a b : Fin 2 => su4KT q a.castSucc.succ b.castSucc.succ) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [hm, det_one]
  exact mul_one _

theorem su4KT_comm (q : F4c × F4c × F4c × F4c × F4c) : su4KT q * su4TM = su4TM * su4KT q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su4KT, su4TM, Matrix.mul_apply, Fin.sum_univ_four,
    add_comm]

theorem su4Mid_su4KT (q : F4c × F4c × F4c × F4c × F4c) : su4Mid (su4KT q) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

@[expose] noncomputable def su4KTElt (q : F4c × F4c × F4c × F4c × F4c) (hq : q ∈ su4KTSet) :
    su4RhoT.ker :=
  ⟨⟨suMk f4Frob (su4KT q) (su4KT_det q) (Finset.mem_filter.1 hq).2, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su4KT_comm q))⟩, by
    rw [MonoidHom.mem_ker]
    exact Units.ext (su4Mid_su4KT q)⟩

theorem su4KTElt_injective :
    Function.Injective fun q : su4KTSet => su4KTElt q.1 q.2 := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  have h' := congrArg (fun x : su4RhoT.ker =>
    su4M ((x : Subgroup.centralizer {su4T}) : SU f4Frob 4)) h
  change su4KT q = su4KT q' at h'
  apply Subtype.ext
  obtain ⟨a, b, c, d, e⟩ := q
  obtain ⟨a', b', c', d', e'⟩ := q'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 0) 2
  have h3 := congrFun (congrFun h' 0) 3
  have h4 := congrFun (congrFun h' 1) 3
  have h5 := congrFun (congrFun h' 2) 3
  simp only [su4KT] at h1 h2 h3 h4 h5
  simp_all

theorem su4KTElt_surjective :
    Function.Surjective fun q : su4KTSet => su4KTElt q.1 q.2 := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hmid : su4Mid (su4M g) = 1 := by
    have := congrArg (fun x : GL (Fin 2) F4c => (x : Matrix (Fin 2) (Fin 2) F4c))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b11 : su4M g 1 1 = 1 := congrFun (congrFun hmid 0) 0
  have b12 : su4M g 1 2 = 0 := congrFun (congrFun hmid 0) 1
  have b21 : su4M g 2 1 = 0 := congrFun (congrFun hmid 1) 0
  have b22 : su4M g 2 2 = 1 := congrFun (congrFun hmid 1) 1
  obtain ⟨s10, s20, s30, s31, s32, s33⟩ := su4_t_shape hg
  have hdet := su4M_det g
  rw [det_of_corners (m := 2) (su4M g) (fun i => by fin_cases i <;> assumption)
    (fun j => by fin_cases j <;> assumption)] at hdet
  have hm : (Matrix.of fun a b : Fin 2 => su4M g a.castSucc.succ b.castSucc.succ) = 1 := hmid
  rw [hm, det_one, mul_one] at hdet
  have s00 : su4M g 0 0 = 1 := by
    refine f4c_eq_one_of_mul_self _ ?_
    have h3 : su4M g (Fin.last 3) (Fin.last 3) = su4M g 0 0 := s33
    rw [h3] at hdet
    exact hdet
  have key : su4KT (su4M g 0 1, su4M g 0 2, su4M g 0 3, su4M g 1 3, su4M g 2 3) = su4M g := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su4KT, b11, b12, b21, b22, s10, s20, s30, s31, s32,
      s33, s00]
  have hq : (su4M g 0 1, su4M g 0 2, su4M g 0 3, su4M g 1 3, su4M g 2 3) ∈ su4KTSet := by
    rw [su4KTSet, Finset.mem_filter, key]
    exact ⟨Finset.mem_univ _, su4M_unitary g⟩
  exact ⟨⟨_, hq⟩, Subtype.ext (Subtype.ext (Subtype.ext (Units.ext key)))⟩

theorem su4_card_ker_rhoT : Nat.card su4RhoT.ker = 32 := by
  rw [← card_su4KTSet]
  exact natCard_eq_of_bijective_finset su4KTSet _ ⟨su4KTElt_injective, su4KTElt_surjective⟩

theorem su4_card_centralizer_t : Nat.card (Subgroup.centralizer ({su4T} : Set (SU f4Frob 4))) =
    576 := by
  rw [card_eq_card_ker_mul_card_range su4RhoT, su4_card_ker_rhoT, su4_card_range_rhoT]

end CFSG.SeitzReduction.F4Pilot
