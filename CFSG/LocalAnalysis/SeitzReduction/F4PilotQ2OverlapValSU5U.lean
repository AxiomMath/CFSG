module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValSU5T
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValSU4T

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

@[expose] def su5UM : M5c :=
  !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem su5UM_det : su5UM.det = 1 := by
  rw [det_of_corners (m := 3) su5UM (by decide) (by decide)]
  have h : (Matrix.of fun a b : Fin 3 => su5UM a.castSucc.succ b.castSucc.succ) = 1 := by
    decide
  rw [h, det_one]
  decide

@[expose] noncomputable def su5U : SU f4Frob 5 :=
  suMk f4Frob su5UM su5UM_det (by decide)

theorem su5M_su5U : su5M su5U = su5UM := rfl

theorem su5_u_comm {g : SU f4Frob 5} (hg : g ∈ Subgroup.centralizer {su5U}) :
    su5M g * su5UM = su5UM * su5M g := by
  have := congrArg su5M (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rwa [su5M_mul, su5M_mul, su5M_su5U] at this

theorem su5_u_shape {g : SU f4Frob 5} (hg : g ∈ Subgroup.centralizer {su5U}) :
    su5M g 2 0 = 0 ∧ su5M g 3 0 = 0 ∧ su5M g 4 0 = 0 ∧ su5M g 2 1 = 0 ∧ su5M g 3 1 = 0 ∧
      su5M g 4 1 = 0 ∧ su5M g 3 2 = 0 ∧ su5M g 4 2 = 0 ∧ su5M g 3 3 = su5M g 0 0 ∧
        su5M g 3 4 = su5M g 0 1 ∧ su5M g 4 3 = su5M g 1 0 ∧ su5M g 4 4 = su5M g 1 1 := by
  have hc := su5_u_comm hg
  have e : ∀ i j, (su5M g * su5UM) i j = (su5UM * su5M g) i j := fun i j => by rw [hc]
  have e23 := e 2 3
  have e33 := e 3 3
  have e43 := e 4 3
  have e24 := e 2 4
  have e34 := e 3 4
  have e44 := e 4 4
  have e02 := e 0 2
  have e12 := e 1 2
  have e03 := e 0 3
  have e04 := e 0 4
  have e13 := e 1 3
  have e14 := e 1 4
  simp [su5UM, Matrix.mul_apply, Fin.sum_univ_five] at e23 e33 e43 e24 e34 e44 e02 e12
  simp [su5UM, Matrix.mul_apply, Fin.sum_univ_five] at e03 e04 e13 e14
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e23
  · linear_combination e33
  · linear_combination e43
  · linear_combination e24
  · linear_combination e34
  · linear_combination e44
  · linear_combination e02
  · linear_combination e12
  · linear_combination -e03
  · linear_combination -e04
  · linear_combination -e13
  · linear_combination -e14

@[expose] def su5Blk (g : M5c) : Matrix (Fin 2) (Fin 2) F4c :=
  Matrix.of fun a b => g (Fin.castAdd 3 a) (Fin.castAdd 3 b)

theorem su5Blk_mul (g : M5c) {h : M5c} (h20 : h 2 0 = 0) (h30 : h 3 0 = 0) (h40 : h 4 0 = 0)
    (h21 : h 2 1 = 0) (h31 : h 3 1 = 0) (h41 : h 4 1 = 0) :
    su5Blk (g * h) = su5Blk g * su5Blk h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [su5Blk, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two, h20, h30, h40, h21,
      h31, h41]

theorem su5Blk_one : su5Blk 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su5Blk_mul_of_mem (g : M5c) {h : SU f4Frob 5} (hh : h ∈ Subgroup.centralizer {su5U}) :
    su5Blk (g * su5M h) = su5Blk g * su5Blk (su5M h) := by
  obtain ⟨h20, h30, h40, h21, h31, h41, -⟩ := su5_u_shape hh
  exact su5Blk_mul g h20 h30 h40 h21 h31 h41

@[expose] noncomputable def su5RhoU : Subgroup.centralizer {su5U} →* GL (Fin 2) F4c where
  toFun g := ⟨su5Blk (su5M g), su5Blk (su5M ((g⁻¹ : Subgroup.centralizer {su5U}) :
      SU f4Frob 5)), by
    rw [← su5Blk_mul_of_mem _ (g⁻¹).2, ← su5M_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, su5M_one, su5Blk_one], by
    rw [← su5Blk_mul_of_mem _ g.2, ← su5M_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, su5M_one, su5Blk_one]⟩
  map_one' := Units.ext (by
    change su5Blk (su5M 1) = 1
    rw [su5M_one, su5Blk_one])
  map_mul' g h := Units.ext (by
    change su5Blk (su5M ((g : SU f4Frob 5) * (h : SU f4Frob 5))) =
      su5Blk (su5M g) * su5Blk (su5M h)
    rw [su5M_mul, su5Blk_mul_of_mem _ h.2])

theorem coe_su5RhoU (g : Subgroup.centralizer {su5U}) :
    ((su5RhoU g : GL (Fin 2) F4c) : Matrix (Fin 2) (Fin 2) F4c) = su5Blk (su5M g) := rfl

theorem su5_det_blockTri (g : M5c) (h20 : g 2 0 = 0) (h30 : g 3 0 = 0) (h40 : g 4 0 = 0)
    (h21 : g 2 1 = 0) (h31 : g 3 1 = 0) (h41 : g 4 1 = 0) (h32 : g 3 2 = 0) (h42 : g 4 2 = 0) :
    g.det = (su5Blk g).det * (g 2 2 * (Matrix.of fun a b : Fin 2 =>
      g (Fin.natAdd 3 a) (Fin.natAdd 3 b)).det) := by
  rw [det_of_blockTri (a := 2) (b := 3) g (fun i j => by
    fin_cases i <;> fin_cases j <;> assumption)]
  congr 1
  rw [det_of_blockTri (a := 1) (b := 2) _ (fun i j => by
    fin_cases i <;> fin_cases j <;> assumption), Matrix.det_unique]
  rfl

@[expose] def su5SecU (p : F4c × F4c × F4c × F4c) : M5c :=
  !![p.1, p.2.1, 0, 0, 0; p.2.2.1, p.2.2.2, 0, 0, 0; 0, 0, det2 p, 0, 0;
    0, 0, 0, p.1, p.2.1; 0, 0, 0, p.2.2.1, p.2.2.2]

theorem su5SecU_facts : ∀ p ∈ gu2Set, conjTr f4Frob (su5SecU p) * (antidiag 5 : M5c) *
    su5SecU p = antidiag 5 ∧ det2 p * (det2 p * det2 p) = 1 := by
  decide +kernel

theorem su5SecU_comm (p : F4c × F4c × F4c × F4c) : su5SecU p * su5UM = su5UM * su5SecU p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su5SecU, su5UM, Matrix.mul_apply, Fin.sum_univ_five]

theorem su5Blk_su5SecU (p : F4c × F4c × F4c × F4c) : su5Blk (su5SecU p) = mk2 p := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su5SecU_det (p : F4c × F4c × F4c × F4c) (h : det2 p * (det2 p * det2 p) = 1) :
    (su5SecU p).det = 1 := by
  rw [su5_det_blockTri _ rfl rfl rfl rfl rfl rfl rfl rfl, su5Blk_su5SecU]
  have hm : (Matrix.of fun a b : Fin 2 => su5SecU p (Fin.natAdd 3 a) (Fin.natAdd 3 b)) =
      mk2 p := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [hm, Matrix.det_fin_two]
  exact h

@[expose] noncomputable def su5SecUElt (p : F4c × F4c × F4c × F4c) (hp : p ∈ gu2Set) :
    Subgroup.centralizer {su5U} :=
  ⟨suMk f4Frob (su5SecU p) (su5SecU_det p (su5SecU_facts p hp).2) (su5SecU_facts p hp).1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su5SecU_comm p))⟩

theorem su5_blk_unitary {g : M5c} (hU : conjTr f4Frob g * (antidiag 5 : M5c) * g = antidiag 5)
    (h20 : g 2 0 = 0) (h30 : g 3 0 = 0) (h40 : g 4 0 = 0) (h21 : g 2 1 = 0) (h31 : g 3 1 = 0)
    (h41 : g 4 1 = 0) (h33 : g 3 3 = g 0 0) (h34 : g 3 4 = g 0 1) (h43 : g 4 3 = g 1 0)
    (h44 : g 4 4 = g 1 1) :
    conjTr f4Frob (su5Blk g) * (antidiag 2 : Matrix (Fin 2) (Fin 2) F4c) * su5Blk g =
      antidiag 2 := by
  ext a b
  have e := congrFun (congrFun hU (Fin.castAdd 3 a)) (Fin.natAdd 3 b)
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_five] at e
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_two]
  simp only [fin5_rev0, fin5_rev1, fin5_rev2, fin5_rev3, fin5_rev4, fin2_rev0, fin2_rev1] at e ⊢
  fin_cases a <;> fin_cases b <;> simp_all [su5Blk, antidiag]

theorem su5_card_range_rhoU : Nat.card su5RhoU.range = 18 := by
  rw [← card_gu2Set]
  refine natCard_eq_of_bijective_finset gu2Set
    (fun p => ⟨su5RhoU (su5SecUElt p.1 p.2), ⟨_, rfl⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have h' := congrArg (fun A : su5RhoU.range =>
      ((A : GL (Fin 2) F4c) : Matrix (Fin 2) (Fin 2) F4c)) h
    simp only [coe_su5RhoU] at h'
    change su5Blk (su5SecU p) = su5Blk (su5SecU p') at h'
    rw [su5Blk_su5SecU, su5Blk_su5SecU] at h'
    apply Subtype.ext
    obtain ⟨a, b, c, d⟩ := p
    obtain ⟨a', b', c', d'⟩ := p'
    have := congrArg par2 h'
    simpa [par2, mk2] using this
  · rintro ⟨A, g, rfl⟩
    obtain ⟨h20, h30, h40, h21, h31, h41, -, -, h33, h34, h43, h44⟩ := su5_u_shape g.2
    have hp : par2 (su5Blk (su5M g)) ∈ gu2Set := by
      rw [gu2Set, Finset.mem_filter, mk2_par2]
      exact ⟨Finset.mem_univ _, su5_blk_unitary (su5M_unitary g) h20 h30 h40 h21 h31 h41 h33
        h34 h43 h44⟩
    refine ⟨⟨_, hp⟩, Subtype.ext (Units.ext ?_)⟩
    change su5Blk (su5SecU _) = su5Blk (su5M g)
    rw [su5Blk_su5SecU, mk2_par2]

@[expose] def su5KU (q : F4c × F4c × F4c × F4c × F4c) : M5c :=
  !![1, 0, q.1, q.2.2.1, q.2.2.2.1;
    0, 1, q.2.1, q.2.2.2.2, f4Frob q.2.2.1 + f4Frob (f4Frob q.2.1) * f4Frob q.1;
    0, 0, 1, f4Frob q.2.1, f4Frob q.1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def su5KUSet : Finset (F4c × F4c × F4c × F4c × F4c) :=
  Finset.univ.filter fun q => conjTr f4Frob (su5KU q) * (antidiag 5 : M5c) * su5KU q =
    antidiag 5

theorem card_su5KUSet : su5KUSet.card = 256 := by
  decide +kernel

theorem su5KU_det (q : F4c × F4c × F4c × F4c × F4c) : (su5KU q).det = 1 := by
  rw [su5_det_blockTri _ rfl rfl rfl rfl rfl rfl rfl rfl]
  have h1 : su5Blk (su5KU q) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  have h2 : (Matrix.of fun a b : Fin 2 => su5KU q (Fin.natAdd 3 a) (Fin.natAdd 3 b)) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [h1, h2, det_one, one_mul]
  exact one_mul _

theorem su5KU_comm (q : F4c × F4c × F4c × F4c × F4c) : su5KU q * su5UM = su5UM * su5KU q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su5KU, su5UM, Matrix.mul_apply, Fin.sum_univ_five,
    add_comm]

theorem su5Blk_su5KU (q : F4c × F4c × F4c × F4c × F4c) : su5Blk (su5KU q) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

@[expose] noncomputable def su5KUElt (q : F4c × F4c × F4c × F4c × F4c) (hq : q ∈ su5KUSet) :
    su5RhoU.ker :=
  ⟨⟨suMk f4Frob (su5KU q) (su5KU_det q) (Finset.mem_filter.1 hq).2, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su5KU_comm q))⟩, by
    rw [MonoidHom.mem_ker]
    exact Units.ext (su5Blk_su5KU q)⟩

theorem su5KUElt_injective :
    Function.Injective fun q : su5KUSet => su5KUElt q.1 q.2 := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  have h' := congrArg (fun x : su5RhoU.ker =>
    su5M ((x : Subgroup.centralizer {su5U}) : SU f4Frob 5)) h
  change su5KU q = su5KU q' at h'
  apply Subtype.ext
  obtain ⟨a, b, c, d, e⟩ := q
  obtain ⟨a', b', c', d', e'⟩ := q'
  have h1 := congrFun (congrFun h' 0) 2
  have h2 := congrFun (congrFun h' 1) 2
  have h3 := congrFun (congrFun h' 0) 3
  have h4 := congrFun (congrFun h' 0) 4
  have h5 := congrFun (congrFun h' 1) 3
  simp only [su5KU] at h1 h2 h3 h4 h5
  simp_all

theorem su5KUElt_surjective :
    Function.Surjective fun q : su5KUSet => su5KUElt q.1 q.2 := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hblk : su5Blk (su5M g) = 1 := by
    have := congrArg (fun x : GL (Fin 2) F4c => (x : Matrix (Fin 2) (Fin 2) F4c))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b00 : su5M g 0 0 = 1 := congrFun (congrFun hblk 0) 0
  have b01 : su5M g 0 1 = 0 := congrFun (congrFun hblk 0) 1
  have b10 : su5M g 1 0 = 0 := congrFun (congrFun hblk 1) 0
  have b11 : su5M g 1 1 = 1 := congrFun (congrFun hblk 1) 1
  obtain ⟨s20, s30, s40, s21, s31, s41, s32, s42, s33, s34, s43, s44⟩ := su5_u_shape hg
  have hdet := su5M_det g
  rw [su5_det_blockTri _ s20 s30 s40 s21 s31 s41 s32 s42, hblk, det_one, one_mul] at hdet
  have hm : (Matrix.of fun a b : Fin 2 => su5M g (Fin.natAdd 3 a) (Fin.natAdd 3 b)) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b
    · exact s33.trans b00
    · exact s34.trans b01
    · exact s43.trans b10
    · exact s44.trans b11
  rw [hm, det_one, mul_one] at hdet
  have s33' : su5M g 3 3 = 1 := s33.trans b00
  have s34' : su5M g 3 4 = 0 := s34.trans b01
  have s43' : su5M g 4 3 = 0 := s43.trans b10
  have s44' : su5M g 4 4 = 1 := s44.trans b11
  have hU := su5M_unitary g
  have ex : ∀ i j : Fin 5, ∑ k, f4Frob (su5M g k i) * su5M g (Fin.rev k) j =
      (antidiag 5 : M5c) i j := fun i j => by
    rw [← conjTr_mul_antidiag_mul_apply, hU]
  have e23 := ex 2 3
  have e24 := ex 2 4
  have e34 := ex 3 4
  simp only [Fin.sum_univ_five, fin5_rev0, fin5_rev1, fin5_rev2, fin5_rev3, fin5_rev4] at e23 e24
  simp only [Fin.sum_univ_five, fin5_rev0, fin5_rev1, fin5_rev2, fin5_rev3, fin5_rev4] at e34
  simp [antidiag, s32, s42, s33', s34', s43', s44', hdet] at e23 e24
  simp [antidiag, s33', s34', s43', s44'] at e34
  have r23 := f4c_eq_of_add_eq_zero _ _ e23
  have r24 := f4c_eq_of_add_eq_zero _ _ e24
  have r14 := f4c_eq_of_add_eq_zero _ _ e34
  have key : su5KU (su5M g 0 2, su5M g 1 2, su5M g 0 3, su5M g 0 4, su5M g 1 3) = su5M g := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su5KU, b00, b01, b10, b11, s20, s30, s40, s21, s31,
      s41, s32, s42, s33', s34', s43', s44', hdet, r23, r24, r14]
  have hq : (su5M g 0 2, su5M g 1 2, su5M g 0 3, su5M g 0 4, su5M g 1 3) ∈ su5KUSet := by
    rw [su5KUSet, Finset.mem_filter, key]
    exact ⟨Finset.mem_univ _, su5M_unitary g⟩
  exact ⟨⟨_, hq⟩, Subtype.ext (Subtype.ext (Subtype.ext (Units.ext key)))⟩

theorem su5_card_ker_rhoU : Nat.card su5RhoU.ker = 256 := by
  rw [← card_su5KUSet]
  exact natCard_eq_of_bijective_finset su5KUSet _ ⟨su5KUElt_injective, su5KUElt_surjective⟩

theorem su5_card_centralizer_u : Nat.card (Subgroup.centralizer ({su5U} : Set (SU f4Frob 5))) =
    4608 := by
  rw [card_eq_card_ker_mul_card_range su5RhoU, su5_card_ker_rhoU, su5_card_range_rhoU]

end CFSG.SeitzReduction.F4Pilot
