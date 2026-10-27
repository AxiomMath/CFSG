module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValSU4T

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

@[expose] def su4UM : M4c := !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem su4UM_det : su4UM.det = 1 := by
  rw [det_of_corners (m := 2) su4UM (by decide) (by decide)]
  have h : (Matrix.of fun a b : Fin 2 => su4UM a.castSucc.succ b.castSucc.succ) = 1 := by
    decide
  rw [h, det_one]
  decide

@[expose] noncomputable def su4U : SU f4Frob 4 :=
  suMk f4Frob su4UM su4UM_det (by decide)

theorem su4M_su4U : su4M su4U = su4UM := rfl

theorem su4_u_comm {g : SU f4Frob 4} (hg : g ∈ Subgroup.centralizer {su4U}) :
    su4M g * su4UM = su4UM * su4M g := by
  have := congrArg su4M (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rwa [su4M_mul, su4M_mul, su4M_su4U] at this

theorem su4_u_shape {g : SU f4Frob 4} (hg : g ∈ Subgroup.centralizer {su4U}) :
    su4M g 2 0 = 0 ∧ su4M g 3 0 = 0 ∧ su4M g 2 1 = 0 ∧ su4M g 3 1 = 0 ∧
      su4M g 2 2 = su4M g 0 0 ∧ su4M g 2 3 = su4M g 0 1 ∧ su4M g 3 2 = su4M g 1 0 ∧
        su4M g 3 3 = su4M g 1 1 := by
  have hc := su4_u_comm hg
  have e : ∀ i j, (su4M g * su4UM) i j = (su4UM * su4M g) i j := fun i j => by rw [hc]
  have e22 := e 2 2
  have e32 := e 3 2
  have e23 := e 2 3
  have e33 := e 3 3
  have e02 := e 0 2
  have e03 := e 0 3
  have e12 := e 1 2
  have e13 := e 1 3
  simp [su4UM, Matrix.mul_apply, Fin.sum_univ_four] at e22 e32 e23 e33 e02 e03 e12 e13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e22
  · linear_combination e32
  · linear_combination e23
  · linear_combination e33
  · linear_combination -e02
  · linear_combination -e03
  · linear_combination -e12
  · linear_combination -e13

@[expose] def su4Blk (g : M4c) : Matrix (Fin 2) (Fin 2) F4c :=
  Matrix.of fun a b => g (Fin.castAdd 2 a) (Fin.castAdd 2 b)

theorem su4Blk_mul (g : M4c) {h : M4c} (h20 : h 2 0 = 0) (h30 : h 3 0 = 0) (h21 : h 2 1 = 0)
    (h31 : h 3 1 = 0) : su4Blk (g * h) = su4Blk g * su4Blk h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [su4Blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h20, h30, h21, h31]

theorem su4Blk_one : su4Blk 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su4Blk_mul_of_mem (g : M4c) {h : SU f4Frob 4} (hh : h ∈ Subgroup.centralizer {su4U}) :
    su4Blk (g * su4M h) = su4Blk g * su4Blk (su4M h) := by
  obtain ⟨h20, h30, h21, h31, -⟩ := su4_u_shape hh
  exact su4Blk_mul g h20 h30 h21 h31

@[expose] noncomputable def su4RhoU : Subgroup.centralizer {su4U} →* GL (Fin 2) F4c where
  toFun g := ⟨su4Blk (su4M g), su4Blk (su4M ((g⁻¹ : Subgroup.centralizer {su4U}) :
      SU f4Frob 4)), by
    rw [← su4Blk_mul_of_mem _ (g⁻¹).2, ← su4M_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, su4M_one, su4Blk_one], by
    rw [← su4Blk_mul_of_mem _ g.2, ← su4M_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, su4M_one, su4Blk_one]⟩
  map_one' := Units.ext (by
    change su4Blk (su4M 1) = 1
    rw [su4M_one, su4Blk_one])
  map_mul' g h := Units.ext (by
    change su4Blk (su4M ((g : SU f4Frob 4) * (h : SU f4Frob 4))) =
      su4Blk (su4M g) * su4Blk (su4M h)
    rw [su4M_mul, su4Blk_mul_of_mem _ h.2])

theorem coe_su4RhoU (g : Subgroup.centralizer {su4U}) :
    ((su4RhoU g : GL (Fin 2) F4c) : Matrix (Fin 2) (Fin 2) F4c) = su4Blk (su4M g) := rfl

@[expose] def su2Set : Finset (F4c × F4c × F4c × F4c) :=
  gu2Set.filter fun p => det2 p = 1

theorem card_su2Set : su2Set.card = 6 := by
  decide +kernel

@[expose] def su4SecU (p : F4c × F4c × F4c × F4c) : M4c :=
  !![p.1, p.2.1, 0, 0; p.2.2.1, p.2.2.2, 0, 0; 0, 0, p.1, p.2.1; 0, 0, p.2.2.1, p.2.2.2]

theorem su4SecU_unitary : ∀ p ∈ su2Set, conjTr f4Frob (su4SecU p) * (antidiag 4 : M4c) *
    su4SecU p = antidiag 4 := by
  decide +kernel

theorem su4SecU_comm (p : F4c × F4c × F4c × F4c) : su4SecU p * su4UM = su4UM * su4SecU p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su4SecU, su4UM, Matrix.mul_apply, Fin.sum_univ_four]

theorem su4Blk_su4SecU (p : F4c × F4c × F4c × F4c) : su4Blk (su4SecU p) = mk2 p := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem su4_det_blockTri (g : M4c) (h20 : g 2 0 = 0) (h30 : g 3 0 = 0) (h21 : g 2 1 = 0)
    (h31 : g 3 1 = 0) :
    g.det = (su4Blk g).det * (Matrix.of fun a b : Fin 2 => g (Fin.natAdd 2 a)
      (Fin.natAdd 2 b)).det := by
  rw [det_of_blockTri (a := 2) (b := 2) g (fun i j => by
    fin_cases i <;> fin_cases j <;> assumption)]
  rfl

theorem su4SecU_det (p : F4c × F4c × F4c × F4c) (h : det2 p = 1) : (su4SecU p).det = 1 := by
  rw [su4_det_blockTri _ rfl rfl rfl rfl, su4Blk_su4SecU]
  have hm : (Matrix.of fun a b : Fin 2 => su4SecU p (Fin.natAdd 2 a) (Fin.natAdd 2 b)) =
      mk2 p := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [hm, Matrix.det_fin_two]
  change det2 p * det2 p = 1
  rw [h, one_mul]

@[expose] noncomputable def su4SecUElt (p : F4c × F4c × F4c × F4c) (hp : p ∈ su2Set) :
    Subgroup.centralizer {su4U} :=
  ⟨suMk f4Frob (su4SecU p) (su4SecU_det p (Finset.mem_filter.1 hp).2) (su4SecU_unitary p hp),
    by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su4SecU_comm p))⟩

theorem su4_blk_unitary {g : M4c} (hU : conjTr f4Frob g * (antidiag 4 : M4c) * g = antidiag 4)
    (h20 : g 2 0 = 0) (h30 : g 3 0 = 0) (h21 : g 2 1 = 0) (h31 : g 3 1 = 0)
    (h22 : g 2 2 = g 0 0) (h23 : g 2 3 = g 0 1) (h32 : g 3 2 = g 1 0) (h33 : g 3 3 = g 1 1) :
    conjTr f4Frob (su4Blk g) * (antidiag 2 : Matrix (Fin 2) (Fin 2) F4c) * su4Blk g =
      antidiag 2 := by
  ext a b
  have e := congrFun (congrFun hU (Fin.castAdd 2 a)) (Fin.natAdd 2 b)
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_four] at e
  rw [conjTr_mul_antidiag_mul_apply, Fin.sum_univ_two]
  simp only [fin4_rev0, fin4_rev1, fin4_rev2, fin4_rev3, fin2_rev0, fin2_rev1] at e ⊢
  fin_cases a <;> fin_cases b <;> simp_all [su4Blk, antidiag]

theorem su4_card_range_rhoU : Nat.card su4RhoU.range = 6 := by
  rw [← card_su2Set]
  refine natCard_eq_of_bijective_finset su2Set
    (fun p => ⟨su4RhoU (su4SecUElt p.1 p.2), ⟨_, rfl⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have h' := congrArg (fun A : su4RhoU.range =>
      ((A : GL (Fin 2) F4c) : Matrix (Fin 2) (Fin 2) F4c)) h
    simp only [coe_su4RhoU] at h'
    change su4Blk (su4SecU p) = su4Blk (su4SecU p') at h'
    rw [su4Blk_su4SecU, su4Blk_su4SecU] at h'
    apply Subtype.ext
    obtain ⟨a, b, c, d⟩ := p
    obtain ⟨a', b', c', d'⟩ := p'
    have := congrArg par2 h'
    simpa [par2, mk2] using this
  · rintro ⟨A, g, rfl⟩
    obtain ⟨h20, h30, h21, h31, h22, h23, h32, h33⟩ := su4_u_shape g.2
    have hp : par2 (su4Blk (su4M g)) ∈ su2Set := by
      rw [su2Set, Finset.mem_filter, gu2Set, Finset.mem_filter, mk2_par2]
      refine ⟨⟨Finset.mem_univ _, su4_blk_unitary (su4M_unitary g) h20 h30 h21 h31 h22 h23 h32
        h33⟩, ?_⟩
      have hdet := su4M_det g
      rw [su4_det_blockTri _ h20 h30 h21 h31] at hdet
      have hm : (Matrix.of fun a b : Fin 2 => su4M g (Fin.natAdd 2 a) (Fin.natAdd 2 b)) =
          su4Blk (su4M g) := by
        ext a b
        fin_cases a <;> fin_cases b
        · exact h22
        · exact h23
        · exact h32
        · exact h33
      rw [hm] at hdet
      have h2 := f4c_eq_one_of_mul_self _ hdet
      rw [Matrix.det_fin_two] at h2
      exact h2
    refine ⟨⟨_, hp⟩, Subtype.ext (Units.ext ?_)⟩
    change su4Blk (su4SecU _) = su4Blk (su4M g)
    rw [su4Blk_su4SecU, mk2_par2]

@[expose] def su4KU (q : F4c × F4c × F4c × F4c) : M4c :=
  !![1, 0, q.1, q.2.1; 0, 1, q.2.2.1, q.2.2.2; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def su4KUSet : Finset (F4c × F4c × F4c × F4c) :=
  Finset.univ.filter fun q => conjTr f4Frob (su4KU q) * (antidiag 4 : M4c) * su4KU q =
    antidiag 4

theorem card_su4KUSet : su4KUSet.card = 16 := by
  decide +kernel

theorem su4KU_det (q : F4c × F4c × F4c × F4c) : (su4KU q).det = 1 := by
  rw [su4_det_blockTri _ rfl rfl rfl rfl]
  have h1 : su4Blk (su4KU q) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  have h2 : (Matrix.of fun a b : Fin 2 => su4KU q (Fin.natAdd 2 a) (Fin.natAdd 2 b)) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [h1, h2, det_one, one_mul]

theorem su4KU_comm (q : F4c × F4c × F4c × F4c) : su4KU q * su4UM = su4UM * su4KU q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su4KU, su4UM, Matrix.mul_apply, Fin.sum_univ_four,
    add_comm]

theorem su4Blk_su4KU (q : F4c × F4c × F4c × F4c) : su4Blk (su4KU q) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

@[expose] noncomputable def su4KUElt (q : F4c × F4c × F4c × F4c) (hq : q ∈ su4KUSet) :
    su4RhoU.ker :=
  ⟨⟨suMk f4Frob (su4KU q) (su4KU_det q) (Finset.mem_filter.1 hq).2, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext (su4KU_comm q))⟩, by
    rw [MonoidHom.mem_ker]
    exact Units.ext (su4Blk_su4KU q)⟩

theorem su4KUElt_injective :
    Function.Injective fun q : su4KUSet => su4KUElt q.1 q.2 := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  have h' := congrArg (fun x : su4RhoU.ker =>
    su4M ((x : Subgroup.centralizer {su4U}) : SU f4Frob 4)) h
  change su4KU q = su4KU q' at h'
  apply Subtype.ext
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨a', b', c', d'⟩ := q'
  have h1 := congrFun (congrFun h' 0) 2
  have h2 := congrFun (congrFun h' 0) 3
  have h3 := congrFun (congrFun h' 1) 2
  have h4 := congrFun (congrFun h' 1) 3
  simp only [su4KU] at h1 h2 h3 h4
  simp_all

theorem su4KUElt_surjective :
    Function.Surjective fun q : su4KUSet => su4KUElt q.1 q.2 := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hblk : su4Blk (su4M g) = 1 := by
    have := congrArg (fun x : GL (Fin 2) F4c => (x : Matrix (Fin 2) (Fin 2) F4c))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b00 : su4M g 0 0 = 1 := congrFun (congrFun hblk 0) 0
  have b01 : su4M g 0 1 = 0 := congrFun (congrFun hblk 0) 1
  have b10 : su4M g 1 0 = 0 := congrFun (congrFun hblk 1) 0
  have b11 : su4M g 1 1 = 1 := congrFun (congrFun hblk 1) 1
  obtain ⟨s20, s30, s21, s31, s22, s23, s32, s33⟩ := su4_u_shape hg
  have key : su4KU (su4M g 0 2, su4M g 0 3, su4M g 1 2, su4M g 1 3) = su4M g := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su4KU, b00, b01, b10, b11, s20, s30, s21, s31, s22,
      s23, s32, s33]
  have hq : (su4M g 0 2, su4M g 0 3, su4M g 1 2, su4M g 1 3) ∈ su4KUSet := by
    rw [su4KUSet, Finset.mem_filter, key]
    exact ⟨Finset.mem_univ _, su4M_unitary g⟩
  exact ⟨⟨_, hq⟩, Subtype.ext (Subtype.ext (Subtype.ext (Units.ext key)))⟩

theorem su4_card_ker_rhoU : Nat.card su4RhoU.ker = 16 := by
  rw [← card_su4KUSet]
  exact natCard_eq_of_bijective_finset su4KUSet _ ⟨su4KUElt_injective, su4KUElt_surjective⟩

theorem su4_card_centralizer_u : Nat.card (Subgroup.centralizer ({su4U} : Set (SU f4Frob 4))) =
    96 := by
  rw [card_eq_card_ker_mul_card_range su4RhoU, su4_card_ker_rhoU, su4_card_range_rhoU]

end CFSG.SeitzReduction.F4Pilot
