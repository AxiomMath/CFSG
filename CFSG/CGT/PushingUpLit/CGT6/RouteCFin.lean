module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCDefs
public import CFSG.CGT.PushingUpLit.CGT6.RouteCData
public import CFSG.CGT.PushingUpLit.CGT6.RouteCRed
public import CFSG.CGT.PushingUpLit.CGT6.RouteCGrp
public import Certificates.Certificate271090
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUpLit.CGT6.RouteC

theorem survivors_eq (n : ℕ) (hn : n = 4 ∨ n = 5 ∨ n = 6) :
    (survivors n).map (fun s => (toMat n n s.1, toMat n n s.2.1, toMat n n s.2.2)) =
      routeCSurvivors n := by
  rcases hn with rfl | rfl | rfl <;> decide

theorem survivors_shape (n : ℕ) (hn : n = 4 ∨ n = 5 ∨ n = 6) :
    ∀ s ∈ survivors n, SurvShape n s := by
  rcases hn with rfl | rfl | rfl <;> decide

section Eval

variable {n : ℕ}

@[expose] def genGL (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    ℕ → Matrix.GeneralLinearGroup (Fin n) (ZMod 2)
  | 0 => y
  | 1 => d
  | 2 => t
  | 3 => y * y
  | _ => d * d

@[expose] def evalGL (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (w : List ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  w.foldl (fun acc l => acc * genGL y d t l) 1

theorem val_genGL (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    ∀ l, ((genGL y d t l : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = genMat (y : Matrix (Fin n) (Fin n) (ZMod 2)) d t l
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => by simp [genGL, genMat]
  | _ + 4 => by simp [genGL, genMat]

theorem val_foldl_genGL (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    ∀ (w : List ℕ) (a : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)),
      ((w.foldl (fun acc l => acc * genGL y d t l) a : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
        w.foldl (fun acc l => acc * genMat (y : Matrix (Fin n) (Fin n) (ZMod 2)) d t l)
          (a : Matrix (Fin n) (Fin n) (ZMod 2))
  | [], _ => rfl
  | l :: w, a => by
    simp only [List.foldl_cons]
    rw [val_foldl_genGL y d t w, Units.val_mul, val_genGL]

theorem val_evalGL (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (w : List ℕ) :
    ((evalGL y d t w : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = evalMat (y : Matrix (Fin n) (Fin n) (ZMod 2)) d t w := by
  unfold evalGL evalMat
  rw [val_foldl_genGL]
  simp

theorem genGL_mem (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (l : ℕ) :
    genGL y d t l ∈ routeCGroup y d t := by
  have hy : y ∈ routeCGroup y d t := Subgroup.subset_closure (by simp)
  have hd : d ∈ routeCGroup y d t := Subgroup.subset_closure (by simp)
  have ht : t ∈ routeCGroup y d t := Subgroup.subset_closure (by simp)
  unfold genGL
  split
  · exact hy
  · exact hd
  · exact ht
  · exact Subgroup.mul_mem _ hy hy
  · exact Subgroup.mul_mem _ hd hd

theorem foldl_genGL_mem (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    ∀ (w : List ℕ) (a : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)), a ∈ routeCGroup y d t →
      w.foldl (fun acc l => acc * genGL y d t l) a ∈ routeCGroup y d t
  | [], _, ha => ha
  | l :: w, _, ha => foldl_genGL_mem y d t w _ (Subgroup.mul_mem _ ha (genGL_mem y d t l))

theorem evalGL_mem (y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (w : List ℕ) :
    evalGL y d t w ∈ routeCGroup y d t :=
  foldl_genGL_mem y d t w 1 (Subgroup.one_mem _)

end Eval

section Main

variable {n : ℕ}

structure MatFacts (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop where
  y3 : y * y * y = 1
  d3 : d * d * d = 1
  t2 : t * t = 1
  ty : t * y = y * t
  rky : Module.finrank (ZMod 2) ↥(imSub y) = 2
  rkd : Module.finrank (ZMod 2) ↥(imSub d) = 2
  comm : imSub y ⊔ imSub d ⊔ imSub t = ⊤
  t1 : t ≠ 1

theorem matFacts_of_hyp {y d t : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)}
    (hyp : RouteCHyp y d t) :
    MatFacts (y : Matrix (Fin n) (Fin n) (ZMod 2)) d t where
  y3 := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) hyp.y3
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [← pow_three']
    exact h
  d3 := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) hyp.d3
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [← pow_three']
    exact h
  t2 := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) hyp.t2
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [← pow_two]
    exact h
  ty := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) hyp.ty
    simpa only [Units.val_mul] using h
  rky := hyp.rk_y
  rkd := hyp.rk_d
  comm := hyp.comm
  t1 := fun h => hyp.t1 (Units.ext h)

theorem conj_val_eq {g X : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)}
    {S : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : (g : Matrix (Fin n) (Fin n) (ZMod 2)) * (X : Matrix (Fin n) (Fin n) (ZMod 2)) =
      S * (g : Matrix (Fin n) (Fin n) (ZMod 2))) :
    ((g * X * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = S := by
  rw [Units.val_mul, Units.val_mul, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem finC_aux (hn : n = 4 ∨ n = 5 ∨ n = 6) (wit : List ℕ)
    (hcheck : check (survivors n) n wit = true) : FinC n (routeCSurvivors n) := by
  have hn4 : 4 ≤ n := by omega
  have hn6 : n ≤ 6 := by omega
  intro y d t hyp
  have hF := matFacts_of_hyp hyp
  obtain ⟨E, φ, ψ, hφ, hψ, R, hkOk⟩ := chart_exists _ _ _ hF.y3 hF.d3 hF.t2 hF.ty hF.rky hF.rkd
    hF.comm
  obtain ⟨Kb, hKb, hK⟩ := exists_Kb E R.surj hn4 hn6
  have hmem := mem_members hKb (R.condT_true hK hkOk hF.t1) hφ (R.condY_true hK) hψ
    (R.condD_true hK)
  obtain ⟨w, -, hw⟩ := check_spec hcheck _ hmem
  have htG : t ∈ routeCGroup y d t := Subgroup.subset_closure (by simp)
  rcases R.member_cases hK (survivors_shape n hn) hw with hB | hC | hS
  ·
    exfalso
    obtain ⟨m, g, W, hWy, hWd, hWt, hkW, hkW', v, hv⟩ := hB
    have hkval : ((evalGL y d t g ^ m : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = evalMat (y : Matrix (Fin n) (Fin n) (ZMod 2)) d t g ^ m
        := by
      rw [Units.val_pow_eq_pow_val, val_evalGL]
    have hk1 : evalGL y d t g ^ m ≠ 1 := fun h => hv (by
      have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
        (z : Matrix (Fin n) (Fin n) (ZMod 2))) h
      simp only [hkval, Units.val_one] at this
      rw [this, Matrix.one_mulVec])
    exact pCore_ne_bot_of_kernel y d t hyp.y3 hyp.d3 hyp.t2 W hWy hWd hWt (evalGL y d t g ^ m)
      (Subgroup.pow_mem _ (evalGL_mem y d t g) m) hk1 (by rw [hkval]; exact hkW)
      (by rw [hkval]; exact hkW') hyp.o2
  ·
    exfalso
    obtain ⟨a, m, cw, hct, hcci, hm, hx, hxm⟩ := hC
    have hcU := val_evalGL y d t cw
    have hciU := val_evalGL y d t (invW cw)
    have hcc : evalGL y d t cw * evalGL y d t (invW cw) = 1 :=
      Units.ext (by rw [Units.val_mul, hcU, hciU, hcci]; rfl)
    have hciinv : evalGL y d t (invW cw) = (evalGL y d t cw)⁻¹ :=
      (inv_eq_of_mul_eq_one_right hcc).symm
    have hct' : t * evalGL y d t cw = evalGL y d t cw * t :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, hcU]; exact hct)
    have hinvval : (((evalGL y d t cw)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
        evalMat (y : Matrix (Fin n) (Fin n) (ZMod 2)) d t (invW cw) := by
      rw [← hciinv, hciU]
    refine not_subnormal_of_word y d t (evalGL y d t cw) hyp.y3 hyp.ty htG
      (evalGL_mem y d t cw) hct' a m hm ?_ ?_ (hyp.cent t htG hyp.t1 hyp.t2 hyp.ty)
    · intro h
      apply hx
      have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
        (z : Matrix (Fin n) (Fin n) (ZMod 2))) h
      simpa [Units.val_pow_eq_pow_val, Units.val_mul, hcU, hinvval] using this
    · apply Units.ext
      simpa [Units.val_pow_eq_pow_val, Units.val_mul, hcU, hinvval] using hxm
  ·
    obtain ⟨s, hs, gM, hunit, hgy, hgd, hgt⟩ := hS
    obtain ⟨gU, rfl⟩ := hunit
    refine ⟨gU, ?_⟩
    have hsmem : (toMat n n s.1, toMat n n s.2.1, toMat n n s.2.2) ∈ routeCSurvivors n := by
      rw [← survivors_eq n hn]
      exact List.mem_map_of_mem hs
    rw [conj_val_eq hgy, conj_val_eq hgd, conj_val_eq hgt]
    exact hsmem

theorem finC (n : ℕ) (hn2 : 2 ≤ n) (hn6 : n ≤ 6) :
    FinC n (routeCSurvivors n) := by
  have hchk := Certificates.certificate271090
  unfold routeCCheck at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨h4, h5⟩, h6⟩ := hchk
  by_cases hsmall : n ≤ 3
  · intro y d t hyp
    exfalso
    have hF := matFacts_of_hyp hyp
    have h4le := four_le_n _ _ hF.y3 hF.rky hF.t2 hF.ty hF.t1
    omega
  · have hn : n = 4 ∨ n = 5 ∨ n = 6 := by omega
    rcases hn with rfl | rfl | rfl
    · exact finC_aux (Or.inl rfl) wit4 h4
    · exact finC_aux (Or.inr (Or.inl rfl)) wit5 h5
    · exact finC_aux (Or.inr (Or.inr rfl)) wit6 h6

end Main

end CFSG.CGT.PushingUpLit.CGT6
