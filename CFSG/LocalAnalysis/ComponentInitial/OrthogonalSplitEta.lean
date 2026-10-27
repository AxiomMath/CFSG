module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.SpecialLinear SymplecticTorusWeyl

section SL2

variable {k : Type*} [Field k]

@[expose] def sl2InvTElt (g : SpecialLinearGroup (Fin 2) k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) k) 1 1, -(g : Matrix (Fin 2) (Fin 2) k) 1 0;
      -(g : Matrix (Fin 2) (Fin 2) k) 0 1, (g : Matrix (Fin 2) (Fin 2) k) 0 0], by
    have hg := g.2
    rw [det_fin_two] at hg
    rw [det_fin_two_of]
    linear_combination hg⟩

@[expose] def sl2InvT : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k where
  toFun := sl2InvTElt
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sl2InvTElt]
  map_mul' g h := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [sl2InvTElt, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_sl2InvT (g : SpecialLinearGroup (Fin 2) k) :
    ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(g : Matrix (Fin 2) (Fin 2) k) 1 1, -(g : Matrix (Fin 2) (Fin 2) k) 1 0;
        -(g : Matrix (Fin 2) (Fin 2) k) 0 1, (g : Matrix (Fin 2) (Fin 2) k) 0 0] :=
  rfl

theorem coe_sl2InvT_eq (g : SpecialLinearGroup (Fin 2) k) :
    ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ((g⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ := by
  rw [coe_sl2InvT]
  change _ = (adjugate (g : Matrix (Fin 2) (Fin 2) k))ᵀ
  rw [adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sl2InvT_sl2InvT (g : SpecialLinearGroup (Fin 2) k) : sl2InvT (sl2InvT g) = g := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2InvT, coe_sl2InvT]
  fin_cases i <;> fin_cases j <;> simp

theorem sl2InvT_sl2Diag (a : kˣ) : sl2InvT (sl2Diag a) = sl2Diag a⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2InvT]
  fin_cases i <;> fin_cases j <;> simp

@[expose] def sl2SwapElt (g : SpecialLinearGroup (Fin 2) k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) k) 1 1, (g : Matrix (Fin 2) (Fin 2) k) 1 0;
      (g : Matrix (Fin 2) (Fin 2) k) 0 1, (g : Matrix (Fin 2) (Fin 2) k) 0 0], by
    have hg := g.2
    rw [det_fin_two] at hg
    rw [det_fin_two_of]
    linear_combination hg⟩

@[expose] def sl2Swap : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k where
  toFun := sl2SwapElt
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sl2SwapElt]
  map_mul' g h := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [sl2SwapElt, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two, add_comm]

theorem coe_sl2Swap (g : SpecialLinearGroup (Fin 2) k) :
    ((sl2Swap g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(g : Matrix (Fin 2) (Fin 2) k) 1 1, (g : Matrix (Fin 2) (Fin 2) k) 1 0;
        (g : Matrix (Fin 2) (Fin 2) k) 0 1, (g : Matrix (Fin 2) (Fin 2) k) 0 0] :=
  rfl

theorem sl2Swap_sl2Diag (a : kˣ) : sl2Swap (sl2Diag a) = sl2Diag a⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2Swap]
  fin_cases i <;> fin_cases j <;> simp

theorem sl2ConjDiag_sl2Diag (u a : kˣ) : sl2ConjDiag u (sl2Diag a) = sl2Diag a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2ConjDiag]
  fin_cases i <;> fin_cases j <;> simp

theorem neg_one_eq_sl2Diag : (-1 : SpecialLinearGroup (Fin 2) k) = sl2Diag (-1) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [SpecialLinearGroup.coe_neg, coe_sl2Diag]
  fin_cases i <;> fin_cases j <;> simp

end SL2

section PairMat

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R] {a b : ι}

theorem pairMat_upper (hab : a ≠ b) (c : R) :
    pairMat a b !![1, c; 0, 1] = 1 + single a b c := by
  ext x y
  simp only [pairMat, of_apply, Matrix.add_apply, single_apply, one_apply]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hya : y = a <;>
    by_cases hyb : y = b <;> subst_vars <;> simp_all [eq_comm]

theorem pairMat_lower (hab : a ≠ b) (c : R) :
    pairMat a b !![1, 0; c, 1] = 1 + single b a c := by
  ext x y
  simp only [pairMat, of_apply, Matrix.add_apply, single_apply, one_apply]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hya : y = a <;>
    by_cases hyb : y = b <;> subst_vars <;> simp_all [eq_comm]

theorem pairMat_swap_args (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) R) :
    pairMat b a g = pairMat a b !![g 1 1, g 1 0; g 0 1, g 0 0] := by
  ext x y
  refine pairMat_cases (P := fun x y v => pairMat b a g x y = v) hab ?_ ?_ ?_ ?_
    (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_) (fun x y hxa hxb hya hyb => ?_) x y
  · exact (pairMat_apply_pair hab.symm g).2.2.2
  · exact (pairMat_apply_pair hab.symm g).2.2.1
  · exact (pairMat_apply_pair hab.symm g).2.1
  · exact (pairMat_apply_pair hab.symm g).1
  · rcases hx with rfl | rfl
    · exact pairMat_apply_snd_of_ne hab.symm hyb hya g
    · exact pairMat_apply_fst_of_ne hyb hya g
  · rw [pairMat_apply_of_ne hxb hxa]
    rcases hy with rfl | rfl
    · exact one_apply_ne hxa
    · exact one_apply_ne hxb
  · exact pairMat_apply_of_ne hxb hxa g y

end PairMat

section Eta

variable {r : ℕ} {k : Type} [Field k]

@[expose] def coordIdx (a : Fin r ⊕ Fin r) : Fin r := Sum.elim id id a

@[simp] theorem coordIdx_inl (i : Fin r) : coordIdx (Sum.inl i : Fin r ⊕ Fin r) = i := rfl

@[simp] theorem coordIdx_inr (i : Fin r) : coordIdx (Sum.inr i : Fin r ⊕ Fin r) = i := rfl

@[simp] theorem coordIdx_swap (a : Fin r ⊕ Fin r) : coordIdx a.swap = coordIdx a := by
  rcases a with i | i <;> rfl

theorem swap_ne_self (a : Fin r ⊕ Fin r) : a.swap ≠ a := by
  rcases a with i | i <;> simp

variable {a b : Fin r ⊕ Fin r}

theorem ne_of_coordIdx_ne (h : coordIdx a ≠ coordIdx b) : a ≠ b :=
  fun h' => h (by rw [h'])

theorem swap_ne_swap_of_coordIdx_ne (h : coordIdx a ≠ coordIdx b) : a.swap ≠ b.swap :=
  fun h' => h (by rw [← coordIdx_swap a, h', coordIdx_swap])

theorem ne_swap_of_coordIdx_ne (h : coordIdx a ≠ coordIdx b) : a ≠ b.swap :=
  fun h' => h (by rw [h', coordIdx_swap])

theorem disjoint_pair_swap (h : coordIdx a ≠ coordIdx b) :
    Disjoint ({a, b} : Set (Fin r ⊕ Fin r)) {a.swap, b.swap} := by
  rw [Set.disjoint_left]
  rintro x (rfl | rfl) (hx | hx)
  · exact swap_ne_self _ hx.symm
  · exact ne_swap_of_coordIdx_ne h hx
  · exact ne_swap_of_coordIdx_ne (Ne.symm h) hx
  · exact swap_ne_self _ hx.symm

theorem commute_pairMat_swap (h : coordIdx a ≠ coordIdx b) (g g' : Matrix (Fin 2) (Fin 2) k) :
    Commute (pairMat a b g) (pairMat a.swap b.swap g') :=
  (isSupp_pairMat g).commute (isSupp_pairMat g') (disjoint_pair_swap h)

@[expose] def etaMat (a b : Fin r ⊕ Fin r) (g : SpecialLinearGroup (Fin 2) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
  pairMat a b (g : Matrix (Fin 2) (Fin 2) k) *
    pairMat a.swap b.swap ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)

@[expose] noncomputable def etaGL (h : coordIdx a ≠ coordIdx b) :
    SpecialLinearGroup (Fin 2) k →* GL (Fin r ⊕ Fin r) k where
  toFun g := pairGL (ne_of_coordIdx_ne h) g * pairGL (swap_ne_swap_of_coordIdx_ne h) (sl2InvT g)
  map_one' := by simp
  map_mul' g g' := by
    have hc : Commute (pairGL (ne_of_coordIdx_ne h) g')
        (pairGL (swap_ne_swap_of_coordIdx_ne h) (sl2InvT g)) :=
      Units.ext (by
        simpa only [Units.val_mul, coe_pairGL] using (commute_pairMat_swap h _ _).eq)
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (pairGL (ne_of_coordIdx_ne h) g'), hc.eq, mul_assoc]

theorem coe_etaGL (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k) :
    ((etaGL h g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      etaMat a b g :=
  rfl

@[expose] noncomputable def etaLin (h : coordIdx a ≠ coordIdx b) :
    SpecialLinearGroup (Fin 2) k →* ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) :=
  (toLinEquiv (Fin r ⊕ Fin r) k).toMonoidHom.comp (etaGL h)

theorem etaLin_eq (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k) :
    etaLin h g = toLinEquiv (Fin r ⊕ Fin r) k (etaGL h g) :=
  rfl

theorem etaLin_apply (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k)
    (v : Fin r ⊕ Fin r → k) : etaLin h g v = etaMat a b g *ᵥ v :=
  rfl

end Eta

section Mem

variable {r : ℕ} {k : Type} [Field k] {a b : Fin r ⊕ Fin r}

theorem coe_transvection_zero_one (h01 : (0 : Fin 2) ≠ 1) (c : k) :
    ((SpecialLinearGroup.transvection h01 c : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![1, c; 0, 1] := by
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_transvection_one_zero (h10 : (1 : Fin 2) ≠ 0) (c : k) :
    ((SpecialLinearGroup.transvection h10 c : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![1, 0; c, 1] := by
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem etaMat_of_upper (h : coordIdx a ≠ coordIdx b) {g : SpecialLinearGroup (Fin 2) k} {c : k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) = !![1, c; 0, 1]) :
    etaMat a b g = 1 + single a b c + single b.swap a.swap (-c) := by
  have hg' : ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; -c, 1] := by
    rw [coe_sl2InvT, hg]
    simp
  rw [etaMat, hg, hg', pairMat_upper (ne_of_coordIdx_ne h),
    pairMat_lower (swap_ne_swap_of_coordIdx_ne h), Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    single_mul_single_of_ne _ _ _ _ (swap_ne_self b).symm, add_zero]

theorem etaMat_of_lower (h : coordIdx a ≠ coordIdx b) {g : SpecialLinearGroup (Fin 2) k} {c : k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) = !![1, 0; c, 1]) :
    etaMat a b g = 1 + single b a c + single a.swap b.swap (-c) := by
  have hg' : ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, -c; 0, 1] := by
    rw [coe_sl2InvT, hg]
    simp
  rw [etaMat, hg, hg', pairMat_lower (ne_of_coordIdx_ne h),
    pairMat_upper (swap_ne_swap_of_coordIdx_ne h), Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    single_mul_single_of_ne _ _ _ _ (swap_ne_self a).symm, add_zero]

theorem etaLin_of_upper (h : coordIdx a ≠ coordIdx b) {g : SpecialLinearGroup (Fin 2) k} {c : k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) = !![1, c; 0, 1]) :
    etaLin h g = eichler (quadPlus r k) (Pi.single a 1) ((-c) • Pi.single b.swap 1) := by
  have hw : polar (quadPlus r k) (Pi.single a 1) ((-c) • Pi.single b.swap 1) = 0 :=
    polar_single_smul_single (swap_ne_swap_of_coordIdx_ne (Ne.symm h)) _
  refine LinearEquiv.ext fun v => ?_
  rw [etaLin_apply, etaMat_of_upper h hg, eichler_apply (quadPlus_single a) hw]
  funext x
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, polar_smul_right_eq, polar_single, Sum.swap_swap,
    map_smul_eq_sq, quadPlus_single, Function.update_apply, Pi.zero_apply, Pi.single_apply]
  split_ifs <;> ring

theorem etaLin_of_lower (h : coordIdx a ≠ coordIdx b) {g : SpecialLinearGroup (Fin 2) k} {c : k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) = !![1, 0; c, 1]) :
    etaLin h g = eichler (quadPlus r k) (Pi.single b 1) ((-c) • Pi.single a.swap 1) := by
  have hw : polar (quadPlus r k) (Pi.single b 1) ((-c) • Pi.single a.swap 1) = 0 :=
    polar_single_smul_single (swap_ne_swap_of_coordIdx_ne h) _
  refine LinearEquiv.ext fun v => ?_
  rw [etaLin_apply, etaMat_of_lower h hg, eichler_apply (quadPlus_single b) hw]
  funext x
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, polar_smul_right_eq, polar_single, Sum.swap_swap,
    map_smul_eq_sq, quadPlus_single, Function.update_apply, Pi.zero_apply, Pi.single_apply]
  split_ifs <;> ring

theorem etaLin_toSpecialLinearGroup_mem (h : coordIdx a ≠ coordIdx b)
    (t : TransvectionStruct (Fin 2) k) :
    etaLin h t.toSpecialLinearGroup ∈ orthElementaryGroup (quadPlus r k) := by
  obtain ⟨p, q, hpq, c⟩ := t
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · rw [etaLin_of_upper h (coe_transvection_zero_one hpq c)]
    exact eichler_mem_elementaryGroup _ _ _
  · rw [etaLin_of_lower h (coe_transvection_one_zero hpq c)]
    exact eichler_mem_elementaryGroup _ _ _
  · exact absurd rfl hpq

theorem etaLin_mem (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k) :
    etaLin h g ∈ orthElementaryGroup (quadPlus r k) := by
  suffices hle : (etaLin h).range ≤ orthElementaryGroup (quadPlus r k) from hle ⟨g, rfl⟩
  rw [MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact etaLin_toSpecialLinearGroup_mem h t

@[expose] noncomputable def eta (h : coordIdx a ≠ coordIdx b) :
    SpecialLinearGroup (Fin 2) k →* orthElementaryGroup (quadPlus r k) :=
  (etaLin h).codRestrict _ (etaLin_mem h)

theorem coe_eta (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k) :
    ((eta h g : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = etaLin h g :=
  rfl

theorem etaMat_apply_of_mem (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k)
    {x : Fin r ⊕ Fin r} (hx : x = a ∨ x = b) (y : Fin r ⊕ Fin r) :
    etaMat a b g x y = pairMat a b (g : Matrix (Fin 2) (Fin 2) k) x y :=
  (isSupp_pairMat _).mul_apply_of_mem (isSupp_pairMat _) (disjoint_pair_swap h) hx y

theorem etaGL_injective (h : coordIdx a ≠ coordIdx b) :
    Function.Injective (etaGL (k := k) h) := by
  intro g g' hgg'
  have he : ∀ x y, etaMat a b g x y = etaMat a b g' x y := fun x y => by
    rw [← coe_etaGL h, ← coe_etaGL h, hgg']
  obtain ⟨h1, h2, h3, h4⟩ := pairMat_apply_pair (ne_of_coordIdx_ne h)
    (g : Matrix (Fin 2) (Fin 2) k)
  obtain ⟨h1', h2', h3', h4'⟩ := pairMat_apply_pair (ne_of_coordIdx_ne h)
    (g' : Matrix (Fin 2) (Fin 2) k)
  have haa := he a a
  have hab := he a b
  have hba := he b a
  have hbb := he b b
  rw [etaMat_apply_of_mem h _ (Or.inl rfl), etaMat_apply_of_mem h _ (Or.inl rfl)] at haa hab
  rw [etaMat_apply_of_mem h _ (Or.inr rfl), etaMat_apply_of_mem h _ (Or.inr rfl)] at hba hbb
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h1.symm.trans (haa.trans h1')
  · exact h2.symm.trans (hab.trans h2')
  · exact h3.symm.trans (hba.trans h3')
  · exact h4.symm.trans (hbb.trans h4')

theorem eta_injective (h : coordIdx a ≠ coordIdx b) : Function.Injective (eta (k := k) h) :=
  fun _ _ hgg' => etaGL_injective h ((toLinEquiv (Fin r ⊕ Fin r) k).injective
    (congrArg Subtype.val hgg'))

end Mem

section Conj

variable {r : ℕ} {k : Type} [Field k] {a b : Fin r ⊕ Fin r}

theorem signedPerm_mul_etaMat (σ : Equiv.Perm (Fin r ⊕ Fin r)) (ε : Fin r ⊕ Fin r → k)
    (h : coordIdx a ≠ coordIdx b) {a' b' : Fin r ⊕ Fin r} (hσa : σ a = a') (hσb : σ b = b')
    (ha : σ a.swap = a'.swap) (hb : σ b.swap = b'.swap) {g g' : SpecialLinearGroup (Fin 2) k}
    (h00 : ε a * (g : Matrix (Fin 2) (Fin 2) k) 0 0 = (g' : Matrix (Fin 2) (Fin 2) k) 0 0 * ε a)
    (h01 : ε a * (g : Matrix (Fin 2) (Fin 2) k) 0 1 = (g' : Matrix (Fin 2) (Fin 2) k) 0 1 * ε b)
    (h10 : ε b * (g : Matrix (Fin 2) (Fin 2) k) 1 0 = (g' : Matrix (Fin 2) (Fin 2) k) 1 0 * ε a)
    (h11 : ε b * (g : Matrix (Fin 2) (Fin 2) k) 1 1 = (g' : Matrix (Fin 2) (Fin 2) k) 1 1 * ε b)
    (k00 : ε a.swap * (g : Matrix (Fin 2) (Fin 2) k) 1 1 =
      (g' : Matrix (Fin 2) (Fin 2) k) 1 1 * ε a.swap)
    (k01 : ε a.swap * (g : Matrix (Fin 2) (Fin 2) k) 1 0 =
      (g' : Matrix (Fin 2) (Fin 2) k) 1 0 * ε b.swap)
    (k10 : ε b.swap * (g : Matrix (Fin 2) (Fin 2) k) 0 1 =
      (g' : Matrix (Fin 2) (Fin 2) k) 0 1 * ε a.swap)
    (k11 : ε b.swap * (g : Matrix (Fin 2) (Fin 2) k) 0 0 =
      (g' : Matrix (Fin 2) (Fin 2) k) 0 0 * ε b.swap) :
    signedPerm σ ε * etaMat a b g = etaMat a' b' g' * signedPerm σ ε := by
  have hdual := signedPerm_mul_pairMat σ ε (swap_ne_swap_of_coordIdx_ne h)
    (g := ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
    (g' := ((sl2InvT g' : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
    (by simpa [coe_sl2InvT] using k00) (by simpa [coe_sl2InvT] using k01)
    (by simpa [coe_sl2InvT] using k10) (by simpa [coe_sl2InvT] using k11)
  have hmain := signedPerm_mul_pairMat σ ε (ne_of_coordIdx_ne h) h00 h01 h10 h11
  rw [ha, hb] at hdual
  rw [hσa, hσb] at hmain
  rw [etaMat, etaMat, ← mul_assoc, hmain, mul_assoc, hdual, mul_assoc]

theorem torusElt_apply_eq_mulVec (d : Fin r → kˣ) (v : Fin r ⊕ Fin r → k) :
    torusElt r k d v = diagonal (fun c => ((Sum.elim d d⁻¹ c : kˣ) : k)) *ᵥ v := by
  funext c
  rw [mulVec_diagonal, torusElt_apply]

theorem sumElim_swap (d : Fin r → kˣ) (c : Fin r ⊕ Fin r) :
    Sum.elim d d⁻¹ c.swap = (Sum.elim d d⁻¹ c)⁻¹ := by
  rcases c with i | i <;> simp

theorem torusElt_mul_etaLin (h : coordIdx a ≠ coordIdx b) (d : Fin r → kˣ)
    (g : SpecialLinearGroup (Fin 2) k) :
    torusElt r k d * etaLin h g =
      etaLin h (sl2ConjDiag ((Sum.elim d d⁻¹ a)⁻¹ * Sum.elim d d⁻¹ b) g) * torusElt r k d := by
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply, etaLin_apply, torusElt_apply_eq_mulVec, mulVec_mulVec]
  congr 1
  have ha := sumElim_swap d a
  have hb := sumElim_swap d b
  have hA : ((Sum.elim d d⁻¹ a : kˣ) : k) ≠ 0 := Units.ne_zero _
  have hB : ((Sum.elim d d⁻¹ b : kˣ) : k) ≠ 0 := Units.ne_zero _
  rw [← signedPerm_one]
  apply signedPerm_mul_etaMat 1 _ h rfl rfl rfl rfl <;>
    simp only [coe_sl2ConjDiag, ha, hb, Units.val_mul, Units.val_inv_eq_inv_val,
      _root_.mul_inv_rev, inv_inv, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one] <;> field_simp


theorem etaMat_sl2W (h : coordIdx a ≠ coordIdx b) :
    etaMat a b (sl2W : SpecialLinearGroup (Fin 2) k) =
      signedPerm (Equiv.swap a b * Equiv.swap a.swap b.swap) (fun s =>
        (if Equiv.swap a.swap b.swap s = b then (-1 : k) else 1) *
          (if s = b.swap then (-1 : k) else 1)) := by
  have hw : ((sl2InvT sl2W : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, -1; 1, 0] := by
    rw [coe_sl2InvT, coe_sl2W]
    simp
  rw [etaMat, coe_sl2W, hw, pairMat_w (ne_of_coordIdx_ne h),
    pairMat_w (swap_ne_swap_of_coordIdx_ne h), signedPerm_mul_signedPerm]

theorem etaMat_sl2W_mul_inl_inl {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (g : SpecialLinearGroup (Fin 2) k) :
    etaMat (Sum.inl i) (Sum.inl j) sl2W * etaMat (Sum.inl j) (Sum.inl l) g =
      etaMat (Sum.inl i) (Sum.inl l) (sl2ConjDiag (-1) g) *
        etaMat (Sum.inl i) (Sum.inl j) sl2W := by
  rw [etaMat_sl2W (a := Sum.inl i) (b := Sum.inl j) hij]
  refine signedPerm_mul_etaMat _ _ (a := Sum.inl j) (b := Sum.inl l) hjl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ <;>
    simp [coe_sl2ConjDiag, Equiv.swap_apply_of_ne_of_ne, hil.symm, hjl.symm]

theorem etaMat_sl2W_mul_inl_inr {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (g : SpecialLinearGroup (Fin 2) k) :
    etaMat (Sum.inl j) (Sum.inl l) sl2W * etaMat (Sum.inl i) (Sum.inr j) g =
      etaMat (Sum.inl i) (Sum.inr l) g * etaMat (Sum.inl j) (Sum.inl l) sl2W := by
  rw [etaMat_sl2W (a := Sum.inl j) (b := Sum.inl l) hjl]
  refine signedPerm_mul_etaMat _ _ (a := Sum.inl i) (b := Sum.inr j) hij ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ <;>
    simp [Equiv.swap_apply_of_ne_of_ne, hij, hil, hjl]


theorem coordIdx_inl_ne {i j : Fin r} (hij : i ≠ j) :
    coordIdx (Sum.inl i : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inl j) :=
  hij

theorem coordIdx_inl_inr_ne {i j : Fin r} (hij : i ≠ j) :
    coordIdx (Sum.inl i : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inr j) :=
  hij

@[expose] noncomputable def cSwap (j : Fin r) : (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k) :=
  LinearEquiv.funCongrLeft k k (Equiv.swap (Sum.inl j) (Sum.inr j))

theorem cSwap_apply (j : Fin r) (v : Fin r ⊕ Fin r → k) (c : Fin r ⊕ Fin r) :
    cSwap j v c = v (Equiv.swap (Sum.inl j) (Sum.inr j) c) :=
  rfl

theorem cSwap_apply_eq_mulVec (j : Fin r) (v : Fin r ⊕ Fin r → k) :
    cSwap j v = signedPerm (Equiv.swap (Sum.inl j) (Sum.inr j)) (fun _ => (1 : k)) *ᵥ v := by
  funext c
  rw [cSwap_apply, mulVec, dotProduct, Finset.sum_eq_single (Equiv.swap (Sum.inl j) (Sum.inr j) c)]
  · simp [signedPerm_apply]
  · intro d _ hd
    rw [signedPerm_apply, ite_eq_right, zero_mul]
    rintro rfl
    exact hd (Equiv.swap_apply_self _ _ _).symm
  · simp

theorem cSwap_mul_cSwap (j : Fin r) : cSwap (k := k) j * cSwap j = 1 :=
  LinearEquiv.ext fun v => funext fun c => by
    simp [cSwap_apply, Equiv.swap_apply_self]

theorem cSwap_inv (j : Fin r) : (cSwap (k := k) j)⁻¹ = cSwap j :=
  inv_eq_of_mul_eq_one_right (cSwap_mul_cSwap j)

theorem signedPerm_swap_mul_etaMat {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    signedPerm (Equiv.swap (Sum.inl j) (Sum.inr j)) (fun _ => (1 : k)) *
        etaMat (Sum.inl i) (Sum.inl j) g =
      etaMat (Sum.inl i) (Sum.inr j) g *
        signedPerm (Equiv.swap (Sum.inl j) (Sum.inr j)) (fun _ => (1 : k)) := by
  refine signedPerm_mul_etaMat _ _ (a := Sum.inl i) (b := Sum.inl j) hij ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ <;>
    simp [Equiv.swap_apply_of_ne_of_ne, hij]

theorem cSwap_mul_etaLin_mul_cSwap {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    cSwap j * etaLin (coordIdx_inl_ne hij) g * cSwap j =
      etaLin (coordIdx_inl_inr_ne hij) g := by
  have hS : signedPerm (Equiv.swap (Sum.inl j) (Sum.inr j)) (fun _ => (1 : k)) *
      signedPerm (Equiv.swap (Sum.inl j) (Sum.inr j)) (fun _ => (1 : k)) = 1 := by
    rw [signedPerm_mul_signedPerm, Equiv.swap_mul_self, signedPerm_one]
    simp
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply, etaLin_apply, cSwap_apply_eq_mulVec, mulVec_mulVec]
  rw [← Matrix.mul_assoc, signedPerm_swap_mul_etaMat hij, Matrix.mul_assoc, hS, Matrix.mul_one]

theorem etaMat_swap_args (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k) :
    etaMat b a g = etaMat a b (sl2Swap g) := by
  rw [etaMat, etaMat, pairMat_swap_args (ne_of_coordIdx_ne h),
    pairMat_swap_args (swap_ne_swap_of_coordIdx_ne h)]
  congr 2

theorem etaMat_swap_swap (h : coordIdx a ≠ coordIdx b) (g : SpecialLinearGroup (Fin 2) k) :
    etaMat a.swap b.swap g = etaMat a b (sl2InvT g) := by
  rw [etaMat, etaMat, Sum.swap_swap, Sum.swap_swap, sl2InvT_sl2InvT]
  exact (commute_pairMat_swap h _ _).eq.symm

theorem etaMat_sl2Diag (h : coordIdx a ≠ coordIdx b) (u : kˣ) :
    etaMat a b (sl2Diag u) = diagonal fun x =>
      (if x = a then (u : k) else if x = b then ((u⁻¹ : kˣ) : k) else 1) *
        (if x = a.swap then ((u⁻¹ : kˣ) : k) else if x = b.swap then (u : k) else 1) := by
  rw [etaMat, sl2InvT_sl2Diag, coe_sl2Diag, coe_sl2Diag, pairMat_diag (ne_of_coordIdx_ne h),
    pairMat_diag (swap_ne_swap_of_coordIdx_ne h), diagonal_mul_diagonal, inv_inv]

theorem etaLin_inl_inl_sl2Diag {i j : Fin r} (hij : i ≠ j) (u : kˣ) :
    etaLin (coordIdx_inl_ne hij) (sl2Diag u) =
      torusElt r k (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) := by
  refine LinearEquiv.ext fun v => funext fun x => ?_
  rw [etaLin_apply, etaMat_sl2Diag (coordIdx_inl_ne hij), mulVec_diagonal, torusElt_apply]
  congr 1
  rcases x with x | x <;> by_cases hxi : x = i <;> by_cases hxj : x = j <;> subst_vars <;>
    simp_all

theorem etaLin_inl_inr_sl2Diag {i j : Fin r} (hij : i ≠ j) (u : kˣ) :
    etaLin (coordIdx_inl_inr_ne hij) (sl2Diag u) =
      torusElt r k (Pi.mulSingle i u * Pi.mulSingle j u) := by
  refine LinearEquiv.ext fun v => funext fun x => ?_
  rw [etaLin_apply, etaMat_sl2Diag (coordIdx_inl_inr_ne hij), mulVec_diagonal, torusElt_apply]
  congr 1
  rcases x with x | x <;> by_cases hxi : x = i <;> by_cases hxj : x = j <;> subst_vars <;>
    simp_all

end Conj

section Commute

theorem eichler_swap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {u v : V} (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 0) :
    eichler Q u v = eichler Q v (-u) := by
  have hvu : polar Q v (-u) = 0 := by rw [polar_neg_right, polar_comm, huv, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huv, eichler_apply hv hvu, hv, QuadraticMap.map_neg, hu, polar_neg_right]
  module

variable {r : ℕ} {k : Type} [Field k]

theorem eichler_single_mem_rootGroup {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (t : k) :
    eichler (quadPlus r k) (Pi.single c 1) (t • Pi.single d 1) ∈
      rootGroup (quadPlus r k) (Pi.single c 1) :=
  eichler_mem_rootGroup (polar_single_smul_single h t)

theorem eichler_single_mem_rootGroup' {c d : Fin r ⊕ Fin r} (h : d ≠ c.swap) (t : k) :
    eichler (quadPlus r k) (Pi.single c 1) (t • Pi.single d 1) ∈
      rootGroup (quadPlus r k) (Pi.single d 1) := by
  have hc : c ≠ d.swap := fun h' => h (by rw [h', Sum.swap_swap])
  rw [eichler_swap (quadPlus_single c)
    (by rw [map_smul_eq_sq, quadPlus_single, mul_zero]) (polar_single_smul_single h t),
    eichler_smul_left, smul_neg, ← neg_smul]
  exact eichler_single_mem_rootGroup hc _

theorem commute_of_forall_toSpecialLinearGroup {G : Type*} [Group G]
    {α β : SpecialLinearGroup (Fin 2) k →* G}
    (h : ∀ t t' : TransvectionStruct (Fin 2) k,
      Commute (α t.toSpecialLinearGroup) (β t'.toSpecialLinearGroup))
    (g g' : SpecialLinearGroup (Fin 2) k) : Commute (α g) (β g') := by
  have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 2) (K := k)
  have h1 : ∀ g', ∀ t : TransvectionStruct (Fin 2) k,
      Commute (α t.toSpecialLinearGroup) (β g') := by
    intro g' t
    have hle : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) k)) ≤
        (Subgroup.centralizer {α t.toSpecialLinearGroup}).comap β := by
      rw [← htop, Subgroup.closure_le]
      rintro _ ⟨t', rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (h t t').eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g'))).symm
  have hle : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) k)) ≤
      (Subgroup.centralizer {β g'}).comap α := by
    rw [← htop, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (h1 g' t).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))

theorem commute_etaLin_inl_inl_inl_inr {i j : Fin r} (hij : i ≠ j)
    (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (etaLin (coordIdx_inl_ne hij) g) (etaLin (coordIdx_inl_inr_ne hij) g') := by
  refine commute_of_forall_toSpecialLinearGroup (fun t t' => ?_) g g'
  obtain ⟨p, q, hpq, c⟩ := t
  obtain ⟨p', q', hpq', c'⟩ := t'
  rw [TransvectionStruct.toSpecialLinearGroup_mk, TransvectionStruct.toSpecialLinearGroup_mk]
  have hij' : Sum.inl i ≠ (Sum.inl j : Fin r ⊕ Fin r) := fun h => hij (Sum.inl_injective h)
  have hij'' : Sum.inr i ≠ (Sum.inr j : Fin r ⊕ Fin r) := fun h => hij (Sum.inr_injective h)
  fin_cases p <;> fin_cases q <;> fin_cases p' <;> fin_cases q' <;>
    first
    | exact absurd rfl hpq
    | exact absurd rfl hpq'
    | skip
  · rw [etaLin_of_upper _ (coe_transvection_zero_one hpq c),
      etaLin_of_upper _ (coe_transvection_zero_one hpq' c')]
    exact rootGroup_commute (eichler_single_mem_rootGroup (by simp [hij.symm]) _)
      (eichler_single_mem_rootGroup (by simp) _)
  · rw [etaLin_of_upper _ (coe_transvection_zero_one hpq c),
      etaLin_of_lower _ (coe_transvection_one_zero hpq' c')]
    exact rootGroup_commute (eichler_single_mem_rootGroup' (by simp [hij.symm]) _)
      (eichler_single_mem_rootGroup (by simp) _)
  · rw [etaLin_of_lower _ (coe_transvection_one_zero hpq c),
      etaLin_of_upper _ (coe_transvection_zero_one hpq' c')]
    exact rootGroup_commute (eichler_single_mem_rootGroup (by simp [hij]) _)
      (eichler_single_mem_rootGroup' (by simp) _)
  · rw [etaLin_of_lower _ (coe_transvection_one_zero hpq c),
      etaLin_of_lower _ (coe_transvection_one_zero hpq' c')]
    exact rootGroup_commute (eichler_single_mem_rootGroup' (by simp [hij]) _)
      (eichler_single_mem_rootGroup' (by simp) _)

end Commute

section Transfer

variable {r : ℕ} {k : Type} [Field k] {a b : Fin r ⊕ Fin r}

theorem etaLin_mul_etaLin {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : Fin r ⊕ Fin r}
    (h₁ : coordIdx a₁ ≠ coordIdx b₁) (h₂ : coordIdx a₂ ≠ coordIdx b₂)
    (h₃ : coordIdx a₃ ≠ coordIdx b₃) (h₄ : coordIdx a₄ ≠ coordIdx b₄)
    {g₁ g₂ g₃ g₄ : SpecialLinearGroup (Fin 2) k}
    (hm : etaMat a₁ b₁ g₁ * etaMat a₂ b₂ g₂ = etaMat a₃ b₃ g₃ * etaMat a₄ b₄ g₄) :
    etaLin h₁ g₁ * etaLin h₂ g₂ = etaLin h₃ g₃ * etaLin h₄ g₄ := by
  simp only [etaLin_eq, ← map_mul]
  exact congrArg _ (Units.ext hm)

theorem conj_eta_of_torusElt (h : coordIdx a ≠ coordIdx b) {x : orthElementaryGroup (quadPlus r k)}
    {d : Fin r → kˣ} (hx : (x : (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k d) :
    (MulAut.conj x).toMonoidHom.comp (eta h) =
      (eta h).comp (sl2ConjDiag ((Sum.elim d d⁻¹ a)⁻¹ * Sum.elim d d⁻¹ b)) :=
  conj_comp_eq fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, coe_eta, MonoidHom.comp_apply, coe_eta]
    exact torusElt_mul_etaLin h d g)

theorem conj_eta_sl2W_inl_inl {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (MulAut.conj (eta (k := k) (coordIdx_inl_ne hij) sl2W)).toMonoidHom.comp
        (eta (coordIdx_inl_ne hjl)) =
      (eta (coordIdx_inl_ne hil)).comp (sl2ConjDiag (-1)) :=
  conj_comp_eq fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eta, coe_eta, MonoidHom.comp_apply, coe_eta]
    exact etaLin_mul_etaLin _ _ _ _ (etaMat_sl2W_mul_inl_inl hij hjl hil g))

theorem conj_eta_sl2W_inl_inr {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (MulAut.conj (eta (k := k) (coordIdx_inl_ne hjl) sl2W)).toMonoidHom.comp
        (eta (coordIdx_inl_inr_ne hij)) =
      eta (coordIdx_inl_inr_ne hil) :=
  conj_comp_eq fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eta, coe_eta, coe_eta]
    exact etaLin_mul_etaLin _ _ _ _ (etaMat_sl2W_mul_inl_inr hij hjl hil g))

theorem eta_swap_args (h : coordIdx a ≠ coordIdx b) :
    eta (k := k) (Ne.symm h) = (eta h).comp sl2Swap :=
  MonoidHom.ext fun g => Subtype.ext (by
    rw [MonoidHom.comp_apply, coe_eta, coe_eta, etaLin_eq, etaLin_eq]
    exact congrArg _ (Units.ext (etaMat_swap_args h g)))

theorem coordIdx_swap_ne (h : coordIdx a ≠ coordIdx b) : coordIdx a.swap ≠ coordIdx b.swap := by
  rwa [coordIdx_swap, coordIdx_swap]

theorem eta_swap_swap (h : coordIdx a ≠ coordIdx b) :
    eta (k := k) (coordIdx_swap_ne h) = (eta h).comp sl2InvT :=
  MonoidHom.ext fun g => Subtype.ext (by
    rw [MonoidHom.comp_apply, coe_eta, coe_eta, etaLin_eq, etaLin_eq]
    exact congrArg _ (Units.ext (etaMat_swap_swap h g)))

end Transfer

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
