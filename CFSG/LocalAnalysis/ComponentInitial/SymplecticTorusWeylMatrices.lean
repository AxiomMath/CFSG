module

public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear

section PairMat

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R] {a b : ι}

@[expose] def pairMat (a b : ι) (g : Matrix (Fin 2) (Fin 2) R) : Matrix ι ι R :=
  Matrix.of fun x y =>
    if x = a then (if y = a then g 0 0 else if y = b then g 0 1 else 0)
    else if x = b then (if y = a then g 1 0 else if y = b then g 1 1 else 0)
    else (1 : Matrix ι ι R) x y

theorem pairMat_apply_fst (g : Matrix (Fin 2) (Fin 2) R) (y : ι) :
    pairMat a b g a y = if y = a then g 0 0 else if y = b then g 0 1 else 0 := by
  simp [pairMat]

theorem pairMat_apply_snd (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) R) (y : ι) :
    pairMat a b g b y = if y = a then g 1 0 else if y = b then g 1 1 else 0 := by
  simp [pairMat, hab.symm]

theorem pairMat_apply_of_ne {x : ι} (hxa : x ≠ a) (hxb : x ≠ b) (g : Matrix (Fin 2) (Fin 2) R)
    (y : ι) : pairMat a b g x y = (1 : Matrix ι ι R) x y := by
  simp [pairMat, hxa, hxb]

theorem pairMat_apply_of_ne' {y : ι} (hya : y ≠ a) (hyb : y ≠ b) (g : Matrix (Fin 2) (Fin 2) R)
    (x : ι) : pairMat a b g x y = (1 : Matrix ι ι R) x y := by
  by_cases hxa : x = a
  · rw [hxa, pairMat_apply_fst, ite_eq_right hya, ite_eq_right hyb, one_apply_ne (Ne.symm hya)]
  by_cases hxb : x = b
  · rw [hxb, pairMat_apply_snd (hxb ▸ Ne.symm hxa), ite_eq_right hya, ite_eq_right hyb,
      one_apply_ne (Ne.symm hyb)]
  · exact pairMat_apply_of_ne hxa hxb g y

theorem pairMat_apply_pair (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) R) :
    pairMat a b g a a = g 0 0 ∧ pairMat a b g a b = g 0 1 ∧ pairMat a b g b a = g 1 0 ∧
      pairMat a b g b b = g 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [pairMat, hab.symm]

theorem pairMat_apply_fst_of_ne {y : ι} (hya : y ≠ a) (hyb : y ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) : pairMat a b g a y = 0 := by
  rw [pairMat_apply_fst, ite_eq_right hya, ite_eq_right hyb]

theorem pairMat_apply_snd_of_ne (hab : a ≠ b) {y : ι} (hya : y ≠ a) (hyb : y ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) : pairMat a b g b y = 0 := by
  rw [pairMat_apply_snd hab, ite_eq_right hya, ite_eq_right hyb]

theorem pairMat_apply_equiv {κ : Type*} [DecidableEq κ] (e : ι ≃ κ) (g : Matrix (Fin 2) (Fin 2) R)
    (x y : ι) : pairMat (e a) (e b) g (e x) (e y) = pairMat a b g x y := by
  simp [pairMat, e.injective.eq_iff, one_apply]

theorem pairMat_cases (hab : a ≠ b) {g : Matrix (Fin 2) (Fin 2) R} {P : ι → ι → R → Prop}
    (haa : P a a (g 0 0)) (hab' : P a b (g 0 1)) (hba : P b a (g 1 0)) (hbb : P b b (g 1 1))
    (hrow : ∀ x y, (x = a ∨ x = b) → y ≠ a → y ≠ b → P x y 0)
    (hcol : ∀ x y, x ≠ a → x ≠ b → (y = a ∨ y = b) → P x y 0)
    (hout : ∀ x y, x ≠ a → x ≠ b → y ≠ a → y ≠ b → P x y ((1 : Matrix ι ι R) x y))
    (x y : ι) : P x y (pairMat a b g x y) := by
  obtain ⟨h1, h2, h3, h4⟩ := pairMat_apply_pair hab g
  by_cases hxa : x = a
  · rw [hxa]
    by_cases hya : y = a
    · rw [hya, h1]; exact haa
    by_cases hyb : y = b
    · rw [hyb, h2]; exact hab'
    rw [pairMat_apply_fst_of_ne hya hyb]
    exact hrow a y (Or.inl rfl) hya hyb
  by_cases hxb : x = b
  · rw [hxb]
    by_cases hya : y = a
    · rw [hya, h3]; exact hba
    by_cases hyb : y = b
    · rw [hyb, h4]; exact hbb
    rw [pairMat_apply_snd_of_ne hab hya hyb]
    exact hrow b y (Or.inr rfl) hya hyb
  rw [pairMat_apply_of_ne hxa hxb]
  by_cases hya : y = a
  · rw [hya, one_apply_ne hxa]
    exact hya ▸ hcol x y hxa hxb (Or.inl hya)
  by_cases hyb : y = b
  · rw [hyb, one_apply_ne hxb]
    exact hyb ▸ hcol x y hxa hxb (Or.inr hyb)
  exact hout x y hxa hxb hya hyb

variable [Fintype ι]

omit [Fintype ι] in
theorem pairMat_one (hab : a ≠ b) : pairMat a b (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext x y
  refine pairMat_cases (P := fun x y c => c = (1 : Matrix ι ι R) x y) hab ?_ ?_ ?_ ?_
    (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_) (fun _ _ _ _ _ _ => rfl) x y
  · simp
  · simp [one_apply_ne hab]
  · simp [one_apply_ne (Ne.symm hab)]
  · simp
  · rcases hx with rfl | rfl
    · rw [one_apply_ne (Ne.symm hya)]
    · rw [one_apply_ne (Ne.symm hyb)]
  · rcases hy with rfl | rfl
    · rw [one_apply_ne hxa]
    · rw [one_apply_ne hxb]

theorem pairMat_mul (hab : a ≠ b) (g h : Matrix (Fin 2) (Fin 2) R) :
    pairMat a b (g * h) = pairMat a b g * pairMat a b h := by
  ext x y
  rw [mul_apply]
  have hrow : ∀ x, (x = a ∨ x = b) → ∑ z, pairMat a b g x z * pairMat a b h z y =
      pairMat a b g x a * pairMat a b h a y + pairMat a b g x b * pairMat a b h b y := by
    intro x hx
    refine Fintype.sum_eq_add a b hab fun z hz => ?_
    rcases hx with rfl | rfl
    · rw [pairMat_apply_fst_of_ne hz.1 hz.2, zero_mul]
    · rw [pairMat_apply_snd_of_ne hab hz.1 hz.2, zero_mul]
  obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hab g
  obtain ⟨h1, h2, h3, h4⟩ := pairMat_apply_pair hab h
  by_cases hxa : x = a
  · rw [hxa, hrow a (Or.inl rfl), g1, g2]
    by_cases hya : y = a
    · rw [hya, h1, h3, (pairMat_apply_pair hab (g * h)).1]
      simp [mul_apply, Fin.sum_univ_two]
    by_cases hyb : y = b
    · rw [hyb, h2, h4, (pairMat_apply_pair hab (g * h)).2.1]
      simp [mul_apply, Fin.sum_univ_two]
    · rw [pairMat_apply_fst_of_ne hya hyb, pairMat_apply_fst_of_ne hya hyb,
        pairMat_apply_snd_of_ne hab hya hyb]
      ring
  by_cases hxb : x = b
  · rw [hxb, hrow b (Or.inr rfl), g3, g4]
    by_cases hya : y = a
    · rw [hya, h1, h3, (pairMat_apply_pair hab (g * h)).2.2.1]
      simp [mul_apply, Fin.sum_univ_two]
    by_cases hyb : y = b
    · rw [hyb, h2, h4, (pairMat_apply_pair hab (g * h)).2.2.2]
      simp [mul_apply, Fin.sum_univ_two]
    · rw [pairMat_apply_snd_of_ne hab hya hyb, pairMat_apply_fst_of_ne hya hyb,
        pairMat_apply_snd_of_ne hab hya hyb]
      ring
  · rw [pairMat_apply_of_ne hxa hxb, Finset.sum_eq_single x]
    · rw [pairMat_apply_of_ne hxa hxb, one_apply_eq, one_mul, pairMat_apply_of_ne hxa hxb]
    · intro z _ hzx
      rw [pairMat_apply_of_ne hxa hxb, one_apply_ne (Ne.symm hzx), zero_mul]
    · simp

@[expose] def pairMatHom (hab : a ≠ b) : Matrix (Fin 2) (Fin 2) R →* Matrix ι ι R where
  toFun := pairMat a b
  map_one' := pairMat_one hab
  map_mul' := pairMat_mul hab

omit [Fintype ι] in
theorem pairMat_transpose (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) R) :
    (pairMat a b g)ᵀ = pairMat a b gᵀ := by
  ext x y
  rw [transpose_apply]
  refine pairMat_cases (P := fun x y c => pairMat a b g y x = c) hab ?_ ?_ ?_ ?_
    (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_) (fun x y hxa hxb hya hyb => ?_) x y
  · exact (pairMat_apply_pair hab g).1
  · exact (pairMat_apply_pair hab g).2.2.1
  · exact (pairMat_apply_pair hab g).2.1
  · exact (pairMat_apply_pair hab g).2.2.2
  · rw [pairMat_apply_of_ne hya hyb]
    rcases hx with rfl | rfl
    · exact one_apply_ne hya
    · exact one_apply_ne hyb
  · rcases hy with rfl | rfl
    · exact pairMat_apply_fst_of_ne hxa hxb g
    · exact pairMat_apply_snd_of_ne hab hxa hxb g
  · rw [pairMat_apply_of_ne hya hyb, one_apply, one_apply]
    simp [eq_comm]

theorem signedPerm_mul_pairMat (σ : Equiv.Perm ι) (ε : ι → R) (hab : a ≠ b)
    {g g' : Matrix (Fin 2) (Fin 2) R}
    (h00 : ε a * g 0 0 = g' 0 0 * ε a) (h01 : ε a * g 0 1 = g' 0 1 * ε b)
    (h10 : ε b * g 1 0 = g' 1 0 * ε a) (h11 : ε b * g 1 1 = g' 1 1 * ε b) :
    signedPerm σ ε * pairMat a b g = pairMat (σ a) (σ b) g' * signedPerm σ ε := by
  ext y x
  obtain ⟨y, rfl⟩ := σ.surjective y
  rw [mul_apply, mul_apply, Finset.sum_eq_single y, Finset.sum_eq_single (σ x)]
  · rw [signedPerm_apply, ite_eq_left rfl, signedPerm_apply, ite_eq_left rfl, pairMat_apply_equiv]
    obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hab g
    obtain ⟨g1', g2', g3', g4'⟩ := pairMat_apply_pair hab g'
    by_cases hya : y = a
    · rw [hya]
      by_cases hxa : x = a
      · rw [hxa, g1, g1']; exact h00
      by_cases hxb : x = b
      · rw [hxb, g2, g2']; exact h01
      · rw [pairMat_apply_fst_of_ne hxa hxb, pairMat_apply_fst_of_ne hxa hxb, mul_zero, zero_mul]
    by_cases hyb : y = b
    · rw [hyb]
      by_cases hxa : x = a
      · rw [hxa, g3, g3']; exact h10
      by_cases hxb : x = b
      · rw [hxb, g4, g4']; exact h11
      · rw [pairMat_apply_snd_of_ne hab hxa hxb, pairMat_apply_snd_of_ne hab hxa hxb, mul_zero,
          zero_mul]
    · rw [pairMat_apply_of_ne hya hyb, pairMat_apply_of_ne hya hyb]
      by_cases hxy : y = x
      · rw [hxy, one_apply_eq, mul_one, one_mul]
      · rw [one_apply_ne hxy, mul_zero, zero_mul]
  · intro z _ hz
    rw [signedPerm_apply, ite_eq_right hz, mul_zero]
  · simp
  · intro z _ hz
    rw [signedPerm_apply, ite_eq_right fun h => hz (σ.injective h).symm, zero_mul]
  · simp

@[expose] def IsSupp (A : Set ι) (M : Matrix ι ι R) : Prop :=
  ∀ x y, x ∉ A ∨ y ∉ A → M x y = (1 : Matrix ι ι R) x y

omit [Fintype ι] in
theorem IsSupp.mono {A B : Set ι} {M : Matrix ι ι R} (hM : IsSupp A M) (hAB : A ⊆ B) :
    IsSupp B M := fun x y h => hM x y (h.imp (fun hx h' => hx (hAB h')) fun hy h' => hy (hAB h'))

theorem IsSupp.mul_apply_of_notMem {A : Set ι} {M : Matrix ι ι R} (hM : IsSupp A M) {x : ι}
    (hx : x ∉ A) (N : Matrix ι ι R) (y : ι) : (M * N) x y = N x y := by
  rw [mul_apply, Finset.sum_eq_single x]
  · rw [hM x x (Or.inl hx), one_apply_eq, one_mul]
  · intro z _ hzx
    rw [hM x z (Or.inl hx), one_apply_ne (Ne.symm hzx), zero_mul]
  · simp

theorem IsSupp.mul_apply_of_mem {A B : Set ι} {M N : Matrix ι ι R} (hM : IsSupp A M)
    (hN : IsSupp B N) (hAB : Disjoint A B) {x : ι} (hx : x ∈ A) (y : ι) :
    (M * N) x y = M x y := by
  rw [mul_apply, Finset.sum_eq_single y]
  · by_cases hy : y ∈ A
    · rw [hN y y (Or.inl (Set.disjoint_left.1 hAB hy)), one_apply_eq, mul_one]
    · rw [hM x y (Or.inr hy), one_apply_ne fun (h : x = y) => hy (h ▸ hx), zero_mul]
  · intro z _ hzy
    by_cases hz : z ∈ A
    · rw [hN z y (Or.inl (Set.disjoint_left.1 hAB hz)), one_apply_ne hzy, mul_zero]
    · rw [hM x z (Or.inr hz), one_apply_ne fun (h : x = z) => hz (h ▸ hx), zero_mul]
  · simp

theorem IsSupp.commute {A B : Set ι} {M N : Matrix ι ι R} (hM : IsSupp A M) (hN : IsSupp B N)
    (hAB : Disjoint A B) : Commute M N := by
  show M * N = N * M
  ext x y
  by_cases hxA : x ∈ A
  · rw [hM.mul_apply_of_mem hN hAB hxA, hN.mul_apply_of_notMem (Set.disjoint_left.1 hAB hxA)]
  · rw [hM.mul_apply_of_notMem hxA]
    by_cases hxB : x ∈ B
    · rw [hN.mul_apply_of_mem hM hAB.symm hxB]
    · rw [hN.mul_apply_of_notMem hxB, hM x y (Or.inl hxA), hN x y (Or.inl hxB)]

omit [Fintype ι] in
theorem isSupp_pairMat (g : Matrix (Fin 2) (Fin 2) R) : IsSupp {a, b} (pairMat a b g) := by
  rintro x y (hx | hy)
  · exact pairMat_apply_of_ne (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h)) g y
  · exact pairMat_apply_of_ne' (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h)) g x

omit [Fintype ι] in
theorem IsSupp.transpose {A : Set ι} {M : Matrix ι ι R} (hM : IsSupp A M) : IsSupp A Mᵀ :=
  fun x y h => by
    rw [transpose_apply, hM y x h.symm]
    simp [one_apply, eq_comm]

omit [Fintype ι] in
theorem pairMat_w (hab : a ≠ b) :
    pairMat a b !![0, -1; 1, 0] =
      signedPerm (Equiv.swap a b) (fun x => if x = b then (-1 : R) else 1) := by
  ext x y
  refine pairMat_cases (P := fun x y c => c = signedPerm (Equiv.swap a b)
    (fun x => if x = b then (-1 : R) else 1) x y) hab ?_ ?_ ?_ ?_
    (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_) (fun x y hxa hxb hya hyb => ?_) x y
  · simp [signedPerm_apply, hab]
  · simp [signedPerm_apply]
  · simp [signedPerm_apply, hab]
  · simp [signedPerm_apply, hab.symm]
  · rw [signedPerm_apply, Equiv.swap_apply_of_ne_of_ne hya hyb, ite_eq_right]
    rintro rfl
    rcases hx with rfl | rfl <;> contradiction
  · rw [signedPerm_apply, ite_eq_right]
    rcases hy with rfl | rfl
    · rw [Equiv.swap_apply_left]; exact hxb
    · rw [Equiv.swap_apply_right]; exact hxa
  · rw [signedPerm_apply, Equiv.swap_apply_of_ne_of_ne hya hyb, one_apply, ite_eq_right hyb]

omit [Fintype ι] in
theorem pairMat_w_inv (hab : a ≠ b) :
    pairMat a b !![0, 1; -1, 0] =
      signedPerm (Equiv.swap a b) (fun x => if x = a then (-1 : R) else 1) := by
  ext x y
  refine pairMat_cases (P := fun x y c => c = signedPerm (Equiv.swap a b)
    (fun x => if x = a then (-1 : R) else 1) x y) hab ?_ ?_ ?_ ?_
    (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_) (fun x y hxa hxb hya hyb => ?_) x y
  · simp [signedPerm_apply, hab]
  · simp [signedPerm_apply, hab.symm]
  · simp [signedPerm_apply]
  · simp [signedPerm_apply, hab.symm]
  · rw [signedPerm_apply, Equiv.swap_apply_of_ne_of_ne hya hyb, ite_eq_right]
    rintro rfl
    rcases hx with rfl | rfl <;> contradiction
  · rw [signedPerm_apply, ite_eq_right]
    rcases hy with rfl | rfl
    · rw [Equiv.swap_apply_left]; exact hxb
    · rw [Equiv.swap_apply_right]; exact hxa
  · rw [signedPerm_apply, Equiv.swap_apply_of_ne_of_ne hya hyb, one_apply, ite_eq_right hya]

omit [Fintype ι] in
theorem pairMat_diag (hab : a ≠ b) (u v : R) :
    pairMat a b !![u, 0; 0, v] = diagonal fun x => if x = a then u else if x = b then v else 1 := by
  ext x y
  refine pairMat_cases (P := fun x y c => c = diagonal
    (fun x => if x = a then u else if x = b then v else 1) x y) hab ?_ ?_ ?_ ?_
    (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_) (fun x y hxa hxb hya hyb => ?_) x y
  · simp
  · simp [diagonal_apply_ne _ hab]
  · simp [diagonal_apply_ne _ (Ne.symm hab)]
  · simp [hab.symm]
  · rw [diagonal_apply_ne]
    rintro rfl
    rcases hx with rfl | rfl <;> contradiction
  · rw [diagonal_apply_ne]
    rintro rfl
    rcases hy with rfl | rfl <;> contradiction
  · rw [diagonal_apply, one_apply]
    by_cases hxy : x = y <;> simp [hxy, hya, hyb]

end PairMat

section Blocks

variable {m : Type*} [DecidableEq m] {R : Type*} [CommRing R]

theorem fromBlocks_signedPerm (σ τ : Equiv.Perm m) (ε δ : m → R) :
    fromBlocks (signedPerm σ ε) 0 0 (signedPerm τ δ) =
      signedPerm (Equiv.sumCongr σ τ) (Sum.elim ε δ) := by
  ext (x | x) (y | y) <;> simp [signedPerm_apply]

theorem isSupp_fromBlocks {S : Set m} {A D : Matrix m m R} (hA : IsSupp S A) (hD : IsSupp S D) :
    IsSupp (Sum.elim id id ⁻¹' S) (fromBlocks A 0 0 D) := by
  rintro (x | x) (y | y) h
  · simpa [one_apply] using hA x y h
  · simp
  · simp
  · simpa [one_apply] using hD x y h

end Blocks

section SL2

variable {k : Type*} [Field k]

@[expose] def sl2DiagElt (a : kˣ) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(a : k), 0; 0, ((a⁻¹ : kˣ) : k)], by simp [det_fin_two_of]⟩

@[expose] def sl2Diag : kˣ →* SpecialLinearGroup (Fin 2) k where
  toFun := sl2DiagElt
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sl2DiagElt]
  map_mul' a b := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [sl2DiagElt, mul_apply, Fin.sum_univ_two, mul_comm]

@[simp] theorem coe_sl2Diag (a : kˣ) :
    ((sl2Diag a : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(a : k), 0; 0, ((a⁻¹ : kˣ) : k)] := rfl

@[expose] def sl2W : SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, -1; 1, 0], by simp [det_fin_two_of]⟩

@[simp] theorem coe_sl2W :
    ((sl2W : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, -1; 1, 0] := rfl

theorem coe_sl2W_inv :
    (((sl2W : SpecialLinearGroup (Fin 2) k)⁻¹ : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := by
  change adjugate (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) k) = _
  rw [adjugate_fin_two_of]
  simp

@[expose] def sl2ConjDiagElt (u : kˣ) (g : SpecialLinearGroup (Fin 2) k) :
    SpecialLinearGroup (Fin 2) k :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) k) 0 0, (g : Matrix (Fin 2) (Fin 2) k) 0 1 * u⁻¹;
      (g : Matrix (Fin 2) (Fin 2) k) 1 0 * u, (g : Matrix (Fin 2) (Fin 2) k) 1 1], by
    have hg := g.2
    rw [det_fin_two] at hg
    have hu : ((u⁻¹ : kˣ) : k) * u = 1 := Units.inv_mul u
    rw [det_fin_two_of]
    linear_combination hg - (g : Matrix (Fin 2) (Fin 2) k) 0 1 *
      (g : Matrix (Fin 2) (Fin 2) k) 1 0 * hu⟩

@[expose] def sl2ConjDiag (u : kˣ) : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k
    where
  toFun := sl2ConjDiagElt u
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sl2ConjDiagElt]
  map_mul' g h := by
    have hu : (u : k) ≠ 0 := u.ne_zero
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [sl2ConjDiagElt, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
    all_goals (field_simp; try ring)

theorem coe_sl2ConjDiag (u : kˣ) (g : SpecialLinearGroup (Fin 2) k) :
    ((sl2ConjDiag u g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(g : Matrix (Fin 2) (Fin 2) k) 0 0, (g : Matrix (Fin 2) (Fin 2) k) 0 1 * u⁻¹;
        (g : Matrix (Fin 2) (Fin 2) k) 1 0 * u, (g : Matrix (Fin 2) (Fin 2) k) 1 1] := rfl

theorem sl2W_mul_sl2W : (sl2W : SpecialLinearGroup (Fin 2) k) * sl2W = sl2Diag (-1) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [sl2W, mul_apply, Fin.sum_univ_two]

theorem sl2W_mul_sl2Diag (a : kˣ) :
    (sl2W : SpecialLinearGroup (Fin 2) k) * sl2Diag a = sl2Diag a⁻¹ * sl2W := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [sl2W, mul_apply, Fin.sum_univ_two]

theorem sl2ConjDiag_inv_sl2W (a : kˣ) :
    sl2ConjDiag a⁻¹ (sl2W : SpecialLinearGroup (Fin 2) k) = sl2Diag a * sl2W := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2ConjDiag]
  fin_cases i <;> fin_cases j <;> simp [sl2W, mul_apply, Fin.sum_univ_two]

theorem sl2ConjDiag_neg_one_sl2W :
    sl2ConjDiag (-1) (sl2W : SpecialLinearGroup (Fin 2) k) = sl2W⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2W_inv, coe_sl2ConjDiag]
  fin_cases i <;> fin_cases j <;> simp [sl2W]

end SL2

section Symplectic

variable {r : ℕ} {k : Type} [Field k]

theorem mem_statedSp_iff {g : GL (Fin r ⊕ Fin r) k} :
    g ∈ StatedSp r k ↔ (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)ᵀ * fromBlocks 0 1 (-1) 0 *
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem statedSp_ext {x y : StatedSp r k}
    (h : ((x : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      ((y : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) : x = y :=
  Subtype.ext (Units.ext h)

theorem statedSp_commute {x y : StatedSp r k}
    (h : Commute ((x : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
      ((y : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) : Commute x y :=
  statedSp_ext (by simpa only [Subgroup.coe_mul, Units.val_mul] using h.eq)

@[expose] noncomputable def leviSp : GL (Fin r) k →* StatedSp r k :=
  (MulEquiv.subgroupCongr
    (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := k)).symm
    ).toMonoidHom.comp TauCeti.GLSymplectic.leviHom

theorem coe_leviSp (A : GL (Fin r) k) :
    (((leviSp A : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      fromBlocks (A : Matrix (Fin r) (Fin r) k) 0 0
        ((A⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)ᵀ := by
  simp [leviSp, MulEquiv.subgroupCongr_apply, TauCeti.GLSymplectic.coe_leviHom]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι}

@[expose] noncomputable def pairGL (hab : a ≠ b) : SpecialLinearGroup (Fin 2) k →* GL ι k :=
  (Units.map (pairMatHom hab)).comp Matrix.SpecialLinearGroup.toGL

theorem coe_pairGL (hab : a ≠ b) (g : SpecialLinearGroup (Fin 2) k) :
    ((pairGL hab g : GL ι k) : Matrix ι ι k) = pairMat a b (g : Matrix (Fin 2) (Fin 2) k) := rfl

theorem coe_pairGL_inv (hab : a ≠ b) (g : SpecialLinearGroup (Fin 2) k) :
    (((pairGL hab g)⁻¹ : GL ι k) : Matrix ι ι k) =
      pairMat a b ((g⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  rw [← map_inv, coe_pairGL]

theorem pairGL_inl_inr_mem (i : Fin r) (g : SpecialLinearGroup (Fin 2) k) :
    pairGL (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i) g ∈ StatedSp r k := by
  suffices h : (pairGL (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i)).range ≤
      StatedSp r k from h ⟨g, rfl⟩
  rw [MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, coe_pairGL,
    TransvectionStruct.toSpecialLinearGroup_def]
  obtain ⟨p, q, hpq, c⟩ := t
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · have h : pairMat (Sum.inl i) (Sum.inr i)
        ((Matrix.SpecialLinearGroup.transvection hpq c : SpecialLinearGroup (Fin 2) k) :
          Matrix (Fin 2) (Fin 2) k) = fromBlocks 1 (single i i c) 0 1 := by
      ext (x | x) (y | y) <;>
        simp [pairMat, Matrix.SpecialLinearGroup.transvection, transvection, one_apply,
          single_apply] <;>
        split_ifs <;> aesop
    rw [h]
    exact SymplecticGroup.fromBlocks_upper_mem (by simp)
  · have h : pairMat (Sum.inl i) (Sum.inr i)
        ((Matrix.SpecialLinearGroup.transvection hpq c : SpecialLinearGroup (Fin 2) k) :
          Matrix (Fin 2) (Fin 2) k) = fromBlocks 1 0 (single i i c) 1 := by
      ext (x | x) (y | y) <;>
        simp [pairMat, Matrix.SpecialLinearGroup.transvection, transvection, one_apply,
          single_apply] <;>
        split_ifs <;> aesop
    rw [h]
    exact SymplecticGroup.fromBlocks_lower_mem (by simp)
  · exact absurd rfl hpq

@[expose] noncomputable def lam (i : Fin r) : SpecialLinearGroup (Fin 2) k →* StatedSp r k :=
  (pairGL (Sum.inl_ne_inr : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i)).codRestrict (StatedSp r k)
    (pairGL_inl_inr_mem i)

theorem coe_lam (i : Fin r) (g : SpecialLinearGroup (Fin 2) k) :
    (((lam i g : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      pairMat (Sum.inl i) (Sum.inr i) (g : Matrix (Fin 2) (Fin 2) k) := rfl

@[expose] noncomputable def rho (i j : Fin r) (hij : i ≠ j) :
    SpecialLinearGroup (Fin 2) k →* StatedSp r k :=
  leviSp.comp (pairGL hij)

theorem coe_rho {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    (((rho i j hij g : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      fromBlocks (pairMat i j (g : Matrix (Fin 2) (Fin 2) k)) 0 0
        (pairMat i j ((g⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))ᵀ := by
  rw [rho, MonoidHom.comp_apply, coe_leviSp, coe_pairGL, coe_pairGL_inv]

theorem coe_rho' {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    (((rho i j hij g : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      fromBlocks (pairMat i j (g : Matrix (Fin 2) (Fin 2) k)) 0 0
        (pairMat i j ((g⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ) := by
  rw [coe_rho, pairMat_transpose hij]

@[expose] noncomputable def torusHom : (Fin r → kˣ) →* StatedSp r k :=
  leviSp.comp TauCeti.diagGL

theorem coe_torusHom (t : Fin r → kˣ) :
    (((torusHom t : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      diagonal (Sum.elim (fun i => (t i : k)) fun i => ((t i)⁻¹ : kˣ)) := by
  rw [torusHom, MonoidHom.comp_apply, coe_leviSp, ← map_inv, TauCeti.diagGL_coe,
    TauCeti.diagGL_coe, diagonal_transpose, fromBlocks_diagonal]
  rfl

@[expose] noncomputable def torus (r : ℕ) (k : Type) [Field k] : Subgroup (StatedSp r k) :=
  (torusHom (r := r) (k := k)).range

theorem torusHom_injective : Function.Injective (torusHom (r := r) (k := k)) := by
  intro s t h
  funext i
  apply Units.ext
  have := congrArg (fun g : StatedSp r k => ((g : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (Sum.inl i) (Sum.inl i)) h
  simpa [coe_torusHom] using this

theorem torusHom_mem_torus (t : Fin r → kˣ) : torusHom t ∈ torus r k := ⟨t, rfl⟩

theorem lam_sl2Diag (i : Fin r) (a : kˣ) : lam i (sl2Diag a) = torusHom (Pi.mulSingle i a) := by
  apply statedSp_ext
  rw [coe_lam, coe_sl2Diag, pairMat_diag Sum.inl_ne_inr, coe_torusHom]
  congr 1
  funext x
  rcases x with x | x
  · by_cases hx : x = i
    · simp [hx]
    · simp [hx, Pi.mulSingle_apply]
  · by_cases hx : x = i
    · simp [hx]
    · simp [hx, Pi.mulSingle_apply]

end Symplectic

@[expose] def signedPermGroup (r : ℕ) : Subgroup (Equiv.Perm (Fin r ⊕ Fin r)) where
  carrier := {w | ∀ x, w x.swap = (w x).swap}
  mul_mem' {v w} hv hw x := by
    change v (w x.swap) = (v (w x)).swap
    rw [hw, hv]
  one_mem' _ := rfl
  inv_mem' {w} hw x := by
    change w⁻¹ x.swap = (w⁻¹ x).swap
    apply w.injective
    rw [hw]
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem mem_signedPermGroup {r : ℕ} {w : Equiv.Perm (Fin r ⊕ Fin r)} :
    w ∈ signedPermGroup r ↔ ∀ x, w x.swap = (w x).swap := Iff.rfl

section Monomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [Field k]

@[expose] def IsLinePerm (σ : Equiv.Perm ι) (M : Matrix ι ι k) : Prop :=
  ∀ x y, M y x ≠ 0 ↔ y = σ x

omit [Fintype ι] [DecidableEq ι] in
theorem IsLinePerm.apply_ne_zero {σ : Equiv.Perm ι} {M : Matrix ι ι k} (h : IsLinePerm σ M)
    (x : ι) : M (σ x) x ≠ 0 :=
  (h x _).2 rfl

omit [Fintype ι] [DecidableEq ι] in
theorem IsLinePerm.apply_eq_zero {σ : Equiv.Perm ι} {M : Matrix ι ι k} (h : IsLinePerm σ M)
    {x y : ι} (hy : y ≠ σ x) : M y x = 0 :=
  not_not.1 (mt (h x y).1 hy)

omit [Fintype ι] [DecidableEq ι] in
theorem IsLinePerm.unique {σ τ : Equiv.Perm ι} {M : Matrix ι ι k} (hσ : IsLinePerm σ M)
    (hτ : IsLinePerm τ M) : σ = τ :=
  Equiv.ext fun x => (hτ x (σ x)).1 (hσ.apply_ne_zero x)

omit [DecidableEq ι] in
theorem IsLinePerm.mul {σ τ : Equiv.Perm ι} {M N : Matrix ι ι k} (hM : IsLinePerm σ M)
    (hN : IsLinePerm τ N) : IsLinePerm (σ * τ) (M * N) := by
  intro x y
  rw [mul_apply, Finset.sum_eq_single (τ x), Equiv.Perm.mul_apply, ← hM (τ x) y]
  · exact ⟨left_ne_zero_of_mul, fun h => mul_ne_zero h (hN.apply_ne_zero x)⟩
  · intro z _ hz
    rw [hN.apply_eq_zero hz, mul_zero]
  · simp

omit [Fintype ι] in
theorem isLinePerm_one : IsLinePerm 1 (1 : Matrix ι ι k) := fun x y => by
  rw [Equiv.Perm.one_apply, one_apply]
  by_cases h : y = x <;> simp [h]

theorem IsLinePerm.inv {σ : Equiv.Perm ι} {g : GL ι k} (h : IsLinePerm σ (g : Matrix ι ι k)) :
    IsLinePerm σ⁻¹ ((g⁻¹ : GL ι k) : Matrix ι ι k) := by
  intro x y
  have hmul : (((g⁻¹ : GL ι k) : Matrix ι ι k) * (g : Matrix ι ι k)) y (σ⁻¹ x) =
      (1 : Matrix ι ι k) y (σ⁻¹ x) := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hx : (g : Matrix ι ι k) x (σ⁻¹ x) ≠ 0 := by
    have := h.apply_ne_zero (σ⁻¹ x)
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using this
  rw [mul_apply, Finset.sum_eq_single x] at hmul
  · constructor
    · intro hne
      by_contra hy
      rw [one_apply_ne hy] at hmul
      exact hne ((mul_eq_zero.1 hmul).resolve_right hx)
    · rintro rfl h0
      rw [h0, zero_mul, one_apply_eq] at hmul
      exact zero_ne_one hmul
  · intro z _ hzx
    rw [h.apply_eq_zero (y := z) (x := σ⁻¹ x)
      (by simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hzx), mul_zero]
  · simp

variable (ι k) in
def monomialGL : Subgroup (GL ι k) where
  carrier := {g | ∃ σ : Equiv.Perm ι, IsLinePerm σ (g : Matrix ι ι k)}
  mul_mem' := fun ⟨σ, hσ⟩ ⟨τ, hτ⟩ => ⟨σ * τ, by rw [Units.val_mul]; exact hσ.mul hτ⟩
  one_mem' := ⟨1, by rw [Units.val_one]; exact isLinePerm_one⟩
  inv_mem' := fun ⟨σ, hσ⟩ => ⟨σ⁻¹, hσ.inv⟩

theorem mem_monomialGL {g : GL ι k} {σ : Equiv.Perm ι} (h : IsLinePerm σ (g : Matrix ι ι k)) :
    g ∈ monomialGL ι k :=
  ⟨σ, h⟩

noncomputable def linePerm : monomialGL ι k →* Equiv.Perm ι where
  toFun g := g.2.choose
  map_one' := (monomialGL ι k).one_mem.choose_spec.unique (by
    show IsLinePerm 1 (((1 : GL ι k) : Matrix ι ι k))
    rw [Units.val_one]
    exact isLinePerm_one)
  map_mul' g h := (g * h).2.choose_spec.unique (by
    show IsLinePerm _ (((g : GL ι k) * h : GL ι k) : Matrix ι ι k)
    rw [Units.val_mul]
    exact g.2.choose_spec.mul h.2.choose_spec)

theorem isLinePerm_linePerm (g : monomialGL ι k) :
    IsLinePerm (linePerm g) ((g : GL ι k) : Matrix ι ι k) :=
  g.2.choose_spec

theorem linePerm_eq {g : monomialGL ι k} {σ : Equiv.Perm ι}
    (h : IsLinePerm σ ((g : GL ι k) : Matrix ι ι k)) : linePerm g = σ :=
  (isLinePerm_linePerm g).unique h

omit [Fintype ι] in
theorem isLinePerm_signedPerm (σ : Equiv.Perm ι) {ε : ι → k} (hε : ∀ x, ε x ≠ 0) :
    IsLinePerm σ (signedPerm σ ε) := by
  intro x y
  rw [signedPerm_apply]
  by_cases h : y = σ x <;> simp [h, hε]

end Monomial

section SymplecticMonomial

variable {r : ℕ} {k : Type} [Field k]

theorem J_apply_ne_zero_iff (u v : Fin r ⊕ Fin r) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) u v ≠ 0 ↔ v = u.swap := by
  rcases u with u | u <;> rcases v with v | v <;> simp [one_apply, eq_comm]

theorem IsLinePerm.mem_signedPermGroup {g : GL (Fin r ⊕ Fin r) k} (hg : g ∈ StatedSp r k)
    {σ : Equiv.Perm (Fin r ⊕ Fin r)} (h : IsLinePerm σ (g : Matrix (Fin r ⊕ Fin r) _ k)) :
    σ ∈ signedPermGroup r := by
  intro x
  have hJ := congrFun (congrFun (mem_statedSp_iff.1 hg) x) x.swap
  rw [mul_apply, Finset.sum_eq_single (σ x.swap), mul_apply, Finset.sum_eq_single (σ x),
    transpose_apply] at hJ
  · have hne : (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) x x.swap ≠ 0 :=
      (J_apply_ne_zero_iff _ _).2 rfl
    rw [← hJ] at hne
    exact (J_apply_ne_zero_iff (σ x) (σ x.swap)).1
      (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
  · intro z _ hz
    rw [transpose_apply, h.apply_eq_zero hz, zero_mul]
  · simp
  · intro z _ hz
    rw [h.apply_eq_zero hz, mul_zero]
  · simp

end SymplecticMonomial

section Identities

variable {r : ℕ} {k : Type} [Field k]

theorem signedPerm_mul_pairMat_of_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (ε : ι → k) {a b a' b' : ι} (hab : a ≠ b) (ha : σ a = a') (hb : σ b = b')
    (hε : ε a = ε b) (g : Matrix (Fin 2) (Fin 2) k) :
    signedPerm σ ε * pairMat a b g = pairMat a' b' g * signedPerm σ ε := by
  rw [signedPerm_mul_pairMat σ ε hab (g' := g) (mul_comm _ _) (by rw [hε, mul_comm])
    (by rw [hε, mul_comm]) (mul_comm _ _), ha, hb]

theorem transpose_w_inv :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k)ᵀ = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coe_lam_sl2W (i : Fin r) :
    (((lam i sl2W : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      signedPerm (Equiv.swap (Sum.inl i) (Sum.inr i))
        (fun x => if x = Sum.inr i then (-1 : k) else 1) := by
  rw [coe_lam, coe_sl2W, pairMat_w Sum.inl_ne_inr]

@[expose] def wSign (j : Fin r) : Fin r → k := fun x => if x = j then -1 else 1

theorem coe_rho_sl2W {i j : Fin r} (hij : i ≠ j) :
    (((rho i j hij sl2W : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      signedPerm (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j))
        (Sum.elim (wSign j) (wSign j)) := by
  rw [coe_rho', coe_sl2W, coe_sl2W_inv, transpose_w_inv, pairMat_w hij, fromBlocks_signedPerm]
  rfl

theorem wSign_ne_zero (j x : Fin r) : wSign (k := k) j x ≠ 0 := by
  unfold wSign
  split_ifs <;> simp

theorem isLinePerm_lam_sl2W (i : Fin r) :
    IsLinePerm (Equiv.swap (Sum.inl i) (Sum.inr i))
      (((lam i sl2W : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  rw [coe_lam_sl2W]
  exact isLinePerm_signedPerm _ fun x => by split_ifs <;> simp

theorem isLinePerm_rho_sl2W {i j : Fin r} (hij : i ≠ j) :
    IsLinePerm (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j))
      (((rho i j hij sl2W : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  rw [coe_rho_sl2W]
  exact isLinePerm_signedPerm _ fun x => by rcases x with x | x <;> exact wSign_ne_zero _ _

theorem isLinePerm_torusHom (t : Fin r → kˣ) :
    IsLinePerm 1 (((torusHom t : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  rw [coe_torusHom, ← signedPerm_one]
  exact isLinePerm_signedPerm _ fun x => by rcases x with x | x <;> simp

theorem conj_comp_eq {G H : Type*} [Group G] [Group H] {x : H} {α β : G →* H}
    (h : ∀ g, x * α g = β g * x) : (MulAut.conj x).toMonoidHom.comp α = β := by
  ext g
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h g, mul_inv_cancel_right]

theorem coe_mul_statedSp (x y : StatedSp r k) :
    (((x * y : StatedSp r k) : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      ((x : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) *
        ((y : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := rfl

theorem conj_rho_sl2W_comp_lam_snd {i j : Fin r} (hij : i ≠ j) :
    (MulAut.conj (rho i j hij sl2W)).toMonoidHom.comp (lam j) = lam (k := k) i := by
  refine conj_comp_eq fun g => statedSp_ext ?_
  rw [coe_mul_statedSp, coe_mul_statedSp, coe_rho_sl2W, coe_lam, coe_lam]
  exact signedPerm_mul_pairMat_of_eq _ _ Sum.inl_ne_inr (by simp) (by simp) rfl _

theorem conj_rho_sl2W_comp_lam_fst {i j : Fin r} (hij : i ≠ j) :
    (MulAut.conj (rho i j hij sl2W)).toMonoidHom.comp (lam i) = lam (k := k) j := by
  refine conj_comp_eq fun g => statedSp_ext ?_
  rw [coe_mul_statedSp, coe_mul_statedSp, coe_rho_sl2W, coe_lam, coe_lam]
  exact signedPerm_mul_pairMat_of_eq _ _ Sum.inl_ne_inr (by simp) (by simp) rfl _

theorem conj_lam_sl2Diag_inv_comp_rho {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    (MulAut.conj (lam j (sl2Diag a))⁻¹).toMonoidHom.comp (rho i j hij) =
      (rho i j hij).comp (sl2ConjDiag a⁻¹) := by
  refine conj_comp_eq fun g => ?_
  rw [lam_sl2Diag, torusHom, MonoidHom.comp_apply, ← map_inv, MonoidHom.comp_apply, rho,
    MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_pairGL, coe_pairGL, ← map_inv, TauCeti.diagGL_coe,
    ← signedPerm_one, coe_sl2ConjDiag]
  refine signedPerm_mul_pairMat _ _ hij ?_ ?_ ?_ ?_ <;> simp [hij, mul_comm]

theorem conj_rho_sl2W_comp_rho {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (MulAut.conj (rho i j hij sl2W)).toMonoidHom.comp (rho j l hjl) =
      (rho (k := k) i l hil).comp (sl2ConjDiag (-1)) := by
  refine conj_comp_eq fun g => ?_
  simp only [rho, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_pairGL, coe_pairGL, coe_pairGL, coe_sl2W, pairMat_w hij,
    coe_sl2ConjDiag]
  have h := signedPerm_mul_pairMat (Equiv.swap i j) (fun x => if x = j then (-1 : k) else 1) hjl
    (g := (g : Matrix (Fin 2) (Fin 2) k))
    (g' := !![(g : Matrix (Fin 2) (Fin 2) k) 0 0, (g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        ((-1 : kˣ)⁻¹ : kˣ); (g : Matrix (Fin 2) (Fin 2) k) 1 0 * ((-1 : kˣ) : k),
        (g : Matrix (Fin 2) (Fin 2) k) 1 1]) (by simp [mul_comm]) (by simp [Ne.symm hjl])
    (by simp [Ne.symm hjl]) (by simp [mul_comm])
  rwa [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)] at h

theorem conj_rho_sl2W_inv_comp_rho {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (MulAut.conj (rho j l hjl sl2W)⁻¹).toMonoidHom.comp (rho i j hij) =
      (rho (k := k) i l hil).comp (sl2ConjDiag (-1)) := by
  refine conj_comp_eq fun g => ?_
  simp only [rho, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, coe_pairGL, coe_pairGL, coe_pairGL, coe_sl2W_inv,
    pairMat_w_inv hjl, coe_sl2ConjDiag]
  have h := signedPerm_mul_pairMat (Equiv.swap j l) (fun x => if x = j then (-1 : k) else 1) hij
    (g := (g : Matrix (Fin 2) (Fin 2) k))
    (g' := !![(g : Matrix (Fin 2) (Fin 2) k) 0 0, (g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        ((-1 : kˣ)⁻¹ : kˣ); (g : Matrix (Fin 2) (Fin 2) k) 1 0 * ((-1 : kˣ) : k),
        (g : Matrix (Fin 2) (Fin 2) k) 1 1]) (by simp [hij, mul_comm]) (by simp [hij])
    (by simp [hij]) (by simp [mul_comm])
  rwa [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hij hil] at h

theorem isSupp_lam (i : Fin r) (g : SpecialLinearGroup (Fin 2) k) :
    IsSupp {Sum.inl i, Sum.inr i} (((lam i g : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  rw [coe_lam]
  exact isSupp_pairMat _

theorem isSupp_rho {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    IsSupp (Sum.elim id id ⁻¹' {i, j}) (((rho i j hij g : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  rw [coe_rho]
  exact isSupp_fromBlocks (isSupp_pairMat _) (isSupp_pairMat _).transpose

theorem commute_lam_lam {i j : Fin r} (hij : i ≠ j) (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (lam i g) (lam j g') :=
  statedSp_commute ((isSupp_lam i g).commute (isSupp_lam j g') (by
    simp [Set.disjoint_left, hij]))

theorem commute_rho_lam {i j l : Fin r} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (g g' : SpecialLinearGroup (Fin 2) k) : Commute (rho i j hij g) (lam l g') :=
  statedSp_commute ((isSupp_rho hij g).commute (isSupp_lam l g') (by
    rw [Set.disjoint_left]
    rintro (x | x) hx <;> simp at hx ⊢ <;> rcases hx with rfl | rfl <;>
      simp [Ne.symm hli, Ne.symm hlj]))

theorem commute_rho_rho {i j l m : Fin r} (hij : i ≠ j) (hlm : l ≠ m) (hil : i ≠ l)
    (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m) (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (rho i j hij g) (rho l m hlm g') :=
  statedSp_commute ((isSupp_rho hij g).commute (isSupp_rho hlm g') (by
    rw [Set.disjoint_left]
    rintro (x | x) hx <;> simp at hx ⊢ <;> rcases hx with rfl | rfl <;> simp [*]))

end Identities

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
