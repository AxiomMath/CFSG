module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Toral
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCore
public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.F4Transfer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

section Generic

variable {P : Type*} [Group P]

@[expose] def Hgen (A : Subgroup (MulAut P)) : Subgroup P :=
  ⨆ (S : Subgroup (MulAut P)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), dPart 3 (c25Fix S)

theorem mem_Hgen_of_pair {A : Subgroup (MulAut P)} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {a b : MulAut P} (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) {x : P} (hxa : a x = x) (hxb : b x = x)
    (hx : Nat.Coprime (orderOf x) 3) : x ∈ Hgen A := by
  have hS : Subgroup.closure ({a, b} : Set (MulAut P)) ≤ A ∧
      Nat.card A ≤ 3 * Nat.card (Subgroup.closure ({a, b} : Set (MulAut P))) := by
    refine ⟨(Subgroup.closure_le _).2 (by rintro y (rfl | rfl); exacts [ha, hb]), ?_⟩
    have := card_closure_pair_ge_nine hAel hA27 ha hb ha1 hba
    omega
  have hfix : x ∈ c25Fix (Subgroup.closure ({a, b} : Set (MulAut P))) := by
    rw [mem_c25Fix_closure]
    rintro y (rfl | rfl)
    exacts [hxa, hxb]
  have hd : x ∈ dPart 3 (c25Fix (Subgroup.closure ({a, b} : Set (MulAut P)))) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hfix, hx⟩)
  have hle : dPart 3 (c25Fix (Subgroup.closure ({a, b} : Set (MulAut P)))) ≤ Hgen A :=
    le_iSup₂_of_le (Subgroup.closure ({a, b} : Set (MulAut P))) hS le_rfl
  exact hle hd

end Generic

section KLevel

variable {K : Type} [Field K] [CharP K 2] {ω : K}

@[expose] noncomputable def ySL (hω : ω ^ 2 + ω + 1 = 0) (z m : Fin 4) (hg : GoodPar z m)
    (i : Fin 2) : SpecialLinearGroup (Fin 3) K :=
  ⟨toMat ω (yM z m i), by rw [det_toMat hω, yM_det z m hg i]; rfl⟩

theorem coe_ySL (hω : ω ^ 2 + ω + 1 = 0) (z m : Fin 4) (hg : GoodPar z m) (i : Fin 2) :
    ((ySL hω z m hg i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      toMat ω (yM z m i) := rfl

theorem ySL_pow_seven (hω : ω ^ 2 + ω + 1 = 0) (z m : Fin 4) (hg : GoodPar z m) (i : Fin 2) :
    ySL hω z m hg i ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_ySL, ← toMat_mpow hω, meq_iff.1 (yM_pow7 z m hg i),
    toMat_mone, Matrix.SpecialLinearGroup.coe_one]

theorem toMat_u_comm_y (hω : ω ^ 2 + ω + 1 = 0) (z m : Fin 4) (hg : GoodPar z m) (i : Fin 2) :
    toMat ω (uM z m i) * toMat ω (yM z m i) = toMat ω (yM z m i) * toMat ω (uM z m i) := by
  rw [← toMat_mmul hω, ← toMat_mmul hω, meq_iff.1 (yM_comm z m hg i)]

theorem ev_fixed {σ : K ≃+* K} (hσω : σ ω = ω) (a : Fin 4) : σ (ev ω a) = ev ω a := by
  fin_cases a <;> simp [ev, hσω]

@[expose] def wordSL (a b : SpecialLinearGroup (Fin 3) K) (w : List Bool) :
    SpecialLinearGroup (Fin 3) K :=
  w.foldl (fun acc t => acc * (if t then b else a)) 1

theorem wordSL_mem {H : Subgroup (SpecialLinearGroup (Fin 3) K)}
    {a b : SpecialLinearGroup (Fin 3) K} (ha : a ∈ H) (hb : b ∈ H) (w : List Bool) :
    wordSL a b w ∈ H := by
  have key : ∀ (w : List Bool) (acc : SpecialLinearGroup (Fin 3) K), acc ∈ H →
      w.foldl (fun acc t => acc * (if t then b else a)) acc ∈ H := by
    intro w
    induction w with
    | nil => intro acc h; exact h
    | cons t w ih =>
      intro acc h
      refine ih _ (H.mul_mem h ?_)
      split_ifs
      exacts [hb, ha]
  exact key w 1 H.one_mem

theorem coe_wordSL (hω : ω ^ 2 + ω + 1 = 0) (a b : SpecialLinearGroup (Fin 3) K) (A B : M3)
    (ha : (a : Matrix (Fin 3) (Fin 3) K) = toMat ω A)
    (hb : (b : Matrix (Fin 3) (Fin 3) K) = toMat ω B) (w : List Bool) :
    ((wordSL a b w : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      toMat ω (evalW A B w) := by
  have key : ∀ (w : List Bool) (acc : SpecialLinearGroup (Fin 3) K) (accM : M3),
      (acc : Matrix (Fin 3) (Fin 3) K) = toMat ω accM →
      ((w.foldl (fun acc t => acc * (if t then b else a)) acc : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        toMat ω (w.foldl (fun acc t => mmul acc (if t then B else A)) accM) := by
    intro w
    induction w with
    | nil => intro acc accM h; exact h
    | cons t w ih =>
      intro acc accM h
      refine ih _ _ ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, h, toMat_mmul hω]
      split_ifs
      · rw [hb]
      · rw [ha]
  exact key w 1 mone (by rw [Matrix.SpecialLinearGroup.coe_one, toMat_mone])

theorem toMat_tvM (i j : Fin 3) (hij : i ≠ j) (a : Fin 4) :
    toMat ω (tvM i j a) =
      ((Matrix.SpecialLinearGroup.transvection hij (ev ω a) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext r c
  simp only [toMat_apply, tvM, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hrc : r = c
  · subst hrc
    have : ¬ (i = r ∧ j = r) := fun h => hij (h.1.trans h.2.symm)
    simp [this, ev]
  · by_cases hr : r = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := hr
      simp [hrc]
    · have : ¬ (i = r ∧ j = c) := fun h => hr ⟨h.1.symm, h.2.symm⟩
      simp [hrc, hr, this, ev]

theorem ne_zero_of_cube_root (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := fun h => by
  rw [h] at hω
  norm_num at hω

theorem ne_one_of_cube_root (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := fun h => by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  rw [h] at hω
  have : (1 : K) = 0 := by linear_combination hω - h2
  exact one_ne_zero this

theorem ev_injective (hω : ω ^ 2 + ω + 1 = 0) : Function.Injective (ev ω) := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have hω0 := ne_zero_of_cube_root hω
  have hω1 := ne_one_of_cube_root hω
  have hω10 : ω + 1 ≠ 0 := fun h => hω1 (by linear_combination h - h2)
  have hω11 : ω + 1 ≠ 1 := fun h => hω0 (by linear_combination h)
  have hωω : ω + 1 ≠ ω := fun h => one_ne_zero (by linear_combination h)
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [ev] at hab ⊢ <;>
    first
    | exact absurd hab hω0 | exact absurd hab.symm hω0
    | exact absurd hab hω1 | exact absurd hab.symm hω1
    | exact absurd hab hω10 | exact absurd hab.symm hω10
    | exact absurd hab hω11 | exact absurd hab.symm hω11
    | exact absurd hab hωω | exact absurd hab.symm hωω
    | exact one_ne_zero hab | exact one_ne_zero hab.symm

theorem ev_cube (hω : ω ^ 2 + ω + 1 = 0) (a : Fin 4) (ha : a ≠ 0) : ev ω a ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  fin_cases a
  · exact absurd rfl ha
  · simp [ev]
  · simpa [ev] using hω3
  · simp only [ev, Matrix.cons_val]
    show (ω + 1) ^ 3 = 1
    linear_combination ω * hω + (ω ^ 2 + ω) * h2

section Fixed

variable [Finite K] {σ : K ≃+* K}

theorem sigma3 (hσ : orderOf σ = 3) (x : K) : σ (σ (σ x)) = x := by
  have h := congrArg (fun τ : K ≃+* K => τ x)
    (show σ ^ 3 = 1 by rw [← hσ]; exact pow_orderOf_eq_one σ)
  simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] at h
  exact h

theorem card_fixSub (hK : Nat.card K = 64) (hσ : orderOf σ = 3) : Nat.card (fixSub σ) = 4 := by
  have h := CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf
    (K := K) (r := 2) (n := 6) (p := 3) Nat.prime_two (by norm_num) (by rw [hK]; norm_num) σ hσ
  have h2 := h.2
  norm_num at h2
  exact h2

theorem exists_ev_of_fixed (hK : Nat.card K = 64) (hσ : orderOf σ = 3)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) {c : K} (hc : σ c = c) : ∃ a : Fin 4, ev ω a = c := by
  let f : Fin 4 → fixSub σ := fun a => ⟨ev ω a, ev_fixed hσω a⟩
  have hinj : Function.Injective f := fun a b hab =>
    ev_injective hω (congrArg Subtype.val hab)
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [card_fixSub hK hσ, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨a, ha⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem exists_seventh_root (hK : Nat.card K = 64) : ∃ a : K, a ^ 7 = 1 ∧ a ≠ 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h : 7 ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 7 h
  refine ⟨(u : K), ?_, fun h1 => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    omega

theorem norm_eq_one_of_pow_seven (hK : Nat.card K = 64) (hσ : orderOf σ = 3)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) {a : K} (ha : a ^ 7 = 1) :
    a * σ a * σ (σ a) = 1 := by
  have hσ3 := sigma3 hσ
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  set n := a * σ a * σ (σ a) with hn
  have hn0 : n ≠ 0 := by
    have : σ a ≠ 0 := fun h => ha0 (σ.injective (by rw [h, map_zero]))
    have : σ (σ a) ≠ 0 := fun h => ‹σ a ≠ 0› (σ.injective (by rw [h, map_zero]))
    exact mul_ne_zero (mul_ne_zero ha0 ‹σ a ≠ 0›) this
  have hnfix : σ n = n := by
    rw [hn, map_mul, map_mul, hσ3]
    ring
  have hn7 : n ^ 7 = 1 := by
    have : n ^ 7 = a ^ 7 * σ (a ^ 7) * σ (σ (a ^ 7)) := by
      simp [hn, mul_pow, map_pow]
    rw [this, ha]
    simp
  obtain ⟨b, hb⟩ := exists_ev_of_fixed hK hσ hω hσω hnfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hn0 (by rw [← hb]; rfl)
  have hn3 : n ^ 3 = 1 := by rw [← hb]; exact ev_cube hω b hb0
  calc n = n * (n ^ 3) ^ 2 * 1 := by rw [hn3]; ring
    _ = n ^ 7 := by ring
    _ = 1 := hn7

theorem fieldAut_not_mem_D (h3 : 3 ∣ Nat.card K - 1) (hσ : orderOf σ = 3) :
    LinearFlag.fieldAut 3 K σ ∉ linearAutGroup 3 K := fun hD => by
  have := (l3FrameLinear h3).fld_inter σ hD
  rw [this] at hσ
  simp at hσ

theorem conjAut_fixes_proj {y : SpecialLinearGroup (Fin 3) K} {g : GL (Fin 3) K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) * y = y * g) :
    LinearFlag.conjAut 3 K g (LinearFlag.proj 3 K y) = LinearFlag.proj 3 K y := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem fieldAut_fixes_proj {y : SpecialLinearGroup (Fin 3) K}
    (h : ∀ i j, σ ((y : Matrix (Fin 3) (Fin 3) K) i j) = (y : Matrix (Fin 3) (Fin 3) K) i j) :
    LinearFlag.fieldAut 3 K σ (LinearFlag.proj 3 K y) = LinearFlag.proj 3 K y := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  exact h i j

theorem orderOf_proj_coprime {y : SpecialLinearGroup (Fin 3) K} (hy : y ^ 7 = 1) :
    Nat.Coprime (orderOf (LinearFlag.proj 3 K y)) 3 := by
  have hdvd : orderOf (LinearFlag.proj 3 K y) ∣ 7 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy, map_one])
  exact Nat.Coprime.coprime_dvd_left hdvd (by norm_num)

theorem proj_ySL_mem_Hgen (hω : ω ^ 2 + ω + 1 = 0) {z m : Fin 4} (hg : GoodPar z m) (i : Fin 2)
    (hσω : σ ω = ω) (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card K - 1)
    {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A)
    (gu : GL (Fin 3) K) (s : K) (hs : s ≠ 0)
    (hgu : (gu : Matrix (Fin 3) (Fin 3) K) = s • toMat ω (uM z m i))
    (hu : LinearFlag.conjAut 3 K gu ∈ A) :
    LinearFlag.proj 3 K (ySL hω z m hg i) ∈ Hgen A := by
  refine mem_Hgen_of_pair hAel hA27 hu hf ?_ ?_ ?_ ?_ ?_
  · intro h1
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff_scalar gu).1 h1
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 0) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      hgu, toMat_apply, uM_entry, Matrix.smul_apply, smul_eq_mul] at this
    exact hs (by simpa [ev] using this.symm)
  · intro hmem
    exact fieldAut_not_mem_D h3 hσ ((Subgroup.zpowers_le.2 (conjAut_mem_linearAutGroup gu)) hmem)
  · refine conjAut_fixes_proj ?_
    rw [hgu, coe_ySL, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    exact toMat_u_comm_y hω z m hg i
  · refine fieldAut_fixes_proj ?_
    intro r c
    rw [coe_ySL, toMat_apply]
    exact ev_fixed hσω _
  · exact orderOf_proj_coprime (ySL_pow_seven hω z m hg i)

@[expose] noncomputable def ydSL (σ : K ≃+* K) (a : K) (hN : a * σ a * σ (σ a) = 1) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![a, σ a, σ (σ a)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using hN⟩

theorem coe_ydSL (σ : K ≃+* K) (a : K) (hN : a * σ a * σ (σ a) = 1) :
    ((ydSL σ a hN : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![a, σ a, σ (σ a)] := rfl

theorem ydSL_pow_seven (σ : K ≃+* K) {a : K} (hN : a * σ a * σ (σ a) = 1) (ha : a ^ 7 = 1) :
    ydSL σ a hN ^ 7 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro r c
  have h := Matrix.SpecialLinearGroup.coe_pow (ydSL σ a hN) 7
  have h' : ((ydSL σ a hN ^ 7 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [h, coe_ydSL, Matrix.diagonal_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, ← map_pow, ha]
  rw [h']
  simp

theorem ydSL_not_rational (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {a : K} (ha7 : a ^ 7 = 1) (ha1 : a ≠ 1) (hN : a * σ a * σ (σ a) = 1) :
    ¬ ∃ c : K, c ≠ 0 ∧ ∀ i j, σ (c * ((Matrix.SpecialLinearGroup.toGL (ydSL σ a hN) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      c * ((Matrix.SpecialLinearGroup.toGL (ydSL σ a hN) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i j := by
  rintro ⟨c, hc0, hc⟩
  have hσ3 := sigma3 hσ
  have h0 := hc 0 0
  have h1 := hc 1 1
  have h2 := hc 2 2
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_ydSL, Matrix.diagonal_apply_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, map_mul, hσ3] at h0 h1 h2
  set s := σ c with hs
  set a1 := σ a with ha1d
  set a2 := σ a1 with ha2d
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha7
  have hs0 : s ≠ 0 := fun h => hc0 (σ.injective (by rw [← hs, h, map_zero]))
  have hs3 : s ^ 3 = c ^ 3 := by
    have : s ^ 3 * (a * a1 * a2) = c ^ 3 * (a * a1 * a2) := by
      linear_combination (s * a2 * (s * a)) * h0 + (c * a * (s * a)) * h1 + (c * a * (c * a1)) * h2
    rw [hN, mul_one, mul_one] at this
    exact this
  have ha13 : a1 ^ 3 = a ^ 3 := by
    have : c ^ 3 * a1 ^ 3 = c ^ 3 * a ^ 3 := by
      linear_combination (s ^ 2 * a1 ^ 2 + s * a1 * c * a + c ^ 2 * a ^ 2) * h0 - a1 ^ 3 * hs3
    exact mul_left_cancel₀ (pow_ne_zero 3 hc0) this
  have ha17 : a1 ^ 7 = 1 := by rw [ha1d, ← map_pow, ha7, map_one]
  have haa1 : a1 = a := by
    have : a1 * (a ^ 3) ^ 2 = a * (a ^ 3) ^ 2 := by
      calc a1 * (a ^ 3) ^ 2 = a1 * (a1 ^ 3) ^ 2 := by rw [ha13]
        _ = a1 ^ 7 := by ring
        _ = 1 := ha17
        _ = a ^ 7 := ha7.symm
        _ = a * (a ^ 3) ^ 2 := by ring
    exact mul_right_cancel₀ (pow_ne_zero 2 (pow_ne_zero 3 ha0)) this
  have hafix : σ a = a := haa1
  obtain ⟨b, hb⟩ := exists_ev_of_fixed hK hσ hω hσω hafix
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact ha0 (by rw [← hb]; rfl)
  have ha3 : a ^ 3 = 1 := by rw [← hb]; exact ev_cube hω b hb0
  apply ha1
  calc a = a * (a ^ 3) ^ 2 * 1 := by rw [ha3]; ring
    _ = a ^ 7 := by ring
    _ = 1 := ha7

theorem conjAut_fieldAut_fixes_proj {y : SpecialLinearGroup (Fin 3) K} {g : GL (Fin 3) K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K).map σ = y * g) :
    (LinearFlag.conjAut 3 K g * LinearFlag.fieldAut 3 K σ) (LinearFlag.proj 3 K y) =
      LinearFlag.proj 3 K y := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  show (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K).map σ *
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = y
  rw [h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem core_gen (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {z m : Fin 4} (hg : GoodPar z m)
    {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A) (gd gC : GL (Fin 3) K)
    (θ : K) (hθ : θ ≠ 0) (hgd : (gd : Matrix (Fin 3) (Fin 3) K) = θ • toMat ω (dM z))
    (hgC : (gC : Matrix (Fin 3) (Fin 3) K) = toMat ω (CM m))
    (hd : LinearFlag.conjAut 3 K gd ∈ A) (hC : LinearFlag.conjAut 3 K gC ∈ A) : GenP A := by
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; norm_num
  set H' : Subgroup (SpecialLinearGroup (Fin 3) K) := (Hgen A).comap (LinearFlag.proj 3 K) with hH'
  have hy0 : ySL hω z m hg 0 ∈ H' :=
    proj_ySL_mem_Hgen hω hg 0 hσω hσ h3 hAel hA27 hf gC 1 one_ne_zero
      (by rw [hgC, one_smul]; rfl) hC
  have hu1 : ((gC * gd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = θ • toMat ω (uM z m 1) := by
    rw [Units.val_mul, hgC, hgd, Matrix.mul_smul]
    congr 1
    exact (toMat_mmul hω (CM m) (dM z)).symm
  have hy1 : ySL hω z m hg 1 ∈ H' :=
    proj_ySL_mem_Hgen hω hg 1 hσω hσ h3 hAel hA27 hf (gC * gd) θ hθ hu1
      (by rw [map_mul]; exact A.mul_mem hC hd)
  have htv : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K), σ c = c →
      Matrix.SpecialLinearGroup.transvection hij c ∈ H' := by
    intro i j hij c hc
    obtain ⟨b, rfl⟩ := exists_ev_of_fixed hK hσ hω hσω hc
    obtain ⟨w, hw⟩ := exists_word z m hg i j hij b
    have : wordSL (ySL hω z m hg 0) (ySL hω z m hg 1) w =
        Matrix.SpecialLinearGroup.transvection hij (ev ω b) := by
      apply Subtype.ext
      rw [coe_wordSL hω _ _ (yM z m 0) (yM z m 1) rfl rfl w, hw, toMat_tvM i j hij b]
    rw [← this]
    exact wordSL_mem hy0 hy1 w
  have hfix : BGL.fixSL3 σ ≤ H' := by
    refine (fixSL3_le_closure_tv σ).trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨i, j, hij, c, hc, rfl⟩
    exact htv i j hij c hc
  obtain ⟨a, ha7, ha1⟩ := exists_seventh_root hK
  have hN := norm_eq_one_of_pow_seven hK hσ hω hσω ha7
  have hyd : ydSL σ a hN ∈ H' := by
    show LinearFlag.proj 3 K (ydSL σ a hN) ∈ Hgen A
    refine mem_Hgen_of_pair hAel hA27 hd (A.mul_mem hC hf) ?_ ?_ ?_ ?_ ?_
    · intro h1
      obtain ⟨c, hc⟩ := (conjAut_eq_one_iff_scalar gd).1 h1
      have e00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
      have e11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, hgd, toMat_apply, Matrix.smul_apply, smul_eq_mul] at e00 e11
      have hz1 : ev ω z = 1 := by
        have : θ * ev ω (dM z 1 1) = θ * ev ω (dM z 0 0) := e11.symm.trans e00
        simpa [dM, ev, hθ] using this
      rcases hg.1 with rfl | rfl
      · exact ne_one_of_cube_root hω (by simpa [ev] using hz1)
      · exact ne_zero_of_cube_root hω (by simpa [ev] using hz1)
    · intro hmem
      have h1 := (Subgroup.zpowers_le.2 (conjAut_mem_linearAutGroup gd)) hmem
      have h2 := (linearAutGroup 3 K).mul_mem
        ((linearAutGroup 3 K).inv_mem (conjAut_mem_linearAutGroup gC)) h1
      rw [inv_mul_cancel_left] at h2
      exact fieldAut_not_mem_D h3 hσ h2
    · refine conjAut_fixes_proj ?_
      rw [hgd, coe_ydSL, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      ext r c
      fin_cases r <;> fin_cases c <;>
        simp [toMat_apply, dM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, ev] <;>
        ring
    · refine conjAut_fieldAut_fixes_proj ?_
      rw [hgC, coe_ydSL]
      ext r c
      fin_cases r <;> fin_cases c <;>
        simp [toMat_apply, CM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, ev,
          Matrix.map_apply, sigma3 hσ] <;> try ring
    · exact orderOf_proj_coprime (ydSL_pow_seven σ hN ha7)
  have hjoin := BGL.sl3SubfieldJoin_holds K σ hσ (Matrix.SpecialLinearGroup.toGL (ydSL σ a hN))
    (ydSL_not_rational hK hσ hω hσω ha7 ha1 hN)
  have htop : ⊤ ≤ H' := by
    refine hjoin.trans (sup_le hfix ?_)
    rintro _ ⟨x, hx, rfl⟩
    rw [BGL.conjGL3_toGL]
    exact H'.mul_mem (H'.mul_mem hyd (hfix hx)) (H'.inv_mem hyd)
  intro x _
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K x
  exact htop (Subgroup.mem_top g)

end Fixed

end KLevel

end CFSG.HardMathSupport.Dickson.Sec6.Heis
