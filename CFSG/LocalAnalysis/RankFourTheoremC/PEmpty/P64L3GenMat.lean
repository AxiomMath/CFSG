module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64L3Gen

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Subgroup

abbrev SL3 (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 3) F

abbrev PSL3 (F : Type) [Field F] : Type := StatedProj (StatedSL 3 F)

@[expose] def utMat {F : Type} [Field F] (a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, b; 0, 1, c; 0, 0, 1]

@[expose] def e1Mat {F : Type} [Field F] (a c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, c; 0, 1, 0; 0, 0, 1]

@[expose] def e2Mat {F : Type} [Field F] (b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, c; 0, 1, b; 0, 0, 1]

theorem det_utMat {F : Type} [Field F] (a b c : F) : (utMat a b c).det = 1 := by
  simp [utMat, Matrix.det_fin_three]

theorem det_e1Mat {F : Type} [Field F] (a c : F) : (e1Mat a c).det = 1 := by
  simp [e1Mat, Matrix.det_fin_three]

theorem det_e2Mat {F : Type} [Field F] (b c : F) : (e2Mat b c).det = 1 := by
  simp [e2Mat, Matrix.det_fin_three]

@[expose] def utSL {F : Type} [Field F] (a b c : F) : SL3 F := ⟨utMat a b c, det_utMat a b c⟩

@[expose] def e1SL {F : Type} [Field F] (a c : F) : SL3 F := ⟨e1Mat a c, det_e1Mat a c⟩

@[expose] def e2SL {F : Type} [Field F] (b c : F) : SL3 F := ⟨e2Mat b c, det_e2Mat b c⟩

theorem utMat_mul {F : Type} [Field F] (a b c a' b' c' : F) :
    utMat a b c * utMat a' b' c' = utMat (a + a') (b + b' + a * c') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem utMat_mul_inv {F : Type} [Field F] (a b c : F) :
    utMat a b c * utMat (-a) (a * c - b) (-c) = 1 := by
  rw [utMat_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utMat] <;> ring

theorem e1SL_mul {F : Type} [Field F] (a c a' c' : F) :
    e1SL a c * e1SL a' c' = e1SL (a + a') (c + c') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show e1Mat a c * e1Mat a' c' = e1Mat (a + a') (c + c')
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1Mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem e1SL_zero {F : Type} [Field F] : e1SL (0 : F) 0 = 1 := by
  apply Subtype.ext
  show e1Mat 0 0 = 1
  simp [e1Mat, Matrix.one_fin_three]

theorem e2SL_mul {F : Type} [Field F] (b c b' c' : F) :
    e2SL b c * e2SL b' c' = e2SL (b + b') (c + c') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show e2Mat b c * e2Mat b' c' = e2Mat (b + b') (c + c')
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2Mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem e2SL_zero {F : Type} [Field F] : e2SL (0 : F) 0 = 1 := by
  apply Subtype.ext
  show e2Mat 0 0 = 1
  simp [e2Mat, Matrix.one_fin_three]

@[expose] def uniT (F : Type) [Field F] : Subgroup (SL3 F) where
  carrier := {m | ∃ a b c : F, (m : Matrix (Fin 3) (Fin 3) F) = utMat a b c}
  mul_mem' := by
    rintro m n ⟨a, b, c, hm⟩ ⟨a', b', c', hn⟩
    exact ⟨_, _, _, by rw [Matrix.SpecialLinearGroup.coe_mul, hm, hn, utMat_mul]⟩
  one_mem' := ⟨0, 0, 0, by simp [utMat, Matrix.one_fin_three]⟩
  inv_mem' := by
    rintro m ⟨a, b, c, hm⟩
    refine ⟨-a, a * c - b, -c, ?_⟩
    have key : m⁻¹ = utSL (-a) (a * c - b) (-c) := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hm]
      exact utMat_mul_inv a b c
    rw [key]
    rfl

theorem card_uniT {F : Type} [Field F] [Finite F] : Nat.card (uniT F) = Nat.card F ^ 3 := by
  let f : F × F × F → uniT F := fun t =>
    ⟨utSL t.1 t.2.1 t.2.2, ⟨t.1, t.2.1, t.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t hst => ?_, fun u => ?_⟩
    · obtain ⟨a, b, c⟩ := s
      obtain ⟨a', b', c'⟩ := t
      have h1 := congrArg (fun u : uniT F => ((u : SL3 F) : Matrix (Fin 3) (Fin 3) F)) hst
      have e1 := congrFun (congrFun h1 0) 1
      have e2 := congrFun (congrFun h1 0) 2
      have e3 := congrFun (congrFun h1 1) 2
      simp [f, utSL, utMat] at e1 e2 e3
      simp [e1, e2, e3]
    · obtain ⟨m, hm⟩ := u
      obtain ⟨a, b, c, h⟩ := hm
      exact ⟨(a, b, c), Subtype.ext (Subtype.ext h.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod]
  ring

@[expose] noncomputable def phi3 (F : Type) [Field F] : SL3 F →* PSL3 F :=
  (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))).comp
    (specialLinearGroupEquivStatedSL 3 F).toMonoidHom

theorem phi3_surjective (F : Type) [Field F] : Function.Surjective (phi3 F) := by
  intro g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨m, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective h
  exact ⟨m, rfl⟩

theorem phi3_offdiag {F : Type} [Field F] {m : SL3 F} (h : phi3 F m = 1) {i j : Fin 3}
    (hij : i ≠ j) : (m : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have h1 : specialLinearGroupEquivStatedSL 3 F m ∈
      (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) :=
    (QuotientGroup.eq_one_iff _).1 h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) i j) hu
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij, specialLinearGroupEquivStatedSL_coe] at this
  exact this.symm

@[expose] noncomputable def e1Hom (F : Type) [Field F] : Multiplicative (F × F) →* SL3 F where
  toFun t := e1SL (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2
  map_one' := by simpa using (e1SL_zero (F := F))
  map_mul' x y := by simp [e1SL_mul]

@[expose] noncomputable def e2Hom (F : Type) [Field F] : Multiplicative (F × F) →* SL3 F where
  toFun t := e2SL (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2
  map_one' := by simpa using (e2SL_zero (F := F))
  map_mul' x y := by simp [e2SL_mul]

theorem injective_phi3_e1 (F : Type) [Field F] :
    Function.Injective ((phi3 F).comp (e1Hom F)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h0 : phi3 F (e1SL (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2) = 1 := ht
  have ha := phi3_offdiag h0 (i := 0) (j := 1) (by decide)
  have hc := phi3_offdiag h0 (i := 0) (j := 2) (by decide)
  simp [e1SL, e1Mat] at ha hc
  exact toAdd_eq_zero.1 (Prod.ext ha hc)

theorem injective_phi3_e2 (F : Type) [Field F] :
    Function.Injective ((phi3 F).comp (e2Hom F)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h0 : phi3 F (e2SL (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2) = 1 := ht
  have hb := phi3_offdiag h0 (i := 1) (j := 2) (by decide)
  have hc := phi3_offdiag h0 (i := 0) (j := 2) (by decide)
  simp [e2SL, e2Mat] at hb hc
  exact toAdd_eq_zero.1 (Prod.ext hb hc)

@[expose] noncomputable def S1 (F : Type) [Field F] : Subgroup (PSL3 F) :=
  ((phi3 F).comp (e1Hom F)).range

@[expose] noncomputable def S2 (F : Type) [Field F] : Subgroup (PSL3 F) :=
  ((phi3 F).comp (e2Hom F)).range

theorem natCast_eq_zero_of_card {F : Type} [Field F] [Finite F] {p : ℕ} (hF : Nat.card F = p) :
    (p : F) = 0 := by
  haveI := Fintype.ofFinite F
  rw [← hF, Nat.card_eq_fintype_card]
  exact FiniteField.cast_card_eq_zero F

theorem two_le_pRank_S1 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) : 2 ≤ CFSG.Open.pRank p (S1 F) := by
  have hp0 : (p : F) = 0 := natCast_eq_zero_of_card hF
  haveI : Finite (PSL3 F) := Finite.of_surjective _ (phi3_surjective F)
  have hcard : Nat.card (Multiplicative (F × F)) = p ^ 2 := by
    rw [← Nat.card_congr (Multiplicative.ofAdd : F × F ≃ Multiplicative (F × F)),
      Nat.card_prod, hF, sq]
  have hpow : ∀ t : Multiplicative (F × F), t ^ p = 1 := by
    intro t
    apply toAdd_eq_zero.1
    rw [toAdd_pow]
    apply Prod.ext <;> simp [hp0, nsmul_eq_mul]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b) hpow hcard
    ((phi3 F).comp (e1Hom F)) (injective_phi3_e1 F) le_rfl

theorem two_le_pRank_S2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) : 2 ≤ CFSG.Open.pRank p (S2 F) := by
  have hp0 : (p : F) = 0 := natCast_eq_zero_of_card hF
  haveI : Finite (PSL3 F) := Finite.of_surjective _ (phi3_surjective F)
  have hcard : Nat.card (Multiplicative (F × F)) = p ^ 2 := by
    rw [← Nat.card_congr (Multiplicative.ofAdd : F × F ≃ Multiplicative (F × F)),
      Nat.card_prod, hF, sq]
  have hpow : ∀ t : Multiplicative (F × F), t ^ p = 1 := by
    intro t
    apply toAdd_eq_zero.1
    rw [toAdd_pow]
    apply Prod.ext <;> simp [hp0, nsmul_eq_mul]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b) hpow hcard
    ((phi3 F).comp (e2Hom F)) (injective_phi3_e2 F) le_rfl

theorem mul_inv_matrix {F : Type} [Field F] (x : SL3 F) :
    (x : Matrix (Fin 3) (Fin 3) F) * ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem inv_P1 {F : Type} [Field F] {x : SL3 F} (h1 : (x : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_three]
  simp [h1, h2]

theorem inv_P2 {F : Type} [Field F] {x : SL3 F} (h1 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_three]
  simp [h1, h2]

theorem e1_conj_matrix {F : Type} [Field F] (X Y : Matrix (Fin 3) (Fin 3) F) (hXY : X * Y = 1)
    (hX1 : X 1 0 = 0) (hX2 : X 2 0 = 0) (hY1 : Y 1 0 = 0) (hY2 : Y 2 0 = 0) (a c : F) :
    X * e1Mat a c * Y =
      e1Mat (X 0 0 * (a * Y 1 1 + c * Y 2 1)) (X 0 0 * (a * Y 1 2 + c * Y 2 2)) := by
  have key : ∀ i j, (X * e1Mat a c * Y) i j = (X * Y) i j + X i 0 * (a * Y 1 j + c * Y 2 j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, e1Mat] <;> ring
  ext i j
  rw [key, hXY]
  fin_cases i <;> fin_cases j <;> simp [e1Mat, hX1, hX2, hY1, hY2]

theorem e2_conj_matrix {F : Type} [Field F] (X Y : Matrix (Fin 3) (Fin 3) F) (hXY : X * Y = 1)
    (hX1 : X 2 0 = 0) (hX2 : X 2 1 = 0) (hY1 : Y 2 0 = 0) (hY2 : Y 2 1 = 0) (b c : F) :
    X * e2Mat b c * Y =
      e2Mat ((b * X 1 1 + c * X 1 0) * Y 2 2) ((b * X 0 1 + c * X 0 0) * Y 2 2) := by
  have key : ∀ i j, (X * e2Mat b c * Y) i j = (X * Y) i j + (b * X i 1 + c * X i 0) * Y 2 j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, e2Mat] <;> ring
  ext i j
  rw [key, hXY]
  fin_cases i <;> fin_cases j <;> simp [e2Mat, hX1, hX2, hY1, hY2]

theorem conj_e1_SL {F : Type} [Field F] {x : SL3 F}
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (a c : F) : ∃ a' c' : F, x * e1SL a c * x⁻¹ = e1SL a' c' := by
  obtain ⟨hy1, hy2⟩ := inv_P1 h1 h2
  refine ⟨(x : Matrix (Fin 3) (Fin 3) F) 0 0 *
      (a * ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 1 +
        c * ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1),
    (x : Matrix (Fin 3) (Fin 3) F) 0 0 *
      (a * ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 2 +
        c * ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2), ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact e1_conj_matrix _ _ (mul_inv_matrix x) h1 h2 hy1 hy2 a c

theorem conj_e2_SL {F : Type} [Field F] {x : SL3 F}
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (b c : F) : ∃ b' c' : F, x * e2SL b c * x⁻¹ = e2SL b' c' := by
  obtain ⟨hy1, hy2⟩ := inv_P2 h1 h2
  refine ⟨(b * (x : Matrix (Fin 3) (Fin 3) F) 1 1 + c * (x : Matrix (Fin 3) (Fin 3) F) 1 0) *
      ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2,
    (b * (x : Matrix (Fin 3) (Fin 3) F) 0 1 + c * (x : Matrix (Fin 3) (Fin 3) F) 0 0) *
      ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact e2_conj_matrix _ _ (mul_inv_matrix x) h1 h2 hy1 hy2 b c

theorem phi3_conj_mem_S1 {F : Type} [Field F] {x : SL3 F}
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    {g : PSL3 F} (hg : g ∈ S1 F) : phi3 F x * g * (phi3 F x)⁻¹ ∈ S1 F := by
  have hg' : g ∈ ((phi3 F).comp (e1Hom F)).range := hg
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hg'
  obtain ⟨a', c', hc⟩ := conj_e1_SL h1 h2 (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2
  refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (a', c'), ?_⟩
  change phi3 F (e1SL a' c') = phi3 F x * phi3 F (e1SL (Multiplicative.toAdd t).1
    (Multiplicative.toAdd t).2) * (phi3 F x)⁻¹
  have e : phi3 F x * phi3 F (e1SL (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2) *
      (phi3 F x)⁻¹ = phi3 F (x * e1SL (Multiplicative.toAdd t).1
        (Multiplicative.toAdd t).2 * x⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [e, hc]

theorem phi3_conj_mem_S2 {F : Type} [Field F] {x : SL3 F}
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    {g : PSL3 F} (hg : g ∈ S2 F) : phi3 F x * g * (phi3 F x)⁻¹ ∈ S2 F := by
  have hg' : g ∈ ((phi3 F).comp (e2Hom F)).range := hg
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hg'
  obtain ⟨b', c', hc⟩ := conj_e2_SL h1 h2 (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2
  refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (b', c'), ?_⟩
  change phi3 F (e2SL b' c') = phi3 F x * phi3 F (e2SL (Multiplicative.toAdd t).1
    (Multiplicative.toAdd t).2) * (phi3 F x)⁻¹
  have e : phi3 F x * phi3 F (e2SL (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2) *
      (phi3 F x)⁻¹ = phi3 F (x * e2SL (Multiplicative.toAdd t).1
        (Multiplicative.toAdd t).2 * x⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [e, hc]

theorem phi3_mem_normalizer_S1 {F : Type} [Field F] {x : SL3 F}
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    phi3 F x ∈ normalizer ((S1 F : Subgroup (PSL3 F)) : Set (PSL3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => phi3_conj_mem_S1 h1 h2 hg, fun hg => ?_⟩
  obtain ⟨h1', h2'⟩ := inv_P1 h1 h2
  have h := phi3_conj_mem_S1 h1' h2' hg
  have e : phi3 F x⁻¹ * (phi3 F x * g * (phi3 F x)⁻¹) * (phi3 F x⁻¹)⁻¹ = g := by
    rw [map_inv]
    group
  rw [e] at h
  exact h

theorem phi3_mem_normalizer_S2 {F : Type} [Field F] {x : SL3 F}
    (h1 : (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h2 : (x : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    phi3 F x ∈ normalizer ((S2 F : Subgroup (PSL3 F)) : Set (PSL3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => phi3_conj_mem_S2 h1 h2 hg, fun hg => ?_⟩
  obtain ⟨h1', h2'⟩ := inv_P2 h1 h2
  have h := phi3_conj_mem_S2 h1' h2' hg
  have e : phi3 F x⁻¹ * (phi3 F x * g * (phi3 F x)⁻¹) * (phi3 F x⁻¹)⁻¹ = g := by
    rw [map_inv]
    group
  rw [e] at h
  exact h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64L3Gen
