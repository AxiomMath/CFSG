module

public import CFSG.LieType.SeitzGeneration.QuasiHigh2Linear
public import CFSG.LieType.SeitzGeneration.HeisTorusGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiagField

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh3

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartOne.CTP (slSub mem_slSub)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

section Lift

variable {G P : Type*} [Group G] [Group P]

@[expose] def hyperLiftSet (p : ℕ) (E : Subgroup (MulAut G)) : Set G :=
  {s | ∃ F ≤ E, F.relIndex E = p ∧
    (((∃ m : ℕ, ¬ p ∣ m ∧ s ^ m = 1) ∧ s ∈ fixedPoints F) ∨
      ∃ x ∈ fixedPoints F, ∃ y ∈ fixedPoints F, s = ⁅x, y⁆)}

theorem mem_hyperLiftSet_of_pow {p : ℕ} {E F : Subgroup (MulAut G)} (hFE : F ≤ E)
    (hF : F.relIndex E = p) {s : G} {m : ℕ} (hm : ¬ p ∣ m) (hsm : s ^ m = 1)
    (hs : s ∈ fixedPoints F) : s ∈ hyperLiftSet p E :=
  ⟨F, hFE, hF, Or.inl ⟨⟨m, hm, hsm⟩, hs⟩⟩

theorem commutator_mem_hyperLiftSet {p : ℕ} {E F : Subgroup (MulAut G)} (hFE : F ≤ E)
    (hF : F.relIndex E = p) {x y : G} (hx : x ∈ fixedPoints F) (hy : y ∈ fixedPoints F) :
    ⁅x, y⁆ ∈ hyperLiftSet p E :=
  ⟨F, hFE, hF, Or.inr ⟨x, hx, y, hy, rfl⟩⟩

theorem image_hyperLiftSet_subset (θ : G ≃* P) (p : ℕ) (E : Subgroup (MulAut G)) :
    θ '' hyperLiftSet p E ⊆ hyperLiftSet p (E.map (MulAut.congr θ).toMonoidHom) := by
  rintro _ ⟨s, ⟨F, hFE, hFp, hs⟩, rfl⟩
  have hfix : ∀ x ∈ fixedPoints F,
      θ x ∈ fixedPoints (F.map (MulAut.congr θ).toMonoidHom) := by
    intro x hx
    rintro _ ⟨φ, hφ, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [hx φ hφ]
  refine ⟨F.map (MulAut.congr θ).toMonoidHom, Subgroup.map_mono hFE, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective F E (MulAut.congr θ).injective, hFp]
  · rcases hs with ⟨⟨m, hm, hsm⟩, hsF⟩ | ⟨x, hx, y, hy, rfl⟩
    · exact Or.inl ⟨⟨m, hm, by rw [← map_pow, hsm, map_one]⟩, hfix s hsF⟩
    · exact Or.inr ⟨θ x, hfix x hx, θ y, hfix y hy, map_commutatorElement θ x y⟩

theorem map_closure_hyperLiftSet_le (θ : G ≃* P) (p : ℕ) (E : Subgroup (MulAut G)) :
    (Subgroup.closure (hyperLiftSet p E)).map θ.toMonoidHom ≤
      Subgroup.closure (hyperLiftSet p (E.map (MulAut.congr θ).toMonoidHom)) := by
  rw [MonoidHom.map_closure]
  exact Subgroup.closure_mono (by
    simpa only [MulEquiv.coe_toMonoidHom] using image_hyperLiftSet_subset θ p E)

theorem map_congr_symm_map_congr (θ : G ≃* P) (E : Subgroup (MulAut G)) :
    (E.map (MulAut.congr θ).toMonoidHom).map (MulAut.congr θ.symm).toMonoidHom = E := by
  rw [Subgroup.map_map]
  have h : (MulAut.congr θ.symm).toMonoidHom.comp (MulAut.congr θ).toMonoidHom =
      MonoidHom.id (MulAut G) := by
    ext φ x
    simp [MulAut.congr_apply]
  rw [h, Subgroup.map_id]

theorem closure_hyperLiftSet_eq_top_of_congr (θ : G ≃* P) {p : ℕ} {E : Subgroup (MulAut G)}
    (h : Subgroup.closure (hyperLiftSet p (E.map (MulAut.congr θ).toMonoidHom)) = ⊤) :
    Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  have h1 := map_closure_hyperLiftSet_le θ.symm p (E.map (MulAut.congr θ).toMonoidHom)
  rw [map_congr_symm_map_congr, h, Subgroup.map_top_of_surjective _ θ.symm.surjective] at h1
  exact top_le_iff.1 h1

theorem seitzHyperGamma_eq_top_of_closure_hyperLiftSet {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} [Fact p.Prime] {E : Subgroup (MulAut K)}
    (hE : IsPGroup p E)
    (h : Subgroup.closure (hyperLiftSet p (E.map (quotientCenterAut' K))) = ⊤) :
    seitzHyperGamma p E = ⊤ := by
  have hinj := quotientCenterAut'_injective hperf
  apply eq_top_of_sup_center_eq_top hperf
  have hgen := closure_sup_center_eq_top_of_image (K := K) (T := (seitzHyperGamma p E : Set K))
  rw [Subgroup.closure_eq] at hgen
  refine hgen ?_
  rw [← h, Subgroup.closure_le]
  rintro s ⟨F₀, hF₀, hrel, hs⟩
  set F : Subgroup (MulAut K) := F₀.comap (quotientCenterAut' K) ⊓ E with hFdef
  have hmap : F.map (quotientCenterAut' K) = F₀ := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hF₀ hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hFE : F ≤ E := inf_le_right
  have hFp : F.relIndex E = p := by
    rw [← Subgroup.relIndex_map_map_of_injective F E hinj, hmap, hrel]
  have hFfix : fixedPoints F ≤ seitzHyperGamma p E :=
    le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hFp⟩ le_rfl
  have hq : ∀ f ∈ F, ∀ t ∈ fixedPoints F₀, quotAut f t = t := by
    intro f hf t ht
    rw [quotAut_eq_quotientCenterAut_model]
    exact ht _ (hmap ▸ Subgroup.mem_map_of_mem _ hf)
  refine Subgroup.subset_closure ?_
  rcases hs with ⟨⟨m, hm, hsm⟩, hsF⟩ | ⟨xb, hxb, yb, hyb, rfl⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨y, hxy, hy⟩ := exists_fixed_mul_center (hE.to_le hFE) (x := x)
      (fun f hf => by
        have h1 := hq f hf _ hsF
        rw [quotAut_mk] at h1
        exact QuotientGroup.eq.1 h1.symm)
      (Or.inr ⟨m, hm, by rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hsm]⟩)
    exact ⟨y, hFfix hy, (QuotientGroup.eq.2 hxy).symm⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    refine ⟨⁅x, y⁆, hFfix fun f hf =>
      apply_commutatorElement_of_fixed (hq f hf _ hxb) (hq f hf _ hyb), ?_⟩
    rw [map_commutatorElement]
    rfl

theorem seitzHyperGamma_eq_top_of_closure_hyperLiftSet_model {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} [Fact p.Prime] {E : Subgroup (MulAut K)}
    (hE : IsPGroup p E) (θ : K ⧸ Subgroup.center K ≃* P)
    (h : Subgroup.closure (hyperLiftSet p (E.map (modelAut θ))) = ⊤) :
    seitzHyperGamma p E = ⊤ :=
  seitzHyperGamma_eq_top_of_closure_hyperLiftSet hperf hE
    (closure_hyperLiftSet_eq_top_of_congr θ (by rwa [Subgroup.map_map]))

end Lift

section Arith

theorem exists_prime_dvd_pow_sub_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : p ∣ q - 1) :
    p * (q - 1) ∣ q ^ p - 1 ∧ ∃ r : ℕ, r.Prime ∧ r ∣ q ^ p - 1 ∧ ¬ r ∣ q - 1 ∧ r ≠ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set m := ∑ i ∈ Finset.range p, q ^ i with hm
  have hmul : m * (q - 1) = q ^ p - 1 := geom_sum_mul_of_one_le (by omega) p
  have hmod : ∀ r : ℕ, r ∣ q - 1 → (m : ZMod r) = p := by
    intro r hr
    have h1 : (q : ZMod r) = 1 := by
      have h0 : ((q - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hr
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero] at h0
      exact h0
    rw [hm]
    push_cast
    rw [h1]
    simp
  have hpm : p ∣ m := by
    have h1 := hmod p hpq
    rw [ZMod.natCast_self] at h1
    exact (ZMod.natCast_eq_zero_iff _ _).1 h1
  refine ⟨?_, ?_⟩
  · rw [← hmul]
    exact Nat.mul_dvd_mul_right hpm _
  have hq1 : q - 1 ≠ 0 := by omega
  have hpm_lt : p < m := by
    have h1 : ∑ _i ∈ Finset.range p, 1 < m := by
      rw [hm]
      refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ (by omega)) ⟨1, ?_, ?_⟩
      · rw [Finset.mem_range]
        exact hp.one_lt
      · rw [pow_one]
        omega
    simpa using h1
  have hm0 : m ≠ 0 := by omega
  have hpq0 : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ q - (q - 1) := Nat.dvd_sub h hpq
    rw [show q - (q - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hval : padicValNat p (q ^ p - 1) = padicValNat p (q - 1) + 1 := by
    have h1 := padicValNat.pow_sub_pow (x := q) (y := 1) (p := p) (hp.odd_of_ne_two hp2)
      (by omega) (by simpa using hpq) hpq0 (n := p) hp.ne_zero
    simpa [padicValNat_self] using h1
  have hvm : padicValNat p m = 1 := by
    rw [← hmul, padicValNat.mul hm0 hq1] at hval
    omega
  obtain ⟨m', hm'⟩ := hpm
  have hpm' : ¬ p ∣ m' := by
    rintro ⟨m'', rfl⟩
    have h1 : p ^ 2 ∣ m := ⟨m'', by rw [hm']; ring⟩
    have h2 := (padicValNat_dvd_iff_le hm0).1 h1
    omega
  have hm'1 : m' ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm'
    omega
  have hm'm : m' ∣ q ^ p - 1 := by
    rw [← hmul, hm']
    exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  refine ⟨m'.minFac, Nat.minFac_prime hm'1, (Nat.minFac_dvd m').trans hm'm, ?_, ?_⟩
  · intro hr
    have h1 := hmod _ hr
    have h2 : (m : ZMod m'.minFac) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, hm']
      exact Dvd.dvd.mul_left (Nat.minFac_dvd m') _
    rw [h2, eq_comm, ZMod.natCast_eq_zero_iff] at h1
    have h3 : m'.minFac = p := (Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hm'1) hp).1 h1
    exact hpm' (h3 ▸ Nat.minFac_dvd m')
  · intro h
    exact hpm' (h ▸ Nat.minFac_dvd m')

end Arith

section Std

variable {F : Type} [Field F]

@[expose] def shiftSL (F : Type) [Field F] {p : ℕ} (hp : Odd p) :
    SpecialLinearGroup (Fin p) F :=
  ⟨heisShiftMat F p, det_heisShiftMat F hp⟩

theorem coe_shiftSL {p : ℕ} (hp : Odd p) :
    ((shiftSL F hp : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      heisShiftMat F p := rfl

@[expose] def diagSL {p : ℕ} {ζ : F} (hζ : ζ ^ p = 1) (hp : Odd p) :
    SpecialLinearGroup (Fin p) F :=
  ⟨heisDiagMat ζ, det_heisDiagMat hζ hp⟩

theorem coe_diagSL {p : ℕ} {ζ : F} (hζ : ζ ^ p = 1) (hp : Odd p) :
    ((diagSL hζ hp : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      heisDiagMat ζ := rfl

theorem sl_ext {n : ℕ} {A B : SpecialLinearGroup (Fin n) F}
    (h : (A : Matrix (Fin n) (Fin n) F) = B) : A = B := Subtype.ext h

theorem conjAut_toGL_proj {n : ℕ} (g h : SpecialLinearGroup (Fin n) F) :
    conjAut n F (Matrix.SpecialLinearGroup.toGL g) (proj n F h) = proj n F (g * h * g⁻¹) := by
  rw [conjAut_proj]
  congr 1
  apply sl_ext
  rw [coe_slConjugation, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem proj_eq_of_coe_eq_smul {n : ℕ} {A B : SpecialLinearGroup (Fin n) F} {c : F}
    (hc0 : c ≠ 0) (hc : c ^ n = 1)
    (h : (B : Matrix (Fin n) (Fin n) F) = c • (A : Matrix (Fin n) (Fin n) F)) :
    proj n F B = proj n F A := by
  have hu : (Units.mk0 c hc0) ^ n = 1 := Units.ext (by simpa using hc)
  have hB : B = scalarElement (Units.mk0 c hc0) hu * A := by
    apply sl_ext
    rw [h, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  rw [hB, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars _ hu), one_mul]

theorem map_shiftSL (f : F →+* F) {p : ℕ} (hp : Odd p) :
    Matrix.SpecialLinearGroup.map f (shiftSL F hp) = shiftSL F hp := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_shiftSL]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, heisShiftMat_entry]
  split_ifs <;> simp

theorem diag_mul_comm {n : ℕ} {A B : SpecialLinearGroup (Fin n) F} {a b : Fin n → F}
    (hA : (A : Matrix (Fin n) (Fin n) F) = diagonal a)
    (hB : (B : Matrix (Fin n) (Fin n) F) = diagonal b) : A * B = B * A := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hA, hB, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem conjAut_toGL_proj_of_comm {n : ℕ} {g h : SpecialLinearGroup (Fin n) F}
    (hgh : g * h = h * g) :
    conjAut n F (Matrix.SpecialLinearGroup.toGL g) (proj n F h) = proj n F h := by
  rw [conjAut_toGL_proj, hgh, mul_inv_cancel_right]

theorem three_le_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  rcases hodd with ⟨k, rfl⟩
  rcases (show k = 0 ∨ 1 ≤ k by omega) with rfl | hk
  · exact absurd hp (by norm_num)
  · omega

theorem conjAut_diagSL_ne_one [Finite F] {p : ℕ} (hp : p.Prime) (hodd : Odd p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) :
    conjAut p F (Matrix.SpecialLinearGroup.toGL (diagSL hζ.pow_eq_one hodd)) ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff
    (three_le_of_odd_prime hp hodd) _).1 h
  have h0 := congrArg (fun A : GL (Fin p) F => (A : Matrix (Fin p) (Fin p) F)
    ⟨0, hp.pos⟩ ⟨0, hp.pos⟩) hu
  have h1 := congrArg (fun A : GL (Fin p) F => (A : Matrix (Fin p) (Fin p) F)
    ⟨1, hp.one_lt⟩ ⟨1, hp.one_lt⟩) hu
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_diagSL, heisDiagMat,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h0 h1
  simp only [pow_zero] at h0
  simp only [pow_one] at h1
  exact hζ.ne_one hp.one_lt (h1.symm.trans h0)

theorem fieldAut_not_mem_linearAutGroup {n : ℕ} {σ : F ≃+* F}
    (hσout : ∀ B : GL (Fin n) F, fieldAut n F σ ≠ conjAut n F B) :
    fieldAut n F σ ∉ linearAutGroup n F := by
  intro h
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 h
  exact hσout A hA.symm

theorem proj_diag_mem_closure_hyperLiftSet [Finite F] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {E : Subgroup (MulAut (projectiveSL p F))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 3) {σ : F ≃+* F}
    (hσout : ∀ B : GL (Fin p) F, fieldAut p F σ ≠ conjAut p F B) (hσE : fieldAut p F σ ∈ E)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hD : conjAut p F (Matrix.SpecialLinearGroup.toGL (diagSL hζ.pow_eq_one hodd)) ∈ E)
    (hroot : ∀ b : F, b ≠ 0 → σ b = b → ∃ c : F, c ^ p = b)
    {g : SpecialLinearGroup (Fin p) F} {s : Fin p → F}
    (hg : (g : Matrix (Fin p) (Fin p) F) = diagonal s) (hs : ∀ i, σ (s i) = s i) :
    proj p F g ∈ Subgroup.closure (hyperLiftSet p E) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (MulAut (projectiveSL p F)) := MulEquiv.finite_left
  set S := shiftSL F hodd with hSdef
  set D := diagSL hζ.pow_eq_one hodd with hDdef
  have hdet : ∏ i, s i = 1 := by
    have h1 := g.2
    rw [hg, det_diagonal] at h1
    exact h1
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i h0
    have h1 : ∏ j, s j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at h1
    exact one_ne_zero h1
  set s' : ℕ → F := fun j => if h : j < p then s ⟨j, h⟩ else 1 with hs'def
  have hs'σ : ∀ j, σ (s' j) = s' j := by
    intro j
    simp only [hs'def]
    split_ifs with h
    · exact hs _
    · exact map_one σ
  have hs'0 : ∀ j, s' j ≠ 0 := by
    intro j
    simp only [hs'def]
    split_ifs with h
    · exact hs0 _
    · exact one_ne_zero
  have hs'i : ∀ i : Fin p, s' i = s i := fun i => by simp [hs'def, i.isLt]
  set d : Fin p → F := fun i => ∏ j ∈ Finset.range i, (s' j)⁻¹ with hddef
  have hdσ : ∀ i, σ (d i) = d i := fun i => by
    simp only [hddef, map_prod, map_inv₀, hs'σ]
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (hs'0 j)
  have hdrel : ∀ i : Fin p, d i = s i * d (finRotate p i) := by
    intro i
    by_cases hi : (i : ℕ) + 1 < p
    · have h1 : ((finRotate p i : Fin p) : ℕ) = (i : ℕ) + 1 := by
        rw [finRotate_val_mod, Nat.mod_eq_of_lt hi]
      simp only [hddef, h1, Finset.prod_range_succ, hs'i]
      field_simp [hs0 i]
    · have hip : (i : ℕ) + 1 = p := by have := i.isLt; omega
      have h1 : ((finRotate p i : Fin p) : ℕ) = 0 := by
        rw [finRotate_val_mod, hip, Nat.mod_self]
      have h2 : ∏ j ∈ Finset.range p, s' j = 1 := by
        rw [← Fin.prod_univ_eq_prod_range]
        simpa [hs'i] using hdet
      rw [← hip, Finset.prod_range_succ, hs'i] at h2
      have h3 : d (finRotate p i) = 1 := by
        show ∏ j ∈ Finset.range ((finRotate p i : Fin p) : ℕ), (s' j)⁻¹ = 1
        rw [h1, Finset.prod_range_zero]
      rw [h3, mul_one]
      show ∏ j ∈ Finset.range (i : ℕ), (s' j)⁻¹ = s i
      rw [Finset.prod_inv_distrib]
      exact inv_eq_of_mul_eq_one_right h2
  have hP0 : ∏ i, d i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd0 i
  obtain ⟨c, hcp⟩ := hroot (∏ i, d i)⁻¹ (inv_ne_zero hP0) (by
    rw [map_inv₀, map_prod]
    simp only [hdσ])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact inv_ne_zero hP0 hcp.symm
  let t : SpecialLinearGroup (Fin p) F := ⟨diagonal fun i => c * d i, by
    rw [det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hcp, inv_mul_cancel₀ hP0]⟩
  have htcoe : (t : Matrix (Fin p) (Fin p) F) = diagonal fun i => c * d i := rfl
  have hcomm : t * S = g * (S * t) := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, htcoe,
      hg, hSdef, coe_shiftSL]
    ext i j
    rw [diagonal_mul, diagonal_mul, mul_diagonal, heisShiftMat_entry]
    split_ifs with h
    · subst h
      rw [hdrel i]
      ring
    · simp
  have hgcomm : ⁅t, S⁆ = g := by
    rw [commutatorElement_def, hcomm]
    group
  have hD1 := conjAut_diagSL_ne_one hp hodd hζ
  have hσD : fieldAut p F σ ∉ Subgroup.zpowers (conjAut p F (Matrix.SpecialLinearGroup.toGL D)) :=
    fun h => fieldAut_not_mem_linearAutGroup hσout
      ((Subgroup.zpowers_le.2 (conjAut_mem_linearAutGroup _)) h)
  have hrel := (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.relIndex_closure_pair_of_indep
    hp hE hc hD hσE hD1 hσD).2
  have hDdiag : (D : Matrix (Fin p) (Fin p) F) = diagonal fun i : Fin p => ζ ^ (i : ℕ) := rfl
  have htfix : proj p F t ∈ fixedPoints (Subgroup.closure
      ({conjAut p F (Matrix.SpecialLinearGroup.toGL D), fieldAut p F σ} :
        Set (MulAut (projectiveSL p F)))) := by
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    rintro φ (rfl | rfl)
    · exact conjAut_toGL_proj_of_comm (diag_mul_comm hDdiag htcoe)
    · rw [fieldAut_proj]
      have hl0 : σ c / c ≠ 0 := div_ne_zero ((map_ne_zero σ).2 hc0) hc0
      refine proj_eq_of_coe_eq_smul hl0 ?_ ?_
      · rw [div_pow, ← map_pow, hcp, map_inv₀, map_prod]
        simp only [hdσ]
        exact div_self (inv_ne_zero hP0)
      · rw [Matrix.SpecialLinearGroup.map_apply_coe, htcoe]
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
          diagonal_apply]
        split_ifs with hij
        · subst hij
          rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul, hdσ]
          field_simp
        · simp
  have hSfix : proj p F S ∈ fixedPoints (Subgroup.closure
      ({conjAut p F (Matrix.SpecialLinearGroup.toGL D), fieldAut p F σ} :
        Set (MulAut (projectiveSL p F)))) := by
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    rintro φ (rfl | rfl)
    · rw [conjAut_toGL_proj]
      have hζ0 : ζ⁻¹ ≠ 0 := inv_ne_zero (hζ.ne_zero hp.ne_zero)
      refine proj_eq_of_coe_eq_smul hζ0 (by rw [inv_pow, hζ.pow_eq_one, inv_one]) ?_
      have h1 : (D : Matrix (Fin p) (Fin p) F) * S = ζ⁻¹ • ((S : Matrix (Fin p) (Fin p) F) * D) :=
        heisDiagMat_mul_heisShiftMat ζ hζ.pow_eq_one
      have hDD : (D : Matrix (Fin p) (Fin p) F) * ((D⁻¹ : SpecialLinearGroup (Fin p) F) :
          Matrix (Fin p) (Fin p) F) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1, Matrix.smul_mul,
        Matrix.mul_assoc, hDD, Matrix.mul_one]
    · rw [fieldAut_proj, map_shiftSL]
  have hmem : proj p F g ∈ hyperLiftSet p E := by
    rw [← hgcomm, map_commutatorElement]
    exact commutator_mem_hyperLiftSet (closure_pair_le hD hσE) hrel htfix hSfix
  exact Subgroup.subset_closure hmem

theorem heisFourierMat_map {σ : F ≃+* F} {ζ : F} (hζσ : σ ζ = ζ) {p : ℕ} :
    (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).map σ = heisFourierMat ζ := by
  ext i j
  simp [heisFourierMat, map_pow, hζσ]

theorem proj_fourier_mem_closure_hyperLiftSet [Finite F] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {E : Subgroup (MulAut (projectiveSL p F))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 3) {σ : F ≃+* F}
    (hσout : ∀ B : GL (Fin p) F, fieldAut p F σ ≠ conjAut p F B) (hσE : fieldAut p F σ ∈ E)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ)
    (hS : conjAut p F (Matrix.SpecialLinearGroup.toGL (shiftSL F hodd)) ∈ E)
    (hroot : ∀ b : F, b ≠ 0 → σ b = b → ∃ c : F, c ^ p = b)
    {g : Matrix.SpecialLinearGroup (Fin p) F} {s : Fin p → F}
    (hg : (g : Matrix (Fin p) (Fin p) F) * heisFourierMat ζ = heisFourierMat ζ * diagonal s)
    (hgσ : (g : Matrix (Fin p) (Fin p) F).map σ = g) :
    proj p F g ∈ Subgroup.closure (hyperLiftSet p E) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Φ : Matrix (Fin p) (Fin p) F := heisFourierMat ζ with hΦdef
  have hΦdet : IsUnit Φ.det := isUnit_iff_ne_zero.2 (det_heisFourierMat_ne_zero hζ)
  set ΦG : GL (Fin p) F := Matrix.nonsingInvUnit Φ hΦdet with hΦG
  have hΦGc : (ΦG : Matrix (Fin p) (Fin p) F) = Φ := rfl
  have hΦGi : ((ΦG⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = Φ⁻¹ := rfl
  set S := shiftSL F hodd with hSdef
  set D := diagSL hζ.pow_eq_one hodd with hDdef
  set h : MulAut (projectiveSL p F) := conjAut p F ΦG with hh
  set E' := E.map (MulAut.congr h.symm).toMonoidHom with hE'
  have hcongr : ∀ φ : MulAut (projectiveSL p F), MulAut.congr h.symm φ = h⁻¹ * φ * h :=
    fun φ => rfl
  have hΦσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) ΦG = ΦG := by
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hΦGc]
    exact congrFun (congrFun (heisFourierMat_map (p := p) hζσ) i) j
  have hfh : fieldAut p F σ * h = h * fieldAut p F σ := by
    have h1 := (standard_automorphism_transport (K := F) (n := p)).2.2.1 σ ΦG
    rw [hΦσ, ← hh] at h1
    calc fieldAut p F σ * h = fieldAut p F σ * h * (fieldAut p F σ)⁻¹ * fieldAut p F σ := by
          group
      _ = h * fieldAut p F σ := by rw [h1]
  have hSΦ : ΦG⁻¹ * Matrix.SpecialLinearGroup.toGL S * ΦG = Matrix.SpecialLinearGroup.toGL D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hΦGi, hΦGc, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hSdef, hDdef, coe_shiftSL, coe_diagSL,
      Matrix.mul_assoc, heisShiftMat_mul_heisFourierMat hζ.pow_eq_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hΦdet, Matrix.one_mul]
    rfl
  have hE'a : IsElemAbelian p E' := isElemAbelian_map_congr h.symm hE
  have hE'c : Nat.card E' = p ^ 3 := (card_map_congr h.symm E).trans hc
  have hσE' : fieldAut p F σ ∈ E' := ⟨fieldAut p F σ, hσE, by
    show MulAut.congr h.symm (fieldAut p F σ) = fieldAut p F σ
    rw [hcongr, mul_assoc, hfh, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  have hDE' : conjAut p F (Matrix.SpecialLinearGroup.toGL D) ∈ E' :=
    ⟨conjAut p F (Matrix.SpecialLinearGroup.toGL S), hS, by
      show MulAut.congr h.symm _ = _
      rw [hcongr, hh, ← map_inv, ← map_mul, ← map_mul, hSΦ]⟩
  have hΦσ' : Φ.map σ = Φ := heisFourierMat_map hζσ
  have hsσ : ∀ i, σ (s i) = s i := by
    set G : Matrix (Fin p) (Fin p) F := (g : Matrix (Fin p) (Fin p) F) with hG
    have h1 : (G * Φ).map σ = (Φ * diagonal s).map σ := by rw [hg]
    rw [Matrix.map_mul, Matrix.map_mul, hgσ, hΦσ', hg, diagonal_map (map_zero σ)] at h1
    have h3 := congrArg (fun M => Φ⁻¹ * M) h1
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΦdet, Matrix.one_mul] at h3
    intro i
    have h4 := congrFun (congrFun h3 i) i
    simp only [diagonal_apply_eq] at h4
    exact h4.symm
  have hdet : (diagonal s).det = 1 := by
    have h1 := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, g.2, one_mul, mul_comm] at h1
    exact (mul_eq_right₀ (det_heisFourierMat_ne_zero hζ)).1 h1.symm
  set g₀ : Matrix.SpecialLinearGroup (Fin p) F := ⟨diagonal s, hdet⟩ with hg₀
  have h0 := proj_diag_mem_closure_hyperLiftSet hp hodd hE'a hE'c hσout hσE' hζ hDE' hroot
    (g := g₀) rfl hsσ
  have h1 := map_closure_hyperLiftSet_le h.symm.symm p E'
  rw [hE', map_congr_symm_map_congr h.symm E] at h1
  have h2 : h (proj p F g₀) = proj p F g := by
    rw [hh, conjAut_proj]
    congr 1
    apply sl_ext
    rw [coe_slConjugation, hΦGc, hΦGi]
    show Φ * diagonal s * Φ⁻¹ = g
    rw [← hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hΦdet, Matrix.mul_one]
  rw [← h2]
  exact h1 ⟨_, h0, rfl⟩

theorem slSub_le_comap_closure_hyperLiftSet [Finite F] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {E : Subgroup (MulAut (projectiveSL p F))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 3) {σ : F ≃+* F} (hgen : TorusFourierGen (semilinearFixedSubfield σ) p)
    (hσout : ∀ B : GL (Fin p) F, fieldAut p F σ ≠ conjAut p F B) (hσE : fieldAut p F σ ∈ E)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ)
    (hS : conjAut p F (Matrix.SpecialLinearGroup.toGL (shiftSL F hodd)) ∈ E)
    (hD : conjAut p F (Matrix.SpecialLinearGroup.toGL (diagSL hζ.pow_eq_one hodd)) ∈ E)
    (hroot : ∀ b : F, b ≠ 0 → σ b = b → ∃ c : F, c ^ p = b) :
    slSub p (semilinearFixedSubfield σ) ≤
      (Subgroup.closure (hyperLiftSet p E)).comap (proj p F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set k : Subfield F := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  set Q := (Subgroup.closure (hyperLiftSet p E)).comap (proj p F) with hQ
  set ι : Matrix.SpecialLinearGroup (Fin p) k →* Matrix.SpecialLinearGroup (Fin p) F :=
    Matrix.SpecialLinearGroup.map k.subtype with hι
  set ζk : k := ⟨ζ, hζσ⟩ with hζk
  have hζk' : IsPrimitiveRoot ζk p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := k.subtype) Subtype.val_injective).1 hζ
  have hιc : ∀ g' : Matrix.SpecialLinearGroup (Fin p) k,
      ((ι g' : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        (g' : Matrix (Fin p) (Fin p) k).map k.subtype := fun g' => by
    rw [hι, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hισ : ∀ g' : Matrix.SpecialLinearGroup (Fin p) k,
      ((ι g' : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F).map σ =
        ((ι g' : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    intro g'
    rw [hιc]
    ext i j
    exact ((g' : Matrix (Fin p) (Fin p) k) i j).2
  have hΦk : (heisFourierMat ζk : Matrix (Fin p) (Fin p) k).map k.subtype = heisFourierMat ζ := by
    ext i j
    simp [heisFourierMat, hζk]
  have htop := hgen ζk hζk' (Q.comap ι) (fun g' ⟨t, ht⟩ => by
      show ι g' ∈ Q
      refine proj_diag_mem_closure_hyperLiftSet hp hodd hE hc hσout hσE hζ hD hroot
        (s := fun i => (t i : F)) ?_ (fun i => (t i).2)
      rw [hιc, ht, diagonal_map (map_zero _)]
      rfl)
    (fun g' ⟨t, ht⟩ => by
      show ι g' ∈ Q
      refine proj_fourier_mem_closure_hyperLiftSet hp hodd hE hc hσout hσE hζ hζσ hS hroot
        (s := fun i => (t i : F)) ?_ (hισ g')
      have h1 := congrArg (fun M : Matrix (Fin p) (Fin p) k => M.map k.subtype) ht
      rw [Matrix.map_mul, Matrix.map_mul, hΦk, diagonal_map (map_zero _)] at h1
      rw [hιc]
      exact h1)
  intro g hg
  have hgk : ∀ i j, (g : Matrix (Fin p) (Fin p) F) i j ∈ k := mem_slSub.1 hg
  set M' : Matrix (Fin p) (Fin p) k := Matrix.of fun i j => ⟨_, hgk i j⟩ with hM'
  have hM'map : M'.map k.subtype = g := by
    ext i j
    rfl
  have hdet' : M'.det = 1 := by
    apply Subtype.val_injective
    have h1 := RingHom.map_det k.subtype M'
    rw [RingHom.mapMatrix_apply, hM'map, g.2] at h1
    exact h1
  set g' : Matrix.SpecialLinearGroup (Fin p) k := ⟨M', hdet'⟩ with hg'
  have hιg : ι g' = g := by
    apply sl_ext
    rw [hιc]
    exact hM'map
  have hmem : g' ∈ Q.comap ι := htop ▸ Subgroup.mem_top g'
  rw [← hιg]
  exact hmem

theorem ringEquiv_pow_succ_apply (σ : F ≃+* F) (i : ℕ) (x : F) :
    (σ ^ (i + 1)) x = σ ((σ ^ i) x) := by
  rw [pow_succ']
  rfl

theorem slConjugation_toGL {n : ℕ} (g h : Matrix.SpecialLinearGroup (Fin n) F) :
    slConjugation n F (Matrix.SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply sl_ext
  rw [coe_slConjugation, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem closure_hyperLiftSet_std [Finite F] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) {E : Subgroup (MulAut (projectiveSL p F))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {σ : F ≃+* F} (hσ : orderOf σ = p)
    (hKk : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p)
    (hgen : TorusFourierGen (semilinearFixedSubfield σ) p)
    (hσout : ∀ B : GL (Fin p) F, fieldAut p F σ ≠ conjAut p F B) (hσE : fieldAut p F σ ∈ E)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζσ : σ ζ = ζ)
    (hS : conjAut p F (Matrix.SpecialLinearGroup.toGL (shiftSL F hodd)) ∈ E)
    (hD : conjAut p F (Matrix.SpecialLinearGroup.toGL (diagSL hζ.pow_eq_one hodd)) ∈ E) :
    Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp3 : 3 ≤ p := three_le_of_odd_prime hp hodd
  have hp2 : p ≠ 2 := by omega
  have : Finite (MulAut (projectiveSL p F)) := MulEquiv.finite_left
  set k : Subfield F := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  haveI : Fintype k := Fintype.ofFinite k
  set q₀ := Nat.card k with hq₀
  have hq₀2 : 2 ≤ q₀ := Finite.one_lt_card
  have hζk : IsPrimitiveRoot (⟨ζ, hζσ⟩ : k) p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := k.subtype) Subtype.val_injective).1 hζ
  have hkpow : ∀ b : F, σ b = b → b ≠ 0 → b ^ (q₀ - 1) = 1 := by
    intro b hb hb0
    have h1 : (⟨b, hb⟩ : k) ^ (Fintype.card k - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one _ (fun h => hb0 (congrArg Subtype.val h))
    have h2 := congrArg Subtype.val h1
    rw [hq₀, Nat.card_eq_fintype_card]
    simpa using h2
  have hpq₀ : p ∣ q₀ - 1 := by
    have h1 : (⟨ζ, hζσ⟩ : k) ^ (Fintype.card k - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one _ (hζk.ne_zero hp.ne_zero)
    rw [hq₀, Nat.card_eq_fintype_card]
    exact hζk.dvd_of_pow_eq_one _ h1
  obtain ⟨hdiv, r, hr, hrF, hrk, hrp⟩ := exists_prime_dvd_pow_sub_one hp hp2 hq₀2 hpq₀
  rw [← hKk] at hdiv hrF
  have hpF : p ∣ Nat.card F - 1 := (Dvd.intro _ rfl).trans hdiv
  have hroot : ∀ b : F, b ≠ 0 → σ b = b → ∃ c : F, c ^ p = b := by
    intro b hb0 hbσ
    obtain ⟨a, ha⟩ := hdiv
    refine (exists_pow_eq_of_pow_div_eq_one hpF hb0 ?_).imp fun c hc => hc.2
    rw [ha, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos, pow_mul, hkpow b hbσ hb0, one_pow]
  have hsub := slSub_le_comap_closure_hyperLiftSet hp hodd hE hc hgen hσout hσE hζ hζσ hS hD hroot
  have hcop : Nat.Coprime r (q₀ - 1) := (Nat.Prime.coprime_iff_not_dvd hr).2 hrk
  have hkone : ∀ x : F, σ x = x → x ≠ 0 → x ^ r = 1 → x = 1 := by
    intro x hx hx0 hxr
    have h2 : x ^ (Nat.gcd r (q₀ - 1)) = 1 := pow_gcd_eq_one.2 ⟨hxr, hkpow x hx hx0⟩
    rwa [hcop.gcd_eq_one, pow_one] at h2
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rw [Nat.card_units]; exact hrF)
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hur : (u : F) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set tv : Fin p → F := fun i => (σ ^ (i : ℕ)) (u : F) with htv
  have hNr : ∏ i, tv i = ∏ i ∈ Finset.range p, (σ ^ i) (u : F) :=
    Fin.prod_univ_eq_prod_range (fun i => (σ ^ i) (u : F)) p
  have hσN : σ (∏ i ∈ Finset.range p, (σ ^ i) (u : F)) =
      ∏ i ∈ Finset.range p, (σ ^ i) (u : F) := by
    rw [map_prod]
    have h1 := Finset.prod_range_succ (fun i => (σ ^ i) (u : F)) p
    have h2 := Finset.prod_range_succ' (fun i => (σ ^ i) (u : F)) p
    rw [hσp] at h1
    rw [pow_zero] at h2
    simp only [ringEquiv_pow_succ_apply] at h2
    exact mul_right_cancel₀ hu0 (h2.symm.trans h1)
  have hN0 : ∏ i ∈ Finset.range p, (σ ^ i) (u : F) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 hu0
  have hN1 : ∏ i ∈ Finset.range p, (σ ^ i) (u : F) = 1 := by
    refine hkone _ hσN hN0 ?_
    rw [← Finset.prod_pow]
    simp only [← map_pow, hur, map_one, Finset.prod_const_one]
  set t : Matrix.SpecialLinearGroup (Fin p) F := ⟨diagonal tv, by rw [det_diagonal, hNr, hN1]⟩
    with htdef
  have htcoe : (t : Matrix (Fin p) (Fin p) F) = diagonal tv := rfl
  set S := shiftSL F hodd with hSdef
  set D := diagSL hζ.pow_eq_one hodd with hDdef
  have hD1 := conjAut_diagSL_ne_one hp hodd hζ
  have hb : (conjAut p F (Matrix.SpecialLinearGroup.toGL S))⁻¹ * fieldAut p F σ ∈ E :=
    E.mul_mem (E.inv_mem hS) hσE
  have hbD : (conjAut p F (Matrix.SpecialLinearGroup.toGL S))⁻¹ * fieldAut p F σ ∉
      Subgroup.zpowers (conjAut p F (Matrix.SpecialLinearGroup.toGL D)) := by
    intro h
    apply fieldAut_not_mem_linearAutGroup hσout
    have e : fieldAut p F σ = conjAut p F (Matrix.SpecialLinearGroup.toGL S) *
        ((conjAut p F (Matrix.SpecialLinearGroup.toGL S))⁻¹ * fieldAut p F σ) := by group
    rw [e]
    exact (linearAutGroup p F).mul_mem (conjAut_mem_linearAutGroup _)
      ((Subgroup.zpowers_le.2 (conjAut_mem_linearAutGroup _)) h)
  have hrel := (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.relIndex_closure_pair_of_indep
    hp hE hc hD hb hD1 hbD).2
  have hDdiag : (D : Matrix (Fin p) (Fin p) F) = diagonal fun i : Fin p => ζ ^ (i : ℕ) := rfl
  have htS : Matrix.SpecialLinearGroup.map σ.toRingHom t * S = S * t := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, htcoe, hSdef, coe_shiftSL,
      diagonal_map (map_zero _)]
    ext i j
    rw [diagonal_mul, mul_diagonal, heisShiftMat_entry]
    split_ifs with h
    · subst h
      rw [one_mul, mul_one]
      show σ ((σ ^ (i : ℕ)) (u : F)) = (σ ^ ((finRotate p i : Fin p) : ℕ)) (u : F)
      rw [← ringEquiv_pow_succ_apply, finRotate_val_mod, ← pow_eq_pow_mod _ hσp]
    · simp
  have htfix : proj p F t ∈ fixedPoints (Subgroup.closure
      ({conjAut p F (Matrix.SpecialLinearGroup.toGL D),
        (conjAut p F (Matrix.SpecialLinearGroup.toGL S))⁻¹ * fieldAut p F σ} :
        Set (MulAut (projectiveSL p F)))) := by
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    rintro φ (rfl | rfl)
    · exact conjAut_toGL_proj_of_comm (diag_mul_comm hDdiag htcoe)
    · rw [MulAut.mul_apply, fieldAut_proj, ← map_inv, ← map_inv, conjAut_toGL_proj, inv_inv,
        mul_assoc, htS, ← mul_assoc, inv_mul_cancel, one_mul]
  have htr : t ^ r = 1 := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_pow, htcoe, diagonal_pow, Matrix.SpecialLinearGroup.coe_one,
      ← diagonal_one]
    congr 1
    ext i
    simp only [Pi.pow_apply, htv, ← map_pow, hur, map_one, Pi.one_apply]
  have hpr : ¬ p ∣ r := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm
  have htmem : proj p F t ∈ hyperLiftSet p E :=
    mem_hyperLiftSet_of_pow (closure_pair_le hD hb) hrel hpr
      (by rw [← map_pow, htr, map_one]) htfix
  set M : GL (Fin p) F := Matrix.SpecialLinearGroup.toGL t with hMdef
  have hMc : (M : Matrix (Fin p) (Fin p) F) = diagonal tv := by
    rw [hMdef, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, htcoe]
  set G : GL (Fin p) F := M * (Matrix.GeneralLinearGroup.map (σ : F →+* F) M)⁻¹ with hGdef
  have hmapc : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) M : GL (Fin p) F) :
      Matrix (Fin p) (Fin p) F) = (M : Matrix (Fin p) (Fin p) F).map σ := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl
  have hGM : (G : Matrix (Fin p) (Fin p) F) * (M : Matrix (Fin p) (Fin p) F).map σ = M := by
    rw [← hmapc, ← Units.val_mul, hGdef, inv_mul_cancel_right]
  have hGns : ∀ c : F, (G : Matrix (Fin p) (Fin p) F) ≠ c • 1 := by
    intro c hcG
    have h1 : (M : Matrix (Fin p) (Fin p) F) = c • (M : Matrix (Fin p) (Fin p) F).map σ :=
      hGM.symm.trans (by rw [hcG, Matrix.smul_mul, Matrix.one_mul])
    rw [hMc] at h1
    have e0 := congrFun (congrFun h1 ⟨0, hp.pos⟩) ⟨0, hp.pos⟩
    have e1 := congrFun (congrFun h1 ⟨1, hp.one_lt⟩) ⟨1, hp.one_lt⟩
    simp only [Matrix.smul_apply, Matrix.map_apply, diagonal_apply_eq, smul_eq_mul] at e0 e1
    have ht0 : tv ⟨0, hp.pos⟩ = (u : F) := by
      show (σ ^ 0) (u : F) = u
      rw [pow_zero]
      rfl
    have ht1 : tv ⟨1, hp.one_lt⟩ = σ (u : F) := by
      show (σ ^ 1) (u : F) = σ u
      rw [pow_one]
    rw [ht0] at e0
    rw [ht1] at e1
    have hσu0 : σ (σ (u : F)) ≠ 0 := (map_ne_zero _).2 ((map_ne_zero _).2 hu0)
    have hcσ : σ c = c := by
      have h2 := congrArg σ e0
      rw [map_mul] at h2
      exact mul_right_cancel₀ hσu0 (h2.symm.trans e1)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_mul] at e0
      exact hu0 e0
    have hcr : c ^ r = 1 := by
      have h2 := congrArg (· ^ r) e0
      simp only [mul_pow, ← map_pow, hur, map_one, mul_one] at h2
      exact h2.symm
    have hc1 := hkone c hcσ hc0 hcr
    rw [hc1, one_mul] at e0
    have hu1 : (u : F) = 1 := hkone _ e0.symm hu0 hur
    have : u = 1 := Units.ext hu1
    rw [this, orderOf_one] at hu
    exact hr.one_lt.ne hu
  have hne := slConjugation_map_ne_of_unit σ hk G hGns M hGM
  have hpair := pairSL_closure hp hp2 hKk hp3 M hne
  set Q := (Subgroup.closure (hyperLiftSet p E)).comap (proj p F) with hQ
  have htQ : t ∈ Q := Subgroup.subset_closure htmem
  have hle : Subgroup.closure ((slSub p k : Set (Matrix.SpecialLinearGroup (Fin p) F)) ∪
      ((slSub p k).map (slConjugation p F M).toMonoidHom :
        Set (Matrix.SpecialLinearGroup (Fin p) F))) ≤ Q := by
    rw [Subgroup.closure_le]
    rintro y (hy | ⟨g, hg, rfl⟩)
    · exact hsub hy
    · show slConjugation p F M g ∈ Q
      rw [hMdef, slConjugation_toGL]
      exact Q.mul_mem (Q.mul_mem htQ (hsub hg)) (Q.inv_mem htQ)
  rw [hpair, top_le_iff] at hle
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := proj_surjective p F y
  have hg : g ∈ Q := hle ▸ Subgroup.mem_top g
  exact hg

end Std

section TorusThree

variable {F : Type} [Field F] {p : ℕ}

theorem caseA_claim2_of_three [NeZero p] (hp : 3 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {ν : F}
    (hν0 : ν ≠ 0) (hν2 : ν ^ 2 ≠ 1) :
    fourierBirefl (p := p) ζ ν⁻¹ 0 1 * fourierBirefl (p := p) ζ ν 1 0 ≠
      fourierBirefl (p := p) ζ ν⁻¹ 1 0 * fourierBirefl (p := p) ζ ν 0 1 := by
  obtain ⟨h01, h10⟩ := caseA_birefl_entries (by omega) hζ hν0
  obtain ⟨i01, i10⟩ := caseA_birefl_entries (by omega) hζ (inv_ne_zero hν0)
  rw [inv_inv] at i01 i10
  rw [h01, h10, i01, i10]
  have hq0 : (p : F)⁻¹ ≠ 0 := inv_ne_zero (heis_natCast_ne_zero hζ (by omega))
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hν1 : ν - 1 ≠ 0 := sub_ne_zero.mpr fun h => hν2 (by rw [h, one_pow])
  have hν2' : 1 - ν ^ 2 ≠ 0 := sub_ne_zero.mpr fun h => hν2 h.symm
  have hab : (ν⁻¹ - 1) ^ 2 - (ν - 1) ^ 2 ≠ 0 := by
    have : (ν⁻¹ - 1) ^ 2 - (ν - 1) ^ 2 = (ν - 1) ^ 2 * (1 - ν ^ 2) / ν ^ 2 := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hν1) hν2') (pow_ne_zero 2 hν0)
  have hζz : ζ - ζ⁻¹ ≠ 0 := by
    have : ζ - ζ⁻¹ = (ζ ^ 2 - 1) / ζ := by
      field_simp
    rw [this]
    exact div_ne_zero (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega))) hζ0
  intro h
  have h0 : (p : F)⁻¹ ^ 2 * (((ν⁻¹ - 1) ^ 2 - (ν - 1) ^ 2) * (ζ - ζ⁻¹)) = 0 := by
    linear_combination h
  exact mul_ne_zero (pow_ne_zero 2 hq0) (mul_ne_zero hab hζz) h0

theorem exists_fix_mem_caseA_of_three (hp : 3 ≤ p) [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν0 : ν ≠ 0) (hνp : ν ^ p ≠ 1) (hν2 : ν ^ 2 ≠ 1)
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)}
    (hT : ContainsDiagTorus K) (hTw : ContainsFourierTorus ζ K) :
    ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      Pi.single 0 1 ᵥ* ((g⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) ≠
        Pi.single 0 1 := by
  have hp2 : 2 ≤ p := by omega
  have hν1 : ν ≠ 1 := fun h => hν2 (by rw [h, one_pow])
  obtain ⟨⟨B, hBK, hBm⟩, ⟨Bt, hBtK, hBtm⟩⟩ := caseA_exists_mem_birefl hp2 hζ hν0 hTw
  obtain ⟨σ, hσ0, hσdet, hσ⟩ := caseA_exists_sigma hp2 hζ hν0 hν1 hνp
  have hBBi : (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F) * fourierBirefl ζ ν⁻¹ = 1 :=
    caseA_birefl_mul_inv hζ hν0
  have hBiB : (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) * fourierBirefl ζ ν = 1 := by
    simpa using caseA_birefl_mul_inv hζ (inv_ne_zero hν0)
  let s : Matrix.SpecialLinearGroup (Fin p) F := ⟨diagonal σ, by rw [det_diagonal, hσdet]⟩
  have hsK : s ∈ K := hT s ⟨σ, rfl⟩
  have hBinv : ((B⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      fourierBirefl ζ ν⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one B (by rw [hBm]; exact hBBi)
  have hBtinv : ((Bt⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (fourierBirefl ζ ν⁻¹)ᵀ :=
    isolate_coe_inv_eq_of_mul_eq_one Bt (by rw [hBtm, ← transpose_mul, hBiB, transpose_one])
  have hsinv : ((s⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal σ⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one s (diagonal_mul_diagonal_inv_eq_one hσ0)
  refine ⟨Bt⁻¹ * s * B, K.mul_mem (K.mul_mem (K.inv_mem hBtK) hsK) hBK, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hBtinv, hBm,
      ← mulVec_mulVec, ← mulVec_mulVec]
    have h1 : diagonal σ *ᵥ ((fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F) *ᵥ Pi.single 0 1) =
        (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F)ᵀ *ᵥ Pi.single 0 1 := by
      funext j
      rw [mulVec_diagonal, caseA_mulVec_e0, caseA_mulVec_e0, transpose_apply]
      exact hσ j
    show (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F)ᵀ *ᵥ (diagonal σ *ᵥ _) = _
    rw [h1, mulVec_mulVec, ← transpose_mul, hBBi, transpose_one, one_mulVec]
  · intro h
    have hginv : (Bt⁻¹ * s * B)⁻¹ = B⁻¹ * s⁻¹ * Bt := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [hginv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hBinv, hsinv,
      hBtm] at h
    have h2 : Pi.single 0 1 ᵥ* ((fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) *
        diagonal σ⁻¹) = Pi.single 0 1 ᵥ* (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F)ᵀ := by
      have h' := congrArg (fun v => v ᵥ* (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F)ᵀ) h
      simp only [vecMul_vecMul] at h'
      rwa [mul_assoc _ (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F)ᵀ, ← transpose_mul, hBiB,
        transpose_one, mul_one] at h'
    have h3 := congrFun h2 1
    rw [caseA_e0_vecMul, caseA_e0_vecMul, transpose_apply, mul_diagonal] at h3
    have h4 := hσ 1
    refine caseA_claim2_of_three hp hζ hν0 hν2 ?_
    have h5 : (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) 0 1 =
        (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) 1 0 * σ 1 := by
      rw [← h3]
      simp [hσ0 1]
    rw [h5, ← h4]
    ring

theorem exists_single_mem_of_row [NeZero p] {a : F} (ha0 : a ≠ 0) (hap : a ^ p ≠ 1)
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)} (hT : ContainsDiagTorus K)
    {w : Fin p → F} (hw0 : w 0 = 0) {b : Fin p} (hb : w b ≠ 0)
    (hx : ∃ x ∈ K, (x : Matrix (Fin p) (Fin p) F) = 1 + vecMulVec (Pi.single 0 1) w) :
    ∃ c : F, c ≠ 0 ∧ ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + Matrix.single 0 b c := by
  classical
  obtain ⟨x, hxK, hxm⟩ := hx
  have hb0 : b ≠ 0 := fun h => hb (h ▸ hw0)
  set t : Fin p → F := fun j => if j = b then (a ^ (p - 1))⁻¹ else a with ht
  have ht0 : ∀ j, t j ≠ 0 := fun j => by
    simp only [ht]
    split_ifs
    · exact inv_ne_zero (pow_ne_zero _ ha0)
    · exact ha0
  have hprod : ∏ j, t j = 1 := by
    rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ b)]
    have h1 : ∏ j ∈ Finset.univ.erase b, t j = a ^ (p - 1) := by
      have h2 : ∏ j ∈ Finset.univ.erase b, t j = ∏ _j ∈ Finset.univ.erase b, a :=
        Finset.prod_congr rfl (fun j hj => by simp only [ht, if_neg (Finset.ne_of_mem_erase hj)])
      rw [h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
        Fintype.card_fin]
    rw [h1]
    simp only [ht, if_pos rfl]
    exact inv_mul_cancel₀ (pow_ne_zero _ ha0)
  set d : Matrix.SpecialLinearGroup (Fin p) F := ⟨diagonal t, by rw [det_diagonal, hprod]⟩
    with hd
  have hdK : d ∈ K := hT d ⟨t, rfl⟩
  set M : Matrix (Fin p) (Fin p) F := vecMulVec (Pi.single 0 1) w with hM
  have hMM : M * M = 0 := by
    rw [hM, vecMulVec_mul_vecMulVec, dotProduct_single, hw0, zero_mul, zero_smul,
      vecMulVec_zero]
  have hxinv : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 - M :=
    isolate_coe_inv_eq_of_mul_eq_one x (by rw [hxm, add_mul, mul_sub, mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hMM]; abel)
  have hdinv : ((d⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal t⁻¹ := isolate_coe_inv_eq_of_mul_eq_one d (diagonal_mul_diagonal_inv_eq_one ht0)
  set c : F := (a ^ p - 1) * w b with hc
  have hc0 : c ≠ 0 := mul_ne_zero (sub_ne_zero.2 hap) hb
  have hM' : diagonal t * M * diagonal t⁻¹ = M + Matrix.single 0 b c := by
    ext i j
    simp only [hM, mul_diagonal, diagonal_mul, vecMulVec_apply, Matrix.add_apply, Pi.inv_apply,
      Matrix.single_apply]
    by_cases hi : i = 0
    · subst hi
      have hta : t 0 = a := by simp only [ht, if_neg (Ne.symm hb0)]
      simp only [hta, Pi.single_eq_same, one_mul, true_and]
      by_cases hj : b = j
      · subst hj
        simp only [ht, if_pos rfl, inv_inv, hc, if_true]
        have hp1 : a ^ p = a * a ^ (p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos p)]
        rw [hp1]
        ring
      · simp only [if_neg hj, add_zero, ht, if_neg (Ne.symm hj)]
        field_simp
    · simp only [Pi.single_eq_of_ne hi, zero_mul, mul_zero, zero_add]
      rw [if_neg (fun h => hi h.1.symm)]
  have hSM : Matrix.single (0 : Fin p) b c * M = 0 := by
    ext i j
    simp only [hM, Matrix.mul_apply, Matrix.single_apply, vecMulVec_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = b
    · subst hl
      rw [Pi.single_eq_of_ne hb0, zero_mul, mul_zero]
    · rw [if_neg (fun h => hl h.2.symm), zero_mul]
  refine ⟨c, hc0, d * x * d⁻¹ * x⁻¹,
    K.mul_mem (K.mul_mem (K.mul_mem hdK hxK) (K.inv_mem hdK)) (K.inv_mem hxK), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hxinv, hdinv, hxm]
  show diagonal t * (1 + M) * diagonal t⁻¹ * (1 - M) = 1 + Matrix.single 0 b c
  have h1 : diagonal t * (1 + M) * diagonal t⁻¹ = 1 + (M + Matrix.single 0 b c) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, diagonal_mul_diagonal_inv_eq_one ht0, hM']
  have h2 : (1 + (M + Matrix.single 0 b c)) * (1 - M) =
      1 + Matrix.single 0 b c - (M * M + Matrix.single 0 b c * M) := by
    rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul]
    abel
  rw [h1, h2, hMM, hSM, zero_add, sub_zero]

theorem torusFourierGen_of_exists [Fact p.Prime] (hp3 : 3 ≤ p) {ν a : F} (hν0 : ν ≠ 0)
    (hνp : ν ^ p ≠ 1) (hν2 : ν ^ 2 ≠ 1) (ha0 : a ≠ 0) (hap : a ^ p ≠ 1) : TorusFourierGen F p := by
  intro ζ hζ K hT hTw
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨g, hgK, hg0, hg1⟩ := exists_fix_mem_caseA_of_three hp3 hζ hν0 hνp hν2 hT hTw
  have hxdet : IsUnit (g : Matrix (Fin p) (Fin p) F).det := by
    rw [g.2]
    exact isUnit_one
  rw [caseA_coe_inv] at hg1
  have hginve : (g : Matrix (Fin p) (Fin p) F)⁻¹ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    calc (g : Matrix (Fin p) (Fin p) F)⁻¹ *ᵥ Pi.single 0 1
        = (g : Matrix (Fin p) (Fin p) F)⁻¹ *ᵥ
            ((g : Matrix (Fin p) (Fin p) F) *ᵥ Pi.single 0 1) := by rw [hg0]
      _ = Pi.single 0 1 := by rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hxdet, one_mulVec]
  let z : Matrix.SpecialLinearGroup (Fin p) F := ⟨zFix ν, caseA_det_zFix hν0⟩
  have hzK : z ∈ K := hT z ⟨_, rfl⟩
  have hcK : z * g * z⁻¹ * g⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hzK hgK) (K.inv_mem hzK)) (K.inv_mem hgK)
  obtain ⟨w, hw⟩ : ∃ w : Fin p → F, w = Pi.single 0 1 ᵥ* (g : Matrix (Fin p) (Fin p) F)⁻¹ -
      Pi.single 0 1 := ⟨_, rfl⟩
  set ρ : F := 1 - (ν ^ p)⁻¹ with hρdef
  have hcm : ((z * g * z⁻¹ * g⁻¹ : Matrix.SpecialLinearGroup (Fin p) F) :
      Matrix (Fin p) (Fin p) F) = 1 + vecMulVec (Pi.single 0 1) (ρ • w) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, caseA_coe_inv z, caseA_coe_inv g, hw, vecMulVec_smul]
    exact zFix_comm_of_fix hxdet hg0 hν0
  have hw0 : w 0 = 0 := by
    rw [hw, Pi.sub_apply, caseA_e0_vecMul]
    have h := congrFun hginve 0
    rw [caseA_mulVec_e0] at h
    rw [h]
    simp
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg1
    funext b
    have h0 := hcon b
    rw [hw, Pi.sub_apply, sub_eq_zero] at h0
    exact h0
  have hρ : ρ ≠ 0 := sub_ne_zero.mpr fun h => hνp (inv_eq_one.mp h.symm)
  obtain ⟨c, hc, g', hg'K, hg'⟩ := exists_single_mem_of_row ha0 hap hT
    (w := ρ • w) (by rw [Pi.smul_apply, hw0, smul_zero]) (b := b)
    (by rw [Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero hρ hb) ⟨_, hcK, hcm⟩
  have hb0 : b ≠ 0 := fun h => hb (h ▸ hw0)
  have hx : Matrix.SpecialLinearGroup.transvection (Ne.symm hb0) c ∈ K := by
    have : Matrix.SpecialLinearGroup.transvection (Ne.symm hb0) c = g' := sl_ext (by
      rw [Matrix.SpecialLinearGroup.transvection_coe, hg'])
    rw [this]
    exact hg'K
  refine eq_top_of_torus_shift_root hp3 hT (fun g'' hg'' => hTw g'' ?_) (Ne.symm hb0) hc hx
  exact ⟨fun j => ζ ^ (j : ℕ), by rw [hg'']; exact heisShiftMat_mul_heisFourierMat hζ.pow_eq_one⟩

theorem torusFourierGen_three [Finite F] (hF : 7 ≤ Nat.card F) : TorusFourierGen F 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hne : ∀ m : ℕ, 0 < m → m < 6 → (g : F) ^ m ≠ 1 := by
    intro m hm hm6 h
    have h1 : g ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have h2 := Nat.le_of_dvd hm (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  exact torusFourierGen_of_exists (le_refl 3) g.ne_zero (hne 3 (by norm_num) (by norm_num))
    (hne 2 (by norm_num) (by norm_num)) g.ne_zero (hne 3 (by norm_num) (by norm_num))

end TorusThree

section Eig

variable {F : Type} [Field F] {n p : ℕ}

@[expose] noncomputable def eigProj (p : ℕ) (W : Matrix (Fin n) (Fin n) F) (ε : F) :
    Matrix (Fin n) (Fin n) F :=
  (p : F)⁻¹ • ∑ j ∈ Finset.range p, ε⁻¹ ^ j • W ^ j

theorem sum_range_pow_eq_zero {θ : F} (hθ : θ ^ p = 1) (hθ1 : θ ≠ 1) :
    ∑ j ∈ Finset.range p, θ ^ j = 0 := by
  have h := geom_sum_mul θ p
  rw [hθ, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hθ1)

theorem sum_eig_succ (W : Matrix (Fin n) (Fin n) F) (hW : W ^ p = 1) {ε : F} (hε : ε ^ p = 1) :
    ∑ j ∈ Finset.range p, ε⁻¹ ^ (j + 1) • W ^ (j + 1) =
      ∑ j ∈ Finset.range p, ε⁻¹ ^ j • W ^ j := by
  have h1 := Finset.sum_range_succ' (fun j => ε⁻¹ ^ j • W ^ j) p
  have h2 := Finset.sum_range_succ (fun j => ε⁻¹ ^ j • W ^ j) p
  rw [inv_pow, hε, hW, inv_one, one_smul] at h2
  simp only [pow_zero, one_smul] at h1
  exact add_right_cancel (h1.symm.trans h2)

theorem mul_eigProj {W : Matrix (Fin n) (Fin n) F} (hW : W ^ p = 1) {ε : F} (hε : ε ^ p = 1)
    (hε0 : ε ≠ 0) : W * eigProj p W ε = ε • eigProj p W ε := by
  unfold eigProj
  rw [Matrix.mul_smul, smul_comm ε]
  congr 1
  calc W * ∑ j ∈ Finset.range p, ε⁻¹ ^ j • W ^ j
      = ∑ j ∈ Finset.range p, ε⁻¹ ^ j • W ^ (j + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_smul, ← pow_succ']
    _ = ε • ∑ j ∈ Finset.range p, ε⁻¹ ^ (j + 1) • W ^ (j + 1) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
        congr 1
        rw [pow_succ]
        field_simp
    _ = ε • ∑ j ∈ Finset.range p, ε⁻¹ ^ j • W ^ j := by rw [sum_eig_succ W hW hε]

theorem eigProj_mul_comm (W : Matrix (Fin n) (Fin n) F) (ε : F) :
    eigProj p W ε * W = W * eigProj p W ε := by
  unfold eigProj
  rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← pow_succ, ← pow_succ']

theorem eigProj_mul {W : Matrix (Fin n) (Fin n) F} (hW : W ^ p = 1) {ε : F} (hε : ε ^ p = 1)
    (hε0 : ε ≠ 0) : eigProj p W ε * W = ε • eigProj p W ε := by
  rw [eigProj_mul_comm, mul_eigProj hW hε hε0]

theorem pow_mul_eigProj {W : Matrix (Fin n) (Fin n) F} (hW : W ^ p = 1) {ε : F} (hε : ε ^ p = 1)
    (hε0 : ε ≠ 0) (j : ℕ) : W ^ j * eigProj p W ε = ε ^ j • eigProj p W ε := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, mul_eigProj hW hε hε0, smul_smul,
      pow_succ', mul_comm]

theorem eigProj_mul_eigProj_eq {W : Matrix (Fin n) (Fin n) F} (hW : W ^ p = 1) {ε η : F}
    (hη : η ^ p = 1) (hη0 : η ≠ 0) :
    eigProj p W ε * eigProj p W η =
      ((p : F)⁻¹ * ∑ j ∈ Finset.range p, (η / ε) ^ j) • eigProj p W η := by
  have h2 : ∀ j ∈ Finset.range p, (ε⁻¹ ^ j • W ^ j) * eigProj p W η =
      (η / ε) ^ j • eigProj p W η := by
    intro j _
    rw [Matrix.smul_mul, pow_mul_eigProj hW hη hη0, smul_smul, div_eq_mul_inv, mul_pow, mul_comm]
  calc eigProj p W ε * eigProj p W η
      = (p : F)⁻¹ • ∑ j ∈ Finset.range p, (ε⁻¹ ^ j • W ^ j) * eigProj p W η := by
        show ((p : F)⁻¹ • ∑ j ∈ Finset.range p, ε⁻¹ ^ j • W ^ j) * eigProj p W η = _
        rw [Matrix.smul_mul, Finset.sum_mul]
    _ = (p : F)⁻¹ • ∑ j ∈ Finset.range p, (η / ε) ^ j • eigProj p W η := by
        rw [Finset.sum_congr rfl h2]
    _ = _ := by rw [← Finset.sum_smul, smul_smul]

theorem eigProj_mul_eigProj_of_ne {W : Matrix (Fin n) (Fin n) F} (hW : W ^ p = 1) {ε η : F}
    (hε : ε ^ p = 1) (hη : η ^ p = 1) (hε0 : ε ≠ 0) (hη0 : η ≠ 0) (hne : ε ≠ η) :
    eigProj p W ε * eigProj p W η = 0 := by
  rw [eigProj_mul_eigProj_eq hW hη hη0, sum_range_pow_eq_zero (by rw [div_pow, hε, hη, div_one])
    (fun h' => hne ((div_eq_one_iff_eq hε0).1 h').symm), mul_zero, zero_smul]

theorem eigProj_mul_self {W : Matrix (Fin n) (Fin n) F} (hW : W ^ p = 1) (hp : (p : F) ≠ 0)
    {ε : F} (hε : ε ^ p = 1) (hε0 : ε ≠ 0) : eigProj p W ε * eigProj p W ε = eigProj p W ε := by
  rw [eigProj_mul_eigProj_eq hW hε hε0, div_self hε0]
  simp [hp]

theorem sum_eigProj {W : Matrix (Fin n) (Fin n) F} (hp : (p : F) ≠ 0) {lam ε₀ : F}
    (hlam : IsPrimitiveRoot lam p) (hε₀0 : ε₀ ≠ 0) :
    ∑ i ∈ Finset.range p, eigProj p W (ε₀ * lam ^ i) = 1 := by
  classical
  have hp0 : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; exact hp (by simp))
  unfold eigProj
  rw [← Finset.smul_sum, Finset.sum_comm]
  have h0 : ∀ j ∈ Finset.range p, ∑ i ∈ Finset.range p, (ε₀ * lam ^ i)⁻¹ ^ j • W ^ j =
      (if j = 0 then (p : F) else 0) • W ^ j := by
    intro j hj
    rw [← Finset.sum_smul]
    congr 1
    split_ifs with h
    · subst h
      simp
    · have h1 : ∀ i, (ε₀ * lam ^ i)⁻¹ ^ j = ε₀⁻¹ ^ j * (lam⁻¹ ^ j) ^ i := fun i => by ring
      simp only [h1]
      rw [← Finset.mul_sum, sum_range_pow_eq_zero, mul_zero]
      · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hlam.pow_eq_one, inv_one, one_pow]
      · rw [Ne, inv_pow, inv_eq_one]
        exact hlam.pow_ne_one_of_pos_of_lt h (Finset.mem_range.1 hj)
  rw [Finset.sum_congr rfl h0]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_range, hp0, if_true, pow_zero]
  rw [smul_smul, inv_mul_cancel₀ hp, one_smul]

theorem mul_eigProj_of_qcomm {W V : Matrix (Fin n) (Fin n) F} {μ : F}
    (hVW : V * W = μ • (W * V)) (ε : F) :
    V * eigProj p W ε = eigProj p W (ε * μ⁻¹) * V := by
  have hpow : ∀ j : ℕ, V * W ^ j = μ ^ j • (W ^ j * V) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc, hVW,
        Matrix.mul_smul, ← Matrix.mul_assoc, smul_smul, pow_succ]
  unfold eigProj
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, hpow, smul_smul, Matrix.smul_mul, mul_inv, inv_inv, mul_pow, mul_comm]

theorem eigProj_map (σ : F ≃+* F) {W : Matrix (Fin n) (Fin n) F} (hW : W.map σ = W) {ε : F}
    (hε : σ ε = ε) : (eigProj p W ε).map σ = eigProj p W ε := by
  have hWj : ∀ j : ℕ, (W ^ j).map σ = W ^ j := fun j => by
    have h := Matrix.map_pow W (σ : F →+* F) j
    rw [show (⇑(σ : F →+* F) : F → F) = ⇑σ from rfl, hW] at h
    exact h
  ext a b
  simp only [eigProj, Matrix.map_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    map_mul, map_sum, map_pow, map_inv₀, map_natCast, hε]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact congrFun (congrFun (hWj j) a) b

end Eig

section Pair

variable {G P : Type*} [Group G] [Group P]

@[expose] def InvPairAt (p : ℕ) (E : Subgroup (MulAut G)) : Prop :=
  ∃ H₁ H₂ : Subgroup G, ¬ p ∣ Nat.card H₁ ∧ ¬ p ∣ Nat.card H₂ ∧
    (∀ φ ∈ E, ∀ s ∈ H₁, φ s ∈ H₁) ∧ (∀ φ ∈ E, ∀ s ∈ H₂, φ s ∈ H₂) ∧ H₁ ⊔ H₂ = ⊤

theorem invPairAt_of_congr (θ : G ≃* P) {p : ℕ} {E : Subgroup (MulAut G)}
    (h : InvPairAt p (E.map (MulAut.congr θ).toMonoidHom)) : InvPairAt p E := by
  obtain ⟨H₁, H₂, h₁, h₂, hs₁, hs₂, hgen⟩ := h
  have hstab : ∀ H : Subgroup P,
      (∀ φ ∈ E.map (MulAut.congr θ).toMonoidHom, ∀ s ∈ H, φ s ∈ H) →
      ∀ φ ∈ E, ∀ s ∈ H.map θ.symm.toMonoidHom, φ s ∈ H.map θ.symm.toMonoidHom := by
    rintro H hH φ hφ _ ⟨s, hs, rfl⟩
    refine ⟨MulAut.congr θ φ s, hH _ ⟨φ, hφ, rfl⟩ s hs, ?_⟩
    simp [MulAut.congr_apply]
  refine ⟨H₁.map θ.symm.toMonoidHom, H₂.map θ.symm.toMonoidHom, ?_, ?_, hstab H₁ hs₁,
    hstab H₂ hs₂, ?_⟩
  · rwa [Subgroup.card_map_of_injective θ.symm.injective]
  · rwa [Subgroup.card_map_of_injective θ.symm.injective]
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ θ.symm.surjective]

@[expose] def stabSub [Finite G] (H : Subgroup G) : Subgroup (MulAut G) where
  carrier := {φ | ∀ s ∈ H, φ s ∈ H}
  mul_mem' := fun ha hb s hs => ha _ (hb s hs)
  one_mem' := fun s hs => hs
  inv_mem' := by
    intro φ hφ s hs
    have hmap : H.map φ.toMonoidHom = H :=
      Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨t, ht, rfl⟩; exact hφ t ht)
        (by rw [Subgroup.card_map_of_injective φ.injective])
    have hs' : s ∈ H.map φ.toMonoidHom := hmap.symm ▸ hs
    obtain ⟨t, ht, rfl⟩ := hs'
    simpa using ht

end Pair

section Idem

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem mem_elationSubgroup_iff {W : Submodule F (Fin n → F)}
    {g : Matrix.SpecialLinearGroup (Fin n) F} :
    g ∈ elationSubgroup W ↔ (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact mem_thetaSpace.2 (mem_elationGenerators.1 hx)
    | one => simpa using (thetaSpace W).zero_mem
    | mul x y _ _ hx hy =>
      have e : ((x * y : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
          ((x : Matrix (Fin n) (Fin n) F) - 1) + ((y : Matrix (Fin n) (Fin n) F) - 1) +
            ((x : Matrix (Fin n) (Fin n) F) - 1) * ((y : Matrix (Fin n) (Fin n) F) - 1) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        noncomm_ring
      rw [e, thetaSpace_mul hx hy, add_zero]
      exact add_mem hx hy
    | inv x _ hx =>
      have h1 : (x : Matrix (Fin n) (Fin n) F) * (1 - ((x : Matrix (Fin n) (Fin n) F) - 1)) = 1 := by
        have h2 := thetaSpace_mul hx hx
        calc (x : Matrix (Fin n) (Fin n) F) * (1 - ((x : Matrix (Fin n) (Fin n) F) - 1))
            = 1 - ((x : Matrix (Fin n) (Fin n) F) - 1) * ((x : Matrix (Fin n) (Fin n) F) - 1) := by
              noncomm_ring
          _ = 1 := by rw [h2, sub_zero]
      have hinv : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          1 - ((x : Matrix (Fin n) (Fin n) F) - 1) := by
        calc ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
            = ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
                ((x : Matrix (Fin n) (Fin n) F) * (1 - ((x : Matrix (Fin n) (Fin n) F) - 1))) := by
              rw [h1, Matrix.mul_one]
          _ = 1 - ((x : Matrix (Fin n) (Fin n) F) - 1) := by
              rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      rw [hinv, sub_sub_cancel_left]
      exact neg_mem hx
  · intro hg
    exact Subgroup.subset_closure (mem_elationGenerators.2 (mem_thetaSpace.1 hg))

theorem one_add_pow_of_sq {φ : Matrix (Fin n) (Fin n) F} (h : φ * φ = 0) (m : ℕ) :
    (1 + φ) ^ m = 1 + (m : F) • φ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [Nat.cast_succ, add_smul, one_smul, add_mul, mul_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, h, smul_zero, add_zero]
    abel

theorem isPGroup_elationSubgroup (W : Submodule F (Fin n → F)) :
    IsPGroup (ringChar F) (elationSubgroup W) := by
  intro g
  refine ⟨1, ?_⟩
  have hφ := mem_elationSubgroup_iff.1 g.2
  apply Subtype.ext
  apply sl_ext
  rw [Subgroup.coe_pow, pow_one, Matrix.SpecialLinearGroup.coe_pow, Subgroup.coe_one,
    Matrix.SpecialLinearGroup.coe_one]
  have h1 : ((g : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + (((g : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) := by abel
  rw [h1, one_add_pow_of_sq (thetaSpace_mul hφ hφ), ringChar.Nat.cast_ringChar, zero_smul,
    add_zero]

theorem not_dvd_card_of_isPGroup_ringChar {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {X : Type*} [Group X] [Finite X] (hX : IsPGroup (ringChar F) X) : ¬ p ∣ Nat.card X := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
  rw [hk]
  intro h
  have h1 := hp.dvd_of_dvd_pow h
  have h2 : p = ringChar F := (Nat.prime_dvd_prime_iff_eq hp Fact.out).1 h1
  exact hpF (by rw [h2]; exact ringChar.Nat.cast_ringChar)

theorem mulVec_comp_of_map (σ : F ≃+* F) {M : Matrix (Fin n) (Fin n) F} (hM : M.map σ = M)
    (x : Fin n → F) : M *ᵥ (σ ∘ x) = σ ∘ (M *ᵥ x) := by
  ext i
  have h := RingHom.map_mulVec (σ : F →+* F) M x i
  rw [show (⇑(σ : F →+* F) : F → F) = ⇑σ from rfl, hM] at h
  exact h.symm

theorem map_symm_of_map (σ : F ≃+* F) {M : Matrix (Fin n) (Fin n) F} (hM : M.map σ = M) :
    M.map σ.symm = M := by
  conv_lhs => rw [← hM]
  ext i j
  simp

theorem map_mem_thetaSpace (σ : F ≃+* F) {W : Submodule F (Fin n → F)}
    (hW : ∀ x ∈ W, σ ∘ x ∈ W) (hW' : ∀ x ∈ W, σ.symm ∘ x ∈ W)
    {φ : Matrix (Fin n) (Fin n) F} (hφ : φ ∈ thetaSpace W) : φ.map σ ∈ thetaSpace W := by
  have key : ∀ x : Fin n → F, φ.map σ *ᵥ x = σ ∘ (φ *ᵥ (σ.symm ∘ x)) := by
    intro x
    ext i
    have h := RingHom.map_mulVec (σ : F →+* F) φ (σ.symm ∘ x) i
    rw [show (⇑(σ : F →+* F) : F → F) = ⇑σ from rfl] at h
    simp only [Function.comp_apply] at h ⊢
    rw [h]
    congr 1
    ext j
    simp
  refine mem_thetaSpace.2 ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [key]
    exact hW _ ((mem_thetaSpace.1 hφ).1 _)
  · rw [key, (mem_thetaSpace.1 hφ).2 _ (hW' x hx)]
    ext i
    simp

theorem invPairAt_of_idempotent (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} {σ : F ≃+* F} {w v : GL (Fin n) F}
    (hgen : E ≤ Subgroup.closure ({conjAut n F w, conjAut n F v, fieldAut n F σ} :
      Set (MulAut (projectiveSL n F))))
    {e : Matrix (Fin n) (Fin n) F} (he : e * e = e) (he0 : e ≠ 0) (he1 : e ≠ 1)
    (heσ : e.map σ = e) (hew : (w : Matrix (Fin n) (Fin n) F) * e = e * w)
    (hev : (v : Matrix (Fin n) (Fin n) F) * e = e * v) : InvPairAt p E := by
  classical
  have : Finite (projectiveSL n F) := inferInstance
  set L := Matrix.toLin' e with hL
  have hLid : IsIdempotentElem L := by
    rw [IsIdempotentElem, hL, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  set W₁ := LinearMap.range L with hW₁
  set W₂ := LinearMap.ker L with hW₂
  have hc : IsCompl W₁ W₂ := LinearMap.IsIdempotentElem.isCompl hLid
  have hmem₁ : ∀ x, x ∈ W₁ ↔ ∃ y, e *ᵥ y = x := fun x => by
    rw [hW₁, LinearMap.mem_range]
    simp [hL, Matrix.toLin'_apply]
  have hmem₂ : ∀ x, x ∈ W₂ ↔ e *ᵥ x = 0 := fun x => by
    rw [hW₂, LinearMap.mem_ker, hL, Matrix.toLin'_apply]
  have hW₁0 : W₁ ≠ ⊥ := by
    rw [Ne, hW₁, LinearMap.range_eq_bot, hL, Matrix.toLin'.map_eq_zero_iff]
    exact he0
  have hW₂0 : W₂ ≠ ⊥ := by
    rw [Ne, hW₂, LinearMap.ker_eq_bot]
    intro hinj
    apply he1
    rw [Matrix.ext_iff_mulVec]
    intro u
    apply hinj
    simp only [hL, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he, Matrix.one_mulVec]
  have hstab : ∀ A : Matrix (Fin n) (Fin n) F, A * e = e * A →
      (∀ x ∈ W₁, A *ᵥ x ∈ W₁) ∧ ∀ x ∈ W₂, A *ᵥ x ∈ W₂ := by
    intro A hA
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, rfl⟩ := (hmem₁ x).1 hx
      exact (hmem₁ _).2 ⟨A *ᵥ y, by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]⟩
    · rw [hmem₂] at hx ⊢
      rw [Matrix.mulVec_mulVec, ← hA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hinvcomm : ∀ A : GL (Fin n) F, (A : Matrix (Fin n) (Fin n) F) * e = e * A →
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e =
        e * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    intro A hA
    calc ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e
        = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e *
            ((A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (e * A) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
      _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A * e) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [hA]
      _ = e * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have heσ' := map_symm_of_map σ heσ
  have hσ₁ : ∀ x ∈ W₁, σ ∘ x ∈ W₁ := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hmem₁ x).1 hx
    exact (hmem₁ _).2 ⟨σ ∘ y, mulVec_comp_of_map σ heσ y⟩
  have hσ₁' : ∀ x ∈ W₁, σ.symm ∘ x ∈ W₁ := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hmem₁ x).1 hx
    exact (hmem₁ _).2 ⟨σ.symm ∘ y, mulVec_comp_of_map σ.symm heσ' y⟩
  have hσ₂ : ∀ x ∈ W₂, σ ∘ x ∈ W₂ := by
    intro x hx
    rw [hmem₂] at hx ⊢
    rw [mulVec_comp_of_map σ heσ, hx]
    ext i
    simp
  have hσ₂' : ∀ x ∈ W₂, σ.symm ∘ x ∈ W₂ := by
    intro x hx
    rw [hmem₂] at hx ⊢
    rw [mulVec_comp_of_map σ.symm heσ', hx]
    ext i
    simp
  set U₁ := elationSubgroup W₁ with hU₁
  set U₂ := elationSubgroup W₂ with hU₂
  have hgenU : U₁ ⊔ U₂ = ⊤ :=
    eq_top_of_unip_isCompl hc hW₁0 hW₂0
      (fun g hg => Subgroup.mem_sup_left (mem_elationSubgroup_iff.2 hg))
      (fun g hg => Subgroup.mem_sup_right (mem_elationSubgroup_iff.2 hg))
  have hinv : ∀ W : Submodule F (Fin n → F),
      (∀ A : GL (Fin n) F, (A : Matrix (Fin n) (Fin n) F) * e = e * A →
        (∀ x ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ x ∈ W)) →
      (∀ x ∈ W, σ ∘ x ∈ W) → (∀ x ∈ W, σ.symm ∘ x ∈ W) →
      E ≤ stabSub ((elationSubgroup W).map (proj n F)) := by
    intro W hWA hWσ hWσ'
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    have hconj : ∀ A : GL (Fin n) F, (A : Matrix (Fin n) (Fin n) F) * e = e * A →
        conjAut n F A ∈ stabSub ((elationSubgroup W).map (proj n F)) := by
      intro A hA
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨slConjugation n F A g, mem_elationSubgroup_iff.2 ?_, (conjAut_proj A g).symm⟩
      have h1 := conjActionGL_mem_thetaSpace (hWA A hA) (hWA A⁻¹ (hinvcomm A hA))
        (mem_elationSubgroup_iff.1 hg)
      rw [conjActionGL_apply] at h1
      rw [coe_slConjugation]
      convert h1 using 1
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
    rintro φ (rfl | rfl | rfl)
    · exact hconj w hew
    · exact hconj v hev
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨Matrix.SpecialLinearGroup.map σ.toRingHom g, mem_elationSubgroup_iff.2 ?_,
        (fieldAut_proj σ g).symm⟩
      have h1 := map_mem_thetaSpace σ hWσ hWσ' (mem_elationSubgroup_iff.1 hg)
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      rw [Matrix.map_sub _ (fun a b => map_sub σ a b), Matrix.map_one _ (map_zero σ) (map_one σ)]
        at h1
      exact h1
  refine ⟨U₁.map (proj n F), U₂.map (proj n F),
    not_dvd_card_of_isPGroup_ringChar hp hpF ((isPGroup_elationSubgroup W₁).map _),
    not_dvd_card_of_isPGroup_ringChar hp hpF ((isPGroup_elationSubgroup W₂).map _),
    fun φ hφ => hinv W₁ (fun A hA => (hstab _ hA).1) hσ₁ hσ₁' hφ,
    fun φ hφ => hinv W₂ (fun A hA => (hstab _ hA).2) hσ₂ hσ₂' hφ, ?_⟩
  rw [← Subgroup.map_sup, hgenU, Subgroup.map_top_of_surjective _ (proj_surjective n F)]

end Idem

section Heis

variable {n p : ℕ} {F : Type} [Field F]

theorem vecMulVec_mul_self' {e₀ φ : Fin n → F} (hφe : φ ⬝ᵥ e₀ = 1) :
    vecMulVec e₀ φ * vecMulVec e₀ φ = vecMulVec e₀ φ := by
  rw [vecMulVec_mul_vecMulVec, hφe, one_smul]

theorem vecMulVec_mulVec_eq (e₀ φ u : Fin n → F) : vecMulVec e₀ φ *ᵥ u = (φ ⬝ᵥ u) • e₀ := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem pow_mul_eigProj_of_qcomm {W : Matrix (Fin n) (Fin n) F} {v : GL (Fin n) F} {μ : F}
    (hVW : (v : Matrix (Fin n) (Fin n) F) * W = μ • (W * v)) (ε : F) (i : ℕ) :
    ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * eigProj p W ε =
      eigProj p W (ε * μ⁻¹ ^ i) * ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Units.val_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      mul_eigProj_of_qcomm hVW, Matrix.mul_assoc]
    congr 2
    rw [pow_succ]
    ring

theorem eigProj_mul_inv_pow_of_qcomm {W : Matrix (Fin n) (Fin n) F} {v : GL (Fin n) F} {μ : F}
    (hVW : (v : Matrix (Fin n) (Fin n) F) * W = μ • (W * v)) (ε : F) (i : ℕ) :
    eigProj p W ε * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * eigProj p W (ε * μ⁻¹ ^ i) := by
  have h1 := pow_mul_eigProj_of_qcomm (p := p) hVW ε i
  have hvv : ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hvv' : ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one]
  calc eigProj p W ε * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * eigProj p W ε) *
            ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        rw [← Matrix.mul_assoc, hvv, Matrix.one_mul]
    _ = ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * eigProj p W (ε * μ⁻¹ ^ i) := by
        rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, hvv', Matrix.mul_one]

@[expose] noncomputable def heisIdem (p : ℕ) (v : GL (Fin n) F) (e₀ φ : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  ∑ i ∈ Finset.range p, ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
    ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)

structure HeisData (p : ℕ) (W : Matrix (Fin n) (Fin n) F) (v : GL (Fin n) F) (μ ε₀ : F)
    (e₀ φ : Fin n → F) : Prop where
  pF : (p : F) ≠ 0
  prime : p.Prime
  Wp : W ^ p = 1
  vp : ∃ c : Fˣ, v ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c
  mu : IsPrimitiveRoot μ p
  qcomm : (v : Matrix (Fin n) (Fin n) F) * W = μ • (W * v)
  eps : ε₀ ^ p = 1
  eps0 : ε₀ ≠ 0
  e0 : eigProj p W ε₀ *ᵥ e₀ = e₀
  phi : φ ᵥ* eigProj p W ε₀ = φ
  phie : φ ⬝ᵥ e₀ = 1

namespace HeisData

variable {W : Matrix (Fin n) (Fin n) F} {v : GL (Fin n) F} {μ ε₀ : F} {e₀ φ : Fin n → F}

theorem mu0 (hD : HeisData p W v μ ε₀ e₀ φ) : μ ≠ 0 := hD.mu.ne_zero hD.prime.ne_zero

theorem eta_pow (hD : HeisData p W v μ ε₀ e₀ φ) (i : ℕ) : (ε₀ * μ⁻¹ ^ i) ^ p = 1 := by
  rw [mul_pow, ← pow_mul, mul_comm i p, pow_mul, inv_pow, hD.mu.pow_eq_one, inv_one, one_pow,
    hD.eps, one_mul]

theorem eta_ne_zero (hD : HeisData p W v μ ε₀ e₀ φ) (i : ℕ) : ε₀ * μ⁻¹ ^ i ≠ 0 :=
  mul_ne_zero hD.eps0 (pow_ne_zero _ (inv_ne_zero hD.mu0))

theorem eta_inj (hD : HeisData p W v μ ε₀ e₀ φ) {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : ε₀ * μ⁻¹ ^ i = ε₀ * μ⁻¹ ^ j) : i = j :=
  hD.mu.inv.pow_inj hi hj (mul_left_cancel₀ hD.eps0 h)

theorem Q_mul_P (hD : HeisData p W v μ ε₀ e₀ φ) :
    vecMulVec e₀ φ * eigProj p W ε₀ = vecMulVec e₀ φ := by
  rw [vecMulVec_mul, hD.phi]

theorem P_mul_Q (hD : HeisData p W v μ ε₀ e₀ φ) :
    eigProj p W ε₀ * vecMulVec e₀ φ = vecMulVec e₀ φ := by
  rw [mul_vecMulVec, hD.e0]

theorem Qi_mul_P (hD : HeisData p W v μ ε₀ e₀ φ) (i : ℕ) :
    ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
        ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * eigProj p W (ε₀ * μ⁻¹ ^ i) =
      ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
        ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [Matrix.mul_assoc, ← eigProj_mul_inv_pow_of_qcomm hD.qcomm, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (vecMulVec e₀ φ), hD.Q_mul_P]

theorem P_mul_Qi (hD : HeisData p W v μ ε₀ e₀ φ) (i : ℕ) :
    eigProj p W (ε₀ * μ⁻¹ ^ i) * (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        vecMulVec e₀ φ * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
        ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← pow_mul_eigProj_of_qcomm hD.qcomm,
    Matrix.mul_assoc _ (eigProj p W ε₀), hD.P_mul_Q]

theorem Qi_mul_Qj (hD : HeisData p W v μ ε₀ e₀ φ) {i j : ℕ} (hi : i < p) (hj : j < p) :
    (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
        ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
      (((v ^ j : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
        ((v⁻¹ ^ j : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      if i = j then ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
        ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) else 0 := by
  split_ifs with h
  · subst h
    have hvv : ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    calc (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
          ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
          ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        = ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (vecMulVec e₀ φ *
            (((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * vecMulVec e₀ φ) *
            ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hvv, Matrix.mul_one, vecMulVec_mul_self' hD.phie]
  · rw [← hD.Qi_mul_P i, ← hD.P_mul_Qi j, Matrix.mul_assoc, ← Matrix.mul_assoc
      (eigProj p W (ε₀ * μ⁻¹ ^ i)), eigProj_mul_eigProj_of_ne hD.Wp (hD.eta_pow i) (hD.eta_pow j)
      (hD.eta_ne_zero i) (hD.eta_ne_zero j) (fun h' => h (hD.eta_inj hi hj h')),
      Matrix.zero_mul, Matrix.mul_zero]

theorem heisIdem_mul_self (hD : HeisData p W v μ ε₀ e₀ φ) :
    heisIdem p v e₀ φ * heisIdem p v e₀ φ = heisIdem p v e₀ φ := by
  classical
  unfold heisIdem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_congr rfl fun j hj => hD.Qi_mul_Qj (Finset.mem_range.1 hi)
    (Finset.mem_range.1 hj)]
  rw [Finset.sum_ite_eq, if_pos hi]

theorem W_mul_heisIdem (hD : HeisData p W v μ ε₀ e₀ φ) :
    W * heisIdem p v e₀ φ = heisIdem p v e₀ φ * W := by
  unfold heisIdem
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← hD.P_mul_Qi i, ← Matrix.mul_assoc, mul_eigProj hD.Wp (hD.eta_pow i)
    (hD.eta_ne_zero i), Matrix.smul_mul, hD.P_mul_Qi i]
  conv_rhs => rw [← hD.Qi_mul_P i, Matrix.mul_assoc, eigProj_mul hD.Wp (hD.eta_pow i)
    (hD.eta_ne_zero i), Matrix.mul_smul, hD.Qi_mul_P i]

theorem v_mul_heisIdem (hD : HeisData p W v μ ε₀ e₀ φ) :
    (v : Matrix (Fin n) (Fin n) F) * heisIdem p v e₀ φ = heisIdem p v e₀ φ * v := by
  obtain ⟨c, hc⟩ := hD.vp
  set Q := vecMulVec e₀ φ with hQ
  set T : ℕ → Matrix (Fin n) (Fin n) F := fun i => ((v ^ i : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F) * Q * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hT
  have hstep : ∀ i, (v : Matrix (Fin n) (Fin n) F) * T i = T (i + 1) * v := by
    intro i
    simp only [hT]
    have e1 : ((v ^ (i + 1) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (v : Matrix (Fin n) (Fin n) F) * ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [pow_succ', Units.val_mul]
    have e2 : ((v⁻¹ ^ (i + 1) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (v : Matrix (Fin n) (Fin n) F) = ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← Units.val_mul, pow_succ, mul_assoc, inv_mul_cancel, mul_one]
    calc (v : Matrix (Fin n) (Fin n) F) * (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          Q * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        = (v : Matrix (Fin n) (Fin n) F) * ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            Q * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc]
      _ = ((v ^ (i + 1) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Q *
            (((v⁻¹ ^ (i + 1) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (v : Matrix (Fin n) (Fin n) F)) := by rw [e1, e2]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hTp : T p = T 0 := by
    simp only [hT, pow_zero, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rw [inv_pow, hc, ← map_inv, scalarGL_coe_eq_smul, scalarGL_coe_eq_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ c.ne_zero, one_smul]
  show (v : Matrix (Fin n) (Fin n) F) * ∑ i ∈ Finset.range p, T i =
    (∑ i ∈ Finset.range p, T i) * v
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl fun i _ => hstep i]
  have h1 := Finset.sum_range_succ' (fun i => T i * v) p
  have h2 := Finset.sum_range_succ (fun i => T i * v) p
  rw [hTp] at h2
  exact add_right_cancel (h1.symm.trans h2)

theorem heisIdem_mul_P (hD : HeisData p W v μ ε₀ e₀ φ) :
    heisIdem p v e₀ φ * eigProj p W ε₀ = vecMulVec e₀ φ := by
  classical
  have hp0 : 0 < p := hD.prime.pos
  unfold heisIdem
  rw [Finset.sum_mul]
  have h0 : ∀ i ∈ Finset.range p, ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      vecMulVec e₀ φ * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        eigProj p W ε₀ = if i = 0 then vecMulVec e₀ φ else 0 := by
    intro i hi
    split_ifs with h
    · subst h
      simp [hD.Q_mul_P]
    · have h1 : eigProj p W ε₀ = eigProj p W (ε₀ * μ⁻¹ ^ 0) := by rw [pow_zero, mul_one]
      rw [← hD.Qi_mul_P i, Matrix.mul_assoc, h1, eigProj_mul_eigProj_of_ne hD.Wp (hD.eta_pow i)
        (hD.eta_pow 0) (hD.eta_ne_zero i) (hD.eta_ne_zero 0)
        (fun h' => h (hD.eta_inj (Finset.mem_range.1 hi) hp0 h')), Matrix.mul_zero]
  rw [Finset.sum_congr rfl h0, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hp0)]

theorem heisIdem_ne_zero (hD : HeisData p W v μ ε₀ e₀ φ) : heisIdem p v e₀ φ ≠ 0 := by
  intro h
  have h1 := hD.heisIdem_mul_P
  rw [h, Matrix.zero_mul] at h1
  have h2 := congrArg (fun M => M *ᵥ e₀) h1
  simp only [Matrix.zero_mulVec, vecMulVec_mulVec_eq, hD.phie, one_smul] at h2
  have h3 := hD.phie
  rw [← h2, dotProduct_zero] at h3
  exact zero_ne_one h3

theorem span_eq_top_of_heisIdem_eq_one (hD : HeisData p W v μ ε₀ e₀ φ)
    (h : heisIdem p v e₀ φ = 1) :
    Submodule.span F (Set.range fun i : Fin p =>
      ((v ^ (i : ℕ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ e₀) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro u
  have hu : u = heisIdem p v e₀ φ *ᵥ u := by rw [h, Matrix.one_mulVec]
  rw [hu]
  unfold heisIdem
  rw [Matrix.sum_mulVec, ← Fin.sum_univ_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec_eq, Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end HeisData

end Heis

section Irr

variable {n p : ℕ} {F : Type} [Field F]

theorem mul_inv_pow_of_qcomm {W : Matrix (Fin n) (Fin n) F} {v : GL (Fin n) F} {μ : F}
    (hμ0 : μ ≠ 0) (hVW : (v : Matrix (Fin n) (Fin n) F) * W = μ • (W * v)) (i : ℕ) :
    W * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      μ ^ i • (((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * W) := by
  have hvv : ((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * v = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hvv' : (v : Matrix (Fin n) (Fin n) F) * ((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : W * ((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      μ • (((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * W) := by
    calc W * ((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = ((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((v : Matrix (Fin n) (Fin n) F) * W) *
            ((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [← Matrix.mul_assoc, hvv, Matrix.one_mul]
      _ = μ • (((v⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * W) := by
          rw [hVW, Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          simp only [Matrix.mul_assoc, hvv', Matrix.mul_one]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, pow_succ]

theorem mul_pow_of_qcomm {W : Matrix (Fin n) (Fin n) F} {v : GL (Fin n) F} {μ : F}
    (hμ0 : μ ≠ 0) (hVW : (v : Matrix (Fin n) (Fin n) F) * W = μ • (W * v)) (i : ℕ) :
    W * ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      μ⁻¹ ^ i • (((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * W) := by
  have h1 : W * (v : Matrix (Fin n) (Fin n) F) = μ⁻¹ • ((v : Matrix (Fin n) (Fin n) F) * W) := by
    rw [hVW, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, pow_succ]

namespace HeisData

variable {W : Matrix (Fin n) (Fin n) F} {v : GL (Fin n) F} {μ ε₀ : F} {e₀ φ : Fin n → F}

theorem e0_ne_zero (hD : HeisData p W v μ ε₀ e₀ φ) : e₀ ≠ 0 := by
  rintro rfl
  have h := hD.phie
  rw [dotProduct_zero] at h
  exact zero_ne_one h

theorem W_e0 (hD : HeisData p W v μ ε₀ e₀ φ) : W *ᵥ e₀ = ε₀ • e₀ := by
  conv_lhs => rw [← hD.e0]
  rw [Matrix.mulVec_mulVec, mul_eigProj hD.Wp hD.eps hD.eps0, Matrix.smul_mulVec, hD.e0]

theorem eq_of_heisIdem_eq_one (hD : HeisData p W v μ ε₀ e₀ φ) (h : heisIdem p v e₀ φ = 1) :
    n = p := by
  have hspan := hD.span_eq_top_of_heisIdem_eq_one h
  set g : Fin p → Fin n → F := fun i =>
    ((v ^ (i : ℕ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ e₀ with hg
  have hli : LinearIndependent F g := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' W)
      (fun i : Fin p => ε₀ * μ⁻¹ ^ (i : ℕ)) (fun i j hij => Fin.ext (hD.eta_inj i.isLt j.isLt hij))
      g fun i => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    refine ⟨?_, ?_⟩
    · simp only [hg]
      rw [Matrix.mulVec_mulVec, mul_pow_of_qcomm hD.mu0 hD.qcomm, Matrix.smul_mulVec,
        ← Matrix.mulVec_mulVec, hD.W_e0, Matrix.mulVec_smul, smul_smul, mul_comm]
    · intro h0
      apply hD.e0_ne_zero
      have h1 := congrArg (fun u => ((v⁻¹ ^ (i : ℕ) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ u) h0
      simp only [hg, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
      rwa [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h1
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
  exact h1

end HeisData

theorem heisShiftMat_mulVec {p : ℕ} (u : Fin p → F) :
    heisShiftMat F p *ᵥ u = fun i => u (finRotate p i) := by
  classical
  ext i
  simp only [Matrix.mulVec, dotProduct, heisShiftMat_entry, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem heisShiftMat_mulVec_single {p : ℕ} (j : Fin p) :
    heisShiftMat F p *ᵥ Pi.single j 1 = Pi.single ((finRotate p).symm j) 1 := by
  classical
  rw [heisShiftMat_mulVec]
  ext i
  simp only [Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

theorem mulVec_single_eq_smul {p : ℕ} (M : Matrix (Fin p) (Fin p) F) (j : Fin p) (t : F) :
    M *ᵥ Pi.single j t = t • (M *ᵥ Pi.single j 1) := by
  classical
  have h : Pi.single j t = t • (Pi.single j 1 : Fin p → F) := by
    ext i
    simp [Pi.single_apply]
  rw [h, Matrix.mulVec_smul]

theorem exists_std_basis [Finite F] (hp : p.Prime) {W : Matrix (Fin p) (Fin p) F} {v : GL (Fin p) F} {μ : F}
    (hμ : IsPrimitiveRoot μ p) (hVW : (v : Matrix (Fin p) (Fin p) F) * W = μ • (W * v))
    {c : Fˣ} (hvp : v ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) c) {ε₀ : F} (hε₀0 : ε₀ ≠ 0)
    {e₀ : Fin p → F} (he₀0 : e₀ ≠ 0) (hWe₀ : W *ᵥ e₀ = ε₀ • e₀) {x : F} (hx : x ^ p = c)
    (σ : F ≃+* F) (hvσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) v = v)
    (he₀σ : σ ∘ e₀ = e₀) :
    ∃ A : Matrix (Fin p) (Fin p) F, IsUnit A.det ∧ W * A = A * (ε₀ • heisDiagMat μ) ∧
      (v : Matrix (Fin p) (Fin p) F) * A = A * (x • heisShiftMat F p) ∧
      A.map σ = A * heisDiagMat (σ x / x) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hμ0 : μ ≠ 0 := hμ.ne_zero hp.ne_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hx
    exact c.ne_zero hx.symm
  set f : Fin p → Fin p → F := fun j =>
    ((v⁻¹ ^ (j : ℕ) : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *ᵥ e₀ with hf
  set a : Fin p → Fin p → F := fun j => x ^ (j : ℕ) • f j with ha
  set A : Matrix (Fin p) (Fin p) F := Matrix.of fun r j => a j r with hA
  have hAcol : ∀ j, A *ᵥ Pi.single j 1 = a j := fun j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have hWf : ∀ j : Fin p, W *ᵥ f j = (ε₀ * μ ^ (j : ℕ)) • f j := by
    intro j
    simp only [hf]
    rw [Matrix.mulVec_mulVec, mul_inv_pow_of_qcomm hμ0 hVW, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hWe₀, Matrix.mulVec_smul, smul_smul, mul_comm]
  have hWa : ∀ j : Fin p, W *ᵥ a j = (ε₀ * μ ^ (j : ℕ)) • a j := by
    intro j
    simp only [ha]
    rw [Matrix.mulVec_smul, hWf, smul_comm]
  have hf0 : ∀ j : Fin p, f j ≠ 0 := by
    intro j h0
    apply he₀0
    have h1 := congrArg (fun u => ((v ^ (j : ℕ) : GL (Fin p) F) :
      Matrix (Fin p) (Fin p) F) *ᵥ u) h0
    simp only [hf, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
  have ha0 : ∀ j : Fin p, a j ≠ 0 := fun j => smul_ne_zero (pow_ne_zero _ hx0) (hf0 j)
  have hli : LinearIndependent F a := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' W)
      (fun j : Fin p => ε₀ * μ ^ (j : ℕ))
      (fun i j hij => Fin.ext (hμ.pow_inj i.isLt j.isLt (mul_left_cancel₀ hε₀0 hij))) a
      fun j => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact ⟨hWa j, ha0 j⟩
  have hAunit : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hvc : (v : Matrix (Fin p) (Fin p) F) =
      (c : F) • ((v⁻¹ ^ (p - 1) : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    have h1 : v = Matrix.GeneralLinearGroup.scalar (Fin p) c * v⁻¹ ^ (p - 1) := by
      have h2 : v ^ p = v * v ^ (p - 1) := by
        rw [← pow_succ']
        congr 1
        have := hp.pos
        omega
      calc v = v * v ^ (p - 1) * (v ^ (p - 1))⁻¹ := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin p) c * v⁻¹ ^ (p - 1) := by
          rw [← h2, hvp, inv_pow]
    conv_lhs => rw [h1]
    rw [Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
  have hvf : ∀ j : Fin p, (v : Matrix (Fin p) (Fin p) F) *ᵥ a j =
      x • a ((finRotate p).symm j) := by
    intro j
    by_cases hj : (j : ℕ) = 0
    · have hsymm : (((finRotate p).symm j : Fin p) : ℕ) = p - 1 := by
        have h1 : finRotate p ⟨p - 1, by have := hp.pos; omega⟩ = j := by
          apply Fin.ext
          rw [finRotate_val_mod, hj, show p - 1 + 1 = p by have := hp.pos; omega, Nat.mod_self]
        conv_lhs => rw [← h1]
        rw [Equiv.symm_apply_apply]
      simp only [ha, hf, hsymm, hj, pow_zero, Units.val_one, Matrix.one_mulVec, one_smul,
        smul_smul]
      rw [hvc, Matrix.smul_mulVec, ← pow_succ', show p - 1 + 1 = p by have := hp.pos; omega, hx]
    · have hsymm : (((finRotate p).symm j : Fin p) : ℕ) = (j : ℕ) - 1 := by
        have h1 : finRotate p ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ = j := by
          apply Fin.ext
          rw [finRotate_val_mod, show (j : ℕ) - 1 + 1 = j by omega, Nat.mod_eq_of_lt j.isLt]
        conv_lhs => rw [← h1]
        rw [Equiv.symm_apply_apply]
      have hv1 : (v : Matrix (Fin p) (Fin p) F) * ((v⁻¹ ^ (j : ℕ) : GL (Fin p) F) :
          Matrix (Fin p) (Fin p) F) = ((v⁻¹ ^ ((j : ℕ) - 1) : GL (Fin p) F) :
            Matrix (Fin p) (Fin p) F) := by
        rw [← Units.val_mul]
        congr 1
        conv_lhs => rw [show (j : ℕ) = ((j : ℕ) - 1) + 1 by omega]
        rw [pow_succ', ← mul_assoc, mul_inv_cancel, one_mul]
      simp only [ha, hf, hsymm, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hv1, smul_smul]
      congr 1
      rw [← pow_succ', show (j : ℕ) - 1 + 1 = j by omega]
  have hfσ : ∀ j : Fin p, σ ∘ f j = f j := by
    intro j
    have hcoe : ∀ g : GL (Fin p) F, ((Matrix.GeneralLinearGroup.map (σ : F →+* F) g :
        GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = (g : Matrix (Fin p) (Fin p) F).map σ := by
      intro g
      ext r l
      rw [Matrix.GeneralLinearGroup.map_apply]
      rfl
    have hM : (((v⁻¹ ^ (j : ℕ) : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)).map σ =
        ((v⁻¹ ^ (j : ℕ) : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      have h1 : Matrix.GeneralLinearGroup.map (σ : F →+* F) (v⁻¹ ^ (j : ℕ)) = v⁻¹ ^ (j : ℕ) := by
        rw [map_pow, map_inv, hvσ]
      rw [← hcoe, h1]
    simp only [hf]
    rw [← mulVec_comp_of_map σ hM, he₀σ]
  refine ⟨A, (Matrix.isUnit_iff_isUnit_det A).1 hAunit, ?_, ?_, ?_⟩
  · refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, hAcol, hWa, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      heisDiagMat, diagonal_mulVec_single, mul_one, Matrix.mulVec_smul, mulVec_single_eq_smul,
      hAcol]
    simp only [ha, smul_smul, mul_assoc]
  · refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, hAcol, hvf, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      heisShiftMat_mulVec_single, Matrix.mulVec_smul, hAcol]
  · refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec, heisDiagMat, diagonal_mulVec_single,
      mul_one, mulVec_single_eq_smul, hAcol]
    ext r
    simp only [Matrix.col_apply, Matrix.map_apply, hA, Matrix.of_apply, ha, Pi.smul_apply,
      smul_eq_mul, map_mul, map_pow]
    have h1 := congrFun (hfσ j) r
    simp only [Function.comp_apply] at h1
    rw [h1, div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hx0)]

end Irr

section Normal

variable {n : ℕ} {F : Type} [Field F]

theorem coe_GLmap (σ : F ≃+* F) (g : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.map (σ : F →+* F) g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F).map σ := by
  ext r l
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

theorem fieldAut_mul_conjAut (σ : F ≃+* F) (A : GL (Fin n) F) :
    fieldAut n F σ * conjAut n F A =
      conjAut n F (Matrix.GeneralLinearGroup.map (σ : F →+* F) A) * fieldAut n F σ := by
  have h1 := (standard_automorphism_transport (K := F) (n := n)).2.2.1 σ A
  rw [← h1]
  group

theorem diagSL_pow {p : ℕ} (hp : Odd p) {μ : F} (hμ : μ ^ p = 1) (s : ℕ) :
    diagSL (p := p) (ζ := μ ^ s) (by rw [← pow_mul, mul_comm, pow_mul, hμ, one_pow]) hp =
      (diagSL hμ hp) ^ s := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL, coe_diagSL, heisDiagMat, heisDiagMat,
    diagonal_pow]
  congr 1
  ext j
  simp only [Pi.pow_apply, ← pow_mul, mul_comm]

theorem closure_hyperLiftSet_of_heis_irr [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F} (hσ : orderOf σ = p)
    (hKk : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p)
    (hgen : TorusFourierGen (semilinearFixedSubfield σ) p)
    (hσout : ∀ B : GL (Fin p) F, fieldAut p F σ ≠ conjAut p F B)
    (hroot : ∀ b : F, b ≠ 0 → σ b = b → ∃ c : F, c ^ p = b)
    {E : Subgroup (MulAut (projectiveSL p F))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hσE : fieldAut p F σ ∈ E) {w v : GL (Fin p) F} (hwE : conjAut p F w ∈ E)
    (hvE : conjAut p F v ∈ E) (hvσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) v = v) {μ : F}
    (hμ : IsPrimitiveRoot μ p) (hμσ : σ μ = μ)
    (hVW : (v : Matrix (Fin p) (Fin p) F) * w = μ • ((w : Matrix (Fin p) (Fin p) F) * v))
    {c : Fˣ} (hvp : v ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) c) (hcσ : σ c = c)
    {ε₀ : F} (hε₀0 : ε₀ ≠ 0) {e₀ : Fin p → F} (he₀0 : e₀ ≠ 0)
    (hWe₀ : (w : Matrix (Fin p) (Fin p) F) *ᵥ e₀ = ε₀ • e₀) (he₀σ : σ ∘ e₀ = e₀) :
    Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨x, hx⟩ := hroot c c.ne_zero hcσ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hx
    exact c.ne_zero hx.symm
  obtain ⟨A, hAdet, hWA, hVA, hAσ⟩ := exists_std_basis hp hμ hVW hvp hε₀0 he₀0 hWe₀ hx σ hvσ
    he₀σ
  set AG : GL (Fin p) F := Matrix.nonsingInvUnit A hAdet with hAG
  have hAGc : (AG : Matrix (Fin p) (Fin p) F) = A := rfl
  have hAGi : ((AG⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = A⁻¹ := rfl
  have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hAdet
  set S := shiftSL F hodd with hSdef
  set D := diagSL hμ.pow_eq_one hodd with hDdef
  set h : MulAut (projectiveSL p F) := conjAut p F AG with hh
  set E₂ := E.map (MulAut.congr h.symm).toMonoidHom with hE₂
  have hcongr : ∀ φ : MulAut (projectiveSL p F), MulAut.congr h.symm φ = h⁻¹ * φ * h :=
    fun φ => rfl
  have hconj : ∀ g : GL (Fin p) F, MulAut.congr h.symm (conjAut p F g) =
      conjAut p F (AG⁻¹ * g * AG) := fun g => by
    rw [hcongr, hh, ← map_inv, ← map_mul, ← map_mul]
  have hwD : AG⁻¹ * w * AG = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 ε₀ hε₀0) *
      Matrix.SpecialLinearGroup.toGL D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAGi, hAGc, coe_scalarGL_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hDdef, coe_diagSL, Matrix.mul_assoc, hWA,
      ← Matrix.mul_assoc, hAinv, Matrix.one_mul, Units.val_mk0]
  have hDE₂ : conjAut p F (Matrix.SpecialLinearGroup.toGL D) ∈ E₂ := ⟨_, hwE, by
    show MulAut.congr h.symm _ = _
    rw [hconj, hwD, map_mul, conjAut_scalar, one_mul]⟩
  have hvS : AG⁻¹ * v * AG = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) *
      Matrix.SpecialLinearGroup.toGL S := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAGi, hAGc, coe_scalarGL_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hSdef, coe_shiftSL, Matrix.mul_assoc, hVA,
      ← Matrix.mul_assoc, hAinv, Matrix.one_mul, Units.val_mk0]
  have hSE₂ : conjAut p F (Matrix.SpecialLinearGroup.toGL S) ∈ E₂ := ⟨_, hvE, by
    show MulAut.congr h.symm _ = _
    rw [hconj, hvS, map_mul, conjAut_scalar, one_mul]⟩
  set ρ : F := σ x / x with hρ
  have hρp : ρ ^ p = 1 := by
    rw [hρ, div_pow, ← map_pow, hx, hcσ, div_self c.ne_zero]
  obtain ⟨s, -, hs⟩ := hμ.eq_pow_of_pow_eq_one hρp
  have hAσG : AG⁻¹ * Matrix.GeneralLinearGroup.map (σ : F →+* F) AG =
      Matrix.SpecialLinearGroup.toGL (diagSL hμ.pow_eq_one hodd) ^ s := by
    apply Units.ext
    rw [Units.val_mul, hAGi, coe_GLmap, hAGc, hAσ, ← Matrix.mul_assoc, hAinv, Matrix.one_mul,
      ← map_pow, ← diagSL_pow hodd hμ.pow_eq_one s, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_diagSL, hs]
  have hσE₂ : fieldAut p F σ ∈ E₂ := by
    have h1 : MulAut.congr h.symm (fieldAut p F σ) =
        conjAut p F (Matrix.SpecialLinearGroup.toGL D) ^ s * fieldAut p F σ := by
      rw [hcongr, hh, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc, ← map_inv, ← map_mul, hAσG,
        map_pow]
    have h2 : MulAut.congr h.symm (fieldAut p F σ) ∈ E₂ := ⟨_, hσE, rfl⟩
    rw [h1] at h2
    have h3 := E₂.mul_mem (E₂.inv_mem (E₂.pow_mem hDE₂ s)) h2
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h3
  have hE₂a : IsElemAbelian p E₂ := isElemAbelian_map_congr h.symm hE
  have hE₂c : Nat.card E₂ = p ^ 3 := (card_map_congr h.symm E).trans hc
  have htop := closure_hyperLiftSet_std hp hodd hE₂a hE₂c hσ hKk hgen hσout hσE₂ hμ hμσ hSE₂ hDE₂
  exact closure_hyperLiftSet_eq_top_of_congr h.symm htop

end Normal

section Dichotomy

variable {n : ℕ} {F : Type} [Field F]

theorem GLmap_scalar_of_fixed (σ : F ≃+* F) {u : Fˣ} (hu : σ u = u) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.GeneralLinearGroup.scalar (Fin n) u) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u := by
  apply Units.ext
  rw [coe_GLmap, scalarGL_coe_eq_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp [hu]

theorem fixed_of_GLmap_scalar (hn : 0 < n) (σ : F ≃+* F) {u : Fˣ}
    (h : Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.GeneralLinearGroup.scalar (Fin n) u) =
      Matrix.GeneralLinearGroup.scalar (Fin n) u) : σ (u : F) = u := by
  have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) h
  simp only [coe_GLmap, scalarGL_coe_eq_smul, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
  exact h1

theorem exists_rational_root_element [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) (σ : F ≃+* F)
    {X Y : GL (Fin n) F} (hX : conjAut n F X ∈ E) (hY : conjAut n F Y ∈ E)
    (hXσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) X = X)
    (hYσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) Y = Y) :
    ∃ (i j : ℕ) (z₀ : GL (Fin n) F), ¬ (p ∣ i ∧ p ∣ j) ∧
      conjAut n F z₀ = conjAut n F X ^ i * conjAut n F Y ^ j ∧ z₀ ^ p = 1 ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) z₀ = z₀ := by
  classical
  set k : Subfield F := semilinearFixedSubfield σ with hkdef
  have hn0 : 0 < n := by omega
  obtain ⟨cX, hcX⟩ := exists_scalarGL_pow hn hE hX
  obtain ⟨cY, hcY⟩ := exists_scalarGL_pow hn hE hY
  have hcXσ : σ (cX : F) = cX := fixed_of_GLmap_scalar hn0 σ (by rw [← hcX, map_pow, hXσ])
  have hcYσ : σ (cY : F) = cY := fixed_of_GLmap_scalar hn0 σ (by rw [← hcY, map_pow, hYσ])
  set kX : kˣ := Units.mk0 ⟨(cX : F), hcXσ⟩ (fun h => cX.ne_zero (congrArg Subtype.val h))
  set kY : kˣ := Units.mk0 ⟨(cY : F), hcYσ⟩ (fun h => cY.ne_zero (congrArg Subtype.val h))
  obtain ⟨i, j, hij, l, hl⟩ := exists_pow_mul_pow_eq_pow_of_cyclic hp kX kY
  have hl0 : ((l : k) : F) ≠ 0 := fun h => l.ne_zero (Subtype.ext h)
  set L : Fˣ := Units.mk0 ((l : k) : F) hl0 with hL
  have hLσ : σ (L : F) = L := (l : k).2
  have hcL : cX ^ i * cY ^ j = L ^ p := by
    apply Units.ext
    have h1 := congrArg (fun u : kˣ => ((u : k) : F)) hl
    simpa [kX, kY, L, Units.val_mul, Units.val_pow_eq_pow_val] using h1
  have hXi : conjAut n F (X ^ i) ∈ E := by
    rw [map_pow]
    exact E.pow_mem hX i
  have hYj : conjAut n F (Y ^ j) ∈ E := by
    rw [map_pow]
    exact E.pow_mem hY j
  obtain ⟨u, hu⟩ := exists_scalarGL_comm hn hE hXi hYj
  have hXip : (X ^ i) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) (cX ^ i) := by
    rw [← pow_mul, mul_comm, pow_mul, hcX, map_pow]
  have hYjp : (Y ^ j) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) (cY ^ j) := by
    rw [← pow_mul, mul_comm, pow_mul, hcY, map_pow]
  have hup : (Matrix.GeneralLinearGroup.scalar (Fin n) u) ^ p = 1 :=
    qcomm_pow_eq_one (A := X ^ i) (B := Y ^ j) (mul_scalarGL_comm u) (mul_scalarGL_comm _) hu hXip
  have hz : (X ^ i * Y ^ j) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) (L ^ p) := by
    rw [mul_pow_prime_eq hp hp2 (fun g => commute_scalarGL u g) hu hup, hXip, hYjp, ← map_mul,
      hcL]
  refine ⟨i, j, Matrix.GeneralLinearGroup.scalar (Fin n) L⁻¹ * (X ^ i * Y ^ j), hij, ?_, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul, map_mul, map_pow, map_pow]
  · rw [(commute_scalarGL L⁻¹ (X ^ i * Y ^ j)).mul_pow, hz, ← map_pow, ← map_mul, inv_pow,
      inv_mul_cancel, map_one]
  · rw [map_mul, map_mul, map_pow, map_pow, hXσ, hYσ, GLmap_scalar_of_fixed σ (by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hLσ])]

theorem dvd_card_fixed_sub_one [Finite F] {p : ℕ} (hp : p.Prime) {σ : F ≃+* F}
    (hKk : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p) (hpq : p ∣ Nat.card F - 1) :
    p ∣ Nat.card (semilinearFixedSubfield σ) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 < Nat.card (semilinearFixedSubfield σ) := Finite.one_lt_card
  have h1 : ((Nat.card F : ℕ) : ZMod p) = 1 := by
    have hK1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    have := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    rw [Nat.cast_sub hK1, Nat.cast_one, sub_eq_zero] at this
    exact this
  rw [hKk, Nat.cast_pow, ZMod.pow_card] at h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hk1.le, Nat.cast_one, h1, sub_self]

theorem exists_pow_eq_of_fixed [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : F ≃+* F}
    (hKk : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p) (hpq : p ∣ Nat.card F - 1)
    {b : F} (hb0 : b ≠ 0) (hbσ : σ b = b) : ∃ c : F, c ^ p = b := by
  classical
  set k : Subfield F := semilinearFixedSubfield σ with hkdef
  haveI : Fintype k := Fintype.ofFinite k
  have hpk := dvd_card_fixed_sub_one hp hKk hpq
  have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
  obtain ⟨hdiv, -⟩ := exists_prime_dvd_pow_sub_one hp hp2 hk2 hpk
  rw [← hKk] at hdiv
  obtain ⟨a, ha⟩ := hdiv
  have hb1 : b ^ (Nat.card k - 1) = 1 := by
    have h1 : (⟨b, hbσ⟩ : k) ^ (Fintype.card k - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one _ (fun h => hb0 (congrArg Subtype.val h))
    have h2 := congrArg Subtype.val h1
    rw [Nat.card_eq_fintype_card]
    simpa using h2
  refine (exists_pow_eq_of_pow_div_eq_one hpq hb0 ?_).imp fun c hc => hc.2
  rw [ha, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos, pow_mul, hb1, one_pow]

end Dichotomy

theorem seven_le_of_dvd_sub_one {a : ℕ} (h2 : 2 ≤ a) (h4 : a ≠ 4) (h : 3 ∣ a - 1) : 7 ≤ a := by
  obtain ⟨r, hr⟩ := h
  omega

section Dichotomy2

variable {n : ℕ} {F : Type} [Field F]

theorem invPairAt_or_closure_of_field [Finite F] {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) (hK : Nat.card F = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (h64 : n = p → p = 3 → Nat.card F ≠ 64) (hpF : (p : F) ≠ 0)
    (hpq : p ∣ Nat.card F - 1) {σ : F ≃+* F}
    (hσ : orderOf σ = p) (hKk : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p)
    (hσout : ∀ B : GL (Fin n) F, fieldAut n F σ ≠ conjAut n F B)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hσE : fieldAut n F σ ∈ E) {x : GL (Fin n) F} (hxE : conjAut n F x ∈ E)
    (hxσ : (x : Matrix (Fin n) (Fin n) F).map σ = x)
    (hxns : ∀ a : F, (x : Matrix (Fin n) (Fin n) F) ≠ a • 1) :
    InvPairAt p E ∨ Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  have : Finite (MulAut (projectiveSL n F)) := MulEquiv.finite_left
  set k : Subfield F := semilinearFixedSubfield σ with hkdef
  have hσD : fieldAut n F σ ∉ linearAutGroup n F := fieldAut_not_mem_linearAutGroup hσout
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hpk := dvd_card_fixed_sub_one hp hKk hpq
  have hroot : ∀ b : F, b ≠ 0 → σ b = b → ∃ c : F, c ^ p = b := fun b hb0 hbσ =>
    exists_pow_eq_of_fixed hp hp2 hKk hpq hb0 hbσ
  have hxσG : Matrix.GeneralLinearGroup.map (σ : F →+* F) x = x :=
    Units.ext (by rw [coe_GLmap, hxσ])
  have hx1 : conjAut n F x ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn x).1 h
    apply hxns u
    rw [← hu, scalarGL_coe_eq_smul]
  have hord : ∀ g ∈ E, g ≠ 1 → Nat.card (Subgroup.zpowers g) = p := fun g hg hg1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 g hg) hg1]
  have hBc := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.card_inf_linearAutGroup
    hℓ hf hn hK hp hp2 hσ hσD hE hc hσE
  obtain ⟨b, hbB, hbx⟩ : ∃ b ∈ E ⊓ linearAutGroup n F,
      b ∉ Subgroup.zpowers (conjAut n F x) := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ linearAutGroup n F ≤ Subgroup.zpowers (conjAut n F x) := fun b hb => hcon b hb
    have hfin : Finite (Subgroup.zpowers (conjAut n F x)) :=
      Nat.finite_of_card_ne_zero (by rw [hord _ hxE hx1]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hBc, hord _ hxE hx1] at h1
    nlinarith [hp.two_le]
  obtain ⟨Y, hY⟩ := mem_linearAutGroup_iff.1 hbB.2
  subst hY
  have hYcomm : fieldAut n F σ * conjAut n F Y = conjAut n F Y * fieldAut n F σ :=
    hcomm _ hσE _ hbB.1
  obtain ⟨u, hu⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.exists_map_eq_smul_of_commute hn
      hYcomm
  have hY0 : (Y : Matrix (Fin n) (Fin n) F) ≠ 0 := by
    intro h0
    have h1 : ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Y = 1 := Units.inv_mul Y
    rw [h0, Matrix.mul_zero] at h1
    exact zero_ne_one (congrFun (congrFun h1 ⟨0, hn0⟩) ⟨0, hn0⟩)
  obtain ⟨c', hc'0, hc'σ⟩ := exists_rational_smul hp hℓ hf hK σ hσ hY0 hu
  set y : GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc'0) * Y
    with hydef
  have hyc : conjAut n F y = conjAut n F Y := by rw [hydef, map_mul, conjAut_scalar, one_mul]
  have hyσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) y = y := by
    apply Units.ext
    rw [coe_GLmap, hydef, coe_scalarGL_mul, Units.val_mk0]
    exact hc'σ
  have hyE : conjAut n F y ∈ E := hyc ▸ hbB.1
  have hyx : conjAut n F y ∉ Subgroup.zpowers (conjAut n F x) := hyc ▸ hbx
  obtain ⟨i, j, w, hij, hwc, hwp, hwσ⟩ :=
    exists_rational_root_element hn hp hp2 hE σ hxE hyE hxσG hyσ
  have hwE : conjAut n F w ∈ E := by
    rw [hwc]
    exact E.mul_mem (E.pow_mem hxE i) (E.pow_mem hyE j)
  have hy1 : conjAut n F y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : conjAut n F x ∉ Subgroup.zpowers (conjAut n F y) := by
    intro h
    apply hyx
    have heq : Subgroup.zpowers (conjAut n F x) = Subgroup.zpowers (conjAut n F y) := by
      haveI : Finite (Subgroup.zpowers (conjAut n F y)) :=
        Nat.finite_of_card_ne_zero (by rw [hord _ hyE hy1]; exact hp.ne_zero)
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h)
        (by rw [hord _ hyE hy1, hord _ hxE hx1])
    rw [heq]
    exact Subgroup.mem_zpowers _
  have hw1 : conjAut n F w ≠ 1 := by
    rw [hwc, hcomm _ (E.pow_mem hxE i) _ (E.pow_mem hyE j)]
    exact pow_mul_pow_ne_one_of_indep hp (hE.2 _ hyE) (hE.2 _ hxE) hx1 (fun h => hxy
      ((Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h)
        (by haveI : Finite (Subgroup.zpowers (conjAut n F x)) :=
              Nat.finite_of_card_ne_zero (by rw [hord _ hxE hx1]; exact hp.ne_zero)
            rw [hord _ hxE hx1, hord _ hyE hy1])) ▸ Subgroup.mem_zpowers _))
      (fun h => hij ⟨h.2, h.1⟩)
  obtain ⟨v, hvE, hvσ, hvw⟩ : ∃ v : GL (Fin n) F, conjAut n F v ∈ E ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) v = v ∧
      conjAut n F v ∉ Subgroup.zpowers (conjAut n F w) := by
    by_cases hxw : conjAut n F x ∈ Subgroup.zpowers (conjAut n F w)
    · refine ⟨y, hyE, hyσ, fun hyw => hyx ?_⟩
      have heq : Subgroup.zpowers (conjAut n F x) = Subgroup.zpowers (conjAut n F w) := by
        haveI : Finite (Subgroup.zpowers (conjAut n F w)) :=
          Nat.finite_of_card_ne_zero (by rw [hord _ hwE hw1]; exact hp.ne_zero)
        exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxw)
          (by rw [hord _ hwE hw1, hord _ hxE hx1])
      rw [heq]
      exact hyw
    · exact ⟨x, hxE, hxσG, hxw⟩
  have hgen : E ≤ Subgroup.closure ({conjAut n F w, conjAut n F v, fieldAut n F σ} :
      Set (MulAut (projectiveSL n F))) :=
    le_closure_triple_of_independent hp hc hwE hvE hσE (hE.2 _ hwE) hw1 hvw (fun h => hσD
      ((Subgroup.closure_le _).2 (by
        rintro _ (rfl | rfl)
        exacts [conjAut_mem_linearAutGroup _, conjAut_mem_linearAutGroup _]) h))
  obtain ⟨μu, hμu⟩ := exists_scalarGL_comm hn hE hwE hvE
  set μ : F := (μu : F) with hμdef
  have hVW : (v : Matrix (Fin n) (Fin n) F) * w = μ • ((w : Matrix (Fin n) (Fin n) F) * v) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.coe_eq_smul_of_eq_scalar_mul hμu
  have hμp : μ ^ p = 1 := by
    have h1 := qcomm_pow_eq_one (A := w) (B := v) (mul_scalarGL_comm μu) (fun g => by simp)
      hμu hwp
    rw [← map_pow] at h1
    have h2 : μu ^ p = 1 :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.scalarGL_injective hn0
        (by rw [h1, map_one])
    rw [hμdef, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  set W : Matrix (Fin n) (Fin n) F := (w : Matrix (Fin n) (Fin n) F) with hWdef
  have hWp : W ^ p = 1 := by rw [hWdef, ← Units.val_pow_eq_pow_val, hwp, Units.val_one]
  have hWσ : W.map σ = W := by rw [hWdef, ← coe_GLmap, hwσ]
  have hVσ : (v : Matrix (Fin n) (Fin n) F).map σ = v := by rw [← coe_GLmap, hvσ]
  have hWns : ∀ a : F, W ≠ a • 1 := fun a ha => hw1 (by
    obtain ⟨u, hu⟩ := exists_scalarGL_of_gl_coe_eq_smul hn0 ha
    rw [← hu, conjAut_scalar])
  have hμσ : σ μ = μ := by
    have h1 : ((v : Matrix (Fin n) (Fin n) F) * W).map σ =
        (μ • (W * (v : Matrix (Fin n) (Fin n) F))).map σ := by rw [hVW]
    rw [Matrix.map_mul, hVσ, hWσ, hVW, Matrix.map_smul' _ _ _ (fun a b => map_mul σ a b),
      Matrix.map_mul, hVσ, hWσ] at h1
    have h2 : (σ μ - μ) • (W * (v : Matrix (Fin n) (Fin n) F)) = 0 := by
      rw [sub_smul, ← h1, sub_self]
    have hWv : W * (v : Matrix (Fin n) (Fin n) F) ≠ 0 := by
      rw [hWdef, ← Units.val_mul]
      intro h0
      have h3 := Units.inv_mul (w * v)
      rw [h0, Matrix.mul_zero] at h3
      exact zero_ne_one (congrFun (congrFun h3 ⟨0, hn0⟩) ⟨0, hn0⟩)
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hWv)
  obtain ⟨ζk, hζk⟩ := CFSG.RankThree.PartOne.CTP.exists_isPrimitiveRoot_of_dvd_natCard_sub_one
    (K := k) hpk
  have hζ₀ : IsPrimitiveRoot (ζk : F) p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := k.subtype) Subtype.val_injective).2 hζk
  have hrootσ : ∀ ε : F, ε ^ p = 1 → σ ε = ε := by
    intro ε hε
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨m, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hε
    rw [map_pow]
    exact congrArg (· ^ m) ζk.2
  have hexP : ∀ {lam : F}, IsPrimitiveRoot lam p →
      ∃ i₀ ∈ Finset.range p, eigProj p W (1 * lam ^ i₀) ≠ 0 := by
    intro lam hlam
    by_contra hcon
    push Not at hcon
    have h1 := sum_eigProj (W := W) hpF hlam one_ne_zero
    rw [Finset.sum_eq_zero hcon] at h1
    exact zero_ne_one h1
  by_cases hμ1 : μ = 1
  ·
    left
    obtain ⟨i₀, -, hP0⟩ := hexP hζ₀
    set ε := 1 * (ζk : F) ^ i₀ with hε
    have hεp : ε ^ p = 1 := by rw [hε, one_mul, ← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one,
      one_pow]
    have hε0 : ε ≠ 0 := by rw [hε, one_mul]; exact pow_ne_zero _ (hζ₀.ne_zero hp.ne_zero)
    have hP1 : eigProj p W ε ≠ 1 := fun h => hWns ε (by
      rw [← Matrix.mul_one W, ← h, mul_eigProj hWp hεp hε0, h])
    refine invPairAt_of_idempotent hn hp hpF hgen (eigProj_mul_self hWp hpF hεp hε0) hP0 hP1
      (eigProj_map σ hWσ (hrootσ ε hεp)) (eigProj_mul_comm W ε).symm ?_
    have h1 := mul_eigProj_of_qcomm (p := p) hVW ε
    rwa [hμ1, inv_one, mul_one] at h1
  ·
    have hμ : IsPrimitiveRoot μ p := isPrimitiveRoot_of_pow_eq_one_ne_one hp hμp hμ1
    obtain ⟨i₀, -, hP0⟩ := hexP hμ
    set ε₀ := 1 * μ ^ i₀ with hε₀
    have hε₀p : ε₀ ^ p = 1 := by rw [hε₀, one_mul, ← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one,
      one_pow]
    have hε₀0 : ε₀ ≠ 0 := by rw [hε₀, one_mul]; exact pow_ne_zero _ (hμ.ne_zero hp.ne_zero)
    set P := eigProj p W ε₀ with hPdef
    have hPP : P * P = P := eigProj_mul_self hWp hpF hε₀p hε₀0
    have hPσ : P.map σ = P := eigProj_map σ hWσ (hrootσ ε₀ hε₀p)
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, P *ᵥ Pi.single j₀ 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hP0 (Matrix.ext_of_mulVec_single fun j => by rw [hcon j, Matrix.zero_mulVec])
    set e₀ := P *ᵥ Pi.single j₀ 1 with he₀
    obtain ⟨i₁, hi₁⟩ : ∃ i₁, e₀ i₁ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hj₀ (funext hcon)
    set φ : Fin n → F := (e₀ i₁)⁻¹ • P i₁ with hφ
    have hPe₀ : P *ᵥ e₀ = e₀ := by rw [he₀, Matrix.mulVec_mulVec, hPP]
    have hD : HeisData p W v μ ε₀ e₀ φ :=
      { pF := hpF, prime := hp, Wp := hWp, vp := exists_scalarGL_pow hn hE hvE, mu := hμ,
        qcomm := hVW, eps := hε₀p, eps0 := hε₀0, e0 := hPe₀
        phi := by
          rw [hφ, Matrix.smul_vecMul]
          congr 1
          ext b
          show (P i₁ ᵥ* P) b = P i₁ b
          have h1 : (P i₁ ᵥ* P) b = (P * P) i₁ b := rfl
          rw [h1, hPP]
        phie := by
          rw [hφ, smul_dotProduct, smul_eq_mul]
          have h1 : P i₁ ⬝ᵥ e₀ = e₀ i₁ := by
            conv_rhs => rw [← hPe₀]
            rfl
          rw [h1, inv_mul_cancel₀ hi₁] }
    have he₀σ : σ ∘ e₀ = e₀ := by
      rw [he₀, ← mulVec_comp_of_map σ hPσ]
      congr 1
      ext l
      simp [Pi.single_apply, apply_ite]
    by_cases hΨ : heisIdem p v e₀ φ = 1
    · right
      have hnp : n = p := hD.eq_of_heisIdem_eq_one hΨ
      have h64' := h64 hnp
      subst hnp
      obtain ⟨cv, hcv⟩ := exists_scalarGL_pow hn hE hvE
      have hcvσ : σ (cv : F) = cv := fixed_of_GLmap_scalar hn0 σ (by rw [← hcv, map_pow, hvσ])
      have hgen : TorusFourierGen (semilinearFixedSubfield σ) n := by
        by_cases hp5 : 5 ≤ n
        · exact torusFourierGen_of_prime hp5
        · have hn3 : n = 3 := by
            have := three_le_of_odd_prime hp (hp.odd_of_ne_two hp2)
            rcases (show n = 3 ∨ n = 4 by omega) with h | h
            · exact h
            · exact absurd (h ▸ hp) (by norm_num)
          subst hn3
          have hk64' : Nat.card (semilinearFixedSubfield σ) ≠ 4 := fun h4 =>
            h64' rfl (by rw [hKk, h4]; norm_num)
          exact torusFourierGen_three (seven_le_of_dvd_sub_one Finite.one_lt_card hk64' hpk)
      exact closure_hyperLiftSet_of_heis_irr hp hp2 hσ hKk hgen hσout hroot hE hc hσE hwE hvE hvσ
        hμ hμσ hVW hcv hcvσ hε₀0 hD.e0_ne_zero hD.W_e0 he₀σ
    · left
      have hΨσ : (heisIdem p v e₀ φ).map σ = heisIdem p v e₀ φ := by
        have hφσ : σ ∘ φ = φ := by
          ext b
          simp only [hφ, Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
          rw [show σ (e₀ i₁) = e₀ i₁ from congrFun he₀σ i₁,
            show σ (P i₁ b) = P i₁ b from congrFun (congrFun hPσ i₁) b]
        have hQσ : (vecMulVec e₀ φ).map σ = vecMulVec e₀ φ := by
          ext a b
          simp only [Matrix.map_apply, vecMulVec_apply, map_mul]
          rw [show σ (e₀ a) = e₀ a from congrFun he₀σ a, show σ (φ b) = φ b from congrFun hφσ b]
        have hpowσ : ∀ g : GL (Fin n) F, Matrix.GeneralLinearGroup.map (σ : F →+* F) g = g →
            (g : Matrix (Fin n) (Fin n) F).map σ = g := fun g hg => by rw [← coe_GLmap, hg]
        unfold heisIdem
        change (σ : F →+* F).mapMatrix (∑ i ∈ Finset.range p,
          ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * vecMulVec e₀ φ *
            ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul]
        change ((v ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ *
          (vecMulVec e₀ φ).map σ * ((v⁻¹ ^ i : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ = _
        rw [hpowσ _ (by rw [map_pow, hvσ]), hpowσ _ (by rw [map_pow, map_inv, hvσ]), hQσ]
      exact invPairAt_of_idempotent hn hp hpF hgen hD.heisIdem_mul_self hD.heisIdem_ne_zero hΨ
        hΨσ hD.W_mul_heisIdem hD.v_mul_heisIdem

end Dichotomy2

section Wrapper

variable {n : ℕ} {F : Type} [Field F]

theorem invPairAt_or_closure_hyperLiftSet [Finite F] {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) (hK : Nat.card F = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (h64 : n = p → p = 3 → Nat.card F ≠ 64) (hpℓ : p ≠ ℓ)
    (hpq : p ∣ Nat.card F - 1)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hout : ¬ E ≤ linearAutGroup n F) :
    InvPairAt p E ∨ Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut (projectiveSL n F)) := MulEquiv.finite_left
  haveI : CharP F ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  have hpF : (p : F) ≠ 0 := by
    intro h
    have h1 := (CharP.cast_eq_zero_iff F ℓ p).1 h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h1).symm
  obtain ⟨a0, ha0E, ha0D⟩ : ∃ a0 ∈ E, a0 ∉ linearAutGroup n F := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have ha01 : a0 ≠ 1 := fun h => ha0D (h ▸ one_mem _)
  have hord : orderOf a0 = p := orderOf_eq_prime (hE.2 a0 ha0E) ha01
  obtain ⟨b0, hb0E, hb0⟩ : ∃ b0 ∈ E, b0 ∉ Subgroup.zpowers a0 := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers a0 := hcon
    have hfin : Finite (Subgroup.zpowers a0) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hc, Nat.card_zpowers, hord] at h1
    have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  set P := Subgroup.closure ({a0, b0} : Set (MulAut (projectiveSL n F))) with hPdef
  have hPE : P ≤ E := closure_pair_le ha0E hb0E
  have hPa : IsElemAbelian p P := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hPE hx)⟩
    have h := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, hPE a.2⟩ : E) ⟨b, hPE b.2⟩)
    exact h
  have hPc : Nat.card P = p ^ 2 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.relIndex_closure_pair_of_indep
      hp hE hc ha0E hb0E ha01 hb0).1
  have hPout : ¬ P ≤ linearAutGroup n F := fun h => ha0D (h (mem_closure_pair_left _ _))
  obtain ⟨h, σ, x, c, hσ, hKk, hσout, hσP, hxP, hxσ, hxns, -, -⟩ :=
    exists_field_normal_form hℓ hf hn hK hp hp2 hpℓ hPa hPc hPout
  set E₁ := E.map (MulAut.congr h⁻¹).toMonoidHom with hE₁
  have hσE₁ : fieldAut n F σ ∈ E₁ := Subgroup.map_mono hPE hσP
  have hxE₁ : conjAut n F x ∈ E₁ := Subgroup.map_mono hPE hxP
  have hE₁a : IsElemAbelian p E₁ := isElemAbelian_map_congr h⁻¹ hE
  have hE₁c : Nat.card E₁ = p ^ 3 := (card_map_congr h⁻¹ E).trans hc
  rcases invPairAt_or_closure_of_field hℓ hf hn hK hp hp2 h64 hpF hpq hσ hKk hσout hE₁a hE₁c hσE₁
    hxE₁ hxσ hxns with h1 | h1
  · exact Or.inl (invPairAt_of_congr h⁻¹ h1)
  · exact Or.inr (closure_hyperLiftSet_eq_top_of_congr h⁻¹ h1)

end Wrapper

end CFSG.LieType.SeitzGeneration.QuasiHigh3
