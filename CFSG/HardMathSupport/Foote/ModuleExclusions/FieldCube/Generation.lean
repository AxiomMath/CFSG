module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Arith
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

set_option linter.unusedSectionVars false

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification
open scoped MatrixGroups

theorem exists_hyperplane_of_orbit_le {G α : Type*} [Group G] [MulAction G α] (B : Subgroup G)
    [Finite B] {s : ℕ} (hs : 1 ≤ s) (hcard : Nat.card B = 3 ^ s) (x : α)
    (horb : (MulAction.orbit B x).ncard ≤ 3) :
    ∃ H : Subgroup G, H ≤ B ∧ H.relIndex B = 3 ∧ ∀ b ∈ H, b • x = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set St : Subgroup B := MulAction.stabilizer B x with hSt
  have hidx : St.index = (MulAction.orbit B x).ncard := MulAction.index_stabilizer B x
  have hdvd : St.index ∣ 3 ^ s := hcard ▸ Subgroup.index_dvd_card St
  obtain ⟨t, hts, ht⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have ht1 : t ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrel : ∀ K : Subgroup B, (K.map B.subtype).relIndex B = K.index := fun K => by
    rw [Subgroup.relIndex]
    congr 1
    ext b
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hle : ∀ K : Subgroup B, K.map B.subtype ≤ B := fun K => Subgroup.map_subtype_le K
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht1 with h0 | h1
  ·
    subst h0
    have hSt1 : St = ⊤ := Subgroup.index_eq_one.1 (by simpa using ht)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 3 (n := s - 1)
      (by rw [hcard]; exact pow_dvd_pow 3 (by omega))
    refine ⟨K.map B.subtype, hle K, ?_, ?_⟩
    · rw [hrel]
      have := Subgroup.card_mul_index K
      rw [hK, hcard, show s = (s - 1) + 1 by omega, pow_succ] at this
      have h3pos : 0 < 3 ^ (s - 1) := by positivity
      have h2 : 3 ^ (s - 1) * K.index = 3 ^ (s - 1) * 3 := by
        rw [show s - 1 + 1 - 1 = s - 1 by omega] at this
        simpa [show s - 1 + 1 - 1 = s - 1 by omega] using this
      exact Nat.eq_of_mul_eq_mul_left h3pos h2
    · rintro b ⟨b', hb', rfl⟩
      have : b' ∈ St := by rw [hSt1]; trivial
      exact this
  · refine ⟨St.map B.subtype, hle St, ?_, ?_⟩
    · rw [hrel, ht, h1]; norm_num
    · rintro b ⟨b', hb', rfl⟩
      exact hb'

section PSL3

variable {F : Type} [Field F]

@[expose] def diagGL (d : Fin 3 → Fˣ) : GL (Fin 3) F where
  val := diagonal fun i => (d i : F)
  inv := diagonal fun i => (((d i)⁻¹ : Fˣ) : F)
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp

theorem coe_diagGL (d : Fin 3 → Fˣ) :
    ((diagGL d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal fun i => (d i : F) := rfl

theorem coe_diagGL_inv (d : Fin 3 → Fˣ) :
    (((diagGL d)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal fun i => (((d i)⁻¹ : Fˣ) : F) := rfl

@[expose] def tbar {i j : Fin 3} (hij : i ≠ j) (c : F) : projectiveSL 3 F :=
  proj 3 F (SpecialLinearGroup.transvection hij c)

theorem tbar_zero {i j : Fin 3} (hij : i ≠ j) : tbar hij (0 : F) = 1 := by
  unfold tbar
  have : SpecialLinearGroup.transvection hij (0 : F) = 1 := by
    apply Subtype.ext
    simp
  rw [this, map_one]

theorem tbar_add {i j : Fin 3} (hij : i ≠ j) (c d : F) :
    tbar hij (c + d) = tbar hij c * tbar hij d := by
  unfold tbar
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  have := Matrix.transvection_mul_transvection_same i j hij c d
  simpa [CFSG.LinearGroups.coe_transvection, Matrix.transvection] using this.symm

theorem diag_conj_transvection' (v : Fin 3 → F) (hv : ∀ i, v i ≠ 0) (a b : Fin 3) (t : F) :
    diagonal v * Matrix.transvection a b t * diagonal (fun i => (v i)⁻¹) =
      Matrix.transvection a b (v a * t * (v b)⁻¹) := by
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.transvection, Matrix.transvection, Matrix.add_apply,
    Matrix.add_apply, mul_add, add_mul]
  congr 1
  · by_cases hij : i = j
    · subst hij
      rw [one_apply_eq, mul_one, mul_inv_cancel₀ (hv i)]
    · rw [one_apply_ne hij, mul_zero, zero_mul]
  · rw [single_apply, single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp [mul_assoc]
    · simp

theorem conjAut_diagGL_tbar (d : Fin 3 → Fˣ) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    conjAut 3 F (diagGL d) (tbar hij c) = tbar hij ((d i : F) * c * ((d j)⁻¹ : Fˣ)) := by
  unfold tbar
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv]
  have := diag_conj_transvection' (fun k => (d k : F)) (fun k => (d k).ne_zero)
    i j c
  simpa [CFSG.LinearGroups.coe_transvection, Matrix.transvection, Units.val_inv_eq_inv_val]
    using this

theorem fieldAut_tbar (σ : F ≃+* F) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    fieldAut 3 F σ (tbar hij c) = tbar hij (σ c) := by
  unfold tbar
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  simp [CFSG.LinearGroups.coe_transvection]

theorem tbar_injective {i j : Fin 3} (hij : i ≠ j) : Function.Injective (tbar (F := F) hij) := by
  intro c c' h
  unfold tbar at h
  obtain ⟨l, -, hl⟩ := proj_eq_proj_iff.1 h
  rw [SpecialLinearGroup.transvection_inv] at hl
  have hl2 : (1 + single i j (-c)) * (1 + single i j c') = scalar (Fin 3) (l : F) := hl
  have h1 := Matrix.transvection_mul_transvection_same i j hij (-c) c'
  have h2 : (1 + single i j (-c)) * (1 + single i j c') = 1 + single i j (-c + c') := by
    simpa [Matrix.transvection] using h1
  rw [h2] at hl2
  have h3 := congrFun (congrFun hl2 i) j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] at h3
  linear_combination -h3


theorem ncard_cube_roots_le : {μ : F | μ ^ 3 = 1}.ncard ≤ 3 := by
  classical
  have hsub : {μ : F | μ ^ 3 = 1} ⊆ ((Polynomial.nthRootsFinset 3 (1 : F) : Finset F) : Set F) := by
    intro μ hμ
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (by norm_num)]
    exact hμ
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  rw [Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)

theorem conjAut_diagGL_pow_tbar (d : Fin 3 → Fˣ) {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (c : F) :
    (conjAut 3 F (diagGL d) ^ n) (tbar hij c) =
      tbar hij (((d i : F) * ((d j)⁻¹ : Fˣ)) ^ n * c) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, conjAut_diagGL_tbar, ih, pow_succ]
    congr 1
    ring

theorem cube_eq_one_of_conjAut_pow {d : Fin 3 → Fˣ} {i j : Fin 3} (hij : i ≠ j)
    (h : conjAut 3 F (diagGL d) ^ 3 = 1) : ((d i : F) * ((d j)⁻¹ : Fˣ)) ^ 3 = 1 := by
  have h1 := conjAut_diagGL_pow_tbar d hij 3 1
  rw [h, MulAut.one_apply, mul_one] at h1
  exact (tbar_injective hij h1).symm

end PSL3

section Gen

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

structure SplitData (σ : F ≃+* F) (A B : Subgroup (MulAut (projectiveSL 3 F))) : Prop where
  A3 : ∀ a ∈ A, a ^ 3 = 1
  Ad : ∀ a ∈ A, ∃ d : Fin 3 → Fˣ, a = conjAut 3 F (diagGL d)
  Bf : ∀ b ∈ B, ∃ k : ℕ, ∃ a ∈ A, b = fieldAut 3 F σ ^ k * a

omit [Finite F] in
theorem pow_apply_of_fixed {x : F} (hx : σ x = x) (k : ℕ) : (σ ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, hx]

theorem SplitData.act_tbar {A B : Subgroup (MulAut (projectiveSL 3 F))} (h : SplitData σ A B)
    {i j : Fin 3} (hij : i ≠ j) {c : F} (hc : σ c = c) {b : MulAut (projectiveSL 3 F)}
    (hb : b ∈ B) : ∃ μ : F, μ ^ 3 = 1 ∧ b (tbar hij c) = tbar hij (μ * c) := by
  obtain ⟨k, a, ha, rfl⟩ := h.Bf b hb
  obtain ⟨d, rfl⟩ := h.Ad a ha
  have hl := cube_eq_one_of_conjAut_pow hij (h.A3 _ ha)
  refine ⟨(σ ^ k) ((d i : F) * ((d j)⁻¹ : Fˣ)), ?_, ?_⟩
  · rw [← map_pow, hl, map_one]
  · rw [MulAut.mul_apply, conjAut_diagGL_tbar, ← map_pow, fieldAut_tbar]
    congr 1
    rw [map_mul, map_mul, map_mul, pow_apply_of_fixed hc]
    ring

theorem SplitData.ncard_orbit_tbar {A B : Subgroup (MulAut (projectiveSL 3 F))}
    (h : SplitData σ A B) {i j : Fin 3} (hij : i ≠ j) {c : F} (hc : σ c = c) :
    (MulAction.orbit B (tbar hij c)).ncard ≤ 3 := by
  classical
  have hsub : MulAction.orbit B (tbar hij c) ⊆
      (fun μ : F => tbar hij (μ * c)) '' {μ : F | μ ^ 3 = 1} := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨μ, hμ, hb⟩ := h.act_tbar hij hc b.2
    exact ⟨μ, hμ, hb.symm⟩
  refine (Set.ncard_le_ncard hsub (Set.Finite.image _ (Set.toFinite _))).trans ?_
  exact (Set.ncard_image_le (Set.toFinite _)).trans ncard_cube_roots_le

theorem conjAut_diagGL_proj_diag (d : Fin 3 → Fˣ) (D : SL(3, F))
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    conjAut 3 F (diagGL d) (proj 3 F D) = proj 3 F D := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij
    simp [mul_comm, mul_assoc]
  · rw [hD i j hij]; simp

theorem SplitData.act_diag {A B : Subgroup (MulAut (projectiveSL 3 F))} (h : SplitData σ A B)
    (D : SL(3, F)) (hD : ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) F) i j = 0)
    {b : MulAut (projectiveSL 3 F)} (hb : b ∈ B) :
    ∃ k : ℕ, b (proj 3 F D) = (fieldAut 3 F σ ^ k) (proj 3 F D) := by
  obtain ⟨k, a, ha, rfl⟩ := h.Bf b hb
  obtain ⟨d, rfl⟩ := h.Ad a ha
  exact ⟨k, by rw [MulAut.mul_apply, conjAut_diagGL_proj_diag d D hD]⟩

theorem SplitData.ncard_orbit_diag {A B : Subgroup (MulAut (projectiveSL 3 F))}
    (h : SplitData σ A B) (hσ : σ ^ 3 = 1) (D : SL(3, F))
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    (MulAction.orbit B (proj 3 F D)).ncard ≤ 3 := by
  classical
  have hf3 : fieldAut 3 F σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  have hsub : MulAction.orbit B (proj 3 F D) ⊆
      (fun k : Fin 3 => (fieldAut 3 F σ ^ (k : ℕ)) (proj 3 F D)) '' Set.univ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk⟩ := h.act_diag D hD b.2
    refine ⟨⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, Set.mem_univ _, ?_⟩
    have : fieldAut 3 F σ ^ (k % 3) = fieldAut 3 F σ ^ k := by
      conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hf3, one_pow, one_mul]
    simp only [this]
    exact hk.symm
  refine (Set.ncard_le_ncard hsub (Set.Finite.image _ (Set.toFinite _))).trans ?_
  exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)

end Gen

section Diag

variable {F : Type} [Field F]

@[expose] def dvec (i j : Fin 3) (u : Fˣ) : Fin 3 → Fˣ :=
  fun l => if l = i then u else if l = j then 1 else u⁻¹

theorem prod_dvec {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) : ∏ l, ((dvec i j u l : Fˣ) : F) = 1 := by
  rw [Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> simp [dvec] at hij ⊢

@[expose] def Dsl {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) : SL(3, F) :=
  ⟨diagonal fun l => ((dvec i j u l : Fˣ) : F), by
    rw [det_diagonal]; exact prod_dvec hij u⟩

theorem Dsl_offdiag {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) :
    ∀ a b : Fin 3, a ≠ b → ((Dsl hij u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) a b = 0 := by
  intro a b hab
  exact diagonal_apply_ne _ hab

theorem toGL_Dsl {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) :
    SpecialLinearGroup.toGL (Dsl hij u : SL(3, F)) = diagGL (dvec i j u) := by
  apply Units.ext
  rfl

theorem dvec_ratio {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) :
    ((dvec i j u i : Fˣ) : F) * (((dvec i j u j)⁻¹ : Fˣ) : F) = u := by
  simp [dvec, hij.symm]

theorem Dsl_conj_tbar {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) (c : F) :
    proj 3 F (Dsl hij u) * tbar hij c * (proj 3 F (Dsl hij u))⁻¹ = tbar hij ((u : F) * c) := by
  have h := conjAut_diagGL_tbar (F := F) (dvec i j u) hij c
  rw [← toGL_Dsl hij u, conjAut_toGL, MulAut.conj_apply] at h
  rw [h]
  congr 1
  have := dvec_ratio (F := F) hij u
  linear_combination c * this

theorem Dsl_pow {i j : Fin 3} (hij : i ≠ j) (u : Fˣ) (n : ℕ) (hn : u ^ n = 1) :
    (Dsl hij u : SL(3, F)) ^ n = 1 := by
  have hcoe : (((Dsl hij u : SL(3, F)) ^ n : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (diagonal fun l => ((dvec i j u l : Fˣ) : F)) ^ n := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    rfl
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  rw [hcoe, diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
  by_cases hab : a = b
  · subst hab
    have : ((dvec i j u a : Fˣ) : F) ^ n = 1 := by
      have h1 : (dvec i j u a) ^ n = 1 := by
        unfold dvec
        split_ifs
        · exact hn
        · exact one_pow n
        · rw [inv_pow, hn, inv_one]
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    simp [this]
  · simp [hab]

theorem orderOf_proj_Dsl_coprime {i j : Fin 3} (hij : i ≠ j) {u : Fˣ}
    (hu : (orderOf u).Coprime 3) : (orderOf (proj 3 F (Dsl hij u))).Coprime 3 := by
  refine Nat.Coprime.coprime_dvd_left ?_ hu
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← map_pow, Dsl_pow hij u _ (pow_orderOf_eq_one u), map_one]

end Diag

section PSL3b

section Main

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem ringChar_ne_three (h3 : 3 ∣ Nat.card F - 1) : ringChar F ≠ 3 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  intro h
  rw [h] at hcard
  rw [Nat.card_eq_fintype_card, hcard] at h3
  have h30 : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 n.ne_zero
  have := Nat.dvd_sub h30 h3
  have h1 : 3 ^ (n : ℕ) - (3 ^ (n : ℕ) - 1) = 1 := by
    have : 1 ≤ 3 ^ (n : ℕ) := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [h1] at this
  omega

theorem tbar_nsmul {i j : Fin 3} (hij : i ≠ j) (c : F) (n : ℕ) :
    tbar hij (n • c) = tbar hij c ^ n := by
  induction n with
  | zero => simp [tbar_zero]
  | succ n ih => rw [succ_nsmul, tbar_add, ih, pow_succ]

theorem orderOf_tbar_coprime (h3 : 3 ∣ Nat.card F - 1) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    (orderOf (tbar hij c)).Coprime 3 := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have hpow : tbar hij c ^ ringChar F = 1 := by
    rw [← tbar_nsmul]
    have : ringChar F • c = 0 := by
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rw [this, tbar_zero]
  have hdvd : orderOf (tbar hij c) ∣ ringChar F := orderOf_dvd_of_pow_eq_one hpow
  exact Nat.Coprime.coprime_dvd_left hdvd
    ((Nat.coprime_primes hp Nat.prime_three).2 (ringChar_ne_three h3))

theorem closure_hyperplane_fixed_eq_top (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card F - 1)
    {A B : Subgroup (MulAut (projectiveSL 3 F))} (hd : SplitData σ A B)
    {s : ℕ} (hs : 1 ≤ s) (hBc : Nat.card B = 3 ^ s) :
    Subgroup.closure {x : projectiveSL 3 F | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup (MulAut (projectiveSL 3 F)), H ≤ B ∧ H.relIndex B = 3 ∧
        ∀ b ∈ H, b x = x} = ⊤ := by
  classical
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hBc]; positivity)
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  set S : Set (projectiveSL 3 F) := {x | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup (MulAut (projectiveSL 3 F)), H ≤ B ∧ H.relIndex B = 3 ∧
        ∀ b ∈ H, b x = x} with hS
  have hT : ∀ {i j : Fin 3} (hij : i ≠ j) (u : Fˣ), (orderOf u).Coprime 3 →
      proj 3 F (Dsl hij u) ∈ S := by
    intro i j hij u hu
    refine ⟨orderOf_proj_Dsl_coprime hij hu, ?_⟩
    obtain ⟨H, hHB, hHi, hHx⟩ := exists_hyperplane_of_orbit_le B hs hBc _
      (hd.ncard_orbit_diag hσ3 _ (Dsl_offdiag hij u))
    exact ⟨H, hHB, hHi, fun b hb => hHx b hb⟩
  have hU : ∀ {i j : Fin 3} (hij : i ≠ j) (c : F), σ c = c → tbar hij c ∈ S := by
    intro i j hij c hc
    refine ⟨orderOf_tbar_coprime h3 hij c, ?_⟩
    obtain ⟨H, hHB, hHi, hHx⟩ := exists_hyperplane_of_orbit_le B hs hBc _
      (hd.ncard_orbit_tbar hij hc)
    exact ⟨H, hHB, hHi, fun b hb => hHx b hb⟩
  have hQ : ∀ {i j : Fin 3} (hij : i ≠ j) (c : F), tbar hij c ∈ Subgroup.closure S := by
    intro i j hij c
    have hspan : c ∈ Submodule.span (fixF σ) {u : F | u ≠ 0 ∧ (orderOf u).Coprime 3} := by
      rw [span_threePrime_eq_top hσ h3]; trivial
    obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hspan
    rw [← hfg]
    have key : ∀ k : Fin n, tbar hij (f k • (g k : F)) ∈ Subgroup.closure S := by
      intro k
      have hu : (g k : F) ≠ 0 := (g k).2.1
      have hu3 := (g k).2.2
      set u : Fˣ := Units.mk0 (g k : F) hu with hudef
      have hor : orderOf u = orderOf (g k : F) := by
        rw [← orderOf_units]; rfl
      have hDS := hT hij u (by rw [hor]; exact hu3)
      have htS := hU hij (f k : F) (mem_fixF.1 (f k).2)
      have := Dsl_conj_tbar hij u (f k : F)
      have e : f k • (g k : F) = (u : F) * (f k : F) := by
        rw [Subfield.smul_def, mul_comm]; rfl
      rw [e, ← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hDS)
        (Subgroup.subset_closure htS)) (Subgroup.inv_mem _ (Subgroup.subset_closure hDS))
    refine Finset.sum_induction _ (fun c => tbar hij c ∈ Subgroup.closure S) ?_ ?_ ?_
    · intro a b ha hb
      rw [tbar_add]
      exact Subgroup.mul_mem _ ha hb
    · rw [tbar_zero]; exact Subgroup.one_mem _
    · intro k _
      exact key k
  rw [eq_top_iff]
  intro p _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F p
  have hg : g ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]; trivial
  refine Subgroup.closure_induction (p := fun g _ => proj 3 F g ∈ Subgroup.closure S)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨i, j, hij, c, rfl⟩
    exact hQ hij c
  · rw [map_one]; exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]; exact Subgroup.inv_mem _ hx

end Main

end PSL3b

end CFSG.HardMathSupport.Foote.ModuleExclusions
