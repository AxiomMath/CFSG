module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource

public noncomputable section

namespace CFSG.ComponentClassification.SymmetricLocal

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Unitriangular

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def utTransvection {i j : Fin n} (hij : i < j) (c : K) : unitriangular n K :=
  ⟨⟨transvection i j c, det_transvection_of_ne i j hij.ne c⟩,
    fun a b hab => by
      change (1 + single i j c : Matrix (Fin n) (Fin n) K) a b = 0
      rw [Matrix.add_apply, one_apply_ne (ne_of_gt hab), zero_add, single_apply_of_ne]
      intro h
      rw [← h.1, ← h.2] at hab
      exact lt_asymm hij hab,
    fun a => by
      change (1 + single i j c : Matrix (Fin n) (Fin n) K) a a = 1
      rw [Matrix.add_apply, one_apply_eq, single_apply_of_ne, add_zero]
      intro h
      exact hij.ne (h.1.trans h.2.symm)⟩

theorem coe_utTransvection {i j : Fin n} (hij : i < j) (c : K) :
    (((utTransvection hij c : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = transvection i j c :=
  rfl

theorem center_unitriangular_row {z : unitriangular n K}
    (hz : z ∈ Subgroup.center (unitriangular n K)) {i j : Fin n} (hij : i < j) {b : Fin n}
    (hb : b ≠ j) : ((z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) j b = 0 := by
  have h0 : transvection i j (1 : K) * ((z : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((z : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * transvection i j 1 :=
    congrArg (fun g : unitriangular n K =>
      ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Subgroup.mem_center_iff.mp hz (utTransvection hij 1))
  have h := congrFun (congrFun h0 i) b
  rw [transvection_mul_apply_same, mul_transvection_apply_of_ne _ _ _ _ hb, one_mul] at h
  simpa using h

theorem center_unitriangular_col {z : unitriangular n K}
    (hz : z ∈ Subgroup.center (unitriangular n K)) {i j : Fin n} (hij : i < j) {a : Fin n}
    (ha : a ≠ i) : ((z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a i = 0 := by
  have h0 : transvection i j (1 : K) * ((z : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((z : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * transvection i j 1 :=
    congrArg (fun g : unitriangular n K =>
      ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Subgroup.mem_center_iff.mp hz (utTransvection hij 1))
  have h := congrFun (congrFun h0 a) j
  rw [transvection_mul_apply_of_ne _ _ _ _ ha, mul_transvection_apply_same, one_mul] at h
  simpa using h

theorem corner_lt (hn : 2 ≤ n) : (⟨0, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ :=
  Fin.mk_lt_mk.mpr (by omega)

theorem eq_utTransvection_of_mem_center (hn : 2 ≤ n) {z : unitriangular n K}
    (hz : z ∈ Subgroup.center (unitriangular n K)) :
    z = utTransvection (corner_lt hn)
      (((z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
        ⟨n - 1, by omega⟩) := by
  have hzU := mem_unitriangular.mp z.2
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set l : Fin n := ⟨n - 1, by omega⟩ with hl
  set c := ((z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i₀ l with hc'
  have key : ((z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      transvection i₀ l c := by
    ext r s
    rw [transvection, Matrix.add_apply]
    rcases lt_trichotomy s r with hsr | rfl | hrs
    · rw [hzU.1 r s hsr, one_apply_ne (ne_of_gt hsr), zero_add, single_apply_of_ne]
      rintro ⟨h1, h2⟩
      rw [← h1, ← h2, Fin.lt_def] at hsr
      simp only [hi₀, hl] at hsr
      omega
    · rw [hzU.2 s, one_apply_eq, single_apply_of_ne, add_zero]
      rintro ⟨h1, h2⟩
      have h3 := congrArg Fin.val (h1.trans h2.symm)
      simp only [hi₀, hl] at h3
      omega
    · rw [one_apply_ne (ne_of_lt hrs), zero_add]
      by_cases hc : (r : ℕ) = 0 ∧ (s : ℕ) = n - 1
      · have hr : r = i₀ := Fin.ext hc.1
        have hs : s = l := Fin.ext hc.2
        rw [hr, hs, single_apply_same]
      · have hne : ¬(i₀ = r ∧ l = s) := by
          rintro ⟨h1, h2⟩
          exact hc ⟨congrArg Fin.val h1.symm, congrArg Fin.val h2.symm⟩
        rw [single_apply_of_ne]
        swap
        · exact hne
        by_cases hs : (s : ℕ) + 1 < n
        · exact center_unitriangular_col hz (j := ⟨s + 1, hs⟩)
            (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)) (ne_of_lt hrs)
        · have hr0 : (r : ℕ) ≠ 0 := fun h => hc ⟨h, by have := s.isLt; omega⟩
          have hr1 : (r : ℕ) - 1 < n := by have := r.isLt; omega
          have hlt : (⟨(r : ℕ) - 1, hr1⟩ : Fin n) < r := Fin.mk_lt_mk.mpr (by omega)
          exact center_unitriangular_row hz hlt (ne_of_gt hrs)
  exact Subtype.ext (Subtype.ext key)

theorem utTransvection_corner_mem_center (hn : 2 ≤ n) (c : K) :
    utTransvection (corner_lt hn) c ∈ Subgroup.center (unitriangular n K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hG := mem_unitriangular.mp g.2
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set l : Fin n := ⟨n - 1, by omega⟩ with hl
  have key : ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      transvection i₀ l c =
      transvection i₀ l c * ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext a b
    by_cases ha : a = i₀ <;> by_cases hb : b = l
    · rw [ha, hb, mul_transvection_apply_same, transvection_mul_apply_same, hG.2, hG.2]
    · have hbl : b < l := by
        rw [Fin.lt_def]
        have := b.isLt
        have : (b : ℕ) ≠ n - 1 := fun h => hb (Fin.ext h)
        simp only [hl]
        omega
      rw [ha, mul_transvection_apply_of_ne _ _ _ _ hb, transvection_mul_apply_same,
        hG.1 l b hbl, mul_zero, add_zero]
    · have ha0 : i₀ < a := by
        rw [Fin.lt_def]
        have : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
        simp only [hi₀]
        omega
      rw [hb, mul_transvection_apply_same, transvection_mul_apply_of_ne _ _ _ _ ha,
        hG.1 a i₀ ha0, mul_zero, add_zero]
    · rw [mul_transvection_apply_of_ne _ _ _ _ hb, transvection_mul_apply_of_ne _ _ _ _ ha]
  exact Subtype.ext (Subtype.ext key)

theorem card_center_unitriangular (hn : 2 ≤ n) :
    Nat.card (Subgroup.center (unitriangular n K)) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun c : K =>
    (⟨utTransvection (corner_lt hn) c, utTransvection_corner_mem_center hn c⟩ :
      Subgroup.center (unitriangular n K))) ⟨fun c d h => ?_, fun z => ?_⟩)).symm
  · have h' := congrArg (fun z : Subgroup.center (unitriangular n K) =>
      (((z : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        ⟨0, by omega⟩ ⟨n - 1, by omega⟩) h
    simpa only [coe_utTransvection, transvection, Matrix.add_apply,
      one_apply_ne (corner_lt hn).ne, single_apply_same, zero_add] using h'
  · exact ⟨_, Subtype.ext (eq_utTransvection_of_mem_center hn z.2).symm⟩

end Unitriangular

theorem card_center_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem projectiveSL_three_four_not_equiv {K₄ K₂ : Type*} [Field K₄] [Finite K₄] [Field K₂]
    [Finite K₂] (h4 : Nat.card K₄ = 4) (h2 : Nat.card K₂ = 2) :
    IsEmpty (projectiveSL 3 K₄ ≃* projectiveSL 4 K₂) := by
  classical
  refine ⟨fun ψ => ?_⟩
  have := Fintype.ofFinite K₄
  have := Fintype.ofFinite K₂
  have : CharP K₄ 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, h4]; norm_num)
  have : CharP K₂ 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, h2]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₃, hP₃⟩ := exists_sylow_projUnitriangular (K := K₄) 2 (n := 3) (by norm_num)
  obtain ⟨P₄, hP₄⟩ := exists_sylow_projUnitriangular (K := K₂) 2 (n := 4) (by norm_num)
  let Q : Sylow 2 (projectiveSL 4 K₂) := Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective P₃
  have hQ : (Q : Subgroup (projectiveSL 4 K₂)) =
      (P₃ : Subgroup (projectiveSL 3 K₄)).map ψ.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  let e : unitriangular 3 K₄ ≃* unitriangular 4 K₂ :=
    (unitriangularEquivProj 3).trans ((MulEquiv.subgroupCongr hP₃.symm).trans
      ((((P₃ : Subgroup (projectiveSL 3 K₄)).equivMapOfInjective ψ.toMonoidHom
        ψ.injective).trans (MulEquiv.subgroupCongr hQ.symm)).trans ((Sylow.equiv Q P₄).trans
          ((MulEquiv.subgroupCongr hP₄).trans (unitriangularEquivProj 4).symm))))
  have h := card_center_congr e
  rw [card_center_unitriangular (by norm_num), card_center_unitriangular (by norm_num), h4,
    h2] at h
  norm_num at h

section RowGroup

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def rowMat (v : Fin (n - 1) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r s =>
    if h : (r : ℕ) = 0 ∧ 0 < (s : ℕ) then v ⟨s - 1, by have := s.isLt; omega⟩ else 0

theorem rowMat_mul_rowMat (v w : Fin (n - 1) → K) : rowMat v * rowMat w = 0 := by
  ext r s
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) = 0
  · simp [rowMat, hk]
  · simp [rowMat, hk]

theorem rowMat_add (v w : Fin (n - 1) → K) : rowMat (v + w) = rowMat v + rowMat w := by
  ext r s
  simp only [rowMat, of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem rowMat_zero : rowMat (0 : Fin (n - 1) → K) = 0 := by
  ext r s
  simp [rowMat]

theorem one_add_rowMat_lower (v : Fin (n - 1) → K) {i j : Fin n} (hij : j < i) :
    (1 + rowMat v) i j = 0 := by
  have hi : (i : ℕ) ≠ 0 := by
    rw [Fin.lt_def] at hij
    omega
  simp [rowMat, one_apply_ne (ne_of_gt hij), hi]

theorem one_add_rowMat_diag (v : Fin (n - 1) → K) (i : Fin n) : (1 + rowMat v) i i = 1 := by
  by_cases hi : (i : ℕ) = 0
  · simp [rowMat, hi]
  · simp [rowMat, hi]

theorem det_one_add_rowMat (v : Fin (n - 1) → K) : (1 + rowMat v).det = 1 := by
  rw [det_of_isUpperTriangular (M := 1 + rowMat v) (fun i j hij => one_add_rowMat_lower v hij)]
  exact Finset.prod_eq_one fun i _ => one_add_rowMat_diag v i

@[expose] def rowHom : Multiplicative (Fin (n - 1) → K) →* SpecialLinearGroup (Fin n) K where
  toFun v := ⟨1 + rowMat (Multiplicative.toAdd v), det_one_add_rowMat _⟩
  map_one' := by
    apply Subtype.ext
    simp [rowMat_zero]
  map_mul' v w := by
    apply Subtype.ext
    change 1 + rowMat (Multiplicative.toAdd v + Multiplicative.toAdd w) =
      (1 + rowMat (Multiplicative.toAdd v)) * (1 + rowMat (Multiplicative.toAdd w))
    rw [rowMat_add]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, rowMat_mul_rowMat,
      add_zero]
    abel

theorem rowHom_mem_unitriangular (v : Multiplicative (Fin (n - 1) → K)) :
    rowHom v ∈ unitriangular n K :=
  ⟨fun _ _ hij => one_add_rowMat_lower _ hij, fun i => one_add_rowMat_diag _ i⟩

theorem proj_rowHom_injective (hn : 1 ≤ n) : Function.Injective ((proj n K).comp rowHom) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h1 : rowHom v ∈ unitriangular n K ⊓ scalars n K :=
    ⟨rowHom_mem_unitriangular v, proj_eq_one_iff.mp hv⟩
  rw [unitriangular_inf_scalars, Subgroup.mem_bot] at h1
  have h2 : rowMat (Multiplicative.toAdd v) = 0 := by
    have h3 : (1 + rowMat (Multiplicative.toAdd v) : Matrix (Fin n) (Fin n) K) = 1 :=
      congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) h1
    simpa using h3
  apply Multiplicative.toAdd.injective
  funext s
  have h4 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨s + 1, by have := s.isLt; omega⟩
  simpa [rowMat] using h4

theorem exists_elementary_projectiveSL [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    ∃ E : Subgroup (projectiveSL n K), CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = Nat.card K ^ (n - 1) := by
  refine ⟨((proj n K).comp rowHom).range, ?_, ?_⟩
  · refine { toIsMulCommutative := isMulCommutative_iff.mpr ?_, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      change ((proj n K).comp rowHom) a * ((proj n K).comp rowHom) b =
        ((proj n K).comp rowHom) b * ((proj n K).comp rowHom) a
      rw [← map_mul, ← map_mul, mul_comm a b]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      change ((proj n K).comp rowHom) a ^ 2 = 1
      have ha : a * a = 1 := by
        apply Multiplicative.toAdd.injective
        funext s
        simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
        exact CharTwo.add_self_eq_zero _
      rw [← map_pow, pow_two, ha, map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (proj_rowHom_injective hn),
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]

end RowGroup

@[expose] def statedProjEquivProjectiveSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K).symm)

theorem card_projectiveSL_eq_two_pow_mul_odd {K : Type*} [Field K] [Finite K] {g n : ℕ}
    (hK : Nat.card K = 2 ^ g) (hn : 1 ≤ n) :
    ∃ m, Odd m ∧ Nat.card (projectiveSL n K) = 2 ^ (g * (n * (n - 1) / 2)) * m := by
  classical
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 hn
  refine ⟨(P : Subgroup (projectiveSL n K)).index, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp P.not_dvd_index)
  · rw [← (P : Subgroup (projectiveSL n K)).card_mul_index, hP, card_projUnitriangular, hK,
      ← pow_mul]

theorem small_standard_source_even_higher_linear_parameters_stated {X : Type} [Group X]
    {n g : ℕ} (hn : 3 ≤ n) (hX : StatedClassicalModel X .PSL n 2 g) :
    (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel X .PSL 2 p f → n = 3 ∧ g = 1 ∧ p = 7 ∧ f = 1) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      (StatedClassicalModel X .PSL 3 2 2 → n = 3 ∧ g = 2) := by
  obtain ⟨⟨-, hg, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : X ≃* projectiveSL n K := e.trans (statedProjEquivProjectiveSL n K)
  obtain ⟨m, hmodd, hcard⟩ := card_projectiveSL_eq_two_pow_mul_odd hK (by omega : 1 ≤ n)
  have hXcard : Nat.card X = 2 ^ (g * (n * (n - 1) / 2)) * m :=
    (Nat.card_congr e'.toEquiv).trans hcard
  have h168 : n = 3 → g = 1 → Nat.card X = 168 := by
    rintro rfl rfl
    rw [Nat.card_congr e.toEquiv,
      Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hK]
    decide
  set N := n * (n - 1) / 2 with hNdef
  have hN3 : 3 ≤ N := by
    have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hN4 : 4 ≤ n → 6 ≤ N := fun h4 => by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul h4 (by omega)
    omega
  have hN5 : 5 ≤ n → 10 ≤ N := fun h5 => by
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul h5 (by omega)
    omega
  have hN33 : n = 3 → N = 3 := fun h => by rw [hNdef, h]
  have hN46 : n = 4 → N = 6 := fun h => by rw [hNdef, h]
  refine ⟨fun p f hp2 hmodel => ?_, ⟨fun e7 => ?_⟩, fun h322 => ?_⟩
  · obtain ⟨⟨hp, hf, -⟩, K', _, _, hK', ⟨ψ⟩⟩ := hmodel
    have hq : Odd (Nat.card K') := by
      rw [hK']
      exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨E, hE, hEcard⟩ := exists_elementary_projectiveSL (K := K) (by omega : 1 ≤ n)
    have hE' : CFSG.IsElementaryAbelian 2 (E.map e'.symm.toMonoidHom) :=
      CFSG.IsElementaryAbelian.map _
    have h4 := UnbalancingLocal.card_le_four_of_odd_psl_two hq ψ (E.map e'.symm.toMonoidHom)
    rw [Subgroup.card_map_of_injective e'.symm.injective, hEcard, hK, ← pow_mul] at h4
    have hle : g * (n - 1) ≤ 2 := by
      by_contra h
      have h8 : 2 ^ 3 ≤ 2 ^ (g * (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hgn : 1 * (n - 1) ≤ g * (n - 1) := Nat.mul_le_mul_right _ hg
    have hn3 : n = 3 := by omega
    subst hn3
    have hg1 : g = 1 := by omega
    subst hg1
    have hXq : Nat.card X * 2 = Nat.card K' * (Nat.card K' ^ 2 - 1) := by
      rw [Nat.card_congr ψ.toEquiv]
      exact UnbalancingLocal.two_mul_card_psl_two_of_odd K' hq
    rw [h168 rfl rfl] at hXq
    have h7 := UnbalancingLocal.eq_of_cubeSub_eq (b := 7) Nat.card_pos (by norm_num)
      (by rw [← hXq]; norm_num)
    rw [hK'] at h7
    obtain ⟨hp7, hf1⟩ := UnbalancingLocal.prime_pow_inj hp (by norm_num : Nat.Prime 7) hf le_rfl
      (h7.trans (pow_one 7).symm)
    exact ⟨rfl, rfl, hp7, hf1⟩
  · have h7 : Nat.card X = 2520 :=
      (Nat.card_congr e7.toEquiv).trans UnbalancingLocal.card_alternating_seven
    have h3 : g * N = 3 := eq_of_two_pow_mul_odd hmodd (by decide : Odd 315)
      (by rw [← hXcard, h7]; norm_num)
    have hgN : 1 * N ≤ g * N := Nat.mul_le_mul_right _ hg
    have hN : N = 3 := by omega
    have hn3 : n = 3 := by
      by_contra h
      have := hN4 (by omega)
      omega
    have hg1 : g = 1 := by
      rw [hN] at h3
      omega
    have := h168 hn3 hg1
    omega
  · obtain ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩ := h322
    have hK₃4 : Nat.card K₃ = 4 := by rw [hK₃]; norm_num
    have h20160 : Nat.card X = 20160 :=
      (Nat.card_congr χ.toEquiv).trans (UnbalancingLocal.card_psl_three_four K₃ hK₃4)
    have h6 : g * N = 6 := eq_of_two_pow_mul_odd hmodd (by decide : Odd 315)
      (by rw [← hXcard, h20160]; norm_num)
    have hgN : 1 * N ≤ g * N := Nat.mul_le_mul_right _ hg
    have hn4 : n ≤ 4 := by
      by_contra h
      have := hN5 (by omega)
      omega
    rcases (show n = 3 ∨ n = 4 by omega) with hn3 | hn4'
    · refine ⟨hn3, ?_⟩
      rw [hN33 hn3] at h6
      omega
    · exfalso
      have hg1 : g = 1 := by
        rw [hN46 hn4'] at h6
        omega
      subst hn4' hg1
      have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
      exact (projectiveSL_three_four_not_equiv hK₃4 hK2).false
        ((statedProjEquivProjectiveSL 3 K₃).symm.trans (χ.symm.trans e'))

theorem small_standard_source_even_higher_linear_parameters {X : Type} [Group X] {n g : ℕ}
    (hn : 3 ≤ n) (hX : Assembly.ComponentType.ClassicalModel X .PSL n 2 g) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → Assembly.ComponentType.ClassicalModel X .PSL 2 p f →
      n = 3 ∧ g = 1 ∧ p = 7 ∧ f = 1) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      (Assembly.ComponentType.ClassicalModel X .PSL 3 2 2 → n = 3 ∧ g = 2) := by
  obtain ⟨h1, h2, h3⟩ := small_standard_source_even_higher_linear_parameters_stated hn
    (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL n 2 g hX)
  exact ⟨fun p f _ hp2 hY => h1 p f hp2
      (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 p f hY), h2,
    fun hZ => h3 (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 3 2 2 hZ)⟩

end CFSG.ComponentClassification.SymmetricLocal
