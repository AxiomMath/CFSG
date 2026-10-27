module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Diagonal

variable {n : ℕ} {K : Type*} [Field K]

theorem isDiag_mul' {a b : Matrix (Fin n) (Fin n) K} (ha : a.IsDiag) (hb : b.IsDiag) :
    (a * b).IsDiag := by
  have h1 := ha.diagonal_diag
  have h2 := hb.diagonal_diag
  rw [← h1, ← h2, diagonal_mul_diagonal]
  exact isDiag_diagonal _

variable (n K) in
@[expose] def diagSL : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) where
  carrier := {d | Matrix.IsDiag (d : Matrix (Fin n) (Fin n) K)}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_one]
    exact isDiag_one
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at ha hb ⊢
    exact isDiag_mul' ha hb
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := ha.diagonal_diag
    rw [Matrix.SpecialLinearGroup.coe_inv, ← h, adjugate_diagonal]
    exact isDiag_diagonal _

theorem mem_diagSL {d : Matrix.SpecialLinearGroup (Fin n) K} :
    d ∈ diagSL n K ↔ Matrix.IsDiag (d : Matrix (Fin n) (Fin n) K) := Iff.rfl

theorem diagSL_commute {a b : Matrix.SpecialLinearGroup (Fin n) K} (ha : a ∈ diagSL n K)
    (hb : b ∈ diagSL n K) : a * b = b * a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have h1 := (mem_diagSL.mp ha).diagonal_diag
  have h2 := (mem_diagSL.mp hb).diagonal_diag
  calc (a : Matrix (Fin n) (Fin n) K) * b
      = diagonal (diag (a : Matrix (Fin n) (Fin n) K)) *
        diagonal (diag (b : Matrix (Fin n) (Fin n) K)) := by rw [h1, h2]
    _ = diagonal (diag (b : Matrix (Fin n) (Fin n) K)) *
        diagonal (diag (a : Matrix (Fin n) (Fin n) K)) := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    _ = (b : Matrix (Fin n) (Fin n) K) * a := by rw [h1, h2]

theorem diagSL_le_upperTriangular : diagSL n K ≤ upperTriangular n K := by
  intro d hd i j hij
  exact (mem_diagSL.mp hd) (ne_of_gt hij)

theorem upperTriangular_le_sup_diagSL :
    upperTriangular n K ≤ unitriangular n K ⊔ diagSL n K := by
  intro b hb
  obtain ⟨u, hu, d, hd, rfl⟩ := exists_unitriangular_mul_diagonal hb
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hd)

theorem conj_mem_unitriangular {b u : Matrix.SpecialLinearGroup (Fin n) K} (hb : b ∈ upperTriangular n K)
    (hu : u ∈ unitriangular n K) : b * u * b⁻¹ ∈ unitriangular n K := by
  have hb' : (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hb _ _ h
  have hu' : (u : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hu.1 _ _ h
  have hbi := coe_inv_isUpperTriangular hb'
  refine ⟨(upperTriangular n K).mul_mem ((upperTriangular n K).mul_mem hb (unitriangular_le_upperTriangular n K hu))
    ((upperTriangular n K).inv_mem hb), fun i => ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    mul_apply_self_of_isUpperTriangular (hb'.mul hu') hbi,
    mul_apply_self_of_isUpperTriangular hb' hu', hu.2 i, mul_one]
  exact coe_inv_apply_self_of_isUpperTriangular hb' i

end Diagonal

section Reflection

variable {n : ℕ} {K : Type*} [Field K]

variable (n K) in
@[expose] def reflGroup (i : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) :=
  unitriangular n K ⊔ Subgroup.closure {reflElt n K i}

theorem unitriangular_le_reflGroup (i : ℕ) : unitriangular n K ≤ reflGroup n K i := le_sup_left

theorem reflElt_mem_reflGroup (i : ℕ) : reflElt n K i ∈ reflGroup n K i :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

theorem lower_transvection_mem_reflGroup {i : ℕ} (hi : 1 ≤ i) (hin : i < n) {y x : Fin n}
    (hyx : y ≠ x) (hy : (y : ℕ) = i) (hx : (x : ℕ) + 1 = i) (s : K) :
    Matrix.SpecialLinearGroup.transvection hyx s ∈ reflGroup n K i := by
  have hxy : x < y := by rw [Fin.lt_def]; omega
  obtain ⟨c, hc⟩ := isMonomial_reflection (K := K) i hi hin
  have hc' : ∀ j, ((reflection n K i hi hin : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 = (c j : K) • Pi.single (adjSwap n i j) 1 := by
    intro j
    rw [coe_reflection]
    exact hc j
  have hyeq : y = ⟨i, hin⟩ := Fin.ext hy
  have hxeq : x = ⟨i - 1, by omega⟩ := Fin.ext (by simp; omega)
  have hwx : adjSwap n i x = y := by
    rw [adjSwap_of_lt hi hin, hyeq, hxeq]
    exact Equiv.swap_apply_left _ _
  have hwy : adjSwap n i y = x := by
    rw [adjSwap_of_lt hi hin, hyeq, hxeq]
    exact Equiv.swap_apply_right _ _
  have hr : reflection n K i hi hin ∈ reflGroup n K i := by
    rw [← reflElt_of_lt hi hin]
    exact reflElt_mem_reflGroup i
  have h1 := mul_mem (mul_mem hr (unitriangular_le_reflGroup i
    (transvection_mem_unitriangular hxy ((c y : K) * (c x : K)⁻¹ * s)))) (inv_mem hr)
  rw [monomial_conj_transvection (M := reflection n K i hi hin) hc' hxy.ne] at h1
  convert h1 using 1
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.transvection_coe, hwx, hwy]
  congr 1
  field_simp [(c x).ne_zero, (c y).ne_zero]

theorem diagSL_conj_reflElt_mem {i : ℕ} (hi : 1 ≤ i) (hin : i < n)
    {t : Matrix.SpecialLinearGroup (Fin n) K} (ht : t ∈ diagSL n K) :
    t * reflElt n K i * t⁻¹ ∈ reflGroup n K i := by
  have e := (monomial_root_transport (K := K) (n := n)).2.2 i hi hin
  rw [reflElt_of_lt hi hin, e]
  set x : Fin n := ⟨i - 1, by omega⟩ with hx
  set y : Fin n := ⟨i, hin⟩ with hy
  have hxy : x < y := by rw [Fin.lt_def]; simp [hx, hy]; omega
  have hyx : y ≠ x := hxy.ne'
  have hconj : ∀ (a b c : Matrix.SpecialLinearGroup (Fin n) K),
      t * (a * b * c) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) * (t * c * t⁻¹) := by
    intro a b c
    group
  rw [hconj]
  have hA : ∀ s : K, t * Matrix.SpecialLinearGroup.transvection hxy.ne s * t⁻¹ ∈ reflGroup n K i :=
    fun s => unitriangular_le_reflGroup i (conj_mem_unitriangular
      (diagSL_le_upperTriangular ht) (transvection_mem_unitriangular hxy s))
  have hB : t * Matrix.SpecialLinearGroup.transvection hyx 1 * t⁻¹ ∈ reflGroup n K i := by
    obtain ⟨c, hc⟩ := isMonomial_of_isDiag (mem_diagSL.mp ht)
    have h2 := monomial_conj_transvection (M := t) (w := 1) (c := c) hc hyx 1
    rw [h2]
    exact lower_transvection_mem_reflGroup hi hin (y := y) (x := x) hyx rfl (by simp [hx]; omega) _
  exact mul_mem (mul_mem (by convert hA (-1) using 2) hB) (by convert hA (-1) using 2)

theorem map_conj_reflGroup_le {i : ℕ} (hi : 1 ≤ i) (hin : i < n)
    {t : Matrix.SpecialLinearGroup (Fin n) K} (ht : t ∈ diagSL n K) :
    (reflGroup n K i).map (MulAut.conj t).toMonoidHom ≤ reflGroup n K i := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
  · exact unitriangular_le_reflGroup i (conj_mem_unitriangular
      (diagSL_le_upperTriangular ht) hu)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact diagSL_conj_reflElt_mem hi hin ht

theorem diagSL_le_normalizer_reflGroup {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    diagSL n K ≤ Subgroup.normalizer (reflGroup n K i : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact map_conj_reflGroup_le hi hin hh ⟨x, hx, rfl⟩
  · have h2 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ reflGroup n K i :=
      map_conj_reflGroup_le hi hin ((diagSL n K).inv_mem hh) ⟨h * x * h⁻¹, hx, rfl⟩
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at h2

end Reflection

section Solvable

variable {n : ℕ} {K : Type*} [Field K]

theorem diag_ne_zero_of_upperTriangular {b : Matrix.SpecialLinearGroup (Fin n) K}
    (hb : b ∈ upperTriangular n K) (i : Fin n) : (b : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
  have hb' : (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hb _ _ h
  exact left_ne_zero_of_mul_eq_one (coe_inv_apply_self_of_isUpperTriangular hb' i)

variable (n K) in
@[expose] noncomputable def diagHomLin : upperTriangular n K →* (Fin n → Kˣ) where
  toFun b i := Units.mk0 ((b : Matrix.SpecialLinearGroup (Fin n) K) i i)
    (diag_ne_zero_of_upperTriangular b.2 i)
  map_one' := by
    funext i
    apply Units.ext
    simp
  map_mul' a b := by
    funext i
    apply Units.ext
    have ha : ((a : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
      fun _ _ h => a.2 _ _ h
    have hb : ((b : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
      fun _ _ h => b.2 _ _ h
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Pi.mul_apply, Units.val_mul,
      Units.val_mk0]
    exact mul_apply_self_of_isUpperTriangular ha hb i

theorem ker_diagHomLin :
    (diagHomLin n K).ker = (unitriangular n K).subgroupOf (upperTriangular n K) := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine ⟨b.2, fun i => ?_⟩
    have := congrFun h i
    exact congrArg Units.val this
  · intro h
    funext i
    apply Units.ext
    exact h.2 i

theorem isSolvable_upperTriangular [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    Group.IsSolvable (upperTriangular n K) := by
  obtain ⟨k, hk⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 (unitriangular n K) :=
    IsPGroup.of_card (n := k * (n * (n - 1) / 2)) (by rw [card_unitriangular, hk, pow_mul])
  have : Finite (unitriangular n K) := inferInstance
  have : Group.IsSolvable (unitriangular n K) := by
    have := hV.isNilpotent
    infer_instance
  have hV' : Group.IsSolvable ((unitriangular n K).subgroupOf (upperTriangular n K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (unitriangular_le_upperTriangular n K)).toMonoidHom)
      (MulEquiv.injective _)
  refine Group.isSolvable_of_ker_le_range
    ((unitriangular n K).subgroupOf (upperTriangular n K)).subtype (diagHomLin n K) ?_
  rw [ker_diagHomLin]
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

end Solvable

section Three

variable {K : Type*} [Field K]

variable (K) in
@[expose] def Q3 (j : Fin 2) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  stabilizer (flagSpace 3 K ((j : ℕ) + 1))

variable (K) in
@[expose] def H3 (j : Fin 2) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  reflGroup 3 K (2 - (j : ℕ))

theorem flagStabilizer_singleton (i : ℕ) :
    flagStabilizer 3 K {i} = stabilizer (flagSpace 3 K i) := by
  ext g
  rw [mem_flagStabilizer]
  simp

theorem Q3_eq (j : Fin 2) : Q3 K j = flagStabilizer 3 K {(j : ℕ) + 1} :=
  (flagStabilizer_singleton _).symm

theorem reflElt_mem_flagStabilizer_singleton_iff {i j : ℕ} (hj : 1 ≤ j) (hjn : j < 3) :
    reflElt 3 K j ∈ flagStabilizer 3 K {i} ↔ j ≠ i := by
  rw [reflElt_of_lt hj hjn, (subflag_stabilizer_generation (K := K) (n := 3) {i}).2.2 j hj hjn]
  simp

theorem reflElt_not_mem_upperTriangular {n : ℕ} {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    reflElt n K i ∉ upperTriangular n K := by
  rw [reflElt_of_lt hi hin]
  intro h
  have hlt : (⟨i - 1, by omega⟩ : Fin n) < ⟨i, hin⟩ := by rw [Fin.lt_def]; simp; omega
  have h0 := h ⟨i, hin⟩ ⟨i - 1, by omega⟩ hlt
  rw [coe_reflection] at h0
  simp [reflectionMatrix, Nat.sub_add_cancel hi] at h0

theorem borelOvergroupCuts_upperTriangular :
    borelOvergroupCuts (upperTriangular 3 K) = {1, 2} := by
  ext i
  constructor
  · rintro ⟨hi, hin, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · intro hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    have h1 : 1 ≤ i := by omega
    have h3 : i < 3 := by omega
    exact ⟨h1, h3, by
      rw [← reflElt_of_lt h1 h3]
      exact reflElt_not_mem_upperTriangular h1 h3⟩

theorem upperTriangular_eq_flagStabilizer :
    upperTriangular 3 K = flagStabilizer 3 K {1, 2} := by
  have := (borel_overgroups (upperTriangular 3 K) le_rfl).1
  rwa [borelOvergroupCuts_upperTriangular] at this

theorem mem_borelOvergroupCuts_of_le_Q3 {j : Fin 2}
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hAQ : A ≤ Q3 K j) :
    (j : ℕ) + 1 ∈ borelOvergroupCuts A := by
  have hj := j.isLt
  by_contra hiJ
  have hr : reflElt 3 K ((j : ℕ) + 1) ∈ A := by
    by_contra hr
    rw [reflElt_of_lt (by omega) (by omega)] at hr
    exact hiJ ⟨by omega, by omega, hr⟩
  have := hAQ hr
  rw [Q3_eq] at this
  exact (reflElt_mem_flagStabilizer_singleton_iff (by omega) (by omega)).mp this rfl

theorem covBy_Q3 (j : Fin 2) : upperTriangular 3 K ⋖ Q3 K j := by
  have hj := j.isLt
  have hBQ : upperTriangular 3 K ≤ Q3 K j := by
    rw [Q3_eq]
    exact upperTriangular_le_flagStabilizer _
  refine ⟨lt_of_le_of_ne hBQ fun h => ?_, fun A hBA hAQ => ?_⟩
  · have h1 : reflElt 3 K (2 - (j : ℕ)) ∈ Q3 K j := by
      rw [Q3_eq, reflElt_mem_flagStabilizer_singleton_iff (by omega) (by omega)]
      omega
    rw [← h] at h1
    exact reflElt_not_mem_upperTriangular (by omega) (by omega) h1
  · have hA := (borel_overgroups A hBA.le).1
    have hiJ := mem_borelOvergroupCuts_of_le_Q3 hAQ.le
    have hoJ : 2 - (j : ℕ) ∉ borelOvergroupCuts A := by
      intro hoJ
      have hJeq : borelOvergroupCuts A = {1, 2} := by
        ext x
        constructor
        · rintro ⟨h1, h3, -⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        · intro hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases (by omega : x = (j : ℕ) + 1 ∨ x = 2 - (j : ℕ)) with rfl | rfl
          · exact hiJ
          · exact hoJ
      apply hBA.ne
      rw [hA, hJeq, upperTriangular_eq_flagStabilizer]
    have hJ : borelOvergroupCuts A = {(j : ℕ) + 1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨h1, h3, -⟩ := id hx
        rw [Set.mem_singleton_iff]
        by_contra hne
        apply hoJ
        have : x = 2 - (j : ℕ) := by omega
        rw [← this]
        exact hx
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hiJ
    apply hAQ.ne
    rw [hA, hJ]
    exact (Q3_eq j).symm

theorem Q3_ne : Q3 K 0 ≠ Q3 K 1 := by
  intro h
  have h1 : reflElt 3 K 2 ∈ Q3 K 0 := by
    rw [Q3_eq, reflElt_mem_flagStabilizer_singleton_iff (by omega) (by omega)]
    decide
  rw [h, Q3_eq, reflElt_mem_flagStabilizer_singleton_iff (by omega) (by omega)] at h1
  exact h1 rfl

theorem contained_in_Q3 {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hVA : unitriangular 3 K ≤ A) (hAt : A ≠ ⊤) : A ≤ Q3 K 0 ∨ A ≤ Q3 K 1 := by
  obtain ⟨hle, hiff⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (n := 3) (K := K)).1 A hVA
  have hne : borelOvergroupCuts A ≠ ∅ := fun he => hAt (hiff.mp he)
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hi1, hin, -⟩ := id hi
  have hAi : A ≤ stabilizer (flagSpace 3 K i) := by
    rw [← flagStabilizer_singleton]
    intro g hg
    rw [mem_flagStabilizer]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mem_flagStabilizer.mp (hle hg) x hi
  rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
  · exact Or.inl hAi
  · exact Or.inr hAi

theorem Q3_le_sup (j : Fin 2) : Q3 K j ≤ diagSL 3 K ⊔ H3 K j := by
  have hj := j.isLt
  rw [Q3_eq, (subflag_stabilizer_generation (K := K) (n := 3) _).1, Subgroup.closure_le]
  rintro g (hg | ⟨k, hk, hkn, hkI, rfl⟩)
  · exact (sup_le (le_sup_of_le_right (unitriangular_le_reflGroup (2 - (j : ℕ)))) le_sup_left :
      unitriangular 3 K ⊔ diagSL 3 K ≤ diagSL 3 K ⊔ H3 K j) (upperTriangular_le_sup_diagSL hg)
  · have hk' : k = 2 - (j : ℕ) := by
      rw [Set.mem_singleton_iff] at hkI
      omega
    subst hk'
    rw [← reflElt_of_lt hk hkn]
    exact Subgroup.mem_sup_right (reflElt_mem_reflGroup (2 - (j : ℕ)))

theorem commutator_Q3_le (j : Fin 2) : ⁅Q3 K j, Q3 K j⁆ ≤ H3 K j := by
  have hj := j.isLt
  exact (Subgroup.commutator_mono (Q3_le_sup j) (Q3_le_sup j)).trans
    (commutator_le_of_sup_normalizer
      (diagSL_le_normalizer_reflGroup (K := K) (n := 3) (i := 2 - (j : ℕ)) (by omega) (by omega))
      (fun a ha b hb => diagSL_commute ha hb))

theorem H3_le_of_nonsolvable (hB : Group.IsSolvable (upperTriangular 3 K)) (j : Fin 2)
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hVA : unitriangular 3 K ≤ A)
    (hAQ : A ≤ Q3 K j) (hAns : ¬ Group.IsSolvable A) : H3 K j ≤ A := by
  obtain ⟨hle, -⟩ := (linear_unitriangular_overgroup_subflag_containment (n := 3) (K := K)).1 A hVA
  have hj := j.isLt
  have hiJ := mem_borelOvergroupCuts_of_le_Q3 hAQ
  have hroA : reflElt 3 K (2 - (j : ℕ)) ∈ A := by
    by_contra hr
    have hoJ : 2 - (j : ℕ) ∈ borelOvergroupCuts A := by
      rw [reflElt_of_lt (by omega) (by omega)] at hr
      exact ⟨by omega, by omega, hr⟩
    have hAB : A ≤ upperTriangular 3 K := by
      rw [upperTriangular_eq_flagStabilizer]
      intro g hg
      rw [mem_flagStabilizer]
      intro x hx
      have hx' : x ∈ borelOvergroupCuts A := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases (by omega : x = (j : ℕ) + 1 ∨ x = 2 - (j : ℕ)) with rfl | rfl
        · exact hiJ
        · exact hoJ
      exact mem_flagStabilizer.mp (hle hg) x hx'
    exact hAns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
      (Subgroup.inclusion_injective hAB))
  exact sup_le hVA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr hroA))

theorem linear_three_residualOvergroupsAt {K : Type} [Field K] [Finite K]
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (projectiveSL 3 K) (projUnitriangular 3 K)
      (fun j : Fin 2 => projStabilizer (flagSpace 3 K ((j : ℕ) + 1))) := by
  have hB := isSolvable_upperTriangular (n := 3) (K := K) hK
  exact residualOvergroupsAt_of_rank_two_data (π := proj 3 K) (proj_surjective 3 K)
    (V := unitriangular 3 K) (B := upperTriangular 3 K) (Q := Q3 K) (H := H3 K)
    (by rw [ker_proj]; exact scalars_le_upperTriangular 3 K)
    (unitriangular_le_upperTriangular 3 K)
    (fun j => by rw [Q3_eq]; exact upperTriangular_le_flagStabilizer _)
    Q3_ne covBy_Q3 (fun A hVA hAt => contained_in_Q3 hVA hAt) hB commutator_Q3_le
    (fun j A hVA hAQ hAns => H3_le_of_nonsolvable hB j hVA hAQ hAns)

theorem H3_le_Q3 (j : Fin 2) : H3 K j ≤ Q3 K j := by
  have hj := j.isLt
  refine sup_le ?_ ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr ?_))
  · rw [Q3_eq]
    exact (unitriangular_le_upperTriangular 3 K).trans (upperTriangular_le_flagStabilizer _)
  · rw [SetLike.mem_coe, Q3_eq, reflElt_mem_flagStabilizer_singleton_iff (by omega) (by omega)]
    omega

theorem H3_normal_in_Q3 (j : Fin 2) : ((H3 K j).subgroupOf (Q3 K j)).Normal := by
  have hj := j.isLt
  have hN : diagSL 3 K ≤ Subgroup.normalizer (H3 K j : Set (Matrix.SpecialLinearGroup (Fin 3) K)) :=
    diagSL_le_normalizer_reflGroup (K := K) (n := 3) (i := 2 - (j : ℕ)) (by omega) (by omega)
  have hQ : Q3 K j ≤ Subgroup.normalizer (H3 K j : Set (Matrix.SpecialLinearGroup (Fin 3) K)) :=
    (Q3_le_sup j).trans (sup_le hN Subgroup.le_normalizer)
  rw [Subgroup.normal_subgroupOf_iff (H3_le_Q3 j)]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.mp (hQ hk) h).mp hh

end Three

end CFSG.QuasithinUnique.Setup.X7a
