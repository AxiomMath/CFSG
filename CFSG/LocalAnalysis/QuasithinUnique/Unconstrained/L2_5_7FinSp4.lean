module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinRed
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.QuasithinUnique.Fin257

namespace Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b CFSG.Open

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

@[expose] def wSMat : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def wTMat : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

omit [CharP K 2] in
theorem wSMat_mul_self : (wSMat : Matrix (Fin 4) (Fin 4) K) * wSMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSMat, mul_apply, Fin.sum_univ_four]

omit [CharP K 2] in
theorem wTMat_mul_self : (wTMat : Matrix (Fin 4) (Fin 4) K) * wTMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wTMat, mul_apply, Fin.sum_univ_four]

omit [CharP K 2] in
theorem wSMat_mem : (wSMat : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * wSMat = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSMat, mul_apply, Fin.sum_univ_four, minorJ_apply]

omit [CharP K 2] in
theorem wTMat_mem : (wTMat : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * wTMat = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wTMat, mul_apply, Fin.sum_univ_four, minorJ_apply]

@[expose] def wS : antiSp K := ⟨⟨wSMat, wSMat, wSMat_mul_self, wSMat_mul_self⟩, wSMat_mem⟩

@[expose] def wT : antiSp K := ⟨⟨wTMat, wTMat, wTMat_mul_self, wTMat_mul_self⟩, wTMat_mem⟩

omit [CharP K 2] in
theorem glMat_wS : glMat ((wS : antiSp K) : GL (Fin 4) K) = wSMat := rfl

omit [CharP K 2] in
theorem glMat_wT : glMat ((wT : antiSp K) : GL (Fin 4) K) = wTMat := rfl

omit [CharP K 2] in
theorem wS_mul_self : (wS : antiSp K) * wS = 1 := antiSp_ext wSMat_mul_self

omit [CharP K 2] in
theorem wT_mul_self : (wT : antiSp K) * wT = 1 := antiSp_ext wTMat_mul_self

omit [CharP K 2] in
theorem wS_inv : (wS : antiSp K)⁻¹ = wS := inv_eq_of_mul_eq_one_right wS_mul_self

omit [CharP K 2] in
theorem wT_inv : (wT : antiSp K)⁻¹ = wT := inv_eq_of_mul_eq_one_right wT_mul_self

omit [CharP K 2] in
theorem glMat_mul (g h : antiSp K) :
    glMat ((g * h : antiSp K) : GL (Fin 4) K) = glMat (g : GL (Fin 4) K) * glMat h := rfl

theorem glMat_wS_conj (a b c d : K) :
    glMat ((wS * uElt a b c d * (wS : antiSp K)⁻¹ : antiSp K) : GL (Fin 4) K) =
      !![1, 0, b + a * d, d; a, 1, c, b; 0, 0, 1, 0; 0, 0, a, 1] := by
  rw [wS_inv, glMat_mul, glMat_mul, glMat_uElt, glMat_wS]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSMat, uMat, mul_apply, Fin.sum_univ_four]

theorem wS_conj_uElt_zero (b c d : K) :
    (wS * uElt 0 b c d * (wS : antiSp K)⁻¹ : antiSp K) = uElt 0 b d c := by
  apply antiSp_ext
  rw [glMat_wS_conj, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem glMat_wT_conj (a b c d : K) :
    glMat ((wT * uElt a b c d * (wT : antiSp K)⁻¹ : antiSp K) : GL (Fin 4) K) =
      !![1, b, a, c; 0, 1, 0, a; 0, d, 1, b + a * d; 0, 0, 0, 1] := by
  rw [wT_inv, glMat_mul, glMat_mul, glMat_uElt, glMat_wT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wTMat, uMat, mul_apply, Fin.sum_univ_four]

theorem wT_conj_uElt_zero (a b c : K) :
    (wT * uElt a b c 0 * (wT : antiSp K)⁻¹ : antiSp K) = uElt b a c 0 := by
  apply antiSp_ext
  rw [glMat_wT_conj, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem conj_mem_radA1 {u x : antiSp K} (hu : u ∈ antiUnipotent K) (hx : x ∈ radA1 K) :
    u * x * u⁻¹ ∈ radA1 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  obtain ⟨B, C, D, rfl⟩ := hx
  rw [uElt_inv, uElt_mul, uElt_mul]
  have h : a + 0 + a = 0 := by rw [add_zero]; exact CharTwo.add_self_eq_zero a
  rw [h]
  exact ⟨_, _, _, rfl⟩

theorem conj_mem_radA2 {u x : antiSp K} (hu : u ∈ antiUnipotent K) (hx : x ∈ radA2 K) :
    u * x * u⁻¹ ∈ radA2 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  obtain ⟨A, B, C, rfl⟩ := hx
  rw [uElt_inv, uElt_mul, uElt_mul]
  have h : d + 0 + d = 0 := by rw [add_zero]; exact CharTwo.add_self_eq_zero d
  rw [h]
  exact ⟨_, _, _, rfl⟩

theorem U_le_normalizer_radA1 :
    antiUnipotent K ≤ Subgroup.normalizer (radA1 K : Set (antiSp K)) := fun u hu =>
  mem_normalizer_of_conj _ (fun v hv => conj_mem_radA1 hu hv)
    (fun v hv => by simpa using conj_mem_radA1 (inv_mem hu) hv)

theorem U_le_normalizer_radA2 :
    antiUnipotent K ≤ Subgroup.normalizer (radA2 K : Set (antiSp K)) := fun u hu =>
  mem_normalizer_of_conj _ (fun v hv => conj_mem_radA2 hu hv)
    (fun v hv => by simpa using conj_mem_radA2 (inv_mem hu) hv)

theorem radA1_ne_radA2 : radA1 K ≠ radA2 K := by
  intro h
  have h1 : (uElt 0 0 0 1 : antiSp K) ∈ radA1 K := ⟨0, 0, 1, rfl⟩
  rw [h] at h1
  obtain ⟨a, b, c, h2⟩ := h1
  have := (uElt_inj h2).2.2.2
  exact one_ne_zero this

theorem conjTo_of_map_eq {M : Type} [Group M] {g : M} {A B : Subgroup M}
    (h : A.map (MulAut.conj g).toMonoidHom = B) : ConjTo g A B := by
  intro x
  rw [← h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have : y = x := by simpa using h1
    rwa [← this]

theorem exists_conjTo_radA [Finite K] {g : antiSp K}
    (hg : g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)))
    {A : Subgroup (antiSp K)} (hAU : A ≤ antiUnipotent K) (hA2 : ∀ y ∈ A, y * y = 1)
    (hAc : Nat.card A = Nat.card K ^ 3) :
    ConjTo g A (radA1 K) ∨ ConjTo g A (radA2 K) := by
  set B := A.map (MulAut.conj g).toMonoidHom with hB
  have hBU : B ≤ antiUnipotent K := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hAU hy)
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have := hA2 y hy
    change g * y * g⁻¹ * (g * y * g⁻¹) = 1
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hBc : Nat.card B = Nat.card K ^ 3 := by
    rw [← hAc]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  rcases elementary_le_radA1_or_radA2 hBU hB2 with h | h
  · left
    exact conjTo_of_map_eq (Subgroup.eq_of_le_of_card_ge h (by rw [hBc, h1]))
  · right
    exact conjTo_of_map_eq (Subgroup.eq_of_le_of_card_ge h (by rw [hBc, h2]))

theorem fixes_radicals [Finite K] : ∀ g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
    ConjTo g (radA1 K) (radA1 K) ∧ ConjTo g (radA2 K) (radA2 K) := by
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  exact fixes_of_odd card_and_isSylowTwoOf_antiUnipotent.2 U_le_normalizer_radA1 radA1_ne_radA2
    (fun g hg => exists_conjTo_radA hg radA1_le_antiUnipotent
      (fun y hy => mul_self_of_mem_radA1 hy) h1)
    (fun g hg => exists_conjTo_radA hg radA2_le_antiUnipotent
      (fun y hy => mul_self_of_mem_radA2 hy) h2)

theorem normalizer_U_le_normalizer_radA1 [Finite K] :
    Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) ≤
      Subgroup.normalizer (radA1 K : Set (antiSp K)) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr (fixes_radicals g hg).1

theorem normalizer_U_le_normalizer_radA2 [Finite K] :
    Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) ≤
      Subgroup.normalizer (radA2 K : Set (antiSp K)) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr (fixes_radicals g hg).2

theorem wS_conj_not_mem_U (b c d : K) :
    (wS * uElt 1 b c d * (wS : antiSp K)⁻¹ : antiSp K) ∉ antiUnipotent K := by
  intro h
  have := ((mem_antiUnipotent_iff_upper _).mp h).1 1 0 (by decide)
  rw [glMat_wS_conj] at this
  simp at this

theorem wT_conj_not_mem_U (a b c : K) :
    (wT * uElt a b c 1 * (wT : antiSp K)⁻¹ : antiSp K) ∉ antiUnipotent K := by
  intro h
  have := ((mem_antiUnipotent_iff_upper _).mp h).1 2 1 (by decide)
  rw [glMat_wT_conj] at this
  simp at this

theorem wS_not_mem_normalizer_U :
    (wS : antiSp K) ∉ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := fun h =>
  wS_conj_not_mem_U 0 0 0
    ((Subgroup.mem_normalizer_iff.mp h _).mp (uElt_mem_antiUnipotent 1 0 0 0))

theorem wT_not_mem_normalizer_U :
    (wT : antiSp K) ∉ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := fun h =>
  wT_conj_not_mem_U 0 0 0
    ((Subgroup.mem_normalizer_iff.mp h _).mp (uElt_mem_antiUnipotent 0 0 0 1))

theorem wS_not_mem_normalizer_radA2 :
    (wS : antiSp K) ∉ Subgroup.normalizer (radA2 K : Set (antiSp K)) := fun h =>
  wS_conj_not_mem_U 0 0 0 (radA2_le_antiUnipotent
    ((Subgroup.mem_normalizer_iff.mp h _).mp (⟨1, 0, 0, rfl⟩ : (uElt 1 0 0 0 : antiSp K) ∈ radA2 K)))

theorem wT_not_mem_normalizer_radA1 :
    (wT : antiSp K) ∉ Subgroup.normalizer (radA1 K : Set (antiSp K)) := fun h =>
  wT_conj_not_mem_U 0 0 0 (radA1_le_antiUnipotent
    ((Subgroup.mem_normalizer_iff.mp h _).mp (⟨0, 0, 1, rfl⟩ : (uElt 0 0 0 1 : antiSp K) ∈ radA1 K)))

theorem wS_mul_conj_radA1 {x : antiSp K} (hx : x ∈ radA1 K) : (wS : antiSp K) * x * wS ∈ radA1 K := by
  obtain ⟨b, c, d, rfl⟩ := hx
  have := wS_conj_uElt_zero (K := K) b c d
  rw [wS_inv] at this
  rw [this]
  exact ⟨b, d, c, rfl⟩

theorem wT_mul_conj_radA2 {x : antiSp K} (hx : x ∈ radA2 K) : (wT : antiSp K) * x * wT ∈ radA2 K := by
  obtain ⟨a, b, c, rfl⟩ := hx
  have := wT_conj_uElt_zero (K := K) a b c
  rw [wT_inv] at this
  rw [this]
  exact ⟨b, a, c, rfl⟩

theorem wS_mem_normalizer_radA1 :
    (wS : antiSp K) ∈ Subgroup.normalizer (radA1 K : Set (antiSp K)) :=
  mem_normalizer_of_conj _ (fun v hv => by rw [wS_inv]; exact wS_mul_conj_radA1 hv)
    (fun v hv => by rw [wS_inv]; exact wS_mul_conj_radA1 hv)

theorem wT_mem_normalizer_radA2 :
    (wT : antiSp K) ∈ Subgroup.normalizer (radA2 K : Set (antiSp K)) :=
  mem_normalizer_of_conj _ (fun v hv => by rw [wT_inv]; exact wT_mul_conj_radA2 hv)
    (fun v hv => by rw [wT_inv]; exact wT_mul_conj_radA2 hv)

theorem lt_normalizer_radA1 [Finite K] :
    Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) <
      Subgroup.normalizer (radA1 K : Set (antiSp K)) :=
  lt_of_le_of_ne normalizer_U_le_normalizer_radA1
    fun h => wS_not_mem_normalizer_U (h ▸ wS_mem_normalizer_radA1)

theorem lt_normalizer_radA2 [Finite K] :
    Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) <
      Subgroup.normalizer (radA2 K : Set (antiSp K)) :=
  lt_of_le_of_ne normalizer_U_le_normalizer_radA2
    fun h => wT_not_mem_normalizer_U (h ▸ wT_mem_normalizer_radA2)

theorem normalizer_radA1_lt_top :
    Subgroup.normalizer (radA1 K : Set (antiSp K)) < ⊤ :=
  lt_top_iff_ne_top.mpr fun h =>
    wT_not_mem_normalizer_radA1 (by rw [h]; exact Subgroup.mem_top _)

theorem normalizer_radA2_lt_top :
    Subgroup.normalizer (radA2 K : Set (antiSp K)) < ⊤ :=
  lt_top_iff_ne_top.mpr fun h =>
    wS_not_mem_normalizer_radA2 (by rw [h]; exact Subgroup.mem_top _)

theorem isElemAbelian_radA1 : IsElemAbelian 2 (radA1 K) :=
  ⟨isMulCommutative_iff_of_setLike.mpr fun x hx y hy => radA1_comm hx hy,
    fun x hx => by rw [pow_two]; exact mul_self_of_mem_radA1 hx⟩

theorem isElemAbelian_radA2 : IsElemAbelian 2 (radA2 K) :=
  ⟨isMulCommutative_iff_of_setLike.mpr fun x hx y hy => radA2_comm hx hy,
    fun x hx => by rw [pow_two]; exact mul_self_of_mem_radA2 hx⟩

theorem isPGroup_radA1 : IsPGroup 2 (radA1 K) :=
  fun x => ⟨1, Subtype.ext (by simpa using isElemAbelian_radA1.2 _ x.2)⟩

theorem isPGroup_radA2 : IsPGroup 2 (radA2 K) :=
  fun x => ⟨1, Subtype.ext (by simpa using isElemAbelian_radA2.2 _ x.2)⟩

theorem core_radA1 [Finite K] :
    pCoreOf 2 (Subgroup.normalizer (radA1 K : Set (antiSp K))) = radA1 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set N := Subgroup.normalizer (radA1 K : Set (antiSp K)) with hN
    have hSyl : IsSylowTwoOf (antiUnipotent K) N :=
      isSylowTwoOf_of_le card_and_isSylowTwoOf_antiUnipotent.2 U_le_normalizer_radA1
    have hC := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
    intro c hc
    obtain ⟨a, b, c', d, rfl⟩ := hC hc
    have hcn : wS * uElt a b c' d * (wS : antiSp K)⁻¹ ∈ pCoreOf 2 N := by
      have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N wS_mem_normalizer_radA1
      exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp hc
    have hcU' := hC hcn
    have ha : a = 0 := by
      by_contra ha
      have := ((mem_antiUnipotent_iff_upper _).mp hcU').1 1 0 (by decide)
      rw [glMat_wS_conj] at this
      simp at this
      exact ha this
    subst ha
    exact ⟨b, c', d, rfl⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      isPGroup_radA1

theorem core_radA2 [Finite K] :
    pCoreOf 2 (Subgroup.normalizer (radA2 K : Set (antiSp K))) = radA2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set N := Subgroup.normalizer (radA2 K : Set (antiSp K)) with hN
    have hSyl : IsSylowTwoOf (antiUnipotent K) N :=
      isSylowTwoOf_of_le card_and_isSylowTwoOf_antiUnipotent.2 U_le_normalizer_radA2
    have hC := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
    intro c hc
    obtain ⟨a, b, c', d, rfl⟩ := hC hc
    have hcn : wT * uElt a b c' d * (wT : antiSp K)⁻¹ ∈ pCoreOf 2 N := by
      have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N wT_mem_normalizer_radA2
      exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp hc
    have hcU' := hC hcn
    have hd : d = 0 := by
      by_contra hd
      have := ((mem_antiUnipotent_iff_upper _).mp hcU').1 2 1 (by decide)
      rw [glMat_wT_conj] at this
      simp at this
      exact hd this
    subst hd
    exact ⟨a, b, c', rfl⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      isPGroup_radA2

theorem mem_antiUnipotent_of_comm {g : antiSp K}
    (h1 : g * uElt 0 1 0 0 = uElt 0 1 0 0 * g) (h2 : g * uElt 0 0 1 0 = uElt 0 0 1 0 * g) :
    g ∈ antiUnipotent K := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h1
  have e2 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h2
  simp only [glMat_mul, glMat_uElt] at e1 e2
  have hJ := mem_antiSp.mp g.2
  have e03 := congrFun (congrFun hJ 0) 3
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at e03
  set M := glMat (g : GL (Fin 4) K) with hM
  have m10 : M 1 0 = 0 := by
    have := congrFun (congrFun e2 1) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have m20 : M 2 0 = 0 := by
    have := congrFun (congrFun e2 2) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have m30 : M 3 0 = 0 := by
    have := congrFun (congrFun e2 3) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have m32 : M 3 2 = 0 := by
    have := congrFun (congrFun e2 0) 2
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have d03 : M 0 0 = M 3 3 := by
    have := congrFun (congrFun e2 0) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have m21 : M 2 1 = 0 := by
    have := congrFun (congrFun e1 2) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have m31 : M 3 1 = 0 := by
    have := congrFun (congrFun e1 3) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have d02 : M 0 0 = M 2 2 := by
    have := congrFun (congrFun e1 0) 2
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have d13 : M 1 1 = M 3 3 := by
    have := congrFun (congrFun e1 1) 3
    simp [uMat, mul_apply, Fin.sum_univ_four] at this
    linear_combination this
  have hsq : M 0 0 * M 0 0 = 1 := by
    have e03' : M 0 0 * M 3 3 + M 1 0 * M 2 3 + M 2 0 * M 1 3 + M 3 0 * M 0 3 = 1 := by
      rw [e03]
      simp
    rw [m10, m20, m30, ← d03] at e03'
    linear_combination e03'
  have h00 : M 0 0 = 1 := by
    have : (M 0 0 - 1) ^ 2 = 0 := by linear_combination hsq + (1 - M 0 0) * h2K
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linear_combination this
  rw [mem_antiUnipotent_iff_upper]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hij; decide)
        | exact m10 | exact m20 | exact m30 | exact m21 | exact m31 | exact m32
  · fin_cases i
    · exact h00
    · show M 1 1 = 1
      rw [d13, ← d03, h00]
    · show M 2 2 = 1
      rw [← d02, h00]
    · show M 3 3 = 1
      rw [← d03, h00]

theorem cent_radA1 {g : antiSp K} (hc : ∀ r ∈ radA1 K, g * r = r * g) : g ∈ radA1 K :=
  mem_radA1_of_commutes
    (mem_antiUnipotent_of_comm (hc _ (⟨1, 0, 0, rfl⟩ : (uElt 0 1 0 0 : antiSp K) ∈ radA1 K))
      (hc _ (⟨0, 1, 0, rfl⟩ : (uElt 0 0 1 0 : antiSp K) ∈ radA1 K))) hc

theorem cent_radA2 {g : antiSp K} (hc : ∀ r ∈ radA2 K, g * r = r * g) : g ∈ radA2 K :=
  mem_radA2_of_commutes
    (mem_antiUnipotent_of_comm (hc _ (⟨0, 1, 0, rfl⟩ : (uElt 0 1 0 0 : antiSp K) ∈ radA2 K))
      (hc _ (⟨0, 0, 1, rfl⟩ : (uElt 0 0 1 0 : antiSp K) ∈ radA2 K))) hc

theorem center_trivial_Sp : ∀ m : antiSp K, (∀ y, m * y = y * m) → m = 1 := by
  intro m hm
  have h : MulAut.conj m = MulAut.conj (1 : antiSp K) := by
    ext y
    rw [MulAut.conj_apply, hm y]
    simp
  exact conj_injective h

theorem not_le_centralizer_radA1 :
    ¬ radA2 K ≤ Subgroup.centralizer (radA1 K : Set (antiSp K)) := by
  intro h
  have h1 : (uElt 1 0 0 0 : antiSp K) ∈ radA2 K := ⟨1, 0, 0, rfl⟩
  have h2 : (uElt 0 0 0 1 : antiSp K) ∈ radA1 K := ⟨0, 0, 1, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp (h h1) _ h2
  rw [uElt_mul, uElt_mul] at hc
  have := (uElt_inj hc).2.1
  simp at this

theorem radA_inf_le_commutator (hK : 2 < Nat.card K) :
    radA1 K ⊓ radA2 K ≤ ⁅radA1 K, radA2 K⁆ := by
  rw [radA1_inf_radA2, ← closure_squares_eq hK, Subgroup.commutator_comm]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨_, ⟨a, b, c, d, rfl⟩, rfl⟩
  rw [uElt_mul_self, ← commutator_uElt]
  exact Subgroup.commutator_mem_commutator
    (⟨a, 0, 0, rfl⟩ : (uElt a 0 0 0 : antiSp K) ∈ radA2 K)
    (⟨0, 0, d, rfl⟩ : (uElt 0 0 0 d : antiSp K) ∈ radA1 K)

@[expose] def dSpMat (s t : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![(s : K), (t : K), ((t⁻¹ : Kˣ) : K), ((s⁻¹ : Kˣ) : K)]

omit [CharP K 2] in
theorem dSpMat_mul (s t s' t' : Kˣ) :
    (dSpMat s t : Matrix (Fin 4) (Fin 4) K) * dSpMat s' t' = dSpMat (s * s') (t * t') := by
  simp only [dSpMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

omit [CharP K 2] in
theorem dSpMat_one : (dSpMat 1 1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dSpMat, one_apply]

omit [CharP K 2] in
theorem dSpMat_mem (s t : Kˣ) :
    (dSpMat s t : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * dSpMat s t = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSpMat, mul_apply, Fin.sum_univ_four, minorJ_apply, Matrix.diagonal_apply]

@[expose] def dSp (s t : Kˣ) : antiSp K :=
  ⟨⟨dSpMat s t, dSpMat s⁻¹ t⁻¹, by rw [dSpMat_mul, mul_inv_cancel, mul_inv_cancel, dSpMat_one],
    by rw [dSpMat_mul, inv_mul_cancel, inv_mul_cancel, dSpMat_one]⟩, dSpMat_mem s t⟩

omit [CharP K 2] in
theorem glMat_dSp (s t : Kˣ) : glMat ((dSp s t : antiSp K) : GL (Fin 4) K) = dSpMat s t := rfl

omit [CharP K 2] in
theorem dSp_mul (s t s' t' : Kˣ) : (dSp s t : antiSp K) * dSp s' t' = dSp (s * s') (t * t') :=
  antiSp_ext (dSpMat_mul s t s' t')

omit [CharP K 2] in
theorem dSp_one : (dSp 1 1 : antiSp K) = 1 := antiSp_ext dSpMat_one

omit [CharP K 2] in
theorem dSp_inv (s t : Kˣ) : (dSp s t : antiSp K)⁻¹ = dSp s⁻¹ t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [dSp_mul, mul_inv_cancel, mul_inv_cancel, dSp_one])

omit [CharP K 2] in
theorem dSp_pow (s t : Kˣ) (k : ℕ) : (dSp s t : antiSp K) ^ k = dSp (s ^ k) (t ^ k) := by
  induction k with
  | zero => simp [dSp_one]
  | succ k ih => rw [pow_succ, ih, dSp_mul, pow_succ, pow_succ]

omit [CharP K 2] in
theorem dSp_eq_one {s t : Kˣ} (h : (dSp s t : antiSp K) = 1) : s = 1 ∧ t = 1 := by
  have h' := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp [glMat_dSp, dSpMat] at h0 h1
  exact ⟨h0, h1⟩

theorem dSp_conj_uElt (s t : Kˣ) (a b c d : K) :
    (dSp s t * uElt a b c d * (dSp s t : antiSp K)⁻¹ : antiSp K) =
      uElt ((s : K) * (t⁻¹ : Kˣ) * a) ((s : K) * t * b) ((s : K) ^ 2 * c) ((t : K) ^ 2 * d) := by
  apply antiSp_ext
  rw [dSp_inv, glMat_mul, glMat_mul, glMat_uElt, glMat_uElt, glMat_dSp, glMat_dSp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSpMat, uMat, mul_apply, Matrix.diagonal_apply] <;>
    field_simp

theorem dSp_mem_normalizer (s t : Kˣ) :
    (dSp s t : antiSp K) ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  have key : ∀ (s t : Kˣ), ∀ u ∈ antiUnipotent K,
      (dSp s t * u * (dSp s t : antiSp K)⁻¹ : antiSp K) ∈ antiUnipotent K := by
    intro s t u hu
    obtain ⟨a, b, c, d, rfl⟩ := hu
    rw [dSp_conj_uElt]
    exact uElt_mem_antiUnipotent _ _ _ _
  refine mem_normalizer_of_conj _ (key s t) fun v hv => ?_
  have := key s⁻¹ t⁻¹ v hv
  rwa [dSp_inv s⁻¹ t⁻¹, inv_inv, inv_inv, ← dSp_inv] at this

theorem exists_torus_Sp [Finite K] (hK : 2 < Nat.card K) {p : ℕ} (hp : p.Prime) {t : Kˣ}
    (ht : orderOf t = p) :
    ∃ h ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), (∃ k : ℕ, orderOf h = p ^ k) ∧
      ¬ ⁅radA1 K, radA2 K⁆ ≤ Subgroup.centralizer ({h} : Set (antiSp K)) := by
  have htp : t ^ p = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  refine ⟨dSp t 1, dSp_mem_normalizer t 1, ?_, ?_⟩
  · have hpow : (dSp t 1 : antiSp K) ^ p = 1 := by
      rw [dSp_pow, htp, one_pow, dSp_one]
    have hd : orderOf (dSp t 1 : antiSp K) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  · intro hle
    have hz : (uElt 0 0 1 0 : antiSp K) ∈ ⁅radA1 K, radA2 K⁆ :=
      radA_inf_le_commutator hK ⟨⟨0, 1, 0, rfl⟩, ⟨0, 0, 1, rfl⟩⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
    have h3 : (dSp t 1 * uElt 0 0 1 0 * (dSp t 1 : antiSp K)⁻¹ : antiSp K) = uElt 0 0 1 0 := by
      rw [← hc]
      group
    rw [dSp_conj_uElt] at h3
    have h4 := (uElt_inj h3).2.2.1
    have h5 : ((t : K) - 1) ^ 2 = 0 := by
      linear_combination h4 + (1 - (t : K)) * (CharTwo.two_eq_zero (R := K))
    have h6 : (t : K) = 1 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h5
      linear_combination this
    have h7 : t = 1 := Units.ext (by simpa using h6)
    rw [h7, orderOf_one] at ht
    exact hp.one_lt.ne ht

omit [CharP K 2] in
theorem exists_P0_Sp [Finite K] {p : ℕ} (hp : p.Prime) {t : Kˣ} (ht : orderOf t = p) :
    ∃ P₀ : Subgroup (antiSp K), IsElemAbelian p P₀ ∧ Nat.card P₀ = p ^ 2 := by
  have htp : t ^ p = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hab : (dSp t 1 : antiSp K) * dSp 1 t = dSp 1 t * dSp t 1 := by
    rw [dSp_mul, dSp_mul]
    simp
  have ha : (dSp t 1 : antiSp K) ^ p = 1 := by rw [dSp_pow, htp, one_pow, dSp_one]
  have hb : (dSp 1 t : antiSp K) ^ p = 1 := by rw [dSp_pow, htp, one_pow, dSp_one]
  have hind : ∀ i j : ℕ, (dSp t 1 : antiSp K) ^ i * (dSp 1 t) ^ j = 1 → p ∣ i ∧ p ∣ j := by
    intro i j hij
    rw [dSp_pow, dSp_pow, dSp_mul, one_pow, one_pow, mul_one, one_mul] at hij
    obtain ⟨h1, h2⟩ := dSp_eq_one hij
    exact ⟨ht ▸ orderOf_dvd_of_pow_eq_one h1, ht ▸ orderOf_dvd_of_pow_eq_one h2⟩
  obtain ⟨P₀, h1, h2, -, -⟩ := exists_elemAbelian_pair hp hab ha hb hind
  exact ⟨P₀, h1, h2⟩

theorem torus_Sp [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (∃ P₀ : Subgroup (antiSp K), IsElemAbelian p P₀ ∧ Nat.card P₀ = p ^ 2) ∧
      ∃ h ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
        (∃ k : ℕ, orderOf h = p ^ k) ∧
        ¬ ⁅radA1 K, radA2 K⁆ ≤ Subgroup.centralizer ({h} : Set (antiSp K)) := by
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK2 : 2 < Nat.card K := by omega
  have hne1 : 2 ^ n - 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 :=
    ⟨_, Nat.minFac_prime hne1, Nat.minFac_dvd _⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
    obtain ⟨k, hk⟩ := hpd
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hpc : p ∣ Nat.card Kˣ := by rw [hcard]; exact hpd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hpc
  obtain ⟨P₀, hP₀⟩ := exists_P0_Sp hp ht
  obtain ⟨h, hh, hk, hc⟩ := exists_torus_Sp hK2 hp ht
  exact ⟨p, hp, hp2, ⟨P₀, hP₀⟩, h, hh, hk, hc⟩

theorem lieModel_Sp [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    CFSG.Blueprint.LieModel (antiSp K) .PSp 2 2 n := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨antiProjEquiv K⟩⟩
  intro h
  have := (Prod.mk.inj h).2
  omega

open CFSG.LocalAnalysis.ComponentInitial in
theorem coverElem_Sp [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (R : Subgroup (antiSp K)) (hR : IsElemAbelian 2 R) : CoverElem (antiSp K) R := by
  intro X _ _ hperf η hη hcen h2 _
  have hC : η.ker ≤ Subgroup.center X := fun z hz =>
    Subgroup.mem_center_iff.mpr fun y => (hcen z hz y).symm
  obtain ⟨-, hbij⟩ := SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial
    η hη hC h2 hn (lieModel_Sp hn hK)
  have hinj : Function.Injective η := hbij.1
  refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
  · intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hR.1.is_comm.comm ⟨η x, hx⟩ ⟨η y, hy⟩)
  · intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hR.2 _ hx

theorem modelData_Sp [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ModelData (antiSp K) (antiUnipotent K) (radA1 K) (radA2 K) where
  center_trivial := center_trivial_Sp
  sylow := card_and_isSylowTwoOf_antiUnipotent.2
  elem₁ := isElemAbelian_radA1
  elem₂ := isElemAbelian_radA2
  le₁ := radA1_le_antiUnipotent
  le₂ := radA2_le_antiUnipotent
  sup := antiUnipotent_eq_radA1_sup_radA2.symm
  ne := radA1_ne_radA2
  noncomm := not_le_centralizer_radA1
  inter_le_comm := radA_inf_le_commutator (by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega)
  cent₁ := fun g hg => cent_radA1 hg
  cent₂ := fun g hg => cent_radA2 hg
  lt₁ := lt_normalizer_radA1
  lt₂ := lt_normalizer_radA2
  lt_top₁ := normalizer_radA1_lt_top
  lt_top₂ := normalizer_radA2_lt_top
  core₁ := core_radA1
  core₂ := core_radA2
  torus := torus_Sp hn hK

theorem modelPkg_Sp [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ModelPkg (antiSp K) (antiUnipotent K) (radA1 K) (radA2 K) where
  data := modelData_Sp hn hK
  cov₁ := coverElem_Sp hn hK _ isElemAbelian_radA1
  cov₂ := coverElem_Sp hn hK _ isElemAbelian_radA2

end Sp4

end CFSG.QuasithinUnique.Fin257
