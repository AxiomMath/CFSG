module

public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverUnitriangularFour

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace UnitaryFourCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag LinearCover LinearFlag

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

include h in
theorem two_eq_zero : (2 : K) = 0 := by
  have := h.charP
  exact_mod_cast CharP.cast_eq_zero K 2

theorem bar_apply_two (c : K) : h.bar c = c ^ 2 := by
  rw [h.bar_apply, pow_one]

@[expose] noncomputable def ι : ZMod 2 →+* K :=
  have := h.charP
  ZMod.castHom (dvd_refl 2) K

theorem ι_mul_self (x : ZMod 2) : ι h x * ι h x = ι h x := by
  rw [← map_mul]
  congr 1
  revert x
  decide

theorem bar_ι (x : ZMod 2) : h.bar (ι h x) = ι h x := by
  rw [bar_apply_two, sq, ι_mul_self]

theorem ι_injective : Function.Injective (ι h) := by
  have := h.charP
  exact (ZMod.castHom (dvd_refl 2) K).injective

include h in
theorem exists_omega : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card]
    norm_num
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra! hc
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hc x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hcard] at this
  refine ⟨ω, ?_⟩
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)

variable (ω : K)

@[expose] noncomputable def tPar (v : Fin 6 → ZMod 2) : K := ι h (v 0) + ι h (v 2) * ω

@[expose] noncomputable def sPar (v : Fin 6 → ZMod 2) : K :=
  ι h (v 3 + v 0 * v 1) + ι h (v 4) * ω

@[expose] noncomputable def cPar (v : Fin 6 → ZMod 2) : K :=
  ι h (v 5 + v 4 * v 0 + v 3 + v 0 * v 1 + v 4)

@[expose] noncomputable def matA (v : Fin 6 → ZMod 2) : Matrix (Fin 2) (Fin 2) K :=
  !![1, tPar h ω v; 0, 1]

@[expose] noncomputable def matC (v : Fin 6 → ZMod 2) : Matrix (Fin 2) (Fin 2) K :=
  !![cPar h v, sPar h ω v; -h.bar (sPar h ω v), ι h (v 1)]

theorem matA_isUnitriangular (v : Fin 6 → ZMod 2) : IsUnitriangular (matA h ω v) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [matA]
  · fin_cases i <;> simp [matA]

theorem bar_cPar (v : Fin 6 → ZMod 2) : h.bar (cPar h v) = cPar h v :=
  bar_ι h _

theorem matC_skew (v : Fin 6 → ZMod 2) : matC h ω v + ((matC h ω v).map h.bar)ᵀ = 0 := by
  have h2 := two_eq_zero h
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.add_apply, transpose_apply, map_apply,
      Matrix.zero_apply]
    simp only [matC, of_apply, cons_val_zero, bar_cPar]
    linear_combination (cPar h v) * h2
  · simp [matC, h.bar_bar]
  · simp [matC]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.add_apply, transpose_apply, map_apply,
      Matrix.zero_apply]
    simp only [matC, of_apply, cons_val_one, cons_val_zero, bar_ι]
    linear_combination (ι h (v 1)) * h2

@[expose] noncomputable def elt (v : Fin 6 → ZMod 2) : hypUnitriangular h 2 0 :=
  evenUnitriangularElt (matA_isUnitriangular h ω v) (matC_skew h ω v)

theorem coe_elt (v : Fin 6 → ZMod 2) :
    ((((elt h ω v : hypUnitriangular h 2 0) : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = evenMat h (matA h ω v) (matC h ω v) :=
  rfl

theorem inv_matA (v : Fin 6 → ZMod 2) : (matA h ω v)⁻¹ = !![1, -tPar h ω v; 0, 1] := by
  refine inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, mul_apply]

theorem barInvT_matA (v : Fin 6 → ZMod 2) :
    barInvT h (matA h ω v) = !![1, 0; -h.bar (tPar h ω v), 1] := by
  refine (eq_barInvT_of_mul_eq_one ?_).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, mul_apply]

theorem elt_eq_mul {u v w : Fin 6 → ZMod 2} (hA : matA h ω w = matA h ω u * matA h ω v)
    (hC : matC h ω w = matC h ω v + !![1, -tPar h ω v; 0, 1] * matC h ω u *
      !![1, 0; -h.bar (tPar h ω v), 1]) :
    elt h ω w = elt h ω u * elt h ω v := by
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change evenMat h (matA h ω w) (matC h ω w) = evenMat h (matA h ω u) (matC h ω u) *
    evenMat h (matA h ω v) (matC h ω v)
  rw [evenMat_mul (matA_isUnitriangular h ω v).isUnit_det, inv_matA, barInvT_matA, hA, hC]

@[expose] def vec (X : U4) : Fin 6 → ZMod 2 :=
  ![((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1,
    ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2,
    ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3,
    ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2,
    ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3,
    ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3]

theorem vec_u4a : vec u4a = ![1, 0, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl

theorem vec_u4b : vec u4b = ![0, 1, 0, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl

theorem vec_u4c : vec u4c = ![0, 0, 1, 0, 0, 0] := by
  funext k
  fin_cases k <;> rfl

theorem coe_U4_mul (g X : U4) :
    (((g * X : U4) : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((g : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  rfl

theorem coe_u4a : ((u4a : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = mA := rfl

theorem coe_u4b : ((u4b : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = mB := rfl

theorem coe_u4c : ((u4c : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = mC := rfl

theorem vec_u4a_mul (X : U4) :
    vec (u4a * X) = ![vec X 0 + 1, vec X 1, vec X 2, vec X 3 + vec X 1, vec X 4,
      vec X 5 + vec X 4] := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp X.2
  funext k
  fin_cases k <;>
    simp [vec, coe_u4a, mA, mul_apply, Fin.sum_univ_four, single_apply, hd, hl 2 1 (by decide),
      hl 3 1 (by decide), hl 3 2 (by decide)]

theorem vec_u4b_mul (X : U4) :
    vec (u4b * X) = ![vec X 0, vec X 1 + 1, vec X 2, vec X 3, vec X 4 + vec X 2, vec X 5] := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp X.2
  funext k
  fin_cases k <;>
    simp [vec, coe_u4b, mB, mul_apply, Fin.sum_univ_four, single_apply, hd, hl 2 1 (by decide),
      hl 3 1 (by decide), hl 3 2 (by decide)]

theorem vec_u4c_mul (X : U4) :
    vec (u4c * X) = ![vec X 0, vec X 1, vec X 2 + 1, vec X 3, vec X 4, vec X 5] := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp X.2
  funext k
  fin_cases k <;>
    simp [vec, coe_u4c, mC, mul_apply, Fin.sum_univ_four, single_apply, hd, hl 2 1 (by decide),
      hl 3 1 (by decide), hl 3 2 (by decide)]

variable {ω} (hω : ω ^ 2 + ω + 1 = 0)

theorem elt_u4a_mul (X : U4) : elt h ω (vec (u4a * X)) = elt h ω (vec u4a) * elt h ω (vec X) := by
  have h2 := two_eq_zero h
  rw [vec_u4a_mul, vec_u4a]
  apply elt_eq_mul
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matA, tPar, mul_apply]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matC, cPar, sPar, tPar]
    · linear_combination (ι h (vec X 4) + ι h (vec X 1)) * h2
    · linear_combination (ι h (vec X 1)) * h2
    · linear_combination (-h.bar (ι h (vec X 1))) * h2

include hω in
theorem elt_u4b_mul (X : U4) : elt h ω (vec (u4b * X)) = elt h ω (vec u4b) * elt h ω (vec X) := by
  have h2 := two_eq_zero h
  have ha := ι_mul_self h (vec X 0)
  have hb := ι_mul_self h (vec X 2)
  rw [vec_u4b_mul, vec_u4b]
  apply elt_eq_mul
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matA, tPar, mul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matC, cPar, sPar, tPar, bar_ι]
    · rw [bar_apply_two h ω]
      linear_combination (-1) * ha + (-ω ^ 3) * hb +
        (-(ι h (vec X 2)) * (ω - 1) - ι h (vec X 0) * ι h (vec X 2)) * hω +
        (ι h (vec X 0) * ι h (vec X 2)) * h2
    · linear_combination (ι h (vec X 0) + ι h (vec X 2) * ω) * h2
    · ring

theorem elt_u4c_mul (X : U4) : elt h ω (vec (u4c * X)) = elt h ω (vec u4c) * elt h ω (vec X) := by
  rw [vec_u4c_mul, vec_u4c]
  apply elt_eq_mul
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matA, tPar, mul_apply]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matC, cPar, sPar, tPar]

theorem map_mul_of_closure_eq_top {G H : Type*} [Group G] [Group H] (Φ : G → H) {S : Set G}
    (hS : Subgroup.closure S = ⊤) (h1 : Φ 1 = 1) (hg : ∀ g ∈ S, ∀ x, Φ (g * x) = Φ g * Φ x)
    (y x : G) : Φ (y * x) = Φ y * Φ x := by
  let T : Subgroup G :=
    { carrier := {y | ∀ x, Φ (y * x) = Φ y * Φ x}
      one_mem' := fun x => by rw [one_mul, h1, one_mul]
      mul_mem' := fun {a b} ha hb x => by
        rw [mul_assoc, ha, hb, ← mul_assoc, ← ha b]
      inv_mem' := fun {a} ha x => by
        have h' : ∀ z, Φ (a⁻¹ * z) = (Φ a)⁻¹ * Φ z := fun z => by
          rw [eq_inv_mul_iff_mul_eq, ← ha, mul_inv_cancel_left]
        have h'' : Φ a⁻¹ = (Φ a)⁻¹ := by
          have := h' 1
          rwa [mul_one, h1, mul_one] at this
        rw [h', h''] }
  have hT : S ⊆ T := fun g hg' x => hg g hg' x
  have := (Subgroup.closure_le T).mpr hT
  rw [hS] at this
  exact this (Subgroup.mem_top y) x

theorem vec_one : vec 1 = 0 := by
  funext k
  fin_cases k <;> rfl

theorem barInvT_one : barInvT h (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero _) (map_one _), inv_one, transpose_one]

theorem evenMat_one_zero : evenMat h (1 : Matrix (Fin 2) (Fin 2) K) 0 = 1 := by
  rw [evenMat, barInvT_one, Matrix.mul_zero]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  all_goals try exact isEmptyElim ‹Fin 0›
  all_goals simp [one_apply]

theorem elt_zero : elt h ω 0 = 1 := by
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change evenMat h (matA h ω 0) (matC h ω 0) = 1
  have hA : matA h ω 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matA, tPar]
  have hC : matC h ω 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matC, cPar, sPar]
  rw [hA, hC, evenMat_one_zero]

include hω in
theorem ι_add_mul_omega_eq_zero {x y : ZMod 2} (hxy : ι h x + ι h y * ω = 0) : x = 0 ∧ y = 0 := by
  have hι1 : ι h 1 = 1 := map_one _
  have hι0 : ι h 0 = 0 := map_zero _
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω1 : (1 : K) + ω ≠ 0 := by
    intro h1
    have : ω = -1 := by linear_combination h1
    rw [this] at hω
    norm_num at hω
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [hι0, hι1, zero_add, one_mul] at hxy
    exact absurd hxy hω0
  · rw [hι0, hι1, zero_mul, add_zero] at hxy
    exact absurd hxy one_ne_zero
  · rw [hι1, one_mul] at hxy
    exact absurd hxy hω1

@[expose] noncomputable def toU : U4 →* hypUnitriangular h 2 0 where
  toFun X := elt h ω (vec X)
  map_one' := by rw [vec_one, elt_zero]
  map_mul' := map_mul_of_closure_eq_top (fun X => elt h ω (vec X)) closure_u4abc
    (by rw [vec_one, elt_zero]) (by
      rintro g hg X
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact elt_u4a_mul h X
      · exact elt_u4b_mul h hω X
      · exact elt_u4c_mul h X)

theorem toU_apply (X : U4) : toU h hω X = elt h ω (vec X) :=
  rfl

theorem toU_injective : Function.Injective (toU h hω) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro X hX
  rw [MonoidHom.mem_ker, toU_apply] at hX
  have hmat : evenMat h (matA h ω (vec X)) (matC h ω (vec X)) =
      evenMat h (1 : Matrix (Fin 2) (Fin 2) K) 0 := by
    rw [evenMat_one_zero, ← coe_elt, hX]
    rfl
  obtain ⟨hA, hC⟩ := evenMat_inj (matA_isUnitriangular h ω _).isUnit_det hmat
  have ht : ι h (vec X 0) + ι h (vec X 2) * ω = 0 := by
    have := congrFun (congrFun hA 0) 1
    simpa [matA, tPar] using this
  have hs : ι h (vec X 3 + vec X 0 * vec X 1) + ι h (vec X 4) * ω = 0 := by
    have := congrFun (congrFun hC 0) 1
    simpa [matC, sPar] using this
  have hc : ι h (vec X 5 + vec X 4 * vec X 0 + vec X 3 + vec X 0 * vec X 1 + vec X 4) = 0 := by
    have := congrFun (congrFun hC 0) 0
    simpa [matC, cPar] using this
  have hj : ι h (vec X 1) = 0 := by
    have := congrFun (congrFun hC 1) 1
    simpa [matC] using this
  obtain ⟨h0, h2⟩ := ι_add_mul_omega_eq_zero h hω ht
  obtain ⟨h3, h4⟩ := ι_add_mul_omega_eq_zero h hω hs
  have h1 : vec X 1 = 0 := ι_injective h (by rw [hj, map_zero])
  have h5 : vec X 5 + vec X 4 * vec X 0 + vec X 3 + vec X 0 * vec X 1 + vec X 4 = 0 :=
    ι_injective h (by rw [hc, map_zero])
  rw [h0, h1, mul_zero, add_zero] at h3
  simp only [h0, h1, h3, h4, mul_zero, add_zero] at h5
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp X.2
  rw [Subgroup.mem_bot]
  apply U4_ext
  ext i j
  have e0 : ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1 = 0 :=
    h0
  have e1 : ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2 = 0 :=
    h1
  have e2 : ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3 = 0 :=
    h2
  have e3 : ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2 = 0 :=
    h3
  have e4 : ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3 = 0 :=
    h4
  have e5 : ((X : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3 = 0 :=
    h5
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, e2, e3, e4, e5, hd, hl 1 0 (by decide), hl 2 0 (by decide), hl 3 0 (by decide),
      hl 2 1 (by decide), hl 3 1 (by decide), hl 3 2 (by decide)]

theorem card_U4 : Nat.card U4 = 64 := by
  rw [card_unitriangular, Nat.card_zmod]
  norm_num

include h in
theorem card_hypUnitriangular_two : Nat.card (hypUnitriangular h 2 0) = 64 := by
  rw [card_hypUnitriangular h (Nat.zero_le 1)]
  norm_num

@[expose] noncomputable def u4Equiv : U4 ≃* hypUnitriangular h 2 0 :=
  MulEquiv.ofBijective (toU h hω)
    ((toU_injective h hω).bijective_of_nat_card_le (by rw [card_U4, card_hypUnitriangular_two h]))

end UnitaryFourCover

open UnitaryFourCover CFSG.ClassicalGroups.UnitaryFlag LinearCover

theorem exists_sylow_mulEquiv_U4_of_lieModel_PSU {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 4 2 1) :
    ∃ S : Sylow 2 Q, Nonempty ((S : Subgroup Q) ≃* U4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hQ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
    obtain ⟨ω, hω⟩ := exists_omega h
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
    let f : hypPSU h 2 0 ≃* Q := (hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm
    obtain ⟨-, -, -, ⟨eU, -⟩, ⟨P₀, hP₀⟩, -, -⟩ :=
      unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)
    let S : Sylow 2 Q := Sylow.mapSurjective (f := (f : hypPSU h 2 0 →* Q)) f.surjective P₀
    refine ⟨S, ⟨?_⟩⟩
    have hS : (S : Subgroup Q) = (hypProjUnitriangular h 2 0).map (f : hypPSU h 2 0 →* Q) := by
      rw [Sylow.coe_mapSurjective, hP₀]
    exact ((((MulEquiv.subgroupCongr hS).trans
      ((hypProjUnitriangular h 2 0).equivMapOfInjective _ f.injective).symm).trans
        eU.symm).trans (u4Equiv h hω).symm)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem unitary_four_field_two_binary_unitriangular_Sylow_and_cover_bound {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.Blueprint.LieModel Q .PSU 4 2 1) :
    (∀ S : Sylow 2 Q, Nonempty ((S : Subgroup Q) ≃* U4)) ∧
    ∀ {P : Type*} [Group P] [Finite P] [Group.IsPerfect P] (η : P →* Q),
      Function.Surjective η → η.ker ≤ Subgroup.center P → IsPGroup 2 η.ker →
        IsElementaryAbelian 2 η.ker ∧ Nat.card η.ker ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, ⟨e₀⟩⟩ := exists_sylow_mulEquiv_U4_of_lieModel_PSU hQ
  exact ⟨fun S => ⟨(Sylow.equiv S S₀).trans e₀⟩,
    fun η hη hK h2 => perfect_cover_kernel_bound_of_sylow η hη hK h2 S₀ e₀⟩

end CFSG.LocalAnalysis.ComponentInitial
