module

public import CFSG.GH74.Generic.BProg.B1.PilotS5Facts
import CFSG.GH74.Generic.BProg.B1.PilotS3Models
import CFSG.GH74.Generic.BProg.B1.PilotS4Facts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic.BProg
open CFSG.GH74.Generic.BProg.B1 CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem commuting_sl2_exists_two_roots (F : Type*) [Field F] :
    ∃ x y : SL(2, F), x ^ 2 = -1 ∧ y ^ 2 = -1 ∧ y ≠ x ∧ y ≠ x⁻¹ := by
  have hdet : (!![1, 1; -2, -1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two_of]
    ring
  obtain ⟨y, hy⟩ : ∃ y : SL(2, F), (y : Matrix (Fin 2) (Fin 2) F) = !![1, 1; -2, -1] :=
    ⟨⟨!![1, 1; -2, -1], hdet⟩, rfl⟩
  refine ⟨slQuatI F, y, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_slQuatI_sq]
    simp
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, sq, hy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · intro h
    have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
    rw [hy] at this
    simp [slQuatI, quatI] at this
  · intro h
    have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
    rw [hy, coe_slQuatI_inv] at this
    simp at this

theorem commuting_sl2_roots_of_equiv {X : Type*} [Group X] {A : Subgroup X} {F : Type*} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (e : ↥A ≃* SL(2, F)) :
    ∃ z i₁ i₂ : X, z ∈ A ∧ i₁ ∈ A ∧ i₂ ∈ A ∧ orderOf z = 2 ∧ (∀ a ∈ A, a * z = z * a) ∧
      i₁ ^ 2 = z ∧ i₂ ^ 2 = z ∧ i₂ ≠ i₁ ∧ i₂ ≠ i₁⁻¹ := by
  obtain ⟨x, y, hx, hy, hxy, hxy'⟩ := commuting_sl2_exists_two_roots F
  refine ⟨(e.symm (-1) : X), (e.symm x : X), (e.symm y : X), (e.symm (-1)).2, (e.symm x).2,
    (e.symm y).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact sl2_orderOf_neg_one hodd
  · intro a ha
    have hc : e.symm (-1) ∈ Subgroup.center ↥A := by
      rw [mem_center_iff_of_equiv_sl2 e, MulEquiv.apply_symm_apply]
      exact (mem_center_sl2_iff _).2 (Or.inr rfl)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨a, ha⟩)
  · rw [← Subgroup.coe_pow, ← map_pow, hx]
  · rw [← Subgroup.coe_pow, ← map_pow, hy]
  · intro h
    exact hxy (e.symm.injective (Subtype.ext h))
  · intro h
    apply hxy'
    apply e.symm.injective
    rw [map_inv]
    exact Subtype.ext h

theorem commuting_sl2_false_of_roots {X : Type*} [Group X] {J : Subgroup X} {F : Type*} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (eJ : ↥J ≃* SL(2, F)) {u u' i₁ i₂ j : X}
    (hu : orderOf u = 2) (hu' : orderOf u' = 2) (hi₁ : i₁ ∈ J) (hi₂ : i₂ ∈ J) (hj : j ∈ J)
    (hi₁u : i₁ ^ 2 = u) (hi₂u : i₂ ^ 2 = u) (hju : j ^ 2 = u')
    (h₁ : i₁ * j = j * i₁) (h₂ : i₂ * j = j * i₂) (hne : i₂ ≠ i₁) (hne' : i₂ ≠ i₁⁻¹) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huJ : u ∈ J := hi₁u ▸ J.pow_mem hi₁ 2
  have hu'J : u' ∈ J := hju ▸ J.pow_mem hj 2
  have hinv : ∀ x ∈ J, ∀ y ∈ J, orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x hx y hy hxo hyo
    have h1 : (⟨x, hx⟩ : ↥J) = eJ.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd eJ _).1 (by rwa [Subgroup.orderOf_mk])
    have h2 : (⟨y, hy⟩ : ↥J) = eJ.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd eJ _).1 (by rwa [Subgroup.orderOf_mk])
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hu'u : u' = u := hinv u' hu'J u huJ hu' hu
  have hu1 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have key : ∀ i ∈ J, i ^ 2 = u → i * j = j * i → j = i⁻¹ ∨ j = i := by
    intro i hiJ hi hij
    have hsq : (i * j) ^ 2 = 1 := by
      rw [(show Commute i j from hij).mul_pow, hi, hju, hu'u, ← pow_two]
      exact hu1
    by_cases h1 : i * j = 1
    · exact Or.inl (eq_inv_of_mul_eq_one_right h1)
    · right
      have h2 : i * j = u :=
        hinv (i * j) (J.mul_mem hiJ hj) u huJ (orderOf_eq_prime hsq h1) hu
      apply mul_left_cancel (a := i)
      rw [h2, ← hi, pow_two]
  rcases key i₁ hi₁ hi₁u h₁ with h | h <;> rcases key i₂ hi₂ hi₂u h₂ with h' | h'
  · exact hne (inv_inj.1 (h.symm.trans h')).symm
  · exact hne' (h'.symm.trans h)
  · exact hne' (inv_eq_iff_eq_inv.1 (h'.symm.trans h))
  · exact hne (h'.symm.trans h)

theorem commuting_sl2_splitLike_false {X : Type} [Group X] {n : ℕ}
    (hY : PilotS5.SplitLike n (⊤ : Subgroup X)) {A : Subgroup X} {u : X} (hu : orderOf u = 2)
    (huA : u ∈ A) (hAu : A ≤ Subgroup.centralizer ({u} : Set X)) (hA : ⁅A, A⁆ = A) : False := by
  obtain ⟨L, -, hL⟩ := hY.split u (Subgroup.mem_top u) hu
  exact hL.not_mem (hL.le_of_perfect' (le_inf hAu le_top) hA huA)

theorem not_qShapeNS_of_commuting_sl2
    {X : Type} [Group X] [Finite X]
    (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1) {A B : Subgroup X}
    {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (hF₁ : Odd (Nat.card F₁)) (h₁ : 5 ≤ Nat.card F₁) (hF₂ : Odd (Nat.card F₂))
    (h₂ : 5 ≤ Nat.card F₂) (eA : ↥A ≃* SL(2, F₁)) (eB : ↥B ≃* SL(2, F₂))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ¬ QShapeNS X := by
  intro hX
  obtain ⟨u, a₁, a₂, huA, ha₁, ha₂, hu2, hucent, ha₁sq, ha₂sq, hne, hne'⟩ :=
    commuting_sl2_roots_of_equiv hF₁ eA
  obtain ⟨u', b, -, -, hbB, -, hu'2, -, hbsq, -, -, -⟩ := commuting_sl2_roots_of_equiv hF₂ eB
  have hAu : A ≤ Subgroup.centralizer ({u} : Set X) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hucent a ha)
  have hBu : B ≤ Subgroup.centralizer ({u} : Set X) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAB u huA b hb).symm
  have hAperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.1 (isPerfect_of_equiv_sl2 (by omega) eA)
  have hBperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.1 (isPerfect_of_equiv_sl2 (by omega) eB)
  rcases hX with h1 | h3 | h4 | h5
  · have hc := CFSG.GH74.L5U5.IsSL4Model.natCard_center h1
    have hz : Subgroup.center X = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      exact hZ z fun g => Subgroup.mem_center_iff.1 hz g
    rw [hz, Subgroup.card_bot] at hc
    omega
  · obtain ⟨F, _, _, P, _, ⟨e⟩, hP⟩ := PilotS3.exists_equiv_grpS3_of_qShape3 h3
    have hY : PilotS3.Split3Like F (⊤ : Subgroup X) :=
      PilotS3.Split3Like.of_equiv (Subgroup.topEquiv.trans e) hP
        (fun z _ hz => hZ z fun g => hz g (Subgroup.mem_top g))
    obtain ⟨J, -, hJ⟩ := hY.split u (Subgroup.mem_top u) hu2
    have hAJ : A ≤ J := hJ.le_of_perfect' (le_inf hAu le_top) hAperf
    have hBJ : B ≤ J := hJ.le_of_perfect' (le_inf hBu le_top) hBperf
    obtain ⟨eJ⟩ := hJ.equiv
    exact commuting_sl2_false_of_roots hJ.odd eJ hu2 hu'2 (hAJ ha₁) (hAJ ha₂) (hBJ hbB) ha₁sq
      ha₂sq hbsq (hAB a₁ ha₁ b hbB) (hAB a₂ ha₂ b hbB) hne hne'
  · obtain ⟨n, hn⟩ := PilotS4.splitGrp_of_qShape4 h4
    exact commuting_sl2_splitLike_false (hn.map_equiv Subgroup.topEquiv.symm).splitLike hu2 huA
      hAu hAperf
  · obtain ⟨e0⟩ := h5
    exact commuting_sl2_splitLike_false (PilotS5.SplitLike.of_equiv
      (Subgroup.topEquiv.trans (e0.trans CFSG.Walter.walterJ1EquivNative.symm))) hu2 huA hAu
      hAperf

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
