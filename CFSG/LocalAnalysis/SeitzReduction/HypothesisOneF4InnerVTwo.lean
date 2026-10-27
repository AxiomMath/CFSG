module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerV
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerTwoTU

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover (xr)
open scoped commutatorElement

@[expose] def f4HeightThree : List ℕ :=
  [29, 30, 31, 32, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

@[expose] def f4ClassVParabolic : List ℕ := f4HeightThree ++ [33, 14, 24, 23]

@[expose] def f4ClassVDeriv : List (ℕ × ℕ × ℕ × ℕ) :=
  [(41, 29, 35, 0), (44, 29, 38, 0), (45, 30, 39, 0), (46, 30, 42, 0), (37, 30, 33, 0),
    (43, 31, 35, 0), (47, 32, 35, 44), (39, 32, 33, 0), (36, 35, 24, 0), (35, 36, 23, 0),
    (30, 37, 14, 0), (38, 37, 24, 39), (32, 39, 14, 0), (42, 40, 24, 41), (40, 42, 23, 41),
    (29, 14, 36, 42), (31, 14, 38, 45)]

theorem f4ClassV_check :
    f4DerivOK f4HeightThree f4ClassVParabolic [] f4ClassVDeriv = true ∧
      (∀ p ∈ f4HeightThree, p ∈ f4ClassVDeriv.map Prod.fst) ∧
      (∀ p ∈ f4HeightThree, p ∈ f4ClassVParabolic) ∧
      (∀ p ∈ f4ClassVParabolic, p < 48 ∧ (p = 41 ∨ f4CommuteRule p 41 = true) ∧
        (p = 45 ∨ f4CommuteRule p 45 = true)) ∧
      (∀ p < 48, 24 ≤ p → 3 ≤ height (orbitCertRoot .F4 p) → p ∈ f4HeightThree) := by
  decide +kernel


variable {K : Type} [Field K]

theorem mem_of_mem_heightSeries_three_of_forall_xr (hK : Nat.card K = 2)
    {H : Subgroup (adjointGroup .F4 K)}
    (h : ∀ p ∈ f4HeightThree, xr (K := K) (orbitCertRoot .F4 p) ∈ H)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ heightSeries .F4 K 3) : u ∈ H := by
  obtain ⟨-, -, -, -, hht⟩ := f4ClassV_check
  refine mem_of_mem_heightSeries_three_of_forall_f4x (fun p hp hp' h3 c => ?_) hu
  rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
  · convert one_mem H
    exact Subtype.ext (f4x_zero p)
  · exact h p (hht p (by omega) hp h3)

theorem heightSeries_three_le_closure_odd_classV_two (hK : Nat.card K = 2)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ heightSeries .F4 K 3) :
    u ∈ closure {c : adjointGroup .F4 K | c * ⟨f4x K 41 1 * f4x K 45 1, mul_mem
      (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ =
        ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩ * c ∧ Odd (orderOf c)} := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hder, hcov, hsub, hcomm, -⟩ := f4ClassV_check
  have hv : (⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) =
      xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45) := rfl
  rw [hv]
  set A : Subgroup (adjointGroup .F4 K) :=
    closure ((fun p => xr (K := K) (orbitCertRoot .F4 p)) '' {p | p ∈ f4HeightThree}) with hA
  set P : Subgroup (adjointGroup .F4 K) :=
    closure ((fun p => xr (K := K) (orbitCertRoot .F4 p)) '' {p | p ∈ f4ClassVParabolic}) with hP
  have hgenA : ∀ p ∈ f4HeightThree, xr (K := K) (orbitCertRoot .F4 p) ∈ A :=
    fun p hp => subset_closure ⟨p, hp, rfl⟩
  have hgenP : ∀ p ∈ f4ClassVParabolic, xr (K := K) (orbitCertRoot .F4 p) ∈ P :=
    fun p hp => subset_closure ⟨p, hp, rfl⟩
  have hAP : A ≤ P := by
    rw [hA, closure_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hgenP p (hsub p hp)
  have hPv : ∀ x ∈ P, x * (xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45)) =
      (xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45)) * x := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨hp48, h41, h45⟩ := hcomm p hp
      have c41 : Commute (xr (K := K) (orbitCertRoot .F4 p)) (xr (orbitCertRoot .F4 41)) := by
        rcases h41 with h | h
        · rw [h]
        · exact f4_commute_sound hK hp48 (by norm_num) h
      have c45 : Commute (xr (K := K) (orbitCertRoot .F4 p)) (xr (orbitCertRoot .F4 45)) := by
        rcases h45 with h | h
        · rw [h]
        · exact f4_commute_sound hK hp48 (by norm_num) h
      exact (c41.mul_right c45).eq
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy => exact (Commute.mul_left (hx : Commute x _) hy).eq
    | inv x _ hx => exact (Commute.inv_left (hx : Commute x _)).eq
  have hcomA : A ≤ ⁅A, P⁆ := by
    rw [hA, closure_le]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (hcov p hp)
    exact f4_deriv_sound hK hgenA hgenP f4ClassVDeriv [] (by simp) hder s hs
  exact le_closure_odd_of_le_commutator hAP (fun x hx => hPv x hx) hcomA
    (mem_of_mem_heightSeries_three_of_forall_xr hK hgenA hu)

theorem innerCentralizerCriterion_F4_v_two [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    InnerCentralizerCriterion
      (⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) :=
  innerCentralizerCriterion_F4_v_of_le le_rfl (by rw [pow_one]; exact hK)
    fun _ hx => heightSeries_three_le_closure_odd_classV_two hK hx

theorem innerCentralizerCriterion_F4_v' {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact innerCentralizerCriterion_F4_v_two (by simpa using hK)
  · exact innerCentralizerCriterion_F4_v h hK

theorem innerInvolutionInput_F4_of_classes'' {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f)
    (hrep : ∀ x : adjointGroup .F4 K, orderOf (MulAut.conj x) = 2 →
      ∃ ψ : MulAut (adjointGroup .F4 K), ∃ s ∈ ({⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩,
        ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩,
        ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩} : Set (adjointGroup .F4 K)), ψ s = x) :
    InnerInvolutionInput (adjointGroup .F4 K) :=
  innerInvolutionInput_F4_of_classes' hf hK (innerCentralizerCriterion_F4_v' hf hK) hrep

end CFSG.SeitzReduction
