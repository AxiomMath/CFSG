module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Core

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem frame01_swap :
    (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false = (frame01 K).swap :=
  toFrame_not _ fin3_zero_ne_one true true

theorem longSL2_mem_centralizer (t : Bool) (A : SL(2, K)) :
    (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true t A ∈
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  mem_centralizer_singleton_iff.mpr (commute_shortSeven_longSL2 t (upperSL2 1) A).eq.symm

theorem exists_decomp (g : spinGroup (quadOdd 3 K)) :
    ∃ k ∈ radThree K, spinAction (quadOdd 3 K) (k⁻¹ * g) =
      ellThree (spinAction (quadOdd 3 K) g) := by
  have hU : eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree (spinAction (quadOdd 3 K) g)) ∈
      rootGroup (quadOdd 3 K) (oddVec 3 K 2 true) := eichler_mem_rootGroup polar_eTwo_yThree
  obtain ⟨c, hc⟩ := exists_prodThree hU
  exact ⟨prodThree c, prodThree_mem c, by rw [map_mul, map_inv, hc]⟩

variable [Finite K]

theorem finite_spin (h2 : (2 : K) ≠ 0) : Finite (spinGroup (quadOdd 3 K)) :=
  CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)

theorem centralizer_le_sup (hodd : Odd (Nat.card K)) :
    centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ≤
      radThree K ⊔ (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
        normalizer (fourT K : Set (spinGroup (quadOdd 3 K)))) := by
  intro g hg
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨k, hk, hπ⟩ := exists_decomp g
  have hl : k⁻¹ * g ∈ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ⊓
      normalizer (fourT K : Set (spinGroup (quadOdd 3 K))) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem (radThree_le_centralizer hodd hk)) hg,
      mem_normalizer_fourT h2 ?_⟩
    rw [hπ]
    exact (spinAction_commThree hodd hg).ell_commute_La
  rw [show g = k * (k⁻¹ * g) by group]
  exact mul_mem_sup hk hl

theorem radThree_le_oddCoreOf (hodd : Odd (Nat.card K)) :
    radThree K ≤ oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) :=
  le_oddCoreOf (radThree_le_centralizer hodd) (fun _ hc _ hx => conj_mem_radThree hodd hc hx)
    (by rw [card_radThree hodd]; exact hodd.pow)

theorem eq_one_of_mem_oddCoreOf (hodd : Odd (Nat.card K)) (h3 : 3 ≤ Nat.card K)
    {l : spinGroup (quadOdd 3 K)}
    (hl : l ∈ oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))))
    (hcomm : spinAction (quadOdd 3 K) l * (frame01 K).La (-1) =
      (frame01 K).La (-1) * spinAction (quadOdd 3 K) l)
    {lam : K} (hlam : lam * lam = 1)
    (hscal : ∀ v, (frame01 K).La (-1) v = v → spinAction (quadOdd 3 K) l v = lam • v) :
    l = 1 := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have := finite_spin h2
  have hgO : spinAction (quadOdd 3 K) l ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ l)
  have hlodd : Odd (orderOf l) := odd_orderOf_of_mem_oddCoreOf hl
  have hgodd : Odd (orderOf (spinAction (quadOdd 3 K) l)) :=
    hlodd.of_dvd_nat (orderOf_map_dvd _ _)
  have hcL : (∀ A : SL(2, K), spinAction (quadOdd 3 K) l * (frame01 K).La A *
        (spinAction (quadOdd 3 K) l)⁻¹ ∈ (frame01 K).La.range) ∧
      ∀ A : SL(2, K), spinAction (quadOdd 3 K) l * (frame01 K).swap.La A *
        (spinAction (quadOdd 3 K) l)⁻¹ ∈ (frame01 K).swap.La.range := by
    rcases Frame.conjSubgroup_La_range h2 hgO hcomm with ⟨-, e1, e2⟩ | ⟨hd, -, -⟩
    · refine ⟨fun A => ?_, fun A => ?_⟩
      · rw [← e1]
        show (spinAction (quadOdd 3 K) l)⁻¹ * (spinAction (quadOdd 3 K) l * (frame01 K).La A *
          (spinAction (quadOdd 3 K) l)⁻¹) * spinAction (quadOdd 3 K) l ∈ (frame01 K).La.range
        rw [show (spinAction (quadOdd 3 K) l)⁻¹ * (spinAction (quadOdd 3 K) l *
          (frame01 K).La A * (spinAction (quadOdd 3 K) l)⁻¹) * spinAction (quadOdd 3 K) l =
          (frame01 K).La A by group]
        exact MonoidHom.mem_range.mpr ⟨A, rfl⟩
      · rw [← e2]
        show (spinAction (quadOdd 3 K) l)⁻¹ * (spinAction (quadOdd 3 K) l *
          (frame01 K).swap.La A * (spinAction (quadOdd 3 K) l)⁻¹) *
          spinAction (quadOdd 3 K) l ∈ (frame01 K).swap.La.range
        rw [show (spinAction (quadOdd 3 K) l)⁻¹ * (spinAction (quadOdd 3 K) l *
          (frame01 K).swap.La A * (spinAction (quadOdd 3 K) l)⁻¹) * spinAction (quadOdd 3 K) l =
          (frame01 K).swap.La A by group]
        exact MonoidHom.mem_range.mpr ⟨A, rfl⟩
    · exact absurd hd (det_transportEquiv_ne_neg_one h2 hcomm hgodd)
  have hL := commute_La_of_mem_oddCoreOf (spinAction (quadOdd 3 K)) (frame01 K)
    ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true)
    (fun A => longSL2_mem_centralizer true A) (fun A => spinAction_longSL2 _ _ true true A)
    hodd h3 hl hcL.1
  have hR := commute_La_of_mem_oddCoreOf (spinAction (quadOdd 3 K)) (frame01 K).swap
    ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false)
    (fun A => longSL2_mem_centralizer false A)
    (fun A => by rw [spinAction_longSL2, frame01_swap]) hodd h3 hl hcL.2
  obtain ⟨μ, hμ, hW⟩ := exists_smul_of_commute_La (frame01 K) h2 hgO hcomm hL hR
  have hsq : spinAction (quadOdd 3 K) l * spinAction (quadOdd 3 K) l = 1 := by
    refine LinearEquiv.ext fun v => ?_
    show spinAction (quadOdd 3 K) l (spinAction (quadOdd 3 K) l v) = v
    have hr : (frame01 K).coords (v - (frame01 K).incl ((frame01 K).coords v)) = 0 := by
      rw [map_sub, Frame.coords_incl, sub_self]
    have key : ∀ (Y : Matrix (Fin 2) (Fin 2) K) (r : Fin 3 ⊕ Fin 3 ⊕ Unit → K),
        (frame01 K).La (-1) r = r →
        spinAction (quadOdd 3 K) l (spinAction (quadOdd 3 K) l ((frame01 K).incl Y + r)) =
          (frame01 K).incl Y + r := by
      intro Y r hr'
      rw [map_add, hW, hscal r hr', map_add, map_smul, map_smul, hW, hscal r hr', smul_smul,
        smul_smul, hμ, hlam, one_smul, one_smul]
    have := key ((frame01 K).coords v) _ ((frame01 K).La_apply_of_coords_eq_zero (-1) hr)
    rwa [add_sub_cancel] at this
  have hdvd : orderOf (spinAction (quadOdd 3 K) l) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two, hsq])
  have hone : orderOf (spinAction (quadOdd 3 K) l) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hgodd
      exact absurd hgodd (Nat.not_odd_iff_even.mpr even_two)
  have hπ1 : spinAction (quadOdd 3 K) l = spinAction (quadOdd 3 K) 1 := by
    rw [orderOf_eq_one_iff.mp hone, map_one]
  exact eq_of_spinAction_eq_of_odd h2 hlodd (by rw [orderOf_one]; exact odd_one) hπ1

theorem oddCoreOf_eq_radThree (hodd : Odd (Nat.card K)) (h3 : 3 ≤ Nat.card K) :
    oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) = radThree K := by
  refine le_antisymm (fun x hx => ?_) (radThree_le_oddCoreOf hodd)
  have hxC := oddCoreOf_le hx
  obtain ⟨k, hk, hπ⟩ := exists_decomp x
  have hc := spinAction_commThree hodd hxC
  have hl : k⁻¹ * x ∈ oddCoreOf (centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) :=
    mul_mem (inv_mem (radThree_le_oddCoreOf hodd hk)) hx
  have h1 := eq_one_of_mem_oddCoreOf hodd h3 hl (by rw [hπ]; exact hc.ell_commute_La) hc.lam
    (fun v hv => by rw [hπ]; exact hc.ell_apply_of_fix hv)
  rw [show x = k * (k⁻¹ * x) by group, h1, mul_one]
  exact hk

theorem f1_holds : F1 := by
  intro K _ _ hodd h5
  have h3 : 3 ≤ Nat.card K := by omega
  rw [oddCoreOf_eq_radThree hodd h3]
  exact ⟨card_radThree hodd, centralizer_le_sup hodd⟩

end CFSG.ComponentClassification.HarrisLit.T1.S74
