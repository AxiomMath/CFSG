module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Sq

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Group

variable {G : Type*} [Group G]

theorem commute_of_normal_of_pPrimeCore_eq_bot {C N J : Subgroup G} (hNC : N ≤ C) (hJC : J ≤ C)
    (hN : ∀ c ∈ C, ∀ y ∈ N, c * y * c⁻¹ ∈ N) (hJ : ∀ c ∈ C, ∀ y ∈ J, c * y * c⁻¹ ∈ J)
    (hcop : Nat.Coprime 2 (Nat.card N)) (hO : pPrimeCore 2 ↥J = ⊥) {x j : G} (hx : x ∈ N)
    (hj : j ∈ J) : x * j = j * x := by
  set H : Subgroup ↥J := (N ⊓ J).subgroupOf J with hH
  have hHn : H.Normal := by
    constructor
    intro a ha g
    rw [hH, mem_subgroupOf, mem_inf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hN _ (hJC g.2) _ ha.1, hJ _ (hJC g.2) _ ha.2⟩
  have hHc : Nat.Coprime 2 (Nat.card H) := by
    have h1 : Nat.card H = Nat.card ↥(N ⊓ J) :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop
  have hbot := (pPrimeCore_eq_bot_iff.mp hO) H hHn hHc
  have hkN : x * j * x⁻¹ * j⁻¹ ∈ N := by
    rw [show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group]
    exact mul_mem hx (hN _ (hJC hj) _ (inv_mem hx))
  have hkJ : x * j * x⁻¹ * j⁻¹ ∈ J := mul_mem (hJ _ (hNC hx) _ hj) (inv_mem hj)
  have hk1 : (⟨x * j * x⁻¹ * j⁻¹, hkJ⟩ : ↥J) ∈ H := by
    rw [hH, mem_subgroupOf]
    exact ⟨hkN, hkJ⟩
  rw [hbot, mem_bot] at hk1
  have hk1' : x * j * x⁻¹ * j⁻¹ = 1 := congrArg Subtype.val hk1
  calc x * j = x * j * x⁻¹ * j⁻¹ * (j * x) := by group
    _ = j * x := by rw [hk1', one_mul]

theorem conj_eq_inv_of_forall_commute_eq_one {M : Subgroup G} [Finite M] {v : G}
    (hv : v * v = 1) (hvM : ∀ y ∈ M, v * y * v⁻¹ ∈ M)
    (hfix : ∀ y ∈ M, v * y = y * v → y = 1) {y : G} (hy : y ∈ M) : v * y * v⁻¹ = y⁻¹ := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  let φ : M → M := fun w => ⟨(w : G)⁻¹ * (v * w * v⁻¹), mul_mem (inv_mem w.2) (hvM _ w.2)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h : (a : G)⁻¹ * (v * a * v⁻¹) = (b : G)⁻¹ * (v * b * v⁻¹) := congrArg Subtype.val hab
    have hc : v * ((b : G) * (a : G)⁻¹) = ((b : G) * (a : G)⁻¹) * v := by
      calc v * ((b : G) * (a : G)⁻¹) =
            (b : G) * ((b : G)⁻¹ * (v * b * v⁻¹)) * v * (a : G)⁻¹ := by group
        _ = (b : G) * ((a : G)⁻¹ * (v * a * v⁻¹)) * v * (a : G)⁻¹ := by rw [h]
        _ = ((b : G) * (a : G)⁻¹) * v := by group
    have h1 := hfix _ (mul_mem b.2 (inv_mem a.2)) hc
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨y, hy⟩
  have hw' : (w : G)⁻¹ * (v * w * v⁻¹) = y := congrArg Subtype.val hw
  rw [← hw', hvi]
  calc v * ((w : G)⁻¹ * (v * w * v)) * v = v * (w : G)⁻¹ * v * w * (v * v) := by group
    _ = v * (w : G)⁻¹ * v * w := by rw [hv, mul_one]
    _ = v⁻¹ * (w : G)⁻¹ * v⁻¹ * w := by rw [hvi]
    _ = ((w : G)⁻¹ * (v * w * v))⁻¹ := by group

theorem commute_conj_mul_inv_of_inverts {M : Subgroup G} {v g : G} (hv : v * v = 1)
    (hinv : ∀ y ∈ M, v * y * v⁻¹ = y⁻¹) (hg : ∀ y ∈ M, g⁻¹ * y * g ∈ M) {x : G} (hx : x ∈ M) :
    x * (v * g * v⁻¹ * g⁻¹) = (v * g * v⁻¹ * g⁻¹) * x := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have h1 : v⁻¹ * (g⁻¹ * x * g) * v = (g⁻¹ * x * g)⁻¹ := by
    have h := hinv _ (hg x hx)
    rw [hvi] at h ⊢
    exact h
  have h2 : (v * g * v⁻¹ * g⁻¹) * x * (v * g * v⁻¹ * g⁻¹)⁻¹ = x := by
    calc (v * g * v⁻¹ * g⁻¹) * x * (v * g * v⁻¹ * g⁻¹)⁻¹ =
          v * g * (v⁻¹ * (g⁻¹ * x * g) * v) * g⁻¹ * v⁻¹ := by group
      _ = v * g * (g⁻¹ * x * g)⁻¹ * g⁻¹ * v⁻¹ := by rw [h1]
      _ = (v * x * v⁻¹)⁻¹ := by group
      _ = x := by rw [hinv x hx, inv_inv]
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

end Group

variable {K : Type} [Field K] {n : ℕ}

theorem mul_self_eq_one_of_mem_ker_spinAction_quadOdd (h2 : (2 : K) ≠ 0)
    {x : spinGroup (quadOdd n K)} (hx : x ∈ (spinAction (quadOdd n K)).ker) : x * x = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rcases (mem_ker_spinAction_iff _ (nondegenerate_quadOdd n K) x).mp hx with rfl | rfl
  · exact mul_one 1
  · exact spinGroup.negOne_mul_self _ _

theorem normal_range_longSL2_quadOdd [Finite K] (hodd : Odd (Nat.card K)) {m : ℕ}
    (F : HypFrame (quadOdd n K) m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) :
    ((F.longSL2 hij s t).range.subgroupOf (centralizer {F.longSL2 hij s t (-1)})).Normal := by
  have hQ : quadOdd n K ≠ 0 := (nondegenerate_quadOdd n K).ne_zero
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set ρ := F.longSL2 hij s t with hρ
  set ρ' := F.longSL2 hij s (!t) with hρ'
  set fr := F.toFrame hij s t with hfr
  have hθ : ∀ A, spinAction (quadOdd n K) (ρ A) = fr.La A := spinAction_longSL2 F hij s t
  have hθ' : ∀ A, spinAction (quadOdd n K) (ρ' A) = fr.swap.La A := fun A => by
    rw [hρ', spinAction_longSL2, toFrame_not]
  have hmapJ : ρ.range.map (spinAction (quadOdd n K)) = fr.La.range :=
    map_longSL2_range F hij s t
  have hmapJ' : ρ'.range.map (spinAction (quadOdd n K)) = fr.swap.La.range := by
    rw [hρ', map_longSL2_range, toFrame_not]
  have hker2 : ∀ k ∈ (spinAction (quadOdd n K)).ker, k * k = 1 := fun k hk =>
    mul_self_eq_one_of_mem_ker_spinAction_quadOdd h2 hk
  rw [normal_subgroupOf_iff (range_longSL2_le_centralizer F hij s t)]
  intro a g ha hg
  have hgt : g * ρ (-1) = ρ (-1) * g := mem_centralizer_singleton_iff.mp hg
  set P := ρ.range.map (MulAut.conj g).toMonoidHom with hP
  have hPsq : P ≤ closure {x | ∃ y ∈ P, y * y = x} := by
    rw [hP, ← MonoidHom.range_comp]
    exact range_le_closure_mul_self_sl2 hodd _
  have hgO : spinAction (quadOdd n K) g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction (quadOdd n K) g)
  have hconj : spinAction (quadOdd n K) g * fr.La (-1) * (spinAction (quadOdd n K) g)⁻¹ =
      fr.La (-1) := by
    rw [← hθ, ← map_inv, ← map_mul, ← map_mul, hgt, mul_inv_cancel_right]
  have hfundP : IsFundamental (quadOdd n K) (P.map (spinAction (quadOdd n K))) (fr.La (-1)) := by
    have h := (IsFundamental.of_frame fr).conj hgO
    rw [hconj] at h
    rwa [hP, map_conj_map, hmapJ]
  obtain ⟨L', -, -, -, huniq⟩ := (IsFundamental.of_frame fr).exists_twin hodd
  have hmem : g * a * g⁻¹ ∈ P := ⟨a, ha, rfl⟩
  rcases huniq _ hfundP with h | h
  · refine le_of_le_comap_map_of_mul_self (spinAction (quadOdd n K))
      (ker_spinAction_le_center (quadOdd n K)) hker2 hPsq ?_ hmem
    rw [hmapJ, ← h]
    exact le_comap_map _ P
  · exfalso
    have hfund' : IsFundamental (quadOdd n K) (ρ'.range.map (spinAction (quadOdd n K)))
        (fr.La (-1)) := by
      rw [hmapJ']
      exact IsFundamental.of_frame_swap fr
    have hJ' : ρ'.range.map (spinAction (quadOdd n K)) = L' := by
      rcases huniq _ hfund' with h' | h'
      · exact absurd (hmapJ'.symm.trans h') (Frame.La_range_ne_swap_La_range fr).symm
      · exact h'
    have hPJ' : P ≤ ρ'.range := le_of_le_comap_map_of_mul_self (spinAction (quadOdd n K))
      (ker_spinAction_le_center (quadOdd n K)) hker2 hPsq
      (by rw [hJ', ← h]; exact le_comap_map _ P)
    have htP : ρ (-1) ∈ P := by
      refine ⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩, ?_⟩
      show g * ρ (-1) * g⁻¹ = ρ (-1)
      rw [hgt, mul_inv_cancel_right]
    obtain ⟨A, hA⟩ := hPJ' htP
    have hA1 : A = -1 := by
      apply fr.swap.La_injective
      rw [← hθ', hA, hθ, Frame.La_swap_neg_one]
    rw [hA1, hρ', longSL2_neg_one_not F hij hQ s t] at hA
    exact spinGroup.negOne_ne_one (quadOdd n K) hQ (mul_right_cancel (hA.trans (one_mul _).symm))

end CFSG.ComponentClassification.HarrisLit.T1
