module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphPlane
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear pairEmbed
  pairEmbed_apply pairEmbed_apply_left_left pairEmbed_apply_left_right pairEmbed_apply_right_left
  pairEmbed_apply_right_right pairEmbed_apply_of_notMem)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open scoped MatrixGroups

variable {K : Type} [Field K]

section Entries

variable {n : ℕ} {a b : Fin n}

theorem sum_mul_pairEmbed_zThree_left (hab : a ≠ b) (M : Matrix (Fin n) (Fin n) K) (r : Fin n) :
    ∑ u, M r u * (pairEmbed hab (zThreeSL (K := K)) : Matrix (Fin n) (Fin n) K) u a = -M r b := by
  rw [Finset.sum_eq_add a b hab (fun u _ hu => by
      rw [pairEmbed_apply_of_notMem hab _ (Or.inl (by simp [hu.1, hu.2])),
        Matrix.one_apply_ne hu.1, mul_zero]) (fun h => absurd (Finset.mem_univ a) h)
      (fun h => absurd (Finset.mem_univ b) h),
    pairEmbed_apply_left_left, pairEmbed_apply_right_left, coe_zThreeSL]
  simp [zThreeMat]

theorem sum_mul_pairEmbed_zThree_right (hab : a ≠ b) (M : Matrix (Fin n) (Fin n) K) (r : Fin n) :
    ∑ u, M r u * (pairEmbed hab (zThreeSL (K := K)) : Matrix (Fin n) (Fin n) K) u b =
      M r a - M r b := by
  rw [Finset.sum_eq_add a b hab (fun u _ hu => by
      rw [pairEmbed_apply_of_notMem hab _ (Or.inl (by simp [hu.1, hu.2])),
        Matrix.one_apply_ne hu.2, mul_zero]) (fun h => absurd (Finset.mem_univ a) h)
      (fun h => absurd (Finset.mem_univ b) h),
    pairEmbed_apply_left_right, pairEmbed_apply_right_right, coe_zThreeSL]
  simp [zThreeMat]
  ring

theorem sum_pairEmbed_zThree_left_mul (hab : a ≠ b) (M : Matrix (Fin n) (Fin n) K) (t : Fin n) :
    ∑ u, (pairEmbed hab (zThreeSL (K := K)) : Matrix (Fin n) (Fin n) K) a u * M u t = M b t := by
  rw [Finset.sum_eq_add a b hab (fun u _ hu => by
      rw [pairEmbed_apply_of_notMem hab _ (Or.inr (by simp [hu.1, hu.2])),
        Matrix.one_apply_ne (Ne.symm hu.1), zero_mul]) (fun h => absurd (Finset.mem_univ a) h)
      (fun h => absurd (Finset.mem_univ b) h),
    pairEmbed_apply_left_left, pairEmbed_apply_left_right, coe_zThreeSL]
  simp [zThreeMat]

theorem sum_pairEmbed_zThree_right_mul (hab : a ≠ b) (M : Matrix (Fin n) (Fin n) K) (t : Fin n) :
    ∑ u, (pairEmbed hab (zThreeSL (K := K)) : Matrix (Fin n) (Fin n) K) b u * M u t =
      -M a t - M b t := by
  rw [Finset.sum_eq_add a b hab (fun u _ hu => by
      rw [pairEmbed_apply_of_notMem hab _ (Or.inr (by simp [hu.1, hu.2])),
        Matrix.one_apply_ne (Ne.symm hu.2), zero_mul]) (fun h => absurd (Finset.mem_univ a) h)
      (fun h => absurd (Finset.mem_univ b) h),
    pairEmbed_apply_right_left, pairEmbed_apply_right_right, coe_zThreeSL]
  simp [zThreeMat]
  ring

theorem sum_pairEmbed_mul_of_ne (hab : a ≠ b) (A : SL(2, K)) (M : Matrix (Fin n) (Fin n) K)
    {r : Fin n} (hra : r ≠ a) (hrb : r ≠ b) (t : Fin n) :
    ∑ u, (pairEmbed hab A : Matrix (Fin n) (Fin n) K) r u * M u t = M r t := by
  have h : ∀ u, (pairEmbed hab A : Matrix (Fin n) (Fin n) K) r u =
      (1 : Matrix (Fin n) (Fin n) K) r u :=
    fun u => pairEmbed_apply_of_notMem hab A (Or.inl (by simp [hra, hrb]))
  simp only [h]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem sum_mul_pairEmbed_of_ne (hab : a ≠ b) (A : SL(2, K)) (M : Matrix (Fin n) (Fin n) K)
    (r : Fin n) {t : Fin n} (hta : t ≠ a) (htb : t ≠ b) :
    ∑ u, M r u * (pairEmbed hab A : Matrix (Fin n) (Fin n) K) u t = M r t := by
  have h : ∀ u, (pairEmbed hab A : Matrix (Fin n) (Fin n) K) u t =
      (1 : Matrix (Fin n) (Fin n) K) u t :=
    fun u => pairEmbed_apply_of_notMem hab A (Or.inr (by simp [hta, htb]))
  simp only [h]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem entries_of_commute_pairEmbed_zThree [CharP K 2] (hab : a ≠ b)
    {x : SpecialLinearGroup (Fin n) K}
    (h : x * pairEmbed hab (zThreeSL (K := K)) = pairEmbed hab (zThreeSL (K := K)) * x) :
    (∀ r, r ≠ a → r ≠ b → (x : Matrix (Fin n) (Fin n) K) r a = 0 ∧
      (x : Matrix (Fin n) (Fin n) K) r b = 0 ∧ (x : Matrix (Fin n) (Fin n) K) a r = 0 ∧
        (x : Matrix (Fin n) (Fin n) K) b r = 0) ∧
      (x : Matrix (Fin n) (Fin n) K) b a = -(x : Matrix (Fin n) (Fin n) K) a b ∧
      (x : Matrix (Fin n) (Fin n) K) b b =
        (x : Matrix (Fin n) (Fin n) K) a a - (x : Matrix (Fin n) (Fin n) K) a b := by
  have hM := congrArg (fun z : SpecialLinearGroup (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hM
  have e : ∀ i j, ∑ u, (x : Matrix (Fin n) (Fin n) K) i u *
      (pairEmbed hab (zThreeSL (K := K)) : Matrix (Fin n) (Fin n) K) u j =
        ∑ u, (pairEmbed hab (zThreeSL (K := K)) : Matrix (Fin n) (Fin n) K) i u *
          (x : Matrix (Fin n) (Fin n) K) u j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simpa only [Matrix.mul_apply] using this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun r hra hrb => ?_, ?_, ?_⟩
  · have e1 := e r a
    have e2 := e r b
    have e3 := e a r
    have e4 := e b r
    rw [sum_mul_pairEmbed_zThree_left, sum_pairEmbed_mul_of_ne hab _ _ hra hrb] at e1
    rw [sum_mul_pairEmbed_zThree_right, sum_pairEmbed_mul_of_ne hab _ _ hra hrb] at e2
    rw [sum_mul_pairEmbed_of_ne hab _ _ _ hra hrb, sum_pairEmbed_zThree_left_mul] at e3
    rw [sum_mul_pairEmbed_of_ne hab _ _ _ hra hrb, sum_pairEmbed_zThree_right_mul] at e4
    have h3 : (3 : K) = 1 := by
      have : (3 : K) = 2 + 1 := by norm_num
      rw [this, h2, zero_add]
    have hb : (x : Matrix (Fin n) (Fin n) K) r b = 0 := by
      have : (3 : K) * (x : Matrix (Fin n) (Fin n) K) r b = 0 := by linear_combination -e1 - e2
      rwa [h3, one_mul] at this
    have hbr : (x : Matrix (Fin n) (Fin n) K) b r = 0 := by
      have : (3 : K) * (x : Matrix (Fin n) (Fin n) K) b r = 0 := by linear_combination e4 - e3
      rwa [h3, one_mul] at this
    exact ⟨by rw [← e1, hb, neg_zero], hb, by rw [e3, hbr], hbr⟩
  · have e1 := e a a
    rw [sum_mul_pairEmbed_zThree_left, sum_pairEmbed_zThree_left_mul] at e1
    linear_combination -e1
  · have e2 := e a b
    rw [sum_mul_pairEmbed_zThree_right, sum_pairEmbed_zThree_left_mul] at e2
    linear_combination -e2

end Entries

section Decomp

variable {n : ℕ} {a b : Fin n}

theorem exists_eq_zpow_mul_of_commute_pairEmbed_zThree [CharP K 2] (hK : Nat.card K = 2)
    (hab : a ≠ b) {x : SpecialLinearGroup (Fin n) K}
    (h : x * pairEmbed hab (zThreeSL (K := K)) = pairEmbed hab (zThreeSL (K := K)) * x) :
    ∃ i : ℤ, ∃ y ∈ blockSpecialLinear ({a, b} : Finset (Fin n))ᶜ,
      x = pairEmbed hab (zThreeSL (K := K)) ^ i * y := by
  obtain ⟨hoff, h10, h11⟩ := entries_of_commute_pairEmbed_zThree hab h
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hXdef
  have hdetB : X a a * X b b - X a b * X b a = 1 := by
    rw [h10, h11]
    rcases eq_zero_or_eq_one_of_natCard_two hK (X a a) with h0 | h0 <;>
      rcases eq_zero_or_eq_one_of_natCard_two hK (X a b) with h1 | h1
    · exfalso
      have hdet := x.2
      rw [Matrix.det_eq_zero_of_row_eq_zero a (fun t => by
        by_cases hta : t = a
        · rw [hta]; exact h0
        by_cases htb : t = b
        · rw [htb]; exact h1
        exact (hoff t hta htb).2.2.1)] at hdet
      exact zero_ne_one hdet
    all_goals rw [h0, h1]; ring
  set B : SL(2, K) := mkSL !![X a a, X a b; X b a, X b b] (by
    rw [Matrix.det_fin_two_of]; exact hdetB) with hBdef
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (mem_zpowers_zThreeSL_of_entries hK (B := B)
    (by simp [hBdef, h10]) (by simp [hBdef, h11]))
  have hci : pairEmbed hab (zThreeSL (K := K)) ^ i = pairEmbed hab B := by
    rw [← map_zpow, hi]
  have hrow : ∀ u, u = a ∨ u = b → ∀ t, X u t =
      (pairEmbed hab B : Matrix (Fin n) (Fin n) K) u t := by
    intro u hu t
    by_cases ht : t = a ∨ t = b
    · rcases hu with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hBdef]
    · push Not at ht
      rw [pairEmbed_apply_of_notMem hab B (Or.inr (by simp [ht.1, ht.2]))]
      rcases hu with rfl | rfl
      · rw [Matrix.one_apply_ne (Ne.symm ht.1)]
        exact (hoff t ht.1 ht.2).2.2.1
      · rw [Matrix.one_apply_ne (Ne.symm ht.2)]
        exact (hoff t ht.1 ht.2).2.2.2
  refine ⟨i, (pairEmbed hab (zThreeSL (K := K)) ^ i)⁻¹ * x, ?_, by group⟩
  rw [mem_blockSpecialLinear]
  intro r t hrt
  rw [hci, ← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_not] at hrt
  by_cases hr : r = a ∨ r = b
  · have e : ∀ u, (pairEmbed hab B⁻¹ : Matrix (Fin n) (Fin n) K) r u * X u t =
        (pairEmbed hab B⁻¹ : Matrix (Fin n) (Fin n) K) r u *
          (pairEmbed hab B : Matrix (Fin n) (Fin n) K) u t := by
      intro u
      by_cases hu : u = a ∨ u = b
      · rw [hrow u hu t]
      · push Not at hu
        have hru : r ≠ u := by
          rcases hr with rfl | rfl
          · exact Ne.symm hu.1
          · exact Ne.symm hu.2
        rw [pairEmbed_apply_of_notMem hab B⁻¹ (Or.inr (by simp [hu.1, hu.2])),
          Matrix.one_apply_ne hru, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl (fun u _ => e u), ← Matrix.mul_apply,
      ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  · push Not at hr
    rw [sum_pairEmbed_mul_of_ne hab _ _ hr.1 hr.2]
    rcases hrt with h' | h'
    · exact absurd h' (by push Not; exact hr)
    · rcases h' with rfl | rfl
      · rw [Matrix.one_apply_ne hr.1]
        exact (hoff r hr.1 hr.2).1
      · rw [Matrix.one_apply_ne hr.2]
        exact (hoff r hr.1 hr.2).2.1

end Decomp

section LeviFact

variable {N ε : ℕ}

theorem planeCoordsQ2_singleton (l : Fin N) :
    planeCoordsQ2 ε {l} =
      {q2Coord N ε (Sum.inl (Sum.inl l)), q2Coord N ε (Sum.inl (Sum.inr l))} := by
  ext a
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  rw [q2Coord_mem_planeCoordsQ2]
  simp only [Finset.mem_insert, Finset.mem_singleton, (q2Coord N ε).injective.eq_iff]
  rcases w with (u | u) | e <;> simp [eq_comm]

theorem planeCoordsQ2_union (R R' : Finset (Fin N)) :
    planeCoordsQ2 ε (R ∪ R') = planeCoordsQ2 ε R ∪ planeCoordsQ2 ε R' := by
  ext a
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  rw [Finset.mem_union, q2Coord_mem_planeCoordsQ2, q2Coord_mem_planeCoordsQ2,
    q2Coord_mem_planeCoordsQ2]
  rcases w with u | e
  · simp
  · simp

theorem card_planeCoordsQ2 (R : Finset (Fin N)) : (planeCoordsQ2 ε R).card = 2 * R.card := by
  classical
  rw [planeCoordsQ2, Finset.card_filter]
  rw [← (q2Coord N ε).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [inPlanes_inl, planeOf_inl, planeOf_inr, not_inPlanes_inr, ite_false,
    Finset.sum_const_zero, add_zero]
  have hR : (∑ x : Fin N, if x ∈ R then (1 : ℕ) else 0) = R.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hR]
  ring

theorem commutator_q2Block_eq {R : Finset (Fin N)} (h : 3 ≤ ((planeCoordsQ2 ε R)ᶜ).card) :
    ⁅q2Block ε K R, q2Block ε K R⁆ = q2Block ε K R := by
  have hperf : Group.IsPerfect
      (SpecialLinearGroup ((planeCoordsQ2 ε R)ᶜ : Finset (Fin (2 * N + ε))) K) :=
    LinearPilot.isPerfect_specialLinearGroup_of_three_le_card _ (by rwa [Fintype.card_coe])
  rw [q2Block, ← LinearPilot.range_blockEmbed, MonoidHom.range_eq_map, ← map_commutator,
    ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem blockSpecialLinear_inf_le {n : ℕ} (I J : Finset (Fin n)) :
    blockSpecialLinear (K := K) I ⊓ blockSpecialLinear J ≤ blockSpecialLinear (I ∩ J) := by
  intro x ⟨hI, hJ⟩ i j hij
  simp only [Finset.mem_inter, not_and_or] at hij
  rcases hij with (h | h) | (h | h)
  · exact hI i j (Or.inl h)
  · exact hJ i j (Or.inl h)
  · exact hI i j (Or.inr h)
  · exact hJ i j (Or.inr h)

theorem perfectCore_q2Block_inf_centralizer [CharP K 2] (hK : Nat.card K = 2) {k l : Fin N}
    (hkl : k ≠ l)
    (hperf : ⁅q2Block ε K {k, l}, q2Block ε K {k, l}⁆ = q2Block ε K {k, l}) :
    perfectCore (q2Block ε K {k} ⊓
        centralizer ({q2Embed ε hK (nsElt l)} : Set (SpecialLinearGroup (Fin (2 * N + ε)) K))) =
      q2Block ε K {k, l} := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set a := q2Coord N ε (Sum.inl (Sum.inl l)) with ha
  set b := q2Coord N ε (Sum.inl (Sum.inr l)) with hb
  have hab : a ≠ b := q2PlaneNe l
  set c := q2Embed ε hK (nsElt l) with hc
  have hc' : c = pairEmbed hab (zThreeSL (K := K)) := q2Embed_longBlock hK l zThreeSL
  have hW : planeCoordsQ2 ε {l} = {a, b} := planeCoordsQ2_singleton l
  have hcpow : ∀ i : ℤ, c ^ i ∈ blockSpecialLinear ({a, b} : Finset (Fin (2 * N + ε))) := by
    intro i
    rw [hc', ← LinearPilot.range_pairEmbed hab, ← map_zpow]
    exact ⟨_, rfl⟩
  have hD : q2Block ε K {k, l} ≤ blockSpecialLinear ({a, b} : Finset (Fin (2 * N + ε)))ᶜ := by
    rw [← hW]
    exact q2Block_anti (by simp)
  have hAD : ∀ i : ℤ, ∀ d ∈ q2Block ε K {k, l}, Commute (c ^ i) d := fun i d hd =>
    LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right (hcpow i) (hD hd)
  have hck : ∀ i : ℤ, c ^ i ∈ q2Block ε K {k} := by
    intro i
    refine LinearPilot.blockSpecialLinear_mono ?_ (hcpow i)
    rw [← hW]
    intro z hz
    rw [Finset.mem_compl]
    intro hz'
    obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective z
    rw [q2Coord_mem_planeCoordsQ2] at hz hz'
    rcases w with u | e
    · exact hkl ((Finset.mem_singleton.1 hz').symm.trans (Finset.mem_singleton.1 hz))
    · exact hz.elim
  have hdec : ∀ g ∈ q2Block ε K {k} ⊓
      centralizer ({c} : Set (SpecialLinearGroup (Fin (2 * N + ε)) K)),
      ∃ a' ∈ zpowers c, ∃ d ∈ q2Block ε K {k, l}, g = a' * d := by
    intro g ⟨hgk, hgc⟩
    have hgc' : g * pairEmbed hab (zThreeSL (K := K)) = pairEmbed hab (zThreeSL (K := K)) * g := by
      rw [← hc']
      exact (mem_centralizer_singleton_iff.1 hgc)
    obtain ⟨i, y, hy, hgy⟩ := exists_eq_zpow_mul_of_commute_pairEmbed_zThree hK hab hgc'
    rw [← hc'] at hgy
    refine ⟨c ^ i, zpow_mem (mem_zpowers c) i, y, ?_, hgy⟩
    have hyk : y ∈ q2Block ε K {k} := by
      have : y = (c ^ i)⁻¹ * g := by rw [hgy]; group
      rw [this]
      exact mul_mem (inv_mem (hck i)) hgk
    have h1 := blockSpecialLinear_inf_le _ _ ⟨hy, hyk⟩
    rw [q2Block, show ({k, l} : Finset (Fin N)) = {k} ∪ {l} from rfl, planeCoordsQ2_union, hW,
      Finset.compl_union, Finset.inter_comm]
    exact h1
  have hcomm : ⁅q2Block ε K {k} ⊓ centralizer ({c} : Set (SpecialLinearGroup (Fin (2 * N + ε)) K)),
      q2Block ε K {k} ⊓ centralizer ({c} : Set (SpecialLinearGroup (Fin (2 * N + ε)) K))⁆ ≤
        q2Block ε K {k, l} := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    rw [commutatorElement_def]
    refine commutator_mem_of_eq_mul (A := zpowers c) ?_ ?_ (hdec g hg) (hdec g' hg')
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (Commute.refl c).zpow_zpow i j
    · rintro _ ⟨i, rfl⟩ d hd
      exact hAD i d hd
  have hle : q2Block ε K {k, l} ≤ q2Block ε K {k} ⊓
      centralizer ({c} : Set (SpecialLinearGroup (Fin (2 * N + ε)) K)) := by
    refine le_inf (q2Block_anti (by simp)) fun d hd => ?_
    rw [mem_centralizer_singleton_iff]
    have := hAD 1 d hd
    rw [zpow_one] at this
    exact this.eq.symm
  apply le_antisymm
  · calc perfectCore _ = ⁅perfectCore _, perfectCore _⁆ := (perfectCore_perfect _).symm
      _ ≤ _ := commutator_mono (perfectCore_le _) (perfectCore_le _)
      _ ≤ _ := hcomm
  · exact le_perfectCore_of_perfect hle hperf

end LeviFact

end CFSG.SeitzReduction.SymplecticPilot
