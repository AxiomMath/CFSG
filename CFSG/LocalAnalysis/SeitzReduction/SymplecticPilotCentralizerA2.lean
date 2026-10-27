module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLongRoot
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n : ℕ}

section Radical

@[expose] def OffPQ (p q : Fin n) (t : Fin n ⊕ Fin n) : Prop := t ∉ coords p ∧ t ∉ coords q

variable (K) in
@[expose] def wRadical (p q : Fin n) : Subgroup (StatedSp n K) where
  carrier := {g | (∀ r, mat n K g r (Sum.inl p) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p)) ∧
    (∀ r, mat n K g r (Sum.inl q) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl q)) ∧
    ∀ t, OffPQ p q t → ∀ r, r ≠ Sum.inl p → r ≠ Sum.inl q →
      mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t}
  one_mem' := ⟨fun r => by rw [map_one], fun r => by rw [map_one], fun t _ r _ _ => by
    rw [map_one]⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun r => ?_, fun r => ?_, fun t ht r hrp hrq => ?_⟩
    · rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl p)]
      · rw [hh1, Matrix.one_apply_eq, mul_one, hg1]
      · intro u _ hu
        rw [hh1, Matrix.one_apply_ne hu, mul_zero]
      · simp
    · rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl q)]
      · rw [hh2, Matrix.one_apply_eq, mul_one, hg2]
      · intro u _ hu
        rw [hh2, Matrix.one_apply_ne hu, mul_zero]
      · simp
    · rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single t]
      · have htp : t ≠ Sum.inl p := fun h => ht.1 (h ▸ inl_mem_coords p)
        have htq : t ≠ Sum.inl q := fun h => ht.2 (h ▸ inl_mem_coords q)
        rw [hh3 t ht t htp htq, Matrix.one_apply_eq, mul_one, hg3 t ht r hrp hrq]
      · intro u _ hut
        by_cases hup : u = Sum.inl p
        · subst hup
          rw [hg1, Matrix.one_apply_ne hrp, zero_mul]
        by_cases huq : u = Sum.inl q
        · subst huq
          rw [hg2, Matrix.one_apply_ne hrq, zero_mul]
        rw [hh3 t ht u hup huq, Matrix.one_apply_ne hut, mul_zero]
      · simp
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hinv : mat n K g⁻¹ * mat n K g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h1 : ∀ r, mat n K g⁻¹ r (Sum.inl p) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p) := by
      intro r
      have e := congrFun (congrFun hinv r) (Sum.inl p)
      rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl p)] at e
      · rwa [hg1, Matrix.one_apply_eq, mul_one] at e
      · intro u _ hu
        rw [hg1, Matrix.one_apply_ne hu, mul_zero]
      · simp
    have h2 : ∀ r, mat n K g⁻¹ r (Sum.inl q) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl q) := by
      intro r
      have e := congrFun (congrFun hinv r) (Sum.inl q)
      rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl q)] at e
      · rwa [hg2, Matrix.one_apply_eq, mul_one] at e
      · intro u _ hu
        rw [hg2, Matrix.one_apply_ne hu, mul_zero]
      · simp
    refine ⟨h1, h2, fun t ht r hrp hrq => ?_⟩
    have htp : t ≠ Sum.inl p := fun h => ht.1 (h ▸ inl_mem_coords p)
    have htq : t ≠ Sum.inl q := fun h => ht.2 (h ▸ inl_mem_coords q)
    have e := congrFun (congrFun hinv r) t
    rw [Matrix.mul_apply, Finset.sum_eq_single t] at e
    · rwa [hg3 t ht t htp htq, Matrix.one_apply_eq, mul_one] at e
    · intro u _ hut
      by_cases hup : u = Sum.inl p
      · subst hup
        rw [h1, Matrix.one_apply_ne hrp, zero_mul]
      by_cases huq : u = Sum.inl q
      · subst huq
        rw [h2, Matrix.one_apply_ne hrq, zero_mul]
      rw [hg3 t ht u hup huq, Matrix.one_apply_ne hut, mul_zero]
    · simp

variable {p q : Fin n}

theorem mem_wRadical {g : StatedSp n K} :
    g ∈ wRadical K p q ↔ (∀ r, mat n K g r (Sum.inl p) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p)) ∧
    (∀ r, mat n K g r (Sum.inl q) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl q)) ∧
    ∀ t, OffPQ p q t → ∀ r, r ≠ Sum.inl p → r ≠ Sum.inl q →
      mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := Iff.rfl


theorem mat_inr_p_of_mem_wRadical {g : StatedSp n K} (hg : g ∈ wRadical K p q)
    (b : Fin n ⊕ Fin n) :
    mat n K g (Sum.inr p) b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inr p) b :=
  mat_inr_apply_of_col_inl hg.1 b

theorem mat_inr_q_of_mem_wRadical {g : StatedSp n K} (hg : g ∈ wRadical K p q)
    (b : Fin n ⊕ Fin n) :
    mat n K g (Sum.inr q) b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inr q) b :=
  mat_inr_apply_of_col_inl hg.2.1 b

theorem mul_single_of_col {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {i j : Fin n ⊕ Fin n}
    (hG : ∀ r, G r i = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r i) (c : K) :
    G * single i j c = single i j c := by
  ext r t
  by_cases ht : t = j
  · subst ht
    rw [Matrix.mul_single_apply_same, hG, Matrix.one_apply, Matrix.single_apply]
    by_cases hr : r = i
    · subst hr
      simp
    · simp [hr, Ne.symm hr]
  · rw [Matrix.mul_single_apply_of_ne (hbj := ht), Matrix.single_apply, ite_eq_right_iff.2]
    exact fun h => absurd h.2.symm ht

theorem single_mul_of_row {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {i j : Fin n ⊕ Fin n}
    (hG : ∀ t, G j t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) j t) (c : K) :
    single i j c * G = single i j c := by
  ext r t
  by_cases hr : r = i
  · subst hr
    rw [Matrix.single_mul_apply_same, hG, Matrix.one_apply, Matrix.single_apply]
    by_cases ht : j = t
    · subst ht
      simp
    · simp [ht]
  · rw [Matrix.single_mul_apply_of_ne (h := hr), Matrix.single_apply, ite_eq_right_iff.2]
    exact fun h => absurd h.1.symm hr

theorem mat_twoCentralElt_eq_add (a b : K) :
    mat n K (twoCentralElt n p q a b) = 1 + single (Sum.inl p) (Sum.inr p) a +
      single (Sum.inl p) (Sum.inr q) b + single (Sum.inl q) (Sum.inr p) b := by
  rw [mat_twoCentralElt]
  ext r t
  rcases r with x | x <;> rcases t with y | y <;>
    simp [Matrix.one_apply, Matrix.single_apply, twoCentralMat_apply, and_comm]

theorem wRadical_le_centralizer_twoCentralElt (a b : K) :
    wRadical K p q ≤ centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K)) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, mat_twoCentralElt_eq_add]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    mul_single_of_col hg.1, mul_single_of_col hg.2.1,
    single_mul_of_row (mat_inr_p_of_mem_wRadical hg),
    single_mul_of_row (mat_inr_q_of_mem_wRadical hg)]
end Radical

section Generation

variable {p q : Fin n}

theorem mat_apply_of_mem_wRadical {g : StatedSp n K} (hg : g ∈ wRadical K p q)
    (hv : ∀ t, OffPQ p q t → mat n K g (Sum.inl p) t = 0 ∧ mat n K g (Sum.inl q) t = 0)
    {t : Fin n ⊕ Fin n} (ht : OffPQ p q t) (r : Fin n ⊕ Fin n) :
    mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
  by_cases hrp : r = Sum.inl p
  · subst hrp
    rw [(hv t ht).1, Matrix.one_apply_ne (by rintro rfl; exact ht.1 (inl_mem_coords p))]
  by_cases hrq : r = Sum.inl q
  · subst hrq
    rw [(hv t ht).2, Matrix.one_apply_ne (by rintro rfl; exact ht.2 (inl_mem_coords q))]
  exact hg.2.2 t ht r hrp hrq

theorem par_offPQ {t : Fin n ⊕ Fin n} : OffPQ p q (par t) ↔ OffPQ p q t := by
  rcases t with x | x <;> simp [OffPQ, mem_coords, par]

theorem mat_inr_eq_zero_of_mem_wRadical {g : StatedSp n K} (hg : g ∈ wRadical K p q)
    (hv : ∀ t, OffPQ p q t → mat n K g (Sum.inl p) t = 0 ∧ mat n K g (Sum.inl q) t = 0)
    {x : Fin n} (hx : x = p ∨ x = q) {r : Fin n ⊕ Fin n} (hr : OffPQ p q r) :
    mat n K g r (Sum.inr x) = 0 := by
  have hcol := mat_apply_of_mem_wRadical hg hv (par_offPQ.2 hr)
  have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) (par r)) (Sum.inr x)
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
    par_par, Finset.sum_eq_single (par r)] at key
  · have hne : ¬ (Sum.inr x = r) := by
      rintro rfl
      rcases hx with rfl | rfl
      · exact hr.1 (inr_mem_coords _)
      · exact hr.2 (inr_mem_coords _)
    rw [hcol, Matrix.one_apply_eq, one_mul, par_par, ite_eq_right_iff.2 (fun h => absurd h hne)]
      at key
    exact (mul_eq_zero.1 key).resolve_left (sgn_ne_zero _)
  · intro c _ hc
    rw [hcol, Matrix.one_apply_ne hc, zero_mul]
  · simp

theorem mat_inl_q_inr_p_of_mem_wRadical (hpq : p ≠ q) {g : StatedSp n K}
    (hg : g ∈ wRadical K p q)
    (hv : ∀ t, OffPQ p q t → mat n K g (Sum.inl p) t = 0 ∧ mat n K g (Sum.inl q) t = 0) :
    mat n K g (Sum.inl q) (Sum.inr p) = mat n K g (Sum.inl p) (Sum.inr q) := by
  have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) (Sum.inr p)) (Sum.inr q)
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
    par_inr, ite_eq_right_iff.2 (fun h => absurd h Sum.inr_ne_inl)] at key
  rw [Fintype.sum_eq_add (Sum.inl q) (Sum.inr p) Sum.inl_ne_inr] at key
  · simp only [sgn_inl, sgn_inr, par_inl, par_inr, mat_inr_p_of_mem_wRadical hg,
      mat_inr_q_of_mem_wRadical hg, Matrix.one_apply_eq] at key
    linear_combination key
  · rintro c ⟨hc1, hc2⟩
    by_cases hcp : c = Sum.inl p
    · subst hcp
      rw [par_inl, mat_inr_p_of_mem_wRadical hg,
        Matrix.one_apply_ne (fun h => hpq (Sum.inr_injective h)), mul_zero, mul_zero]
    by_cases hcq : c = Sum.inr q
    · subst hcq
      rw [mat_inr_q_of_mem_wRadical hg,
        Matrix.one_apply_ne (fun h => hpq (Sum.inr_injective h).symm),
        zero_mul]
    have hc : OffPQ p q c := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases mem_coords.1 h with rfl | rfl
        · exact hcp rfl
        · exact hc2 rfl
      · rcases mem_coords.1 h with rfl | rfl
        · exact hc1 rfl
        · exact hcq rfl
    rw [mat_inr_eq_zero_of_mem_wRadical hg hv (Or.inl rfl) hc, zero_mul]


theorem eq_siegel_of_mem_wRadical (hpq : p ≠ q) {g : StatedSp n K} (hg : g ∈ wRadical K p q)
    (hv : ∀ t, OffPQ p q t → mat n K g (Sum.inl p) t = 0 ∧ mat n K g (Sum.inl q) t = 0) :
    g = siegDiag K p (mat n K g (Sum.inl p) (Sum.inr p)) *
      siegDiag K q (mat n K g (Sum.inl q) (Sum.inr q)) *
      siegPair K p q (mat n K g (Sum.inl p) (Sum.inr q)) := by
  have hsym := mat_inl_q_inr_p_of_mem_wRadical hpq hg hv
  have hoff : ∀ x : Fin n, x ≠ p → x ≠ q → ∀ (r : Fin n ⊕ Fin n),
      (r = Sum.inl x ∨ r = Sum.inr x) → OffPQ p q r := by
    rintro x hxp hxq r (rfl | rfl)
    · exact ⟨fun h => hxp (by simpa [mem_coords] using h),
        fun h => hxq (by simpa [mem_coords] using h)⟩
    · exact ⟨fun h => hxp (by simpa [mem_coords] using h),
        fun h => hxq (by simpa [mem_coords] using h)⟩
  apply mat_injective
  rw [siegDiag, siegDiag, siegPair, upperUnipotentSp_mul, upperUnipotentSp_mul,
    mat_upperUnipotentSp]
  ext r t
  rcases t with y | y
  · have hcol : mat n K g r (Sum.inl y) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl y) := by
      by_cases hyp : y = p
      · subst hyp
        exact hg.1 r
      by_cases hyq : y = q
      · subst hyq
        exact hg.2.1 r
      exact mat_apply_of_mem_wRadical hg hv (hoff y hyp hyq _ (Or.inl rfl)) r
    rw [hcol]
    rcases r with x | x <;> simp [Matrix.one_apply]
  · by_cases hyp : y = p
    · subst hyp
      rcases r with x | x
      · rw [fromBlocks_apply₁₂]
        by_cases hxp : x = y
        · subst hxp
          simp [Ne.symm hpq]
        by_cases hxq : x = q
        · subst hxq
          rw [hsym]
          simp [hpq, Ne.symm hpq]
        rw [mat_inr_eq_zero_of_mem_wRadical hg hv (Or.inl rfl) (hoff x hxp hxq _ (Or.inl rfl))]
        simp [Ne.symm hxp, Ne.symm hxq]
      · rw [fromBlocks_apply₂₂]
        by_cases hxp : x = y
        · subst hxp
          rw [mat_inr_p_of_mem_wRadical hg]
          simp
        by_cases hxq : x = q
        · subst hxq
          rw [mat_inr_q_of_mem_wRadical hg]
          simp [hxp]
        rw [mat_inr_eq_zero_of_mem_wRadical hg hv (Or.inl rfl) (hoff x hxp hxq _ (Or.inr rfl))]
        simp [hxp]
    by_cases hyq : y = q
    · subst hyq
      rcases r with x | x
      · rw [fromBlocks_apply₁₂]
        by_cases hxp : x = p
        · subst hxp
          simp [hpq, Ne.symm hpq]
        by_cases hxq : x = y
        · subst hxq
          simp [hpq]
        rw [mat_inr_eq_zero_of_mem_wRadical hg hv (Or.inr rfl) (hoff x hxp hxq _ (Or.inl rfl))]
        simp [Ne.symm hxp, Ne.symm hxq]
      · rw [fromBlocks_apply₂₂]
        by_cases hxq : x = y
        · subst hxq
          rw [mat_inr_q_of_mem_wRadical hg]
          simp
        by_cases hxp : x = p
        · subst hxp
          rw [mat_inr_p_of_mem_wRadical hg]
          simp [hxq]
        rw [mat_inr_eq_zero_of_mem_wRadical hg hv (Or.inr rfl) (hoff x hxp hxq _ (Or.inr rfl))]
        simp [hxq]
    · rw [mat_apply_of_mem_wRadical hg hv (hoff y hyp hyq _ (Or.inr rfl))]
      rcases r with x | x
      · simp [Ne.symm hyp, Ne.symm hyq]
      · simp [Matrix.one_apply]

theorem mat_leviTv_mul_apply_of_ne {i j : Fin n} (hij : i ≠ j) (c : K) (g : StatedSp n K)
    {r : Fin n ⊕ Fin n} (hr1 : r ≠ Sum.inl i) (hr2 : r ≠ Sum.inr j) (t : Fin n ⊕ Fin n) :
    mat n K (leviTv K hij c * g) r t = mat n K g r t := by
  rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
    rcases r with x | x
    · have hx : i ≠ x := fun h => hr1 (h ▸ rfl)
      simp [transvection, hx]
    · have hx : j ≠ x := fun h => hr2 (h ▸ rfl)
      simp [hx]
  · intro u _ hur
    rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
    rcases r with x | x <;> rcases u with y | y
    · have hx : i ≠ x := fun h => hr1 (h ▸ rfl)
      have hxy : x ≠ y := fun h => hur (h ▸ rfl)
      simp [transvection, hx, hxy]
    · simp
    · simp
    · have hx : j ≠ x := fun h => hr2 (h ▸ rfl)
      have hxy : x ≠ y := fun h => hur (h ▸ rfl)
      simp [hx, hxy]
  · simp

theorem mat_siegPair_mul_apply_of_ne {i j : Fin n} (c : K) (g : StatedSp n K)
    {r : Fin n ⊕ Fin n} (hr1 : r ≠ Sum.inl i) (hr2 : r ≠ Sum.inl j) (t : Fin n ⊕ Fin n) :
    mat n K (siegPair K i j c * g) r t = mat n K g r t := by
  rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [mat_siegPair]
    rcases r with x | x <;> simp
  · intro u _ hur
    rw [mat_siegPair]
    rcases r with x | x <;> rcases u with y | y
    · have hxy : x ≠ y := fun h => hur (h ▸ rfl)
      simp [hxy]
    · have hx1 : i ≠ x := fun h => hr1 (h ▸ rfl)
      have hx2 : j ≠ x := fun h => hr2 (h ▸ rfl)
      simp [hx1, hx2]
    · simp
    · have hxy : x ≠ y := fun h => hur (h ▸ rfl)
      simp [hxy]
  · simp

variable (hpq : p ≠ q)
include hpq

theorem leviTv_mem_wRadical {i j : Fin n} (hij : i ≠ j) (hi : i = p ∨ i = q) (hjp : j ≠ p)
    (hjq : j ≠ q) (c : K) : leviTv K hij c ∈ wRadical K p q := by
  refine ⟨fun r => ?_, fun r => ?_, fun t ht r hrp hrq => ?_⟩ <;>
    rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
  · rcases r with x | x
    · simp [transvection, Matrix.one_apply, hjp]
    · simp
  · rcases r with x | x
    · simp [transvection, Matrix.one_apply, hjq]
    · simp
  · rcases t with y | y <;> rcases r with x | x
    · have hx : i ≠ x := by
        rintro rfl
        rcases hi with rfl | rfl
        exacts [hrp rfl, hrq rfl]
      simp [transvection, Matrix.one_apply, hx]
    · simp
    · simp
    · have hy : i ≠ y := by
        rintro rfl
        rcases hi with rfl | rfl
        exacts [ht.1 (inr_mem_coords _), ht.2 (inr_mem_coords _)]
      simp [Matrix.one_apply, hy]

omit hpq in
theorem siegPair_mem_wRadical {i j : Fin n} (hi : i = p ∨ i = q) (c : K) :
    siegPair K i j c ∈ wRadical K p q := by
  refine ⟨fun r => ?_, fun r => ?_, fun t ht r hrp hrq => ?_⟩ <;> rw [mat_siegPair]
  · rcases r with x | x <;> simp [Matrix.one_apply]
  · rcases r with x | x <;> simp [Matrix.one_apply]
  · rcases t with y | y <;> rcases r with x | x
    · simp [Matrix.one_apply]
    · simp
    · have hx : i ≠ x := by
        rintro rfl
        rcases hi with rfl | rfl
        exacts [hrp rfl, hrq rfl]
      have hy : i ≠ y := by
        rintro rfl
        rcases hi with rfl | rfl
        exacts [ht.1 (inr_mem_coords _), ht.2 (inr_mem_coords _)]
      simp [hx, hy]
    · simp [Matrix.one_apply]

omit hpq in
theorem siegDiag_mem_wRadical {i : Fin n} (hi : i = p ∨ i = q) (c : K) :
    siegDiag K i c ∈ wRadical K p q := by
  refine ⟨fun r => ?_, fun r => ?_, fun t ht r hrp hrq => ?_⟩ <;> rw [mat_siegDiag]
  · rcases r with x | x <;> simp [Matrix.one_apply]
  · rcases r with x | x <;> simp [Matrix.one_apply]
  · rcases t with y | y <;> rcases r with x | x
    · simp [Matrix.one_apply]
    · simp
    · have hy : i ≠ y := by
        rintro rfl
        rcases hi with rfl | rfl
        exacts [ht.1 (inr_mem_coords _), ht.2 (inr_mem_coords _)]
      simp [hy]
    · simp [Matrix.one_apply]

theorem wRadical_le_of_forall_mem {H : Subgroup (StatedSp n K)}
    (hD : ∀ c : K, siegDiag K p c ∈ H) (hD' : ∀ c : K, siegDiag K q c ∈ H)
    (hP : ∀ c : K, siegPair K p q c ∈ H)
    (hL : ∀ (i j : Fin n) (hij : i ≠ j), (i = p ∨ i = q) → j ≠ p → j ≠ q → ∀ c : K,
      leviTv K hij c ∈ H)
    (hS : ∀ (i j : Fin n), (i = p ∨ i = q) → j ≠ p → j ≠ q → ∀ c : K, siegPair K i j c ∈ H) :
    wRadical K p q ≤ H := by
  classical
  have hpe : Sum.inl p ≠ (Sum.inl q : Fin n ⊕ Fin n) := fun h => hpq (Sum.inl_injective h)
  have key : ∀ T : Finset (Fin n ⊕ Fin n), ∀ g ∈ wRadical K p q,
      (∀ t, OffPQ p q t → t ∉ T → mat n K g (Sum.inl p) t = 0 ∧ mat n K g (Sum.inl q) t = 0) →
        g ∈ H := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro g hg hv
      rw [eq_siegel_of_mem_wRadical hpq hg fun t ht => hv t ht (Finset.notMem_empty t)]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hD _) (hD' _)) (hP _)
    | insert t T htT ih =>
      intro g hg hv
      by_cases ht : OffPQ p q t
      swap
      · refine ih g hg fun t' ht' hT => hv t' ht' ?_
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => ht (h ▸ ht'), hT⟩
      set cp := mat n K g (Sum.inl p) t
      set cq := mat n K g (Sum.inl q) t
      have hrow : ∀ (u : Fin n ⊕ Fin n), u ≠ Sum.inl p → u ≠ Sum.inl q → ∀ t', OffPQ p q t' →
          mat n K g u t' = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) u t' :=
        fun u hup huq t' ht' => hg.2.2 t' ht' u hup huq
      rcases t with j | j
      · have hjp : j ≠ p := fun h => ht.1 (h ▸ inl_mem_coords p)
        have hjq : j ≠ q := fun h => ht.2 (h ▸ inl_mem_coords q)
        set h1 := leviTv K (Ne.symm hjq) (-cq) * g
        set g' := leviTv K (Ne.symm hjp) (-cp) * h1
        have hg' : g' ∈ wRadical K p q :=
          Subgroup.mul_mem _ (leviTv_mem_wRadical hpq _ (Or.inl rfl) hjp hjq _)
            (Subgroup.mul_mem _ (leviTv_mem_wRadical hpq _ (Or.inr rfl) hjp hjq _) hg)
        have hej : ∀ t', mat n K h1 (Sum.inl j) t' = mat n K g (Sum.inl j) t' := fun t' =>
          mat_leviTv_mul_apply_of_ne _ _ _ (fun h => hjq (Sum.inl_injective h))
            Sum.inl_ne_inr t'
        have hmem := ih g' hg' fun t' ht' hT => by
          refine ⟨?_, ?_⟩
          · rw [mat_leviTv_mul_apply (Ne.symm hjp), hej,
              mat_leviTv_mul_apply_of_ne _ _ _ hpe (Sum.inl_ne_inr) t',
              hrow _ (fun h => hjp (Sum.inl_injective h)) (fun h => hjq (Sum.inl_injective h))
                t' ht']
            by_cases h : t' = Sum.inl j
            · subst h
              simp [cp]
            · have hT' : t' ∉ insert (Sum.inl j) T := by
                rw [Finset.mem_insert, not_or]; exact ⟨h, hT⟩
              rw [(hv t' ht' hT').1, Matrix.one_apply_ne (Ne.symm h), mul_zero, add_zero]
          · rw [mat_leviTv_mul_apply_of_ne _ _ _ hpe.symm Sum.inl_ne_inr t',
              mat_leviTv_mul_apply (Ne.symm hjq),
              hrow _ (fun h => hjp (Sum.inl_injective h)) (fun h => hjq (Sum.inl_injective h))
                t' ht']
            by_cases h : t' = Sum.inl j
            · subst h
              simp [cq]
            · have hT' : t' ∉ insert (Sum.inl j) T := by
                rw [Finset.mem_insert, not_or]; exact ⟨h, hT⟩
              rw [(hv t' ht' hT').2, Matrix.one_apply_ne (Ne.symm h), mul_zero, add_zero]
        have e : g =
            (leviTv K (Ne.symm hjq) (-cq))⁻¹ * ((leviTv K (Ne.symm hjp) (-cp))⁻¹ * g') := by
          simp only [g', h1]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL _ _ _ (Or.inr rfl) hjp hjq _))
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL _ _ _ (Or.inl rfl) hjp hjq _)) hmem)
      · have hjp : j ≠ p := fun h => ht.1 (h ▸ inr_mem_coords p)
        have hjq : j ≠ q := fun h => ht.2 (h ▸ inr_mem_coords q)
        set h1 := siegPair K q j (-cq) * g
        set g' := siegPair K p j (-cp) * h1
        have hg' : g' ∈ wRadical K p q :=
          Subgroup.mul_mem _ (siegPair_mem_wRadical (Or.inl rfl) _)
            (Subgroup.mul_mem _ (siegPair_mem_wRadical (Or.inr rfl) _) hg)
        have hfj : ∀ t', mat n K h1 (Sum.inr j) t' = mat n K g (Sum.inr j) t' := fun t' =>
          mat_siegPair_mul_apply_of_ne _ _ Sum.inr_ne_inl Sum.inr_ne_inl t'
        have hmem := ih g' hg' fun t' ht' hT => by
          refine ⟨?_, ?_⟩
          · rw [mat_siegPair_mul_apply (Ne.symm hjp), hfj,
              mat_siegPair_mul_apply_of_ne _ _ hpe (fun h => hjp (Sum.inl_injective h).symm) t',
              hrow _ Sum.inr_ne_inl Sum.inr_ne_inl t' ht']
            by_cases h : t' = Sum.inr j
            · subst h
              simp [cp]
            · have hT' : t' ∉ insert (Sum.inr j) T := by
                rw [Finset.mem_insert, not_or]; exact ⟨h, hT⟩
              rw [(hv t' ht' hT').1, Matrix.one_apply_ne (Ne.symm h), mul_zero, add_zero]
          · rw [mat_siegPair_mul_apply_of_ne _ _ hpe.symm
              (fun h => hjq (Sum.inl_injective h).symm) t',
              mat_siegPair_mul_apply (Ne.symm hjq), hrow _ Sum.inr_ne_inl Sum.inr_ne_inl t' ht']
            by_cases h : t' = Sum.inr j
            · subst h
              simp [cq]
            · have hT' : t' ∉ insert (Sum.inr j) T := by
                rw [Finset.mem_insert, not_or]; exact ⟨h, hT⟩
              rw [(hv t' ht' hT').2, Matrix.one_apply_ne (Ne.symm h), mul_zero, add_zero]
        have e : g = (siegPair K q j (-cq))⁻¹ * ((siegPair K p j (-cp))⁻¹ * g') := by
          simp only [g', h1]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS _ _ (Or.inr rfl) hjp hjq _))
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS _ _ (Or.inl rfl) hjp hjq _)) hmem)
  exact fun g hg => key Finset.univ g hg fun t _ h => absurd (Finset.mem_univ t) h
end Generation

section TwoGroup

variable {p q : Fin n}

theorem isPGroup_wRadical [CharP K 2] (hpq : p ≠ q) : IsPGroup 2 (wRadical K p q) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  have hg := g.2
  set x : StatedSp n K := (g : StatedSp n K) with hxg
  have hpe : Sum.inl p ≠ (Sum.inl q : Fin n ⊕ Fin n) := fun h => hpq (Sum.inl_injective h)
  have hrow : ∀ (i : Fin n ⊕ Fin n), (i = Sum.inl p ∨ i = Sum.inl q) → ∀ t, OffPQ p q t →
      mat n K (x * x) i t = 0 := by
    intro i hi t ht
    have htp : t ≠ Sum.inl p := fun h => ht.1 (h ▸ inl_mem_coords p)
    have htq : t ≠ Sum.inl q := fun h => ht.2 (h ▸ inl_mem_coords q)
    rw [map_mul, Matrix.mul_apply,
      Fintype.sum_eq_add t i (by rcases hi with rfl | rfl <;> assumption)]
    · rw [hg.2.2 t ht t htp htq, Matrix.one_apply_eq, mul_one]
      rcases hi with rfl | rfl
      · rw [hg.1, Matrix.one_apply_eq, one_mul, CharTwo.add_self_eq_zero]
      · rw [hg.2.1, Matrix.one_apply_eq, one_mul, CharTwo.add_self_eq_zero]
    · rintro u ⟨hut, hui⟩
      by_cases hup : u = Sum.inl p
      · subst hup
        rcases hi with rfl | rfl
        · exact absurd rfl hui
        · rw [hg.1, Matrix.one_apply_ne (Ne.symm hpe), zero_mul]
      by_cases huq : u = Sum.inl q
      · subst huq
        rcases hi with rfl | rfl
        · rw [hg.2.1, Matrix.one_apply_ne hpe, zero_mul]
        · exact absurd rfl hui
      rw [hg.2.2 t ht u hup huq, Matrix.one_apply_ne hut, mul_zero]
  have hxx : x * x ∈ wRadical K p q := Subgroup.mul_mem _ hg hg
  have e := eq_siegel_of_mem_wRadical hpq hxx fun t ht =>
    ⟨hrow _ (Or.inl rfl) t ht, hrow _ (Or.inr rfl) t ht⟩
  set α := mat n K (x * x) (Sum.inl p) (Sum.inr p)
  set β := mat n K (x * x) (Sum.inl q) (Sum.inr q)
  set γ := mat n K (x * x) (Sum.inl p) (Sum.inr q)
  have hsq : ∀ {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C),
      upperUnipotentSp n K hC * upperUnipotentSp n K hC = 1 := by
    intro C hC
    rw [upperUnipotentSp_mul, ← upperUnipotentSp_zero (m := n) (K := K)]
    exact upperUnipotentSp_congr _ _ (by rw [← two_smul K C, CharTwo.two_eq_zero, zero_smul])
  have hY : siegDiag K p α * siegDiag K q β * siegPair K p q γ =
      upperUnipotentSp n K (C := single p p α + single q q β + (single p q γ + single q p γ))
        (by simp only [transpose_add, transpose_single]; abel) := by
    rw [siegDiag, siegDiag, siegPair, upperUnipotentSp_mul, upperUnipotentSp_mul]
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add,
    pow_two]
  change x * x * (x * x) = 1
  rw [e, hY, hsq]

end TwoGroup

section Centralizer

variable {p q : Fin n}

theorem mul_single_apply' (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (i j r t : Fin n ⊕ Fin n)
    (c : K) : (M * single i j c) r t = if t = j then M r i * c else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.mul_single_apply_same (c := c) i t r M
  · exact Matrix.mul_single_apply_of_ne (c := c) i j r t h M

theorem single_mul_apply' (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (i j r t : Fin n ⊕ Fin n)
    (c : K) : (single i j c * M) r t = if r = i then c * M j t else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_apply_same (c := c) r j t M
  · exact Matrix.single_mul_apply_of_ne (c := c) i j r t h M

@[expose] def zHat (p q : Fin n) (a b : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  single (Sum.inl p) (Sum.inr p) a + single (Sum.inl p) (Sum.inr q) b +
    single (Sum.inl q) (Sum.inr p) b

theorem mul_zHat_apply (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (a b : K)
    (r t : Fin n ⊕ Fin n) : (G * zHat p q a b) r t =
      (if t = Sum.inr p then G r (Sum.inl p) * a + G r (Sum.inl q) * b else 0) +
        (if t = Sum.inr q then G r (Sum.inl p) * b else 0) := by
  simp only [zHat, Matrix.mul_add, Matrix.add_apply, mul_single_apply']
  split_ifs <;> ring

theorem zHat_mul_apply (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (a b : K)
    (r t : Fin n ⊕ Fin n) : (zHat p q a b * G) r t =
      (if r = Sum.inl p then a * G (Sum.inr p) t + b * G (Sum.inr q) t else 0) +
        (if r = Sum.inl q then b * G (Sum.inr p) t else 0) := by
  simp only [zHat, Matrix.add_mul, Matrix.add_apply, single_mul_apply']
  split_ifs <;> ring

theorem commute_twoCentralElt_iff {g : StatedSp n K} (a b : K) :
    g * twoCentralElt n p q a b = twoCentralElt n p q a b * g ↔
      mat n K g * zHat p q a b = zHat p q a b * mat n K g := by
  rw [← mat_injective.eq_iff, map_mul, map_mul, mat_twoCentralElt_eq_add]
  have e1 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) + single (Sum.inl p) (Sum.inr p) a +
      single (Sum.inl p) (Sum.inr q) b + single (Sum.inl q) (Sum.inr p) b = 1 + zHat p q a b := by
    rw [zHat]
    abel
  rw [e1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj]

variable (hpq : p ≠ q) {a b : K} (hb : b ≠ 0)
include hpq hb

theorem col_eq_zero_of_commute {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * zHat p q a b = zHat p q a b * G) {r : Fin n ⊕ Fin n} (hrp : r ≠ Sum.inl p)
    (hrq : r ≠ Sum.inl q) : G r (Sum.inl p) = 0 ∧ G r (Sum.inl q) = 0 := by
  have hpq' : (Sum.inr p : Fin n ⊕ Fin n) ≠ Sum.inr q := fun h => hpq (Sum.inr_injective h)
  have e1 := congrFun (congrFun h r) (Sum.inr q)
  rw [mul_zHat_apply, zHat_mul_apply, ite_eq_right hpq'.symm, ite_eq_left rfl, ite_eq_right hrp,
    ite_eq_right hrq]
    at e1
  simp only [zero_add, add_zero] at e1
  have hp : G r (Sum.inl p) = 0 := (mul_eq_zero.1 e1).resolve_right hb
  have e2 := congrFun (congrFun h r) (Sum.inr p)
  rw [mul_zHat_apply, zHat_mul_apply, ite_eq_left rfl, ite_eq_right hpq', ite_eq_right hrp,
    ite_eq_right hrq, hp]
    at e2
  simp only [zero_mul, zero_add, add_zero] at e2
  exact ⟨hp, (mul_eq_zero.1 e2).resolve_right hb⟩

theorem row_eq_zero_of_commute {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * zHat p q a b = zHat p q a b * G) {t : Fin n ⊕ Fin n} (htp : t ≠ Sum.inr p)
    (htq : t ≠ Sum.inr q) : G (Sum.inr p) t = 0 ∧ G (Sum.inr q) t = 0 := by
  have hpq' : (Sum.inl p : Fin n ⊕ Fin n) ≠ Sum.inl q := fun h => hpq (Sum.inl_injective h)
  have e1 := congrFun (congrFun h (Sum.inl q)) t
  rw [mul_zHat_apply, zHat_mul_apply, ite_eq_right htp, ite_eq_right htq, ite_eq_right hpq'.symm,
    ite_eq_left rfl]
    at e1
  simp only [zero_add, add_zero] at e1
  have hp : G (Sum.inr p) t = 0 := (mul_eq_zero.1 e1.symm).resolve_left hb
  have e2 := congrFun (congrFun h (Sum.inl p)) t
  rw [mul_zHat_apply, zHat_mul_apply, ite_eq_right htp, ite_eq_right htq, ite_eq_left rfl,
    ite_eq_right hpq', hp]
    at e2
  simp only [mul_zero, zero_add, add_zero] at e2
  exact ⟨hp, (mul_eq_zero.1 e2.symm).resolve_left hb⟩


omit hb in
@[expose] def blk (p q : Fin n) (r : Fin n ⊕ Fin n) : Fin 3 :=
  if r = Sum.inl p ∨ r = Sum.inl q then 0 else if r = Sum.inr p ∨ r = Sum.inr q then 1 else 2

omit hpq hb in
theorem blk_eq_zero_iff {r : Fin n ⊕ Fin n} : blk p q r = 0 ↔ r = Sum.inl p ∨ r = Sum.inl q := by
  unfold blk
  split_ifs with h1 h2 <;> simp_all

omit hpq hb in
theorem blk_eq_one_iff {r : Fin n ⊕ Fin n} : blk p q r = 1 ↔ r = Sum.inr p ∨ r = Sum.inr q := by
  unfold blk
  split_ifs with h1 h2
  · simp only [zero_ne_one, false_iff]
    rintro (rfl | rfl) <;> simp_all
  · simp_all
  · simp_all

omit hpq hb in
theorem blk_eq_two_iff {r : Fin n ⊕ Fin n} : blk p q r = 2 ↔ OffPQ p q r := by
  unfold blk OffPQ
  rcases r with x | x <;> split_ifs with h1 h2 <;> simp_all [mem_coords] <;> tauto

omit hpq hb in
theorem blk_par (r : Fin n ⊕ Fin n) :
    blk p q (par r) = if blk p q r = 0 then 1 else if blk p q r = 1 then 0 else 2 := by
  rcases r with x | x <;> simp only [blk, par, Sum.swap_inl, Sum.swap_inr, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, or_self, ite_false] <;> split_ifs <;>
    simp_all

omit hpq hb in
@[expose] def leviPart (p q : Fin n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun r t => if blk p q r = blk p q t then G r t else 0

omit hpq hb in
theorem leviPart_apply (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (r t : Fin n ⊕ Fin n) :
    leviPart p q G r t = if blk p q r = blk p q t then G r t else 0 := rfl

omit hpq hb in
theorem leviPart_one : leviPart p q (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
  ext r t
  rw [leviPart_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply_ne (by rintro rfl; exact h rfl)]

omit hpq hb in
@[expose] def BlockCond (p q : Fin n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Prop :=
  (∀ r u, blk p q u = 0 → blk p q r ≠ 0 → G r u = 0) ∧
    ∀ u t, blk p q u = 1 → blk p q t ≠ 1 → G u t = 0

omit hpq hb in
theorem leviPart_mul {G H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hG : BlockCond p q G)
    (hH : BlockCond p q H) : leviPart p q (G * H) = leviPart p q G * leviPart p q H := by
  ext r t
  simp only [leviPart_apply, Matrix.mul_apply]
  split_ifs with hrt
  · refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hru : blk p q r = blk p q u
    · rw [ite_eq_left hru, ite_eq_left (hru.symm.trans hrt)]
    · rw [ite_eq_right hru, zero_mul]
      have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases h3 (blk p q r) with h0 | h1 | h2
      · rw [hH.1 u t (hrt ▸ h0) (fun h => hru (h0.trans h.symm)), mul_zero]
      · rw [hG.2 r u h1 (fun h => hru (h1.trans h.symm)), zero_mul]
      · rcases h3 (blk p q u) with hu0 | hu1 | hu2
        · rw [hG.1 r u hu0 (by rw [h2]; decide), zero_mul]
        · rw [hH.2 u t hu1 (by rw [← hrt, h2]; decide), mul_zero]
        · exact absurd (h2.trans hu2.symm) hru
  · symm
    refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h1 h2
    · exact absurd (h1.trans h2) hrt
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]

omit hpq hb in
theorem leviPart_symplectic {g : StatedSp n K} (hg : BlockCond p q (mat n K g)) :
    (leviPart p q (mat n K g))ᵀ * gram K n * leviPart p q (mat n K g) = gram K n := by
  set σ : Fin 3 → Fin 3 := fun x => if x = 0 then 1 else if x = 1 then 0 else 2 with hσ
  have hbp : ∀ r, blk p q (par r) = σ (blk p q r) := blk_par
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  ext a b
  rw [transpose_mul_gram_mul_apply]
  simp only [leviPart_apply]
  by_cases hab : blk p q b = σ (blk p q a)
  · have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) a) b
    rw [transpose_mul_gram_mul_apply] at key
    rw [← key]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hca : blk p q c = blk p q a
    · rw [ite_eq_left hca, ite_eq_left (by rw [hbp, hca, hab])]
    · rw [ite_eq_right hca, zero_mul]
      rcases h3 (blk p q a) with ha0 | ha1 | ha2
      · rw [hg.1 c a ha0 (fun h => hca (h.trans ha0.symm)), zero_mul]
      · have hb0 : blk p q b = 0 := by rw [hab, ha1]; decide
        have hpc : blk p q (par c) ≠ 0 := by
          rw [hbp]
          intro h
          apply hca
          rw [ha1]
          rcases h3 (blk p q c) with h' | h' | h' <;> rw [h'] at h ⊢ <;> simp_all
        rw [hg.1 (par c) b hb0 hpc, mul_zero, mul_zero]
      · have hb2 : blk p q b = 2 := by rw [hab, ha2]; decide
        rcases h3 (blk p q c) with hc0 | hc1 | hc2
        · have hpc : blk p q (par c) = 1 := by rw [hbp, hc0]; decide
          rw [hg.2 (par c) b hpc (by rw [hb2]; decide), mul_zero, mul_zero]
        · rw [hg.2 c a hc1 (by rw [ha2]; decide), zero_mul]
        · exact absurd (hc2.trans ha2.symm) hca
  · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, ite_eq_right_iff.2
      (fun h => absurd (by rw [h, hbp]) hab)]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : blk p q c = blk p q a
    · have hpc : ¬ blk p q (par c) = blk p q b := fun h => hab (by rw [← h, hbp, hca])
      simp only [hpc, ite_false, mul_zero]
    · simp only [hca, ite_false, zero_mul]

theorem blockCond_of_commute {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * zHat p q a b = zHat p q a b * G) : BlockCond p q G := by
  refine ⟨fun r u hu hr => ?_, fun u t hu ht => ?_⟩
  · have hr' : ¬(r = Sum.inl p ∨ r = Sum.inl q) := fun h' => hr (blk_eq_zero_iff.2 h')
    push Not at hr'
    rcases blk_eq_zero_iff.1 hu with rfl | rfl
    · exact (col_eq_zero_of_commute hpq hb h hr'.1 hr'.2).1
    · exact (col_eq_zero_of_commute hpq hb h hr'.1 hr'.2).2
  · have ht' : ¬(t = Sum.inr p ∨ t = Sum.inr q) := fun h' => ht (blk_eq_one_iff.2 h')
    push Not at ht'
    rcases blk_eq_one_iff.1 hu with rfl | rfl
    · exact (row_eq_zero_of_commute hpq hb h ht'.1 ht'.2).1
    · exact (row_eq_zero_of_commute hpq hb h ht'.1 ht'.2).2

omit hb in
theorem leviPart_commute {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * zHat p q a b = zHat p q a b * G) :
    leviPart p q G * zHat p q a b = zHat p q a b * leviPart p q G := by
  ext r t
  have e := congrFun (congrFun h r) t
  rw [mul_zHat_apply, zHat_mul_apply] at e ⊢
  simp only [leviPart_apply]
  have hb0 : ∀ x, x = p ∨ x = q → blk p q (Sum.inl x) = 0 := fun x hx =>
    blk_eq_zero_iff.2 (by rcases hx with rfl | rfl <;> simp)
  have hb1 : ∀ y, y = p ∨ y = q → blk p q (Sum.inr y) = 1 := fun y hy =>
    blk_eq_one_iff.2 (by rcases hy with rfl | rfl <;> simp)
  rw [hb0 p (Or.inl rfl), hb0 q (Or.inr rfl), hb1 p (Or.inl rfl), hb1 q (Or.inr rfl)]
  by_cases hr : blk p q r = 0
  · by_cases ht : blk p q t = 1
    · simp only [hr, ht, ite_true] at e ⊢
      exact e
    · have ht' : t ≠ Sum.inr p ∧ t ≠ Sum.inr q := by
        constructor <;> rintro rfl <;> exact ht (hb1 _ (by simp))
      simp [ht'.1, ht'.2, Ne.symm ht]
  · have hr' : r ≠ Sum.inl p ∧ r ≠ Sum.inl q := by
      constructor <;> rintro rfl <;> exact hr (hb0 _ (by simp))
    simp [hr, hr'.1, hr'.2]

variable (a) in
@[expose] noncomputable def leviHom :
    centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K)) →* StatedSp n K where
  toFun g := ofSymplecticMat (leviPart p q (mat n K g)) (leviPart_symplectic
    (blockCond_of_commute hpq hb ((commute_twoCentralElt_iff a b).1
      (mem_centralizer_singleton_iff.1 g.2))))
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, OneMemClass.coe_one, map_one, leviPart_one])
  map_mul' g h := mat_injective (by
    rw [map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat, mat_ofSymplecticMat,
      Subgroup.coe_mul, map_mul]
    exact leviPart_mul
      (blockCond_of_commute hpq hb ((commute_twoCentralElt_iff a b).1
        (mem_centralizer_singleton_iff.1 g.2)))
      (blockCond_of_commute hpq hb ((commute_twoCentralElt_iff a b).1
        (mem_centralizer_singleton_iff.1 h.2))))

theorem mat_leviHom (g : centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K))) :
    mat n K (leviHom hpq a hb g) = leviPart p q (mat n K g) := rfl

theorem leviHom_mem_centralizer (g : centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K))) :
    leviHom hpq a hb g ∈ centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff, commute_twoCentralElt_iff, mat_leviHom]
  exact leviPart_commute hpq ((commute_twoCentralElt_iff a b).1
    (mem_centralizer_singleton_iff.1 g.2))

theorem leviHom_leviHom (g : centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K))) :
    leviHom hpq a hb ⟨leviHom hpq a hb g, leviHom_mem_centralizer hpq hb g⟩ =
      leviHom hpq a hb g := by
  apply mat_injective
  rw [mat_leviHom, mat_leviHom]
  ext r t
  simp only [leviPart_apply]
  split_ifs <;> rfl

theorem mem_wRadical_iff_leviHom_eq_one
    {g : centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K))} :
    (g : StatedSp n K) ∈ wRadical K p q ↔ leviHom hpq a hb g = 1 := by
  have hc := blockCond_of_commute hpq hb ((commute_twoCentralElt_iff a b).1
    (mem_centralizer_singleton_iff.1 g.2))
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  constructor
  · intro hg
    apply mat_injective
    rw [mat_leviHom, map_one]
    ext r t
    rw [leviPart_apply]
    split_ifs with hrt
    · rcases h3 (blk p q t) with ht0 | ht1 | ht2
      · rcases blk_eq_zero_iff.1 ht0 with rfl | rfl
        exacts [hg.1 r, hg.2.1 r]
      · rcases blk_eq_one_iff.1 (hrt.trans ht1) with rfl | rfl
        exacts [mat_inr_p_of_mem_wRadical hg t, mat_inr_q_of_mem_wRadical hg t]
      · have hr2 := blk_eq_two_iff.1 (hrt.trans ht2)
        refine hg.2.2 t (blk_eq_two_iff.1 ht2) r ?_ ?_ <;> rintro rfl
        exacts [hr2.1 (inl_mem_coords _), hr2.2 (inl_mem_coords _)]
    · rw [Matrix.one_apply_ne (by rintro rfl; exact hrt rfl)]
  · intro h1
    have hL : ∀ r t, blk p q r = blk p q t →
        mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
      intro r t hrt
      have e := congrFun (congrFun (congrArg (mat n K) h1) r) t
      rwa [mat_leviHom, map_one, leviPart_apply, ite_eq_left hrt] at e
    have hcol : ∀ x, x = p ∨ x = q → ∀ r, mat n K g r (Sum.inl x) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl x) := by
      intro x hx r
      have hx0 : blk p q (Sum.inl x) = 0 := blk_eq_zero_iff.2 (by rcases hx with rfl | rfl <;> simp)
      by_cases hr : blk p q r = 0
      · exact hL r _ (hr.trans hx0.symm)
      · rw [hc.1 r _ hx0 hr, Matrix.one_apply_ne (by rintro rfl; exact hr hx0)]
    refine ⟨hcol p (Or.inl rfl), hcol q (Or.inr rfl), fun t ht r hrp hrq => ?_⟩
    have ht2 : blk p q t = 2 := blk_eq_two_iff.2 ht
    rcases h3 (blk p q r) with hr0 | hr1 | hr2
    · rcases blk_eq_zero_iff.1 hr0 with rfl | rfl
      exacts [absurd rfl hrp, absurd rfl hrq]
    · have hrt : r ≠ t := by
        rintro rfl
        rw [hr1] at ht2
        exact absurd ht2 (by decide)
      rw [hc.2 r t hr1 (by rw [ht2]; decide), Matrix.one_apply_ne hrt]
    · exact hL r t (hr2.trans ht2.symm)

theorem centralizer_twoCentralElt_eq_sup :
    centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K)) =
      wRadical K p q ⊔ (leviHom hpq a hb).range := by
  set C := centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K))
  refine le_antisymm (fun g hg => ?_) (sup_le (wRadical_le_centralizer_twoCentralElt a b) ?_)
  · set g' : C := ⟨g, hg⟩
    set m' : C := ⟨leviHom hpq a hb g', leviHom_mem_centralizer hpq hb g'⟩
    have hq : ((g' * m'⁻¹ : C) : StatedSp n K) ∈ wRadical K p q := by
      rw [mem_wRadical_iff_leviHom_eq_one hpq hb, map_mul, map_inv, leviHom_leviHom,
        mul_inv_cancel]
    have e : g = ((g' * m'⁻¹ : C) : StatedSp n K) * leviHom hpq a hb g' := by
      simp [g', m']
    rw [e]
    exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right ⟨g', rfl⟩)
  · rintro _ ⟨g, rfl⟩
    exact leviHom_mem_centralizer hpq hb g

theorem disjoint_wRadical_range_leviHom :
    Disjoint (wRadical K p q) (leviHom hpq a hb).range := by
  rw [Subgroup.disjoint_def]
  rintro _ hq ⟨g, rfl⟩
  have h1 := (mem_wRadical_iff_leviHom_eq_one hpq hb
    (g := ⟨leviHom hpq a hb g, leviHom_mem_centralizer hpq hb g⟩)).1 hq
  rwa [leviHom_leviHom] at h1

theorem range_leviHom_le_normalizer_wRadical :
    (leviHom hpq a hb).range ≤ normalizer (wRadical K p q : Set (StatedSp n K)) := by
  set C := centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K))
  have key : ∀ (c : StatedSp n K) (hc : c ∈ C) {x : StatedSp n K}, x ∈ wRadical K p q →
      c * x * c⁻¹ ∈ wRadical K p q := by
    intro c hc x hx
    set c' : C := ⟨c, hc⟩
    set x' : C := ⟨x, wRadical_le_centralizer_twoCentralElt a b hx⟩
    have h := (mem_wRadical_iff_leviHom_eq_one hpq hb (g := x')).1 hx
    have : ((c' * x' * c'⁻¹ : C) : StatedSp n K) ∈ wRadical K p q := by
      rw [mem_wRadical_iff_leviHom_eq_one hpq hb, map_mul, map_mul, h, mul_one, map_inv,
        mul_inv_cancel]
    simpa [c', x'] using this
  rintro _ ⟨g, rfl⟩
  have hmC := leviHom_mem_centralizer hpq hb g
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key _ hmC, fun hx => ?_⟩
  have := key _ (Subgroup.inv_mem _ hmC) hx
  simpa [mul_assoc] using this

omit hb in
theorem commute_entries {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * zHat p q a b = zHat p q a b * G) :
    G (Sum.inl p) (Sum.inl p) * a + G (Sum.inl p) (Sum.inl q) * b =
        a * G (Sum.inr p) (Sum.inr p) + b * G (Sum.inr q) (Sum.inr p) ∧
      G (Sum.inl p) (Sum.inl p) * b =
        a * G (Sum.inr p) (Sum.inr q) + b * G (Sum.inr q) (Sum.inr q) ∧
      G (Sum.inl q) (Sum.inl p) * a + G (Sum.inl q) (Sum.inl q) * b =
        b * G (Sum.inr p) (Sum.inr p) ∧
      G (Sum.inl q) (Sum.inl p) * b = b * G (Sum.inr p) (Sum.inr q) := by
  have hpq' : (Sum.inr p : Fin n ⊕ Fin n) ≠ Sum.inr q := fun h => hpq (Sum.inr_injective h)
  have hpq'' : (Sum.inl p : Fin n ⊕ Fin n) ≠ Sum.inl q := fun h => hpq (Sum.inl_injective h)
  have e1 := congrFun (congrFun h (Sum.inl p)) (Sum.inr p)
  have e2 := congrFun (congrFun h (Sum.inl p)) (Sum.inr q)
  have e3 := congrFun (congrFun h (Sum.inl q)) (Sum.inr p)
  have e4 := congrFun (congrFun h (Sum.inl q)) (Sum.inr q)
  simp only [mul_zHat_apply, zHat_mul_apply, hpq', hpq'.symm, hpq'', hpq''.symm, ite_true,
    ite_false, add_zero, zero_add] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4⟩

omit hb in
theorem form_entries {g : StatedSp n K} (hc : BlockCond p q (mat n K g)) :
    mat n K g (Sum.inl p) (Sum.inl p) * mat n K g (Sum.inr p) (Sum.inr p) +
        mat n K g (Sum.inl q) (Sum.inl p) * mat n K g (Sum.inr q) (Sum.inr p) = 1 ∧
      mat n K g (Sum.inl p) (Sum.inl p) * mat n K g (Sum.inr p) (Sum.inr q) +
        mat n K g (Sum.inl q) (Sum.inl p) * mat n K g (Sum.inr q) (Sum.inr q) = 0 ∧
      mat n K g (Sum.inl p) (Sum.inl q) * mat n K g (Sum.inr p) (Sum.inr p) +
        mat n K g (Sum.inl q) (Sum.inl q) * mat n K g (Sum.inr q) (Sum.inr p) = 0 ∧
      mat n K g (Sum.inl p) (Sum.inl q) * mat n K g (Sum.inr p) (Sum.inr q) +
        mat n K g (Sum.inl q) (Sum.inl q) * mat n K g (Sum.inr q) (Sum.inr q) = 1 := by
  have hpq'' : (Sum.inl p : Fin n ⊕ Fin n) ≠ Sum.inl q := fun h => hpq (Sum.inl_injective h)
  have hb0 : ∀ x, x = p ∨ x = q → blk p q (Sum.inl x) = 0 := fun x hx =>
    blk_eq_zero_iff.2 (by rcases hx with rfl | rfl <;> simp)
  have key : ∀ x y, x = p ∨ x = q →
      mat n K g (Sum.inl p) (Sum.inl x) * mat n K g (Sum.inr p) (Sum.inr y) +
        mat n K g (Sum.inl q) (Sum.inl x) * mat n K g (Sum.inr q) (Sum.inr y) =
      (if y = x then 1 else 0) := by
    intro x y hx
    have e := congrFun (congrFun (mat_transpose_mul_gram_mul g) (Sum.inl x)) (Sum.inr y)
    rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      Fintype.sum_eq_add (Sum.inl p) (Sum.inl q) hpq''] at e
    · simpa [Sum.inr_injective.eq_iff] using e
    · rintro c ⟨hcp, hcq⟩
      have hc0 : blk p q c ≠ 0 := by
        intro h
        rcases blk_eq_zero_iff.1 h with h' | h'
        exacts [hcp h', hcq h']
      rw [hc.1 c _ (hb0 x hx) hc0, zero_mul]
  have k1 := key p p (Or.inl rfl)
  have k2 := key p q (Or.inl rfl)
  have k3 := key q p (Or.inr rfl)
  have k4 := key q q (Or.inr rfl)
  simp only [ite_true, Ne.symm hpq, hpq, ite_false] at k1 k2 k3 k4
  exact ⟨k1, k2, k3, k4⟩

omit hb in
theorem c2_blocks [CharP K 2] {g : StatedSp n K}
    (h : mat n K g * zHat p q 1 1 = zHat p q 1 1 * mat n K g) :
    mat n K g (Sum.inl p) (Sum.inl p) = 1 ∧ mat n K g (Sum.inl q) (Sum.inl p) = 0 ∧
      mat n K g (Sum.inl q) (Sum.inl q) = 1 ∧ mat n K g (Sum.inr p) (Sum.inr p) = 1 ∧
      mat n K g (Sum.inr p) (Sum.inr q) = 0 ∧ mat n K g (Sum.inr q) (Sum.inr q) = 1 ∧
      mat n K g (Sum.inr q) (Sum.inr p) = mat n K g (Sum.inl p) (Sum.inl q) := by
  have hc := blockCond_of_commute hpq one_ne_zero h
  obtain ⟨c1, c2, c3, c4⟩ := commute_entries hpq h
  obtain ⟨f1, f2, f3, f4⟩ := form_entries hpq hc
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set App := mat n K g (Sum.inl p) (Sum.inl p)
  set Apq := mat n K g (Sum.inl p) (Sum.inl q)
  set Aqp := mat n K g (Sum.inl q) (Sum.inl p)
  set Aqq := mat n K g (Sum.inl q) (Sum.inl q)
  set Dpp := mat n K g (Sum.inr p) (Sum.inr p)
  set Dpq := mat n K g (Sum.inr p) (Sum.inr q)
  set Dqp := mat n K g (Sum.inr q) (Sum.inr p)
  set Dqq := mat n K g (Sum.inr q) (Sum.inr q)
  have hDpq : Dpq = Aqp := by linear_combination -c4
  have hDqq : Dqq = App - Aqp := by linear_combination -c2 - hDpq
  have hAqp2 : Aqp * Aqp = 0 := by
    linear_combination -f2 + App * hDpq + Aqp * hDqq + (App * Aqp) * h2
  have hAqp : Aqp = 0 := mul_self_eq_zero.1 hAqp2
  have hDpp : Dpp = Aqq := by linear_combination -c3 + hAqp
  have hAA : App * Aqq = 1 := by linear_combination f1 - App * hDpp + (-Dqp) * hAqp
  have hAqq0 : Aqq ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hAA
    exact zero_ne_one hAA
  have hDqp : Dqp = -Apq := by
    have e : Aqq * (Dqp + Apq) = 0 := by linear_combination f3 - Apq * hDpp
    have e' := (mul_eq_zero.1 e).resolve_left hAqq0
    linear_combination e'
  have hApp : App = Aqq := by linear_combination c1 + hDpp + hDqp - Apq * h2
  have hApp1 : App = 1 := eq_one_of_mul_self_eq_one_of_charTwo (by
    linear_combination hAA + App * hApp)
  refine ⟨hApp1, hAqp, by rw [← hApp, hApp1], by rw [hDpp, ← hApp, hApp1], by rw [hDpq, hAqp],
    by rw [hDqq, hAqp, sub_zero, hApp1], ?_⟩
  rw [hDqp]
  linear_combination (-Apq) * h2
end Centralizer

section Perfect12

variable {n : ℕ}

theorem exists_planes12_eq {j : Fin (n + 3)} (hj1 : j ≠ 1) (hj2 : j ≠ 2) :
    ∃ i, planes12 n i = j := by
  obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq hj1
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hj2
    rw [← hx, Fin.succAbove_of_le_castSucc]
    · rfl
    · rw [Fin.le_def]
      simp
  obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hx1
  exact ⟨y, by rw [planes12, Function.comp_apply, hy, hx]⟩

theorem longRootSp2_le_spCompl12_of_ne {j : Fin (n + 3)} (hj1 : j ≠ 1) (hj2 : j ≠ 2) :
    longRootSp2 K (n + 3) j ≤ spCompl12 K n := by
  obtain ⟨i, rfl⟩ := exists_planes12_eq hj1 hj2
  rintro _ ⟨A, rfl⟩
  exact ⟨longBlock K (n + 1) i A, spEmbed_longBlock _ i A⟩

variable [Finite K]

theorem commutator_wRadical_sup_spCompl12 (hK : 4 ≤ Nat.card K) :
    ⁅wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n,
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n⁆ =
      wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  set P := wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n with hP
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one, Fin.val_two] at h'
    omega
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK
  have hκ1 : (κ : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hκ (Units.ext h)
  have hκ2 : ((κ⁻¹ : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hκ (inv_eq_one.1 (Units.ext h))
  have hQP : wRadical K (1 : Fin (n + 3)) 2 ≤ P := le_sup_left
  have hMP : spCompl12 K n ≤ P := le_sup_right
  have hM : spCompl12 K n ≤ ⁅P, P⁆ := by
    rw [← commutator_spCompl12 n hK]
    exact commutator_mono hMP hMP
  have hh : ∀ j : Fin (n + 3), j ≠ 1 → j ≠ 2 → rootTorusHom K (n + 3) j κ ∈ P := fun j hj1 hj2 =>
    hMP (longRootSp2_le_spCompl12_of_ne hj1 hj2 (rootTorusSp_le_longRootSp2 j ⟨κ, rfl⟩))
  have hS : ∀ (i j : Fin (n + 3)), (i = 1 ∨ i = 2) → j ≠ 1 → j ≠ 2 → ∀ c : K,
      siegPair K i j c ∈ ⁅P, P⁆ := by
    intro i j hi hj1 hj2 c
    have hij : i ≠ j := by rintro rfl; rcases hi with rfl | rfl; exacts [hj1 rfl, hj2 rfl]
    have e := commutatorElement_rootTorusHom_siegPair (k := j) hij κ (((κ : K) - 1)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hκ1, one_mul] at e
    rw [siegPair_comm, ← e]
    refine commutator_mem_commutator (hh j hj1 hj2) (hQP ?_)
    rw [siegPair_comm]
    exact siegPair_mem_wRadical hi _
  have hL : ∀ (i j : Fin (n + 3)) (hij : i ≠ j), (i = 1 ∨ i = 2) → j ≠ 1 → j ≠ 2 → ∀ c : K,
      leviTv K hij c ∈ ⁅P, P⁆ := by
    intro i j hij hi hj1 hj2 c
    have e := commutatorElement_rootTorusHom_leviTv (k := j) hij κ
      ((((κ⁻¹ : Kˣ) : K) - 1)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hκ2, one_mul] at e
    rw [← e]
    exact commutator_mem_commutator (hh j hj1 hj2)
      (hQP (leviTv_mem_wRadical h12 hij hi hj1 hj2 _))
  have h0 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have h0' : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_two] at h'
    omega
  have hD : ∀ (i : Fin (n + 3)), (i = 1 ∨ i = 2) → ∀ c : K, siegDiag K i c ∈ ⁅P, P⁆ := by
    intro i hi c
    have hi0 : i ≠ 0 := by rintro rfl; rcases hi with h | h; exacts [h0 h, h0' h]
    have e := commutatorElement_leviTv_siegDiag hi0 1 c
    rw [one_mul, one_mul, one_mul] at e
    have h1 : ⁅leviTv K hi0 1, siegDiag K 0 c⁆ ∈ ⁅P, P⁆ :=
      commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 hi0 hi h0 h0' 1))
        (hMP (longRootSp2_le_spCompl12_of_ne h0 h0' (siegDiag_mem_longRootSp2 0 c)))
    rw [e] at h1
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS i 0 hi h0 h0' c)) h1
    rwa [inv_mul_cancel_left] at h2
  have hP12 : ∀ c : K, siegPair K (1 : Fin (n + 3)) 2 c ∈ ⁅P, P⁆ := by
    intro c
    have h10 : (1 : Fin (n + 3)) ≠ 0 := Ne.symm h0
    have e := commutatorElement_leviTv_siegPair h10 (Ne.symm h0') 1 c
    rw [one_mul] at e
    rw [← e]
    refine commutator_mem_commutator (hQP (leviTv_mem_wRadical h12 h10 (Or.inl rfl) h0 h0' 1))
      (hQP ?_)
    rw [siegPair_comm]
    exact siegPair_mem_wRadical (Or.inr rfl) _
  have hQ : wRadical K (1 : Fin (n + 3)) 2 ≤ ⁅P, P⁆ :=
    wRadical_le_of_forall_mem h12 (hD 1 (Or.inl rfl)) (hD 2 (Or.inr rfl)) hP12
      (fun i j hij hi hj1 hj2 c => hL i j hij hi hj1 hj2 c)
      (fun i j hi hj1 hj2 c => hS i j hi hj1 hj2 c)
  exact le_antisymm (Subgroup.commutator_le_self _) (sup_le hQ hM)

theorem wRadical_sup_spCompl12_le_perfectCore (hK : 4 ≤ Nat.card K) (a b : K) :
    wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n ≤
      perfectCore (centralizer ({twoCentralElt (n + 3) 1 2 a b} : Set (StatedSp (n + 3) K))) :=
  le_perfectCore_of_perfect
    (sup_le (wRadical_le_centralizer_twoCentralElt a b)
      (spCompl12_le_centralizer_twoCentralElt n a b))
    (commutator_wRadical_sup_spCompl12 hK)


omit [Finite K] in
theorem spCompl12_eq_suppGroup :
    spCompl12 K n = suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | OffPQ 1 2 t} := by
  rw [spCompl12, range_spEmbed]
  congr 1
  ext t
  simp only [Set.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    rcases u with u | u
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exact planes12_ne_one n u (by simpa [mem_coords] using h)
      · exact planes12_ne_two n u (by simpa [mem_coords] using h)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exact planes12_ne_one n u (by simpa [mem_coords] using h)
      · exact planes12_ne_two n u (by simpa [mem_coords] using h)
  · intro ht
    rcases t with x | x
    · obtain ⟨i, hi⟩ := exists_planes12_eq (n := n) (j := x)
        (fun h => ht.1 (h ▸ inl_mem_coords _)) (fun h => ht.2 (h ▸ inl_mem_coords _))
      exact ⟨Sum.inl i, by simp [hi]⟩
    · obtain ⟨i, hi⟩ := exists_planes12_eq (n := n) (j := x)
        (fun h => ht.1 (h ▸ inr_mem_coords _)) (fun h => ht.2 (h ▸ inr_mem_coords _))
      exact ⟨Sum.inr i, by simp [hi]⟩

variable [CharP K 2]

@[expose] noncomputable def c2Coord :
    centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} : Set (StatedSp (n + 3) K)) →*
      Multiplicative K where
  toFun g := Multiplicative.ofAdd (mat (n + 3) K g (Sum.inl 1) (Sum.inl 2))
  map_one' := by
    rw [OneMemClass.coe_one, map_one, Matrix.one_apply_ne, ofAdd_zero]
    intro h
    have h' := congrArg Fin.val (Sum.inl_injective h)
    rw [Fin.val_one, Fin.val_two] at h'
    omega
  map_mul' g h := by
    have h12 : (1 : Fin (n + 3)) ≠ 2 := by
      intro h
      have h' := congrArg Fin.val h
      rw [Fin.val_one, Fin.val_two] at h'
      omega
    have hg := (commute_twoCentralElt_iff (1 : K) 1).1 (mem_centralizer_singleton_iff.1 g.2)
    have hh := (commute_twoCentralElt_iff (1 : K) 1).1 (mem_centralizer_singleton_iff.1 h.2)
    have hch := blockCond_of_commute h12 one_ne_zero hh
    obtain ⟨g1, -, -, -, -, -, -⟩ := c2_blocks h12 hg
    obtain ⟨-, -, h3, -, -, -, -⟩ := c2_blocks h12 hh
    rw [← ofAdd_add, Subgroup.coe_mul, map_mul, Matrix.mul_apply,
      Fintype.sum_eq_add (Sum.inl 1) (Sum.inl 2) (fun h => h12 (Sum.inl_injective h))]
    · rw [g1, one_mul, h3, mul_one, add_comm]
    · rintro u ⟨hu1, hu2⟩
      have hu0 : blk 1 2 u ≠ 0 := by
        intro h0
        rcases blk_eq_zero_iff.1 h0 with h' | h'
        exacts [hu1 h', hu2 h']
      rw [hch.1 u _ (blk_eq_zero_iff.2 (Or.inr rfl)) hu0, mul_zero]

theorem perfectCore_centralizer_c2 (hK : 4 ≤ Nat.card K) :
    perfectCore (centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} :
      Set (StatedSp (n + 3) K))) = wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one, Fin.val_two] at h'
    omega
  set C := centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} : Set (StatedSp (n + 3) K))
  refine le_antisymm ?_ (wRadical_sup_spCompl12_le_perfectCore hK 1 1)
  have hker : ∀ g : C, c2Coord g = 1 →
      (g : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
    intro g hg1
    have hy : mat (n + 3) K g (Sum.inl 1) (Sum.inl 2) = 0 := by
      have := congrArg Multiplicative.toAdd hg1
      simpa [c2Coord] using this
    have hg := (commute_twoCentralElt_iff (1 : K) 1).1 (mem_centralizer_singleton_iff.1 g.2)
    obtain ⟨a1, a2, a3, d1, d2, d3, d4⟩ := c2_blocks h12 hg
    rw [hy] at d4
    set m' : C := ⟨leviHom h12 1 one_ne_zero g, leviHom_mem_centralizer h12 one_ne_zero g⟩
    have hq : ((g * m'⁻¹ : C) : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 := by
      rw [mem_wRadical_iff_leviHom_eq_one h12 one_ne_zero, map_mul, map_inv, leviHom_leviHom,
        mul_inv_cancel]
    have hm : leviHom h12 1 one_ne_zero g ∈ spCompl12 K n := by
      rw [spCompl12_eq_suppGroup]
      intro r t hrt
      rw [mat_leviHom, leviPart_apply]
      have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      have h21 : (2 : Fin (n + 3)) ≠ 1 := Ne.symm h12
      split_ifs with hb
      · have hnot : blk 1 2 r ≠ 2 := fun h2 => hrt ⟨blk_eq_two_iff.1 h2,
          blk_eq_two_iff.1 (hb ▸ h2)⟩
        rcases h3 (blk 1 2 r) with h0 | h1 | h2
        · rcases blk_eq_zero_iff.1 h0 with rfl | rfl <;>
            rcases blk_eq_zero_iff.1 (hb ▸ h0) with h' | h' <;> subst h' <;>
            simp_all
        · rcases blk_eq_one_iff.1 h1 with rfl | rfl <;>
            rcases blk_eq_one_iff.1 (hb ▸ h1) with h' | h' <;> subst h' <;>
            simp_all
        · exact absurd h2 hnot
      · rw [Matrix.one_apply_ne (by rintro rfl; exact hb rfl)]
    have e : (g : StatedSp (n + 3) K) =
        ((g * m'⁻¹ : C) : StatedSp (n + 3) K) * leviHom h12 1 one_ne_zero g := by
      simp [m']
    rw [e]
    exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right hm)
  calc perfectCore C ≤ ⁅C, C⁆ := CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1
    _ ≤ wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hc : ⁅(⟨g₁, hg₁⟩ : C), ⟨g₂, hg₂⟩⁆ = (⟨⁅g₁, g₂⁆, Subgroup.commutator_mem_commutator
          hg₁ hg₂ |> fun h => (Subgroup.commutator_le_self C) h⟩ : C) := rfl
      have h1 : c2Coord ⁅(⟨g₁, hg₁⟩ : C), ⟨g₂, hg₂⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
      rw [hc] at h1
      exact hker _ h1

omit [CharP K 2] in
theorem eq_bot_of_normal_of_isPGroup_statedSp [CharP K 2] {m : ℕ} (hK : 4 ≤ Nat.card K)
    (hm : 1 ≤ m) (N : Subgroup (StatedSp m K)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have : IsSimpleGroup (StatedSp m K) := isSimpleGroup_statedSp hK hm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  exfalso
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK
  set x := rootTorusHom K m ⟨0, by omega⟩ κ
  have hxN : x ∈ N := h ▸ Subgroup.mem_top x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN) ⟨x, hxN⟩
  rw [Subgroup.orderOf_mk] at hk
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    have := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hf]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, f.ne_zero⟩) odd_one
  have hdvd : orderOf x ∣ Nat.card Kˣ := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card Kˣ := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hκ (rootTorusHom_injective _ (hk.trans (map_one _).symm))

omit [CharP K 2] in
theorem eq_bot_of_normal_of_isPGroup_of_mulEquiv [CharP K 2] {m : ℕ} (hK : 4 ≤ Nat.card K)
    (hm : 1 ≤ m) {M : Type*} [Group M] (e : M ≃* StatedSp m K) (N : Subgroup M) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  have hN' : IsPGroup 2 (N.map e.toMonoidHom) := hN.map _
  have : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have h := eq_bot_of_normal_of_isPGroup_statedSp hK hm _ hN'
  rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
  exact h

omit [Finite K] [CharP K 2] in
theorem spRep_c2_eq (n : ℕ) : spRep (K := K) n .c2 = twoCentralElt (n + 3) 1 2 1 1 := rfl

theorem perfectCore_centralizer_spRep_c2 (hK : 4 ≤ Nat.card K) :
    ∃ Q M S : Subgroup (StatedSp (n + 3) K), IsPGroup 2 Q ∧
      M ≤ normalizer (Q : Set (StatedSp (n + 3) K)) ∧ Disjoint Q M ∧
      perfectCore (centralizer ({spRep n .c2} : Set (StatedSp (n + 3) K))) = Q ⊔ M ∧
      (∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      spRep n .c2 ∈ perfectCore (centralizer ({spRep n .c2} : Set (StatedSp (n + 3) K))) ∧
      longRootSp2 K (n + 3) 0 ≤ S ∧ S = perfectCore M ∧
      Nonempty (S ≃* StatedSp (n + 1) K) := by
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one, Fin.val_two] at h'
    omega
  set C := centralizer ({twoCentralElt (n + 3) 1 2 (1 : K) 1} : Set (StatedSp (n + 3) K))
  have hML : ∀ m ∈ spCompl12 K n, ∃ hm : m ∈ C,
      leviHom h12 (1 : K) one_ne_zero ⟨m, hm⟩ = m := by
    intro m hm
    have hmC : m ∈ C := spCompl12_le_centralizer_twoCentralElt n 1 1 hm
    refine ⟨hmC, mat_injective ?_⟩
    rw [mat_leviHom]
    have hsupp : IsSupp {t : Fin (n + 3) ⊕ Fin (n + 3) | OffPQ 1 2 t} (mat (n + 3) K m) := by
      rw [spCompl12_eq_suppGroup] at hm
      exact hm
    ext r t
    rw [leviPart_apply]
    split_ifs with hb
    · rfl
    · have hnt : ¬(OffPQ 1 2 r ∧ OffPQ 1 2 t) := fun h =>
        hb ((blk_eq_two_iff.2 h.1).trans (blk_eq_two_iff.2 h.2).symm)
      rw [hsupp r t hnt, Matrix.one_apply_ne (by rintro rfl; exact hb rfl)]
  refine ⟨wRadical K (1 : Fin (n + 3)) 2, spCompl12 K n, spCompl12 K n, isPGroup_wRadical h12,
    ?_, ?_, ?_, ?_, spRep_mem_perfectCore_centralizer hK n .c2, longRootSp2_le_spCompl12 n,
    (CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_spCompl12 n hK)).symm,
    ⟨(spCompl12Equiv K n).symm⟩⟩
  · intro m hm
    obtain ⟨hmC, e⟩ := hML m hm
    exact range_leviHom_le_normalizer_wRadical h12 one_ne_zero ⟨⟨m, hmC⟩, e⟩
  · rw [Subgroup.disjoint_def]
    intro m hq hm
    obtain ⟨hmC, e⟩ := hML m hm
    have h1 := (mem_wRadical_iff_leviHom_eq_one h12 one_ne_zero (g := ⟨m, hmC⟩)).1 hq
    rw [e] at h1
    exact h1
  · rw [spRep_c2_eq]
    exact perfectCore_centralizer_c2 hK
  · intro N hN hN2
    exact eq_bot_of_normal_of_isPGroup_of_mulEquiv hK (by omega) (spCompl12Equiv K n).symm N hN2
end Perfect12

section A2

variable {n : ℕ} {p q : Fin n}

theorem shortBlock_eq_leviEmbedGL (hpq : p ≠ q) (A : SL(2, K)) :
    shortBlock K hpq A = leviEmbedGL K n (CFSG.LieType.Steinberg.Sp.blockHom K hpq A) := rfl

theorem shortBlock_mem_centralizer [CharP K 2] (hpq : p ≠ q) (A : SL(2, K)) (b : K) :
    shortBlock K hpq A ∈ centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact A.2
  have hconj : shortBlock K hpq A * twoCentralElt n p q 0 b * (shortBlock K hpq A)⁻¹ =
      twoCentralElt n p q 0 b := by
    rw [shortBlock_eq_leviEmbedGL, twoCentralElt, leviEmbedGL_conj_upperUnipotentSp]
    refine upperUnipotentSp_congr _ _ ?_
    rw [CFSG.LieType.Steinberg.Sp.coe_blockHom]
    set B := CFSG.LieType.Steinberg.Sp.blockMat p q (A : Matrix (Fin 2) (Fin 2) K)
    have hQ : twoCentralMat p q (0 : K) b = single p q b + single q p b := by
      rw [twoCentralMat, single_zero, zero_add]
    rw [hQ, Matrix.mul_add, Matrix.add_mul]
    ext x y
    rw [Matrix.add_apply, mul_single_mul_transpose_apply, mul_single_mul_transpose_apply,
      Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
    simp only [B, CFSG.LieType.Steinberg.Sp.blockMat, Matrix.of_apply]
    by_cases hxp : x = p
    · subst hxp
      by_cases hyp : y = x
      · subst hyp
        simp only [ite_true, hpq, ite_false, Ne.symm hpq, and_false, false_and, add_zero]
        linear_combination (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
          b * h2
      by_cases hyq : y = q
      · subst hyq
        simp only [ite_true, hpq, ite_false, Ne.symm hpq, and_self, add_zero]
        linear_combination b * hdet + (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
          (A : Matrix (Fin 2) (Fin 2) K) 1 0 * b * h2
      · simp [hyp, hyq, Ne.symm hyp, Ne.symm hyq]
    by_cases hxq : x = q
    · subst hxq
      by_cases hyp : y = p
      · subst hyp
        simp only [ite_true, hxp, ite_false, Ne.symm hxp, and_self, zero_add]
        linear_combination b * hdet + (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
          (A : Matrix (Fin 2) (Fin 2) K) 1 0 * b * h2
      by_cases hyq : y = x
      · subst hyq
        simp only [ite_true, hxp, ite_false, Ne.symm hxp, and_false, false_and, add_zero]
        linear_combination (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 *
          b * h2
      · simp [hyp, hyq, Ne.symm hyp, Ne.symm hyq]
    · simp [hxp, hxq, Ne.symm hxp, Ne.symm hxq, Matrix.one_apply]
  calc shortBlock K hpq A * twoCentralElt n p q 0 b =
      shortBlock K hpq A * twoCentralElt n p q 0 b * (shortBlock K hpq A)⁻¹ *
        shortBlock K hpq A := by group
    _ = twoCentralElt n p q 0 b * shortBlock K hpq A := by rw [hconj]


@[expose] def wBlock (p q : Fin n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![G (Sum.inl p) (Sum.inl p), G (Sum.inl p) (Sum.inl q);
    G (Sum.inl q) (Sum.inl p), G (Sum.inl q) (Sum.inl q)]

theorem wBlock_mul (hpq : p ≠ q) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    {H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hH : BlockCond p q H) :
    wBlock p q (G * H) = wBlock p q G * wBlock p q H := by
  have hpq' : (Sum.inl p : Fin n ⊕ Fin n) ≠ Sum.inl q := fun h => hpq (Sum.inl_injective h)
  have key : ∀ x y, (y = p ∨ y = q) → (G * H) (Sum.inl x) (Sum.inl y) =
      G (Sum.inl x) (Sum.inl p) * H (Sum.inl p) (Sum.inl y) +
        G (Sum.inl x) (Sum.inl q) * H (Sum.inl q) (Sum.inl y) := by
    intro x y hy
    rw [Matrix.mul_apply, Fintype.sum_eq_add (Sum.inl p) (Sum.inl q) hpq']
    rintro u ⟨hup, huq⟩
    have hu0 : blk p q u ≠ 0 := by
      intro h0
      rcases blk_eq_zero_iff.1 h0 with h' | h'
      exacts [hup h', huq h']
    rw [hH.1 u _ (blk_eq_zero_iff.2 (by rcases hy with rfl | rfl <;> simp)) hu0, mul_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wBlock, Matrix.mul_apply, Fin.sum_univ_two, key _ _ (Or.inl rfl), key _ _ (Or.inr rfl)]

variable [CharP K 2]

theorem a2_blocks (hpq : p ≠ q) {b : K} (hb : b ≠ 0) {g : StatedSp n K}
    (h : mat n K g * zHat p q 0 b = zHat p q 0 b * mat n K g) :
    (wBlock p q (mat n K g)).det = 1 ∧
      mat n K g (Sum.inr p) (Sum.inr p) = mat n K g (Sum.inl q) (Sum.inl q) ∧
      mat n K g (Sum.inr p) (Sum.inr q) = mat n K g (Sum.inl q) (Sum.inl p) ∧
      mat n K g (Sum.inr q) (Sum.inr p) = mat n K g (Sum.inl p) (Sum.inl q) ∧
      mat n K g (Sum.inr q) (Sum.inr q) = mat n K g (Sum.inl p) (Sum.inl p) := by
  have hc := blockCond_of_commute hpq hb h
  obtain ⟨c1, c2, c3, c4⟩ := commute_entries hpq h
  obtain ⟨f1, -, -, -⟩ := form_entries hpq hc
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [mul_zero, zero_mul, zero_add] at c1 c2 c3 c4
  have e1 : mat n K g (Sum.inr q) (Sum.inr p) = mat n K g (Sum.inl p) (Sum.inl q) :=
    (mul_left_cancel₀ hb (by linear_combination c1)).symm
  have e2 : mat n K g (Sum.inr q) (Sum.inr q) = mat n K g (Sum.inl p) (Sum.inl p) :=
    (mul_left_cancel₀ hb (by linear_combination c2)).symm
  have e3 : mat n K g (Sum.inr p) (Sum.inr p) = mat n K g (Sum.inl q) (Sum.inl q) :=
    (mul_left_cancel₀ hb (by linear_combination c3)).symm
  have e4 : mat n K g (Sum.inr p) (Sum.inr q) = mat n K g (Sum.inl q) (Sum.inl p) :=
    (mul_left_cancel₀ hb (by linear_combination c4)).symm
  refine ⟨?_, e3, e4, e1, e2⟩
  rw [wBlock, Matrix.det_fin_two_of]
  rw [e3, e1] at f1
  linear_combination f1 - mat n K g (Sum.inl p) (Sum.inl q) * mat n K g (Sum.inl q) (Sum.inl p) * h2

@[expose] noncomputable def a2Coord (hpq : p ≠ q) {b : K} (hb : b ≠ 0) :
    centralizer ({twoCentralElt n p q 0 b} : Set (StatedSp n K)) →* SL(2, K) where
  toFun g := ⟨wBlock p q (mat n K g), (a2_blocks hpq hb ((commute_twoCentralElt_iff 0 b).1
    (mem_centralizer_singleton_iff.1 g.2))).1⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wBlock, hpq, Ne.symm hpq]
  map_mul' g h := by
    have hh := blockCond_of_commute hpq hb ((commute_twoCentralElt_iff 0 b).1
      (mem_centralizer_singleton_iff.1 h.2))
    apply Subtype.ext
    change wBlock p q (mat n K ((g : StatedSp n K) * h)) =
      wBlock p q (mat n K g) * wBlock p q (mat n K h)
    rw [map_mul, wBlock_mul hpq _ hh]

omit [CharP K 2] in
theorem wBlock_shortBlock (hpq : p ≠ q) (B : SL(2, K)) :
    wBlock p q (mat n K (shortBlock K hpq B)) = (B : Matrix (Fin 2) (Fin 2) K) := by
  rw [mat_shortBlock]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wBlock, CFSG.LieType.Steinberg.Sp.blockMat, Ne.symm hpq]

end A2

section A2Planes

variable {n : ℕ}

theorem one_ne_two_fin : (1 : Fin (n + 3)) ≠ 2 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_one, Fin.val_two] at h'
  omega

theorem leviHom_mem_spCompl12 {a b : K} (hb : b ≠ 0)
    (g : centralizer ({twoCentralElt (n + 3) 1 2 a b} : Set (StatedSp (n + 3) K)))
    (hA : ∀ x y : Fin (n + 3), (x = 1 ∨ x = 2) → (y = 1 ∨ y = 2) →
      mat (n + 3) K g (Sum.inl x) (Sum.inl y) = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y)
    (hD : ∀ x y : Fin (n + 3), (x = 1 ∨ x = 2) → (y = 1 ∨ y = 2) →
      mat (n + 3) K g (Sum.inr x) (Sum.inr y) = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y) :
    leviHom one_ne_two_fin a hb g ∈ spCompl12 K n := by
  rw [spCompl12_eq_suppGroup]
  intro r t hrt
  rw [mat_leviHom, leviPart_apply]
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  split_ifs with hb'
  · rcases h3 (blk 1 2 r) with h0 | h1 | h2
    · obtain ⟨x, rfl, hx⟩ : ∃ x, r = Sum.inl x ∧ (x = 1 ∨ x = 2) := by
        rcases blk_eq_zero_iff.1 h0 with h' | h' <;> exact ⟨_, h', by simp⟩
      obtain ⟨y, rfl, hy⟩ : ∃ y, t = Sum.inl y ∧ (y = 1 ∨ y = 2) := by
        rcases blk_eq_zero_iff.1 (hb' ▸ h0) with h' | h' <;> exact ⟨_, h', by simp⟩
      rw [hA x y hx hy]
      simp [Matrix.one_apply]
    · obtain ⟨x, rfl, hx⟩ : ∃ x, r = Sum.inr x ∧ (x = 1 ∨ x = 2) := by
        rcases blk_eq_one_iff.1 h1 with h' | h' <;> exact ⟨_, h', by simp⟩
      obtain ⟨y, rfl, hy⟩ : ∃ y, t = Sum.inr y ∧ (y = 1 ∨ y = 2) := by
        rcases blk_eq_one_iff.1 (hb' ▸ h1) with h' | h' <;> exact ⟨_, h', by simp⟩
      rw [hD x y hx hy]
      simp [Matrix.one_apply]
    · exact absurd ⟨blk_eq_two_iff.1 h2, blk_eq_two_iff.1 (hb' ▸ h2)⟩ hrt
  · rw [Matrix.one_apply_ne (by rintro rfl; exact hb' rfl)]

variable [CharP K 2]

theorem centralizer_a2_le :
    centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) ≤
      wRadical K (1 : Fin (n + 3)) 2 ⊔
        ((shortBlock K (one_ne_two_fin (n := n))).range ⊔ spCompl12 K n) := by
  set C := centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K))
  have h12 := one_ne_two_fin (n := n)
  intro g hg
  set A := a2Coord h12 (one_ne_zero (α := K)) ⟨g, hg⟩
  have hsC : shortBlock K h12 A ∈ C := shortBlock_mem_centralizer h12 A 1
  set s : C := ⟨shortBlock K h12 A, hsC⟩
  have hsA : a2Coord h12 (one_ne_zero (α := K)) s = A := Subtype.ext (wBlock_shortBlock h12 A)
  set g' : C := s⁻¹ * ⟨g, hg⟩
  have hg'A : a2Coord h12 (one_ne_zero (α := K)) g' = 1 := by
    rw [map_mul, map_inv, hsA, inv_mul_cancel]
  have hW : wBlock 1 2 (mat (n + 3) K g') = 1 := congrArg Subtype.val hg'A
  have hcomm := (commute_twoCentralElt_iff (0 : K) 1).1 (mem_centralizer_singleton_iff.1 g'.2)
  obtain ⟨-, d1, d2, d3, d4⟩ := a2_blocks h12 one_ne_zero hcomm
  have hW' : ∀ i j : Fin 2,
      wBlock 1 2 (mat (n + 3) K g') i j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by rw [hW]
  have a11 := hW' 0 0
  have a12 := hW' 0 1
  have a21 := hW' 1 0
  have a22 := hW' 1 1
  simp only [wBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq] at a11 a12 a21 a22
  simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at a12 a21
  have hA : ∀ x y : Fin (n + 3), (x = 1 ∨ x = 2) → (y = 1 ∨ y = 2) →
      mat (n + 3) K g' (Sum.inl x) (Sum.inl y) =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [a11, a12, a21, a22, h12, Ne.symm h12]
  have hD : ∀ x y : Fin (n + 3), (x = 1 ∨ x = 2) → (y = 1 ∨ y = 2) →
      mat (n + 3) K g' (Sum.inr x) (Sum.inr y) =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) x y := by
    rintro x y (rfl | rfl) (rfl | rfl) <;>
      simp [d1, d2, d3, d4, a11, a12, a21, a22, h12, Ne.symm h12]
  have hm := leviHom_mem_spCompl12 (one_ne_zero (α := K)) g' hA hD
  set m' : C := ⟨leviHom h12 0 one_ne_zero g', leviHom_mem_centralizer h12 one_ne_zero g'⟩
  have hq : ((g' * m'⁻¹ : C) : StatedSp (n + 3) K) ∈ wRadical K (1 : Fin (n + 3)) 2 := by
    rw [mem_wRadical_iff_leviHom_eq_one h12 one_ne_zero, map_mul, map_inv, leviHom_leviHom,
      mul_inv_cancel]
  have e1 : ((g' * m'⁻¹ : C) : StatedSp (n + 3) K) * leviHom h12 0 one_ne_zero g' =
      (g' : StatedSp (n + 3) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    change (g' : StatedSp (n + 3) K) * (leviHom h12 0 one_ne_zero g')⁻¹ *
      leviHom h12 0 one_ne_zero g' = g'
    group
  have e2 : (g' : StatedSp (n + 3) K) = (shortBlock K h12 A)⁻¹ * g := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have e : g = shortBlock K h12 A *
      (((g' * m'⁻¹ : C) : StatedSp (n + 3) K) * leviHom h12 0 one_ne_zero g') := by
    rw [e1, e2]
    group
  rw [e]
  refine Subgroup.mul_mem _ (mem_sup_right (mem_sup_left ⟨A, rfl⟩)) ?_
  exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right (mem_sup_right hm))


omit [CharP K 2] in
theorem commutator_range_shortBlock [Finite K] {p q : Fin n} (hpq : p ≠ q) (hK : 4 ≤ Nat.card K) :
    ⁅(shortBlock K hpq).range, (shortBlock K hpq).range⁆ = (shortBlock K hpq).range := by
  have : Group.IsPerfect (StatedSp 1 K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 1 K (Or.inl (exists_finset_card_four hK))
  have : Group.IsPerfect SL(2, K) :=
    Group.IsPerfect.ofSurjective (f := (longBlockEquivOne K).symm.toMonoidHom)
      (MulEquiv.surjective _)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem perfectCore_centralizer_a2 [Finite K] (hK : 4 ≤ Nat.card K) :
    perfectCore (centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} :
      Set (StatedSp (n + 3) K))) =
      wRadical K (1 : Fin (n + 3)) 2 ⊔
        ((shortBlock K (one_ne_two_fin (n := n))).range ⊔ spCompl12 K n) ∧
    centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) =
      wRadical K (1 : Fin (n + 3)) 2 ⊔
        ((shortBlock K (one_ne_two_fin (n := n))).range ⊔ spCompl12 K n) := by
  have h12 := one_ne_two_fin (n := n)
  set P := wRadical K (1 : Fin (n + 3)) 2 ⊔ ((shortBlock K h12).range ⊔ spCompl12 K n)
  set C := centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K))
  have hPC : P ≤ C := sup_le (wRadical_le_centralizer_twoCentralElt 0 1)
    (sup_le (by rintro _ ⟨A, rfl⟩; exact shortBlock_mem_centralizer h12 A 1)
      (spCompl12_le_centralizer_twoCentralElt n 0 1))
  have hCP : C = P := le_antisymm centralizer_a2_le hPC
  have hperf : ⁅P, P⁆ = P := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    have h1 : wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n ≤ ⁅P, P⁆ := by
      rw [← commutator_wRadical_sup_spCompl12 hK]
      have hle : wRadical K (1 : Fin (n + 3)) 2 ⊔ spCompl12 K n ≤ P :=
        sup_le le_sup_left (le_sup_right.trans le_sup_right)
      exact commutator_mono hle hle
    have h2 : (shortBlock K h12).range ≤ ⁅P, P⁆ := by
      rw [← commutator_range_shortBlock h12 hK]
      have hle : (shortBlock K h12).range ≤ P := le_sup_left.trans le_sup_right
      exact commutator_mono hle hle
    exact sup_le (le_sup_left.trans h1) (sup_le h2 (le_sup_right.trans h1))
  refine ⟨?_, hCP⟩
  rw [hCP, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

omit [CharP K 2] in
theorem leviHom_eq_self_of_blockDiag {a b : K} (hb : b ≠ 0)
    (g : centralizer ({twoCentralElt (n + 3) 1 2 a b} : Set (StatedSp (n + 3) K)))
    (hg : ∀ r t, blk 1 2 r ≠ blk 1 2 t → mat (n + 3) K g r t = 0) :
    leviHom one_ne_two_fin a hb g = g := by
  apply mat_injective
  rw [mat_leviHom]
  ext r t
  rw [leviPart_apply]
  split_ifs with h
  · rfl
  · exact (hg r t h).symm

omit [CharP K 2] in
theorem spCompl12_le_range_leviHom {a b : K} (hb : b ≠ 0) :
    spCompl12 K n ≤ (leviHom (one_ne_two_fin (n := n)) a hb).range := by
  intro m hm
  have hmC := spCompl12_le_centralizer_twoCentralElt n a b hm
  refine ⟨⟨m, hmC⟩, leviHom_eq_self_of_blockDiag hb _ fun r t hrt => ?_⟩
  rw [spCompl12_eq_suppGroup] at hm
  have hnt : ¬(OffPQ 1 2 r ∧ OffPQ 1 2 t) := fun h =>
    hrt ((blk_eq_two_iff.2 h.1).trans (blk_eq_two_iff.2 h.2).symm)
  change mat (n + 3) K m r t = 0
  rw [hm r t hnt, Matrix.one_apply_ne (by rintro rfl; exact hrt rfl)]

theorem range_shortBlock_le_range_leviHom {b : K} (hb : b ≠ 0) :
    (shortBlock K (one_ne_two_fin (n := n))).range ≤
      (leviHom (one_ne_two_fin (n := n)) 0 hb).range := by
  rintro _ ⟨A, rfl⟩
  refine ⟨⟨_, shortBlock_mem_centralizer one_ne_two_fin A b⟩,
    leviHom_eq_self_of_blockDiag hb _ fun r t hrt => ?_⟩
  change mat (n + 3) K (shortBlock K one_ne_two_fin A) r t = 0
  rw [mat_shortBlock]
  have h12 := one_ne_two_fin (n := n)
  have hb0 : ∀ x : Fin (n + 3), blk 1 2 (Sum.inl x) = 0 ↔ (x = 1 ∨ x = 2) := fun x => by
    rw [blk_eq_zero_iff]; simp
  have hb1 : ∀ x : Fin (n + 3), blk 1 2 (Sum.inr x) = 1 ↔ (x = 1 ∨ x = 2) := fun x => by
    rw [blk_eq_one_iff]; simp
  have hbl : ∀ x : Fin (n + 3), ¬(x = 1 ∨ x = 2) → blk 1 2 (Sum.inl x) = 2 ∧
      blk 1 2 (Sum.inr x) = 2 := fun x hx => by
    refine ⟨blk_eq_two_iff.2 ⟨?_, ?_⟩, blk_eq_two_iff.2 ⟨?_, ?_⟩⟩ <;> intro h <;>
      simp [mem_coords] at h <;> tauto
  rcases r with x | x <;> rcases t with y | y
  · rw [fromBlocks_apply₁₁]
    by_cases hx : x = 1 ∨ x = 2
    · have hy : ¬(y = 1 ∨ y = 2) := fun hy => hrt (((hb0 x).2 hx).trans ((hb0 y).2 hy).symm)
      push Not at hy
      rcases hx with rfl | rfl <;>
        simp [CFSG.LieType.Steinberg.Sp.blockMat, hy.1, hy.2, Ne.symm h12]
    · have hy : y = 1 ∨ y = 2 := by
        by_contra hy
        exact hrt (((hbl x hx).1).trans ((hbl y hy).1).symm)
      have hxy : x ≠ y := by rintro rfl; exact hx hy
      push Not at hx
      simp [CFSG.LieType.Steinberg.Sp.blockMat, hx.1, hx.2, Matrix.one_apply_ne hxy]
  · rfl
  · rfl
  · rw [fromBlocks_apply₂₂, Matrix.transpose_apply]
    by_cases hy : y = 1 ∨ y = 2
    · have hx : ¬(x = 1 ∨ x = 2) := fun hx => hrt (((hb1 x).2 hx).trans ((hb1 y).2 hy).symm)
      push Not at hx
      rcases hy with rfl | rfl <;>
        simp [CFSG.LieType.Steinberg.Sp.blockMat, hx.1, hx.2, Ne.symm h12]
    · have hx : x = 1 ∨ x = 2 := by
        by_contra hx
        exact hrt (((hbl x hx).2).trans ((hbl y hy).2).symm)
      have hxy : y ≠ x := by rintro rfl; exact hy hx
      push Not at hy
      simp [CFSG.LieType.Steinberg.Sp.blockMat, hy.1, hy.2, Matrix.one_apply_ne hxy]

variable (K n) in
@[expose] noncomputable def a2Levi : Subgroup (StatedSp (n + 3) K) :=
  (shortBlock K (one_ne_two_fin (n := n))).range ⊔ spCompl12 K n

omit [CharP K 2] in
theorem spRep_a2_eq : spRep (K := K) n .a2 = twoCentralElt (n + 3) 1 2 0 1 := rfl

theorem eq_bot_of_normal_of_isPGroup_a2Levi [Finite K] (hK : 4 ≤ Nat.card K)
    (N : Subgroup (a2Levi K n)) [hN : N.Normal] (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have h12 := one_ne_two_fin (n := n)
  have hMC : a2Levi K n ≤
      centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) :=
    sup_le (by rintro _ ⟨A, rfl⟩; exact shortBlock_mem_centralizer h12 A 1)
      (spCompl12_le_centralizer_twoCentralElt n 0 1)
  have hML : a2Levi K n ≤ (leviHom h12 0 (one_ne_zero (α := K))).range :=
    sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero)
  set φ : a2Levi K n →* SL(2, K) :=
    (a2Coord h12 (one_ne_zero (α := K))).comp (Subgroup.inclusion hMC) with hφdef
  have hφ : Function.Surjective φ := by
    intro B
    refine ⟨⟨shortBlock K h12 B, mem_sup_left ⟨B, rfl⟩⟩, Subtype.ext ?_⟩
    exact wBlock_shortBlock h12 B
  have hNφ : N.map φ = ⊥ := by
    have : (N.map φ).Normal := Subgroup.Normal.map hN φ hφ
    exact eq_bot_of_normal_of_isPGroup_of_mulEquiv hK le_rfl (longBlockEquivOne K) _
      (hN2.map φ)
  have hNS : ∀ x ∈ N, (x : StatedSp (n + 3) K) ∈ spCompl12 K n := by
    intro x hx
    have hx1 : φ x = 1 := by
      have : φ x ∈ N.map φ := ⟨x, hx, rfl⟩
      rw [hNφ] at this
      exact this
    obtain ⟨y, hy⟩ := hML x.2
    set x' : centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) :=
      ⟨x, hMC x.2⟩
    have hx'eq : x' = ⟨leviHom h12 0 one_ne_zero y, leviHom_mem_centralizer h12 one_ne_zero y⟩ :=
      Subtype.ext hy.symm
    have hfix : leviHom h12 0 (one_ne_zero (α := K)) x' = x := by
      rw [hx'eq, leviHom_leviHom, hy]
    have hW : wBlock 1 2 (mat (n + 3) K x') = 1 := congrArg Subtype.val hx1
    have hcomm := (commute_twoCentralElt_iff (0 : K) 1).1 (mem_centralizer_singleton_iff.1 x'.2)
    obtain ⟨-, d1, d2, d3, d4⟩ := a2_blocks h12 one_ne_zero hcomm
    have hW' : ∀ i j : Fin 2, wBlock 1 2 (mat (n + 3) K x') i j =
        (1 : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by rw [hW]
    have a11 := hW' 0 0
    have a12 := hW' 0 1
    have a21 := hW' 1 0
    have a22 := hW' 1 1
    simp only [wBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.one_apply_eq] at a11 a12 a21 a22
    simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at a12 a21
    have hA : ∀ u v : Fin (n + 3), (u = 1 ∨ u = 2) → (v = 1 ∨ v = 2) →
        mat (n + 3) K x' (Sum.inl u) (Sum.inl v) =
          (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) u v := by
      rintro u v (rfl | rfl) (rfl | rfl) <;> simp [a11, a12, a21, a22, h12, Ne.symm h12]
    have hD : ∀ u v : Fin (n + 3), (u = 1 ∨ u = 2) → (v = 1 ∨ v = 2) →
        mat (n + 3) K x' (Sum.inr u) (Sum.inr v) =
          (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) u v := by
      rintro u v (rfl | rfl) (rfl | rfl) <;>
        simp [d1, d2, d3, d4, a11, a12, a21, a22, h12, Ne.symm h12]
    have hm := leviHom_mem_spCompl12 (one_ne_zero (α := K)) x' hA hD
    rwa [hfix] at hm
  set N₁ : Subgroup (spCompl12 K n) := (N.map (a2Levi K n).subtype).subgroupOf (spCompl12 K n)
  have hN₁ : N₁.Normal := by
    refine ⟨fun x hx s => ?_⟩
    obtain ⟨y, hyN, hyx⟩ := hx
    have hyx' : (y : StatedSp (n + 3) K) = x := hyx
    have hsM : (s : StatedSp (n + 3) K) ∈ a2Levi K n := mem_sup_right s.2
    have hc := hN.conj_mem y hyN ⟨s, hsM⟩
    refine ⟨_, hc, ?_⟩
    change (s : StatedSp (n + 3) K) * y * (s : StatedSp (n + 3) K)⁻¹ = (s * x * s⁻¹ : spCompl12 K n)
    rw [hyx']
    rfl
  have hN₁2 : IsPGroup 2 N₁ := by
    intro x
    obtain ⟨y, hyN, hyx⟩ := x.2
    have hyx' : (y : StatedSp (n + 3) K) = ((x : spCompl12 K n) : StatedSp (n + 3) K) := hyx
    obtain ⟨k, hk⟩ := hN2 ⟨y, hyN⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : N => ((z : a2Levi K n) : StatedSp (n + 3) K)) hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hyx']
    exact this
  have hbot := eq_bot_of_normal_of_isPGroup_of_mulEquiv hK (by omega) (spCompl12Equiv K n).symm
    N₁ hN₁2
  rw [eq_bot_iff]
  intro x hx
  have hxS := hNS x hx
  have hmem : (⟨x, hxS⟩ : spCompl12 K n) ∈ N₁ := ⟨x, hx, rfl⟩
  rw [hbot] at hmem
  have h1 := congrArg Subtype.val ((Subgroup.mem_bot).1 hmem)
  exact (Subgroup.mem_bot).2 (Subtype.ext h1)

theorem perfectCore_centralizer_spRep_a2 [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ Q M S : Subgroup (StatedSp (n + 3) K), IsPGroup 2 Q ∧
      M ≤ normalizer (Q : Set (StatedSp (n + 3) K)) ∧ Disjoint Q M ∧
      perfectCore (centralizer ({spRep n .a2} : Set (StatedSp (n + 3) K))) = Q ⊔ M ∧
      (∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      spRep n .a2 ∈ perfectCore (centralizer ({spRep n .a2} : Set (StatedSp (n + 3) K))) ∧
      longRootSp2 K (n + 3) 0 ≤ S ∧ S ≤ M ∧ S = perfectCore S ∧
      Nonempty (S ≃* StatedSp (n + 1) K) := by
  have h12 := one_ne_two_fin (n := n)
  have hML : a2Levi K n ≤ (leviHom h12 0 (one_ne_zero (α := K))).range :=
    sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero)
  refine ⟨wRadical K (1 : Fin (n + 3)) 2, a2Levi K n, spCompl12 K n, isPGroup_wRadical h12,
    hML.trans (range_leviHom_le_normalizer_wRadical h12 one_ne_zero),
    (disjoint_wRadical_range_leviHom h12 one_ne_zero).mono_right hML, ?_,
    fun N hN hN2 => eq_bot_of_normal_of_isPGroup_a2Levi hK N hN2,
    spRep_mem_perfectCore_centralizer hK n .a2, longRootSp2_le_spCompl12 n, le_sup_right,
    (CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_spCompl12 n hK)).symm,
    ⟨(spCompl12Equiv K n).symm⟩⟩
  rw [spRep_a2_eq]
  exact (perfectCore_centralizer_a2 hK).1

end A2Planes

end CFSG.SeitzReduction.SymplecticPilot
