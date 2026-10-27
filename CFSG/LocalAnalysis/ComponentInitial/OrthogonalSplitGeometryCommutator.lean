module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPairs

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix
open scoped commutatorElement

variable {r : ℕ} {K : Type*} [Field K]

theorem coordIdx_ne_of_ne {a d : Fin r ⊕ Fin r} (h1 : a ≠ d) (h2 : a ≠ d.swap) :
    coordIdx a ≠ coordIdx d := by
  rcases a with i | i <;> rcases d with j | j <;> simp_all

theorem swap_ne_of_ne_swap {a b : Fin r ⊕ Fin r} (h : a ≠ b.swap) : a.swap ≠ b :=
  fun h' => h (by rw [← h', Sum.swap_swap])

theorem swap_ne_swap_of_ne {a b : Fin r ⊕ Fin r} (h : a ≠ b) : a.swap ≠ b.swap :=
  fun h' => h (by simpa using congrArg Sum.swap h')

section Products

variable {a b c d : Fin r ⊕ Fin r}

theorem rpMat_mul_rpMat_eq_zero (h1 : b ≠ c) (h2 : b ≠ d.swap) (h3 : a ≠ d) (h4 : a ≠ c.swap) :
    rpMat K a b * rpMat K c d = 0 := by
  rw [rpMat, rpMat, sub_mul, mul_sub, mul_sub, single_mul_single_of_ne _ _ _ _ h1,
    single_mul_single_of_ne _ _ _ _ h2, single_mul_single_of_ne _ _ _ _ (swap_ne_of_ne_swap h4),
    single_mul_single_of_ne _ _ _ _ (swap_ne_swap_of_ne h3), sub_zero, sub_self]

theorem rpMat_mul_self_eq_zero (h : coordIdx a ≠ coordIdx b) : rpMat K a b * rpMat K a b = 0 :=
  rpMat_mul_rpMat_eq_zero (ne_of_coordIdx_ne (Ne.symm h)) (swap_ne_self b).symm
    (ne_of_coordIdx_ne h) (swap_ne_self a).symm

theorem rpMat_mul_rpMat_chain (hab : coordIdx a ≠ coordIdx b) (hbd : coordIdx b ≠ coordIdx d)
    (had : a ≠ d) : rpMat K a b * rpMat K b d = single a d 1 := by
  rw [rpMat, rpMat, sub_mul, mul_sub, mul_sub, single_mul_single_same, mul_one,
    single_mul_single_of_ne _ _ _ _ (ne_swap_of_coordIdx_ne hbd),
    single_mul_single_of_ne _ _ _ _ (swap_ne_of_ne_swap (ne_swap_of_coordIdx_ne hab)),
    single_mul_single_of_ne _ _ _ _ (swap_ne_swap_of_ne had), sub_zero, sub_zero, sub_zero]

theorem rpMat_mul_rpMat_chain_rev (hab : coordIdx a ≠ coordIdx b)
    (hbd : coordIdx b ≠ coordIdx d) (had : a ≠ d) :
    rpMat K b d * rpMat K a b = single d.swap a.swap 1 := by
  rw [rpMat, rpMat, sub_mul, mul_sub, mul_sub, single_mul_single_of_ne _ _ _ _ (Ne.symm had),
    single_mul_single_of_ne _ _ _ _ (ne_swap_of_coordIdx_ne (Ne.symm hbd)),
    single_mul_single_of_ne _ _ _ _ (swap_ne_of_ne_swap (ne_swap_of_coordIdx_ne (Ne.symm hab))),
    single_mul_single_same, mul_one, sub_zero, zero_sub, zero_sub, neg_neg]

end Products

section RingIdentities

variable {A : Type*} [Ring A] [Algebra K A]

theorem one_add_smul_mul_one_add_smul (M N : A) (s u : K) :
    (1 + s • M) * (1 + u • N) = 1 + s • M + u • N + (s * u) • (M * N) := by
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm]
  abel

theorem commute_one_add_smul {M N : A} (h : M * N = N * M) (s u : K) :
    Commute (1 + s • M) (1 + u • N) := by
  rw [Commute, SemiconjBy, one_add_smul_mul_one_add_smul, one_add_smul_mul_one_add_smul, h,
    mul_comm s u]
  abel

theorem one_add_smul_mul_eq {M N : A} (hCN : (M * N - N * M) * N = 0)
    (hCM : (M * N - N * M) * M = 0) (s u : K) :
    (1 + s • M) * (1 + u • N) =
      (1 + (s * u) • (M * N - N * M)) * (1 + u • N) * (1 + s • M) := by
  set C := M * N - N * M with hC
  have hCNM : C * (N * M) = 0 := by rw [← mul_assoc, hCN, zero_mul]
  have h1 : C * ((1 + u • N) * (1 + s • M)) = C := by
    rw [one_add_smul_mul_one_add_smul, mul_add, mul_add, mul_add, mul_one, mul_smul_comm,
      mul_smul_comm, mul_smul_comm, hCN, hCM, hCNM, smul_zero, smul_zero, smul_zero, add_zero,
      add_zero, add_zero]
  have hR : (1 + (s * u) • C) * (1 + u • N) * (1 + s • M) =
      1 + u • N + s • M + (u * s) • (N * M) + (s * u) • C := by
    rw [mul_assoc, add_mul, one_mul, smul_mul_assoc, h1, one_add_smul_mul_one_add_smul]
  rw [hR, one_add_smul_mul_one_add_smul, hC, smul_sub, mul_comm u s]
  abel

end RingIdentities

section Commutation

variable {a b c d : Fin r ⊕ Fin r}

theorem rpElt_mul (h : coordIdx a ≠ coordIdx b) (s t : K) :
    rpElt a b s * rpElt a b t = rpElt a b (s + t) := by
  apply autMat_injective
  rw [map_mul, autMat_rpElt h, autMat_rpElt h, autMat_rpElt h, one_add_smul_mul_one_add_smul,
    rpMat_mul_self_eq_zero h, smul_zero, add_zero, add_smul]
  abel

theorem rpElt_inv (h : coordIdx a ≠ coordIdx b) (t : K) : (rpElt a b t)⁻¹ = rpElt a b (-t) := by
  rw [inv_eq_iff_mul_eq_one, rpElt_mul h, add_neg_cancel]
  apply autMat_injective
  rw [autMat_rpElt h, zero_smul, add_zero, map_one]

theorem commute_rpElt (hab : coordIdx a ≠ coordIdx b) (hcd : coordIdx c ≠ coordIdx d)
    (h : rpMat K a b * rpMat K c d = rpMat K c d * rpMat K a b) (t u : K) :
    Commute (rpElt a b t) (rpElt c d u) := by
  change rpElt a b t * rpElt c d u = rpElt c d u * rpElt a b t
  apply autMat_injective
  rw [map_mul, map_mul, autMat_rpElt hab, autMat_rpElt hcd]
  exact (commute_one_add_smul h t u).eq

theorem commute_rpElt_chain_swap (hab : coordIdx a ≠ coordIdx b) (t u : K) :
    Commute (rpElt a b t) (rpElt b a.swap u) := by
  have hba : coordIdx b ≠ coordIdx a.swap := by rw [coordIdx_swap]; exact Ne.symm hab
  refine commute_rpElt hab hba ?_ t u
  rw [rpMat_mul_rpMat_chain hab hba (swap_ne_self a).symm,
    rpMat_mul_rpMat_chain_rev hab hba (swap_ne_self a).symm, Sum.swap_swap]

theorem commutatorElement_rpElt_chain (hab : coordIdx a ≠ coordIdx b)
    (hbd : coordIdx b ≠ coordIdx d) (had : a ≠ d) (had' : a ≠ d.swap) (t u : K) :
    ⁅rpElt a b t, rpElt b d u⁆ = rpElt a d (t * u) := by
  have hadI : coordIdx a ≠ coordIdx d := coordIdx_ne_of_ne had had'
  have hC : rpMat K a b * rpMat K b d - rpMat K b d * rpMat K a b = rpMat K a d := by
    rw [rpMat_mul_rpMat_chain hab hbd had, rpMat_mul_rpMat_chain_rev hab hbd had, rpMat]
  have hCN : rpMat K a d * rpMat K b d = 0 :=
    rpMat_mul_rpMat_eq_zero (ne_of_coordIdx_ne (Ne.symm hbd)) (swap_ne_self d).symm had
      (ne_swap_of_coordIdx_ne hab)
  have hCM : rpMat K a d * rpMat K a b = 0 :=
    rpMat_mul_rpMat_eq_zero (Ne.symm had) (ne_swap_of_coordIdx_ne (Ne.symm hbd))
      (ne_of_coordIdx_ne hab) (swap_ne_self a).symm
  rw [commutatorElement_eq_iff]
  apply autMat_injective
  rw [map_mul, map_mul, map_mul, autMat_rpElt hab, autMat_rpElt hbd, autMat_rpElt hadI, ← hC]
  exact one_add_smul_mul_eq (by rw [hC]; exact hCN) (by rw [hC]; exact hCM) t u

end Commutation

section Weights

theorem coordWt_sub_dotProduct_coordWt_sub (a b c d : Fin r ⊕ Fin r) :
    (coordWt a - coordWt b) ⬝ᵥ (coordWt c - coordWt d) =
      ((if a = c then 1 else if a = c.swap then -1 else 0) -
        (if a = d then 1 else if a = d.swap then -1 else 0)) -
      ((if b = c then 1 else if b = c.swap then -1 else 0) -
        (if b = d then 1 else if b = d.swap then -1 else 0)) := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct,
    coordWt_dotProduct, coordWt_dotProduct]

theorem add_notMem_roots_of_dotProduct_ne {α β : Fin r → ℤ} (hα : α ∈ roots r)
    (hβ : β ∈ roots r) (h : α ⬝ᵥ β ≠ -1) : α + β ∉ roots r :=
  fun hs => h (dotProduct_eq_neg_one_of_add_mem_roots hα hβ hs)

end Weights

section Dichotomy

variable {a b c d : Fin r ⊕ Fin r}

theorem rpElt_chain_dichotomy (hab : coordIdx a ≠ coordIdx b) (hbd : coordIdx b ≠ coordIdx d)
    (had : a ≠ d) :
    (coordWt a - coordWt b + (coordWt b - coordWt d) ∉ roots r ∧
      ∀ t u : K, Commute (rpElt a b t) (rpElt b d u)) ∨
    (coordIdx a ≠ coordIdx d ∧
      ∀ t u : K, ⁅rpElt a b t, rpElt b d u⁆ = rpElt a d (t * u)) := by
  by_cases had' : a = d.swap
  · left
    have hd : d = a.swap := by rw [had', Sum.swap_swap]
    subst hd
    refine ⟨add_notMem_roots_of_dotProduct_ne (coordWt_sub_mem_roots hab)
      (coordWt_sub_mem_roots (by rw [coordIdx_swap]; exact Ne.symm hab)) ?_,
      commute_rpElt_chain_swap hab⟩
    rw [coordWt_sub_dotProduct_coordWt_sub]
    simp [ne_of_coordIdx_ne hab, ne_swap_of_coordIdx_ne hab, ne_of_coordIdx_ne (Ne.symm hab),
      ne_swap_of_coordIdx_ne (Ne.symm hab), (swap_ne_self a).symm]
  · exact Or.inr ⟨coordIdx_ne_of_ne had had',
      fun t u => commutatorElement_rpElt_chain hab hbd had had' t u⟩

theorem rpElt_commute_or_commutator (hab : coordIdx a ≠ coordIdx b)
    (hcd : coordIdx c ≠ coordIdx d) (hne : coordWt a - coordWt b ≠ -(coordWt c - coordWt d)) :
    (coordWt a - coordWt b + (coordWt c - coordWt d) ∉ roots r ∧
      ∀ t u : K, Commute (rpElt a b t) (rpElt c d u)) ∨
    ∃ a' d' : Fin r ⊕ Fin r, coordIdx a' ≠ coordIdx d' ∧
      coordWt a' - coordWt d' = coordWt a - coordWt b + (coordWt c - coordWt d) ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        ∀ t u : K, ⁅rpElt a b t, rpElt c d u⁆ = rpElt a' d' ((ε : K) * t * u) := by
  have hdc : coordIdx d.swap ≠ coordIdx c.swap := by
    rw [coordIdx_swap, coordIdx_swap]; exact Ne.symm hcd
  have hrev : ∀ u : K, rpElt c d u = rpElt d.swap c.swap (-u) := fun u => by
    rw [rpElt_swap_swap hcd, neg_neg]
  by_cases h1 : b = c
  ·
    subst c
    have had : a ≠ d := by
      rintro rfl
      exact hne (by abel)
    rcases rpElt_chain_dichotomy (K := K) hab hcd had with h | ⟨had', h⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, d, had', by abel, 1, Or.inl rfl, fun t u => ?_⟩
      rw [h, Int.cast_one, one_mul]
  by_cases h2 : b = d.swap
  ·
    have hd : d.swap = b := h2.symm
    have hbc : coordIdx b ≠ coordIdx c.swap := by rw [← hd]; exact hdc
    have hw : coordWt c - coordWt d = coordWt b - coordWt c.swap := by
      rw [← hd, coordWt_swap, coordWt_swap]; abel
    have hac : a ≠ c.swap := by
      intro h
      exact hne (by rw [hw, ← h]; abel)
    rcases rpElt_chain_dichotomy (K := K) hab hbc hac with ⟨hn, hc⟩ | ⟨had', h⟩
    · refine Or.inl ⟨by rwa [hw], fun t u => ?_⟩
      rw [hrev, hd]
      exact hc t (-u)
    · refine Or.inr ⟨a, c.swap, had', by rw [hw]; abel, -1, Or.inr rfl, fun t u => ?_⟩
      rw [hrev, hd, h, Int.cast_neg, Int.cast_one]
      congr 1
      ring
  by_cases h3 : a = d
  ·
    subst d
    have hca : c ≠ b := by
      rintro rfl
      exact hne (by abel)
    rcases rpElt_chain_dichotomy (K := K) hcd hab hca with ⟨hn, hc⟩ | ⟨hcb, h⟩
    · refine Or.inl ⟨?_, fun t u => (hc u t).symm⟩
      rw [add_comm]
      exact hn
    · refine Or.inr ⟨c, b, hcb, by abel, -1, Or.inr rfl, fun t u => ?_⟩
      rw [← commutatorElement_inv, h, rpElt_inv hcb, Int.cast_neg, Int.cast_one]
      congr 1
      ring
  by_cases h4 : a = c.swap
  ·
    have hc : c.swap = a := h4.symm
    have hda : coordIdx d.swap ≠ coordIdx a := by rw [← hc]; exact hdc
    have hw : coordWt c - coordWt d = coordWt d.swap - coordWt a := by
      rw [← hc, coordWt_swap, coordWt_swap]; abel
    have hdb : d.swap ≠ b := by
      intro h
      exact hne (by rw [hw, h]; abel)
    rcases rpElt_chain_dichotomy (K := K) hda hab hdb with ⟨hn, hcm⟩ | ⟨hdb', h⟩
    · refine Or.inl ⟨?_, fun t u => ?_⟩
      · rw [hw, add_comm]
        exact hn
      · rw [hrev, hc]
        exact (hcm (-u) t).symm
    · refine Or.inr ⟨d.swap, b, hdb', by rw [hw]; abel, 1, Or.inl rfl, fun t u => ?_⟩
      rw [hrev, hc, ← commutatorElement_inv, h, rpElt_inv hdb', Int.cast_one]
      congr 1
      ring
  ·
    refine Or.inl ⟨add_notMem_roots_of_dotProduct_ne (coordWt_sub_mem_roots hab)
      (coordWt_sub_mem_roots hcd) ?_, fun t u => commute_rpElt hab hcd ?_ t u⟩
    · rw [coordWt_sub_dotProduct_coordWt_sub]
      rw [ite_eq_right h1, ite_eq_right h3, ite_eq_right h4, ite_eq_right h2]
      split_ifs <;> norm_num
    · rw [rpMat_mul_rpMat_eq_zero h1 h2 h3 h4,
        rpMat_mul_rpMat_eq_zero (Ne.symm h3) (fun h => h2 (by rw [h, Sum.swap_swap]))
          (Ne.symm h1) (fun h => h4 (by rw [h, Sum.swap_swap]))]

end Dichotomy

theorem orthogonal_geometry_split_root_commutators {K : Type*} [Field K] {r : ℕ} :
    (∀ α ∈ roots r, Function.Injective (rootElt r K α) ∧
      (∀ s t, rootElt r K α (s + t) = rootElt r K α s * rootElt r K α t) ∧
      Set.range (rootElt r K α) = (rootSubgroup r K α : Set _)) ∧
    (∀ α ∈ roots r, ∀ β ∈ roots r, α ≠ -β → α + β ∉ roots r →
      ∀ t u : K, Commute (rootElt r K α t) (rootElt r K β u)) ∧
    (∀ α ∈ roots r, ∀ β ∈ roots r, α + β ∈ roots r →
      ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ∀ t u : K,
        ⁅rootElt r K α t, rootElt r K β u⁆ = rootElt r K (α + β) ((c : K) * t * u)) := by
  refine ⟨fun α hα => ⟨?_, fun s t => (rootElt_mul α s t).symm, rfl⟩, ?_, ?_⟩
  ·
    obtain ⟨a, b, hab, -, h, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
    intro s t hst
    have he := congrArg (fun g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) =>
      g (Pi.single b 1) a) hst
    simpa [h, rpElt_apply hab, Pi.single_apply, ne_of_coordIdx_ne hab, ne_swap_of_coordIdx_ne hab,
      swap_ne_of_ne_swap (ne_swap_of_coordIdx_ne hab)] using he
  · intro α hα β hβ hne hsum t u
    obtain ⟨a, b, hab, rfl, h, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
    obtain ⟨c, d, hcd, rfl, h', -⟩ := exists_rootElt_eq_rpElt (K := K) hβ
    rw [h, h']
    rcases rpElt_commute_or_commutator (K := K) hab hcd hne with ⟨-, hc⟩ | ⟨a', d', had, hw, -⟩
    · exact hc t u
    · exact absurd (hw ▸ coordWt_sub_mem_roots had) hsum
  · intro α hα β hβ hsum
    have hne : α ≠ -β := by
      rintro rfl
      exact zero_notMem_roots (by rwa [neg_add_cancel] at hsum)
    obtain ⟨a, b, hab, rfl, h, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
    obtain ⟨c, d, hcd, rfl, h', -⟩ := exists_rootElt_eq_rpElt (K := K) hβ
    rcases rpElt_commute_or_commutator (K := K) hab hcd hne with
      ⟨hn, -⟩ | ⟨a', d', had, hw, ε, hε, hc⟩
    · exact absurd hsum hn
    obtain ⟨ε', hε', hr, -⟩ := exists_sign_rootElt_eq_rpElt (K := K) had
    refine ⟨ε' * ε, by rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> simp,
      fun t u => ?_⟩
    have hsq : (ε' : K) * ε' = 1 := by rcases hε' with rfl | rfl <;> simp
    rw [h, h', hc, ← hw, hr]
    congr 1
    push_cast
    linear_combination (-(ε : K) * t * u) * hsq

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
