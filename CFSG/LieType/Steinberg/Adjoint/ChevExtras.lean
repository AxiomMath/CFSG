module

public import CFSG.LieType.Steinberg.Adjoint.Datum
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
open scoped commutatorElement

variable {τ : Tag}

@[expose] def pairs₀ : List (ℕ × ℕ) := [(1, 1), (1, 2), (2, 1)]

theorem mem_expPairs_iff (hτ : NoG2 τ) {Φ : CFSG.LieType.Steinberg.RootSystem (Fin τ.rank)}
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) (p : ℕ × ℕ) :
    p ∈ expPairs Φ α β ↔ p ∈ pairs₀ ∧ IsRoot τ (p.1 • α + p.2 • β) := by
  change (0 < p.1 ∧ 0 < p.2 ∧ p.1 • α + p.2 • β ∈ Φ.roots) ↔ _
  rw [hΦ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h3⟩
    obtain ⟨a, b⟩ := p
    rcases exponent_pair_cases hτ hα hβ hne hne' h1 h2 h3 with h | h | h
    · obtain ⟨rfl, rfl⟩ := h
      simp [pairs₀]
    · obtain ⟨rfl, rfl, -⟩ := h
      simp [pairs₀]
    · obtain ⟨rfl, rfl, -⟩ := h
      simp [pairs₀]
  · rintro ⟨hp, h3⟩
    simp only [pairs₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num, h3⟩

theorem prod_map_filter_of_eq_one {X G : Type*} [Monoid G] (L : List X) (q : X → Bool)
    (f : X → G) (h : ∀ x ∈ L, q x = false → f x = 1) :
    ((L.filter q).map f).prod = (L.map f).prod := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    by_cases ha : q a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, ih']
    · rw [List.filter_cons_of_neg ha, List.map_cons, List.prod_cons,
        h a (by simp) (by simpa using ha), one_mul, ih']

theorem prod_map_commOrder_list (hτ : NoG2 τ) {Φ : CFSG.LieType.Steinberg.RootSystem (Fin τ.rank)}
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) (O : CommOrder Φ) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) {G : Type*} [Monoid G]
    (f : ℕ × ℕ → G) (hcomm : ∀ p ∈ O.list α β, ∀ q ∈ O.list α β, Commute (f p) (f q))
    (hone : ∀ p : ℕ × ℕ, ¬IsRoot τ (p.1 • α + p.2 • β) → f p = 1) :
    ((O.list α β).map f).prod = f (1, 1) * f (1, 2) * f (2, 1) := by
  classical
  have hαΦ : α ∈ Φ.roots := by rw [hΦ]; exact hα
  have hβΦ : β ∈ Φ.roots := by rw [hΦ]; exact hβ
  have hsum : α + β ≠ 0 := fun h => hne' (eq_neg_of_add_eq_zero_left h)
  have hperm : (O.list α β).Perm
      (pairs₀.filter fun p => decide (IsRoot τ (p.1 • α + p.2 • β))) := by
    refine (List.perm_ext_iff_of_nodup (O.nodup α β)
      ((by decide : pairs₀.Nodup).filter _)).2 fun p => ?_
    rw [O.mem_iff α hαΦ β hβΦ hsum, mem_expPairs_iff hτ hΦ hα hβ hne hne']
    simp only [List.mem_filter, decide_eq_true_eq]
  rw [(hperm.map f).prod_eq' (List.pairwise_map.2 (List.pairwise_of_forall_mem_list hcomm)),
    prod_map_filter_of_eq_one _ _ _ fun p _ hp => hone p (by simpa using hp)]
  simp only [pairs₀, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc]

section Coeff

variable (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid)

open RootOperatorFamily'

theorem natAbs_coeff11 {α β : Root τ} (hne' : β.1 ≠ -α.1) (h : IsRoot τ (α.1 + β.1)) :
    (coeff11 F hD α β).natAbs = 1 ∨ (coeff11 F hD α β).natAbs = 2 := by
  rw [coeff11, bracketCoeff_natAbs F hD hne' h]
  by_cases hr : IsRoot τ (β.1 - α.1)
  · exact Or.inr (stringNorm_of_isRoot hr)
  · exact Or.inl (stringNorm_of_not_isRoot hr)

theorem natAbs_div_two_of_natAbs_eq_two {m : ℤ} (h : m.natAbs = 2) : (m / 2).natAbs = 1 := by
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl <;> decide

theorem not_isRoot_sub_of_iform (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ}
    (h : iform α α + iform β β = 6) (hαβ : iform α β = -2) : ¬IsRoot τ (β - α) := fun hr => by
  have h2 := iform_self_cases hτ hr
  simp only [iform_sub_left, iform_sub_right] at h2
  rw [iform_comm β α] at h2
  omega

theorem natAbs_coeff12 (hτ : NoG2 τ) {α β : Root τ} (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1)
    (h : IsRoot τ (α.1 + 2 • β.1)) : (coeff12 F hD α β).natAbs = 1 := by
  have h1 : IsRoot τ (α.1 + β.1) := isRoot_add_of_isRoot_add_two_smul β.2 α.2 hne hne' h
  have h' : IsRoot τ (1 • α.1 + 2 • β.1) := by rwa [one_smul]
  obtain ⟨hαα, hββ, hαβ⟩ : iform α.1 α.1 = 4 ∧ iform β.1 β.1 = 2 ∧ iform α.1 β.1 = -2 := by
    rcases exponent_pair_cases hτ α.2 β.2 hne hne' le_rfl (by norm_num) h' with h | h | h
    · omega
    · exact h.2.2
    · omega
  have hn : ¬IsRoot τ (β.1 - α.1) := not_isRoot_sub_of_iform hτ (by omega) hαβ
  have hN1 : (bracketCoeff F hD α β).natAbs = 1 := by
    rw [bracketCoeff_natAbs F hD (fun h' => hne' (by rw [h', neg_neg])) h1,
      stringNorm_of_not_isRoot hn]
  have hsum : β.1 + (α.1 + β.1) = α.1 + 2 • β.1 := by
    rw [two_nsmul]
    abel
  have hN2 : (bracketCoeff F hD β ⟨α.1 + β.1, h1⟩).natAbs = 2 := by
    rw [bracketCoeff_natAbs F hD (γ := ⟨α.1 + β.1, h1⟩)
        (fun h' => h.ne_zero (by rw [← hsum, show α.1 + β.1 = -β.1 from h', add_neg_cancel]))
        (by rw [hsum]; exact h),
      stringNorm_of_isRoot (by rw [add_sub_cancel_right]; exact α.2)]
  rw [coeff12, dite_eq_left h1]
  exact natAbs_div_two_of_natAbs_eq_two (by rw [Int.natAbs_mul, hN1, hN2])

theorem natAbs_coeff21 (hτ : NoG2 τ) {α β : Root τ} (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1)
    (h : IsRoot τ (2 • α.1 + β.1)) : (coeff21 F hD α β).natAbs = 1 := by
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have h1 : IsRoot τ (α.1 + β.1) := by
    rw [add_comm]
    exact isRoot_add_of_isRoot_add_two_smul α.2 β.2 (Ne.symm hne) hβα (by rwa [add_comm])
  have h' : IsRoot τ (2 • α.1 + 1 • β.1) := by rwa [one_smul]
  obtain ⟨hαα, hββ, hαβ⟩ : iform α.1 α.1 = 2 ∧ iform β.1 β.1 = 4 ∧ iform α.1 β.1 = -2 := by
    rcases exponent_pair_cases hτ α.2 β.2 hne hne' (by norm_num) le_rfl h' with h | h | h
    · omega
    · omega
    · exact h.2.2
  have hn : ¬IsRoot τ (β.1 - α.1) := not_isRoot_sub_of_iform hτ (by omega) hαβ
  have hN1 : (bracketCoeff F hD α β).natAbs = 1 := by
    rw [bracketCoeff_natAbs F hD hβα h1, stringNorm_of_not_isRoot hn]
  have hsum : α.1 + (α.1 + β.1) = 2 • α.1 + β.1 := by
    rw [two_nsmul]
    abel
  have hN2 : (bracketCoeff F hD α ⟨α.1 + β.1, h1⟩).natAbs = 2 := by
    rw [bracketCoeff_natAbs F hD (γ := ⟨α.1 + β.1, h1⟩)
        (fun h' => h.ne_zero (by rw [← hsum, show α.1 + β.1 = -α.1 from h', add_neg_cancel]))
        (by rw [hsum]; exact h),
      stringNorm_of_isRoot (by rw [add_sub_cancel_left]; exact β.2)]
  rw [coeff21, dite_eq_left h1]
  exact natAbs_div_two_of_natAbs_eq_two (by rw [Int.natAbs_mul, hN1, hN2])

open _root_.Classical in
@[expose] def commC (α β : Fin τ.rank → ℤ) (p : ℕ × ℕ) : ℤ :=
  if h : IsRoot τ α ∧ IsRoot τ β ∧ α + β ≠ 0 then
    if p = (1, 1) then coeff11 F hD ⟨α, h.1⟩ ⟨β, h.2.1⟩
    else if p = (1, 2) then coeff12 F hD ⟨α, h.1⟩ ⟨β, h.2.1⟩
    else if p = (2, 1) then coeff21 F hD ⟨α, h.1⟩ ⟨β, h.2.1⟩
    else 1
  else 1

variable {F hD}

theorem commC_11 {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hsum : α + β ≠ 0) :
    commC F hD α β (1, 1) = coeff11 F hD ⟨α, hα⟩ ⟨β, hβ⟩ := by
  classical
  rw [commC, dite_eq_left ⟨hα, hβ, hsum⟩, ite_eq_left (rfl : ((1, 1) : ℕ × ℕ) = (1, 1))]

theorem commC_12 {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hsum : α + β ≠ 0) :
    commC F hD α β (1, 2) = coeff12 F hD ⟨α, hα⟩ ⟨β, hβ⟩ := by
  classical
  rw [commC, dite_eq_left ⟨hα, hβ, hsum⟩, ite_eq_right (by decide : ((1, 2) : ℕ × ℕ) ≠ (1, 1)),
    ite_eq_left (rfl : ((1, 2) : ℕ × ℕ) = (1, 2))]

theorem commC_21 {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hsum : α + β ≠ 0) :
    commC F hD α β (2, 1) = coeff21 F hD ⟨α, hα⟩ ⟨β, hβ⟩ := by
  classical
  rw [commC, dite_eq_left ⟨hα, hβ, hsum⟩, ite_eq_right (by decide : ((2, 1) : ℕ × ℕ) ≠ (1, 1)),
    ite_eq_right (by decide : ((2, 1) : ℕ × ℕ) ≠ (1, 2)),
    ite_eq_left (rfl : ((2, 1) : ℕ × ℕ) = (2, 1))]

theorem commC_natAbs (hτ : NoG2 τ) {Φ : CFSG.LieType.Steinberg.RootSystem (Fin τ.rank)}
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) {α β : Fin τ.rank → ℤ} (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) {p : ℕ × ℕ} (hp : p ∈ expPairs Φ α β) :
    (commC F hD α β p).natAbs ∈ ({1, 2, 3} : Set ℕ) := by
  classical
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  by_cases hsum : α + β = 0
  · rw [commC, dite_eq_right fun h => h.2.2 hsum]
    simp
  have hne' : α ≠ -β := fun h => hsum (by rw [h, neg_add_cancel])
  by_cases hne : α = β
  · exfalso
    subst hne
    obtain ⟨h1, h2, h3⟩ := hp
    rw [hΦ, ← add_nsmul] at h3
    have := eq_one_of_isRoot_nsmul (τ := τ) h3
    omega
  rw [mem_expPairs_iff hτ hΦ hα' hβ' hne hne'] at hp
  obtain ⟨hp, hr⟩ := hp
  simp only [pairs₀, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hβα : β ≠ -α := fun h => hne' (by rw [h, neg_neg])
  rcases hp with rfl | rfl | rfl
  · rw [commC_11 hα' hβ' hsum]
    rcases natAbs_coeff11 F hD (α := ⟨α, hα'⟩) (β := ⟨β, hβ'⟩) hβα
        (by simpa using hr) with h | h <;> simp [h]
  · rw [commC_12 hα' hβ' hsum, natAbs_coeff12 F hD hτ (α := ⟨α, hα'⟩) (β := ⟨β, hβ'⟩) hne hne'
      (by simpa using hr)]
    simp
  · rw [commC_21 hα' hβ' hsum, natAbs_coeff21 F hD hτ (α := ⟨α, hα'⟩) (β := ⟨β, hβ'⟩) hne hne'
      (by simpa using hr)]
    simp

end Coeff

section Formula

variable {F : RootOperatorFamily τ} {K : Type} [Field K] {D : AdjData τ} (hD : D.Valid)
include hD

theorem commute_xPar_pairs (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) {p q : ℕ × ℕ} (hp1 : 1 ≤ p.1)
    (hp2 : 1 ≤ p.2) (hq1 : 1 ≤ q.1) (hq2 : 1 ≤ q.2) (a b : K) :
    Commute (xPar F (p.1 • α + p.2 • β) a) (xPar F (q.1 • α + q.2 • β) b) := by
  by_cases hrp : IsRoot τ (p.1 • α + p.2 • β)
  · by_cases hrq : IsRoot τ (q.1 • α + q.2 • β)
    · have hlin := linIndepPair_of_ne hα hβ hne hne'
      have e : p.1 • α + p.2 • β + (q.1 • α + q.2 • β) = (p.1 + q.1) • α + (p.2 + q.2) • β := by
        rw [add_nsmul, add_nsmul]
        abel
      refine commute_xPar hD hτ hrp hrq ?_ ?_ a b
      · rw [e]
        exact nsmul_add_nsmul_ne_zero hlin (Or.inl (by omega))
      · rw [e]
        exact not_isRoot_nsmul_add_nsmul hτ hα hβ hne hne' (by omega) (by omega) (by omega)
    · rw [xPar_of_not_isRoot hrq]
      exact Commute.one_right _
  · rw [xPar_of_not_isRoot hrp]
    exact Commute.one_left _

theorem commutatorFormula_commC (hτ : NoG2 τ) (Φ : CFSG.LieType.Steinberg.RootSystem (Fin τ.rank))
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) (O : CommOrder Φ) :
    CommutatorFormula (xPar (K := K) F) O (commC F hD) := by
  intro α hα β hβ hsum c d
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  have hne' : α ≠ -β := fun h => hsum (by rw [h, neg_add_cancel])
  by_cases hne : α = β
  · subst hne
    have hnil : O.list α α = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      rw [O.mem_iff α hα α hα hsum] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      rw [hΦ, ← add_nsmul] at h3
      have := eq_one_of_isRoot_nsmul (τ := τ) h3
      omega
    rw [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute, Commute,
      SemiconjBy, ← xPar_add, ← xPar_add, add_comm]
  · rw [prod_map_commOrder_list hτ hΦ O hα' hβ' hne hne' _ ?_ ?_,
      commutator_xPar hD hτ hα' hβ' hne hne']
    · simp only [one_smul, pow_one, commC_11 hα' hβ' hsum, commC_12 hα' hβ' hsum,
        commC_21 hα' hβ' hsum]
    · intro p hp q hq
      rw [O.mem_iff α hα β hβ hsum] at hp hq
      exact commute_xPar_pairs hD hτ hα' hβ' hne hne' hp.1 hp.2.1 hq.1 hq.2.1 _ _
    · intro p hp
      exact xPar_of_not_isRoot hp _

theorem rankTwo (hτ : NoG2 τ) {Φ : CFSG.LieType.Steinberg.RootSystem (Fin τ.rank)}
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) {O : CommOrder Φ}
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (xPar (K := K) F) O C) (i : Fin τ.rank) {l : Fin τ.rank}
    (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) :
    ∃ δ ∈ Φ.roots, ∃ γ ∈ Φ.roots, δ + γ ≠ 0 ∧ ∃ j : ℕ, (j = 1 ∨ j = 2) ∧
      Pi.single i 1 = δ + j • γ ∧ IsUnit (C δ γ (1, j) : K) := by
  have hli' : l ≠ i := ne_of_cartan_eq_neg_one hil
  have hδ : IsRoot τ (Pi.single l 1 + Pi.single i 1) := isRoot_single_add_single hil
  have hγ : IsRoot τ (-Pi.single l 1) := isRoot_neg_single τ l
  have hsum : Pi.single l 1 + Pi.single i 1 + -Pi.single l 1 = (Pi.single i 1 : Fin τ.rank → ℤ) :=
    by abel
  have hsum0 : Pi.single l 1 + Pi.single i 1 + -Pi.single l 1 ≠ (0 : Fin τ.rank → ℤ) := by
    rw [hsum]
    exact (isRoot_single τ i).ne_zero
  have hne : (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single l 1 := fun h => by
    have := congrFun h i
    simp [hli'.symm] at this
  have hne' : (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) ≠ -(-Pi.single l 1) := fun h => by
    have := congrFun h i
    simp [hli'.symm] at this
  have hδΦ : Pi.single l 1 + Pi.single i 1 ∈ Φ.roots := by rw [hΦ]; exact hδ
  have hγΦ : -Pi.single l 1 ∈ Φ.roots := by rw [hΦ]; exact hγ
  refine ⟨_, hδΦ, _, hγΦ, hsum0, 1, Or.inl rfl, by rw [one_smul, hsum], ?_⟩
  have h12 : ¬IsRoot τ (Pi.single l 1 + Pi.single i 1 + 2 • -Pi.single l 1) := by
    rw [show (Pi.single l 1 + Pi.single i 1 + 2 • -Pi.single l 1 : Fin τ.rank → ℤ) =
      Pi.single i 1 - Pi.single l 1 by rw [two_nsmul]; abel]
    exact not_isRoot_single_sub_single hli'.symm
  have h21 : ¬IsRoot τ (2 • (Pi.single l 1 + Pi.single i 1) + -Pi.single l 1) := by
    rw [show (2 • (Pi.single l 1 + Pi.single i 1) + -Pi.single l 1 : Fin τ.rank → ℤ) =
      Pi.single l 1 + (2 : ℤ) • Pi.single i 1 by rw [two_nsmul, two_zsmul]; abel]
    exact not_isRoot_single_add_two hil
  have h1 := hC _ hδΦ _ hγΦ hsum0 1 1
  rw [prod_map_commOrder_list hτ hΦ O hδ hγ hne hne' _ ?_ ?_,
    commutator_xPar hD hτ hδ hγ hne hne', xPar_of_not_isRoot h12, xPar_of_not_isRoot h21,
    mul_one, mul_one] at h1
  · simp only [one_smul, one_pow, mul_one, xPar_of_not_isRoot h12, xPar_of_not_isRoot h21] at h1
    have hc := xPar_injective (by rw [hsum]; exact isRoot_single τ i) h1
    rw [← hc]
    have hN : (RootOperatorFamily'.coeff11 F hD ⟨_, hδ⟩ ⟨_, hγ⟩).natAbs = 1 := by
      rw [RootOperatorFamily'.coeff11,
        RootOperatorFamily'.bracketCoeff_natAbs F hD (β := ⟨_, hδ⟩) (γ := ⟨_, hγ⟩)
          (fun h => hne' (by rw [show -Pi.single l 1 = -(Pi.single l 1 + Pi.single i 1) from h,
            neg_neg]))
          (show IsRoot τ (Pi.single l 1 + Pi.single i 1 + -Pi.single l 1) by
            rw [hsum]; exact isRoot_single τ i)]
      refine stringNorm_of_not_isRoot fun hr => not_isRoot_single_add_two hli ?_
      rw [show (Pi.single i 1 + (2 : ℤ) • Pi.single l 1 : Fin τ.rank → ℤ) =
        -(-Pi.single l 1 - (Pi.single l 1 + Pi.single i 1)) by rw [two_zsmul]; abel]
      exact isRoot_neg_iff.2 hr
    rcases Int.natAbs_eq_iff.1 hN with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  · intro p hp q hq
    rw [O.mem_iff _ hδΦ _ hγΦ hsum0] at hp hq
    exact commute_xPar_pairs hD hτ hδ hγ hne hne' hp.1 hp.2.1 hq.1 hq.2.1 _ _
  · intro p hp
    exact xPar_of_not_isRoot hp _

variable (F K) in
theorem adjDatum_chevalleyExtras (hτ : NoG2 τ)
    (hnb : ∀ i, ∃ l, τ.cartan i l = -1 ∧ τ.cartan l i = -1)
    (O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan (adjDatum F K).isFiniteType
      (adjDatum F K).divisible))
    (C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (xPar (K := K) F) O C) :
    ChevalleyExtras (adjDatum F K) K (xPar F) C O where
  param := adjDatum_isParametrization _ (adjDatum_roots F K)
  comm := hC
  weyl i β hβ := weylElement_xPar_conj i (mem_adjDatum_roots.1 hβ)
  rankOne i := by
    obtain ⟨l, hil, -⟩ := hnb i
    obtain ⟨φ, hφ, hup, hlow⟩ := exists_sl2_hom (K := K) F hil
    exact ⟨φ, hφ, fun c => (hup c).trans (xPar_simple i c).symm,
      fun c => (hlow c).trans (xPar_neg_simple i c).symm⟩
  prodInjective f L hnd hL hsort := prodInjective f L hnd
    (fun γ hγ => ⟨mem_adjDatum_roots.1 (hL γ hγ).1, (hL γ hγ).2⟩) hsort
  rankTwo i := by
    obtain ⟨l, hil, hli⟩ := hnb i
    exact rankTwo hD hτ (adjDatum_roots F K) hC i hil hli

end Formula

end CFSG.LieType.Steinberg.Adjoint
