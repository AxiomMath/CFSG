module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthLayer
public import CFSG.ClassicalInvolution.ModelFacts.E8D8AdjOrth

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD.Gaps (ModelAdj adj_data orth_or_twin)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem not_commutes_self_of_isFundamental {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) : ¬ Commutes L L := by
  obtain ⟨F, rfl, -⟩ := h
  exact CFSG.ClassicalInvolution.RouteD.NonClassical.not_commutes_self_range F

omit [FiniteDimensional K V] in
theorem polar_negSpace_eq_zero_of_commutes_adj (hodd : Odd (Nat.card K))
    {c l M : Subgroup (V ≃ₗ[K] V)} {ic il iM : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (hl : IsFundamental Q l il) (hM : IsFundamental Q M iM) (hcl : ic * il = il * ic)
    (hne : c ≠ l) (hnc : ¬ Commutes c l) (hMc : Commutes M c) (hMl : Commutes M l) :
    (∀ x ∈ negSpace ic, ∀ y ∈ negSpace iM, polar Q x y = 0) ∧
      ∀ x ∈ negSpace il, ∀ y ∈ negSpace iM, polar Q x y = 0 := by
  have hsymm : ∀ {A B : Subgroup (V ≃ₗ[K] V)}, Commutes A B → Commutes B A :=
    fun h a ha b hb => (h b hb a ha).symm
  have hlc : il * ic = ic * il := hcl.symm
  have hlM : l ≠ M := fun h => not_commutes_self_of_isFundamental hl (h ▸ hMl)
  have hcM : c ≠ M := fun h => not_commutes_self_of_isFundamental hc (h ▸ hMc)
  have hlc' : l ≠ c := hne.symm
  constructor
  · rcases orth_or_twin hodd hc hM (hsymm hMc) with h | h
    · exact h
    · exfalso
      subst h
      have e1 := IsFundamental.commute_iff hodd hl hM hlc hlM
      have e2 := IsFundamental.commute_iff hodd hl hc hlc hlc'
      have hlc'' : Commutes l c := e2.mpr (e1.mp (hsymm hMl))
      exact hnc (hsymm hlc'')
  · rcases orth_or_twin hodd hl hM (hsymm hMl) with h | h
    · exact h
    · exfalso
      subst h
      have e1 := IsFundamental.commute_iff hodd hc hM hcl hcM
      have e2 := IsFundamental.commute_iff hodd hc hl hcl hne
      have hcl'' : Commutes c l := e2.mpr (e1.mp (hsymm hMc))
      exact hnc hcl''

@[expose] def planeOf (i₁ i₂ : V ≃ₗ[K] V) : Fin 3 → Submodule K V
  | 0 => negSpace i₁ ⊓ posSpace i₂
  | 1 => negSpace i₁ ⊓ negSpace i₂
  | 2 => posSpace i₁ ⊓ negSpace i₂

@[expose] def planeSide : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1

omit [Finite K] [FiniteDimensional K V] in
theorem planeOf_le_negSpace (ι : Fin 2 → V ≃ₗ[K] V) (k : Fin 3) :
    planeOf (ι 0) (ι 1) k ≤ negSpace (ι (planeSide k)) := by
  fin_cases k
  · exact inf_le_left
  · exact inf_le_left
  · exact inf_le_right

section Pair

variable {i₁ i₂ : V ≃ₗ[K] V}

omit [Finite K] [FiniteDimensional K V] in
theorem planeOf_finrank (hP : PairDecomposition Q i₁ i₂) (k : Fin 3) :
    Module.finrank K ↥(planeOf i₁ i₂ k) = 2 := by
  fin_cases k
  · exact hP.finrank_U₁
  · exact hP.finrank_U₂
  · exact hP.finrank_U₃

omit [Finite K] [FiniteDimensional K V] in
theorem planeOf_nondeg (hP : PairDecomposition Q i₁ i₂) (k : Fin 3) :
    PolarNondegOn Q (planeOf i₁ i₂ k) := by
  fin_cases k
  · exact hP.nondeg₁
  · exact hP.nondeg₂
  · exact hP.nondeg₃

omit [Finite K] [FiniteDimensional K V] in
theorem planeOf_orth (hP : PairDecomposition Q i₁ i₂) (k k' : Fin 3) (hk : k ≠ k') :
    ∀ x ∈ planeOf i₁ i₂ k, ∀ y ∈ planeOf i₁ i₂ k', polar Q x y = 0 := by
  have s12 := hP.orth₁₂
  have s13 := hP.orth₁₃
  have s23 := hP.orth₂₃
  fin_cases k <;> fin_cases k'
  · exact absurd rfl hk
  · exact s12
  · exact s13
  · intro x hx y hy
    rw [polar_comm]
    exact s12 y hy x hx
  · exact absurd rfl hk
  · exact s23
  · intro x hx y hy
    rw [polar_comm]
    exact s13 y hy x hx
  · intro x hx y hy
    rw [polar_comm]
    exact s23 y hy x hx
  · exact absurd rfl hk

end Pair

theorem false_of_three_adjacent_pairs (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    (hlt : Module.finrank K V < 18) (L : Fin 3 → Fin 2 → Subgroup (V ≃ₗ[K] V))
    (ι : Fin 3 → Fin 2 → V ≃ₗ[K] V) (hfund : ∀ i j, IsFundamental Q (L i j) (ι i j))
    (hadj : ∀ i, ModelAdj (scalars K V) (L i 0) (L i 1))
    (hcomm : ∀ i i', i ≠ i' → ∀ j j', Commutes (L i j) (L i' j')) : False := by
  have hdata := fun i => adj_data hodd hdim (hfund i 0) (hfund i 1) (hadj i)
  have hpd : ∀ i, PairDecomposition Q (ι i 0) (ι i 1) := fun i =>
    (lemma_6_10 hodd (hfund i 0) (hfund i 1) (hdata i).1 (hdata i).2.1 (hdata i).2.2).1
  have horth : ∀ i i', i ≠ i' → ∀ j j', ∀ x ∈ negSpace (ι i j), ∀ y ∈ negSpace (ι i' j'),
      polar Q x y = 0 := by
    intro i i' hii' j j' x hx y hy
    have h := polar_negSpace_eq_zero_of_commutes_adj hodd (hfund i 0) (hfund i 1)
      (hfund i' j') (hdata i).1 (hadj i).1 (hadj i).2.1
      (hcomm i' i (Ne.symm hii') j' 0) (hcomm i' i (Ne.symm hii') j' 1)
    fin_cases j
    · exact h.1 x hx y hy
    · exact h.2 x hx y hy
  let U : Fin 3 × Fin 3 → Submodule K V := fun a => planeOf (ι a.1 0) (ι a.1 1) a.2
  have hsum := sum_finrank_le_of_orth (Q := Q) U (fun a => planeOf_nondeg (hpd a.1) a.2) (by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne x hx y hy
    by_cases hii : i = i'
    · subst hii
      have hkk : k ≠ k' := fun h => hne (by rw [h])
      exact planeOf_orth (hpd i) k k' hkk x hx y hy
    · exact horth i i' hii _ _ x (planeOf_le_negSpace (ι i) k hx) y
        (planeOf_le_negSpace (ι i') k' hy))
  have h18 : ∑ a : Fin 3 × Fin 3, Module.finrank K ↥(U a) = 18 := by
    rw [Finset.sum_congr rfl fun a _ => planeOf_finrank (hpd a.1) a.2, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  omega

end CFSG.ClassicalInvolution.ModelFacts.E8D8
