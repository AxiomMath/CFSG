module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Multiplicative Equiv

@[expose] def pairVec (a b : Fin 7) : Fin 7 → ZMod 2 := Pi.single a 1 + Pi.single b 1

@[expose] def pairsOf (v : Fin 7 → ZMod 2) : List (Fin 7 × Fin 7) :=
  match (List.finRange 7).filter (fun i => v i = 1) with
  | [] => []
  | p :: rest => rest.map fun q => (p, q)

theorem exists_pair : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 →
    ∃ p q r s : Fin 7, p ≠ q ∧ r ≠ s ∧ ∀ i, v i + v (swap r s (swap p q i)) = pairVec p q i := by
  decide +kernel

theorem pair_to01 : ∀ a b : Fin 7, a ≠ b →
    ∃ p q r s : Fin 7, p ≠ q ∧ r ≠ s ∧ ∀ i, pairVec a b (swap r s (swap p q i)) = pairVec 0 1 i := by
  decide +kernel

theorem pair_from01 : ∀ a b : Fin 7, a ≠ b →
    ∃ p q r s : Fin 7, p ≠ q ∧ r ≠ s ∧ ∀ i, pairVec 0 1 (swap r s (swap p q i)) = pairVec a b i := by
  decide +kernel

theorem sum_pairsOf : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    ((pairsOf v).map fun pr => pairVec pr.1 pr.2).sum = v := by
  decide +kernel

theorem pairVec_self (a : Fin 7) : pairVec a a = 0 := by
  funext i
  simp [pairVec, ← two_mul, show (2 : ZMod 2) = 0 from rfl]

theorem permAct_pairVec_swap (p q r s : Fin 7) (v : Fin 7 → ZMod 2) :
    toAdd (G6.permAct 7 (swap p q * swap r s) (ofAdd v)) = fun i => v (swap r s (swap p q i)) := by
  funext i
  show v ((swap p q * swap r s)⁻¹ i) = v (swap r s (swap p q i))
  rw [mul_inv_rev, swap_inv, swap_inv]
  rfl

theorem double_swap_mem_alt (p q r s : Fin 7) (hpq : p ≠ q) (hrs : r ≠ s) :
    swap p q * swap r s ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq,
    Equiv.Perm.sign_swap hrs]
  decide

theorem coreMod7_irreducible (U : Subgroup (G6.PermMod 7)) (hU : U ≤ G6.coreMod 7)
    (hinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ U, G6.permAct 7 σ u ∈ U) :
    U = ⊥ ∨ U = G6.coreMod 7 := by
  by_cases hU1 : U = ⊥
  · exact Or.inl hU1
  right
  obtain ⟨⟨u, hu⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have hev : ∑ i, toAdd u i = 0 := G6.mem_coreMod.1 (hU hu)
  have hv0 : toAdd u ≠ 0 := fun h => hu1 (by rw [← ofAdd_toAdd u, h]; rfl)
  obtain ⟨p, q, r, s, hpq, hrs, hpair⟩ := exists_pair (toAdd u) hev hv0
  have h1 : (ofAdd (pairVec p q) : G6.PermMod 7) ∈ U := by
    have hτ := hinv _ (double_swap_mem_alt p q r s hpq hrs) u hu
    have hmul := U.mul_mem hu hτ
    have e : u * G6.permAct 7 (swap p q * swap r s) u = ofAdd (pairVec p q) := by
      apply toAdd.injective
      funext i
      show toAdd u i + toAdd (G6.permAct 7 (swap p q * swap r s) u) i = pairVec p q i
      have := permAct_pairVec_swap p q r s (toAdd u)
      rw [ofAdd_toAdd] at this
      rw [this]
      exact hpair i
    rwa [e] at hmul
  have h01 : (ofAdd (pairVec 0 1) : G6.PermMod 7) ∈ U := by
    obtain ⟨p', q', r', s', hpq', hrs', hmap⟩ := pair_to01 p q hpq
    have hτ := hinv _ (double_swap_mem_alt p' q' r' s' hpq' hrs') _ h1
    have e : G6.permAct 7 (swap p' q' * swap r' s') (ofAdd (pairVec p q)) = ofAdd (pairVec 0 1) := by
      apply toAdd.injective
      rw [permAct_pairVec_swap p' q' r' s']
      funext i
      exact hmap i
    rwa [e] at hτ
  have hall : ∀ a b : Fin 7, (ofAdd (pairVec a b) : G6.PermMod 7) ∈ U := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [pairVec_self]
      exact U.one_mem
    · obtain ⟨p', q', r', s', hpq', hrs', hmap⟩ := pair_from01 a b hab
      have hτ := hinv _ (double_swap_mem_alt p' q' r' s' hpq' hrs') _ h01
      have e : G6.permAct 7 (swap p' q' * swap r' s') (ofAdd (pairVec 0 1)) =
          ofAdd (pairVec a b) := by
        apply toAdd.injective
        rw [permAct_pairVec_swap p' q' r' s']
        funext i
        exact hmap i
      rwa [e] at hτ
  apply le_antisymm hU
  intro z hz
  have hzev : ∑ i, toAdd z i = 0 := G6.mem_coreMod.1 hz
  have hsum := sum_pairsOf (toAdd z) hzev
  have hlist : ∀ l : List (Fin 7 × Fin 7),
      (ofAdd ((l.map fun pr => pairVec pr.1 pr.2).sum) : G6.PermMod 7) ∈ U := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact U.one_mem
    | cons pr l ih =>
      simp only [List.map_cons, List.sum_cons]
      have : (ofAdd (pairVec pr.1 pr.2 + (l.map fun pr => pairVec pr.1 pr.2).sum) :
          G6.PermMod 7) =
          ofAdd (pairVec pr.1 pr.2) * ofAdd ((l.map fun pr => pairVec pr.1 pr.2).sum) := rfl
      rw [this]
      exact U.mul_mem (hall _ _) ih
  have := hlist (pairsOf (toAdd z))
  rw [hsum] at this
  rwa [ofAdd_toAdd] at this

end CFSG.QuasithinUnique.B42A57
