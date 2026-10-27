module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.RootTransport
public import CFSG.LieType.Steinberg.Adjoint.CertE6Valid
public import CFSG.LieType.Steinberg.Adjoint.CertE7
public import CFSG.LieType.Steinberg.Adjoint.ExtraPairs

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section EType

theorem cartanE_connected_aux (r : ℕ) (hr : 4 ≤ r) (i j : Fin r) :
    Relation.ReflTransGen (fun a b : Fin r => Tag.cartanE r a b = -1 ∧ Tag.cartanE r b a = -1) i j := by
  set R := (fun a b : Fin r => Tag.cartanE r a b = -1 ∧ Tag.cartanE r b a = -1) with hR
  have hsymm : Symmetric R := fun a b h => ⟨h.2, h.1⟩
  have hpath : ∀ k (hk : 2 + k < r), Relation.ReflTransGen R ⟨2, by omega⟩ ⟨2 + k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      refine Relation.ReflTransGen.tail (ih (by omega)) ?_
      have hne : ¬ (2 + k = 2 + (k + 1)) := by omega
      have hne' : ¬ (2 + (k + 1) = 2 + k) := by omega
      constructor
      · simp only [Tag.cartanE, Fin.mk.injEq, hne, if_false]
        rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))]
      · simp only [Tag.cartanE, Fin.mk.injEq, hne', if_false]
        rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))]
  have h02 : R ⟨0, by omega⟩ ⟨2, by omega⟩ := by
    constructor <;> simp [Tag.cartanE]
  have h13 : R ⟨1, by omega⟩ ⟨3, by omega⟩ := by
    constructor <;> simp [Tag.cartanE]
  have h2 : ∀ i : Fin r, Relation.ReflTransGen R ⟨2, by omega⟩ i := by
    intro i
    obtain ⟨v, hv⟩ := i
    rcases (by omega : v = 0 ∨ v = 1 ∨ 2 ≤ v) with rfl | rfl | h
    · exact Relation.ReflTransGen.single (hsymm h02)
    · exact (hpath 1 (by omega)).tail (hsymm h13)
    · obtain ⟨k, rfl⟩ : ∃ k, v = 2 + k := ⟨v - 2, by omega⟩
      exact hpath k hv
  have hsymm' : ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm hbc) ih
  exact (hsymm' _ _ (h2 i)).trans (h2 j)

theorem cartanE_connected {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) :
    Relation.ReflTransGen (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) i j := by
  rcases hτ with rfl | rfl | rfl
  · exact cartanE_connected_aux 6 (by norm_num) i j
  · exact cartanE_connected_aux 7 (by norm_num) i j
  · exact cartanE_connected_aux 8 (by norm_num) i j

theorem exists_neighbour_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ i l : Fin τ.rank, τ.cartan i l = -1 ∧ τ.cartan l i = -1 := by
  rcases hτ with rfl | rfl | rfl
  · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide, by decide⟩
  · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide, by decide⟩
  · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide, by decide⟩

theorem exists_adjData_valid_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ D : AdjData τ, D.Valid ∧ NoG2 τ := by
  rcases hτ with rfl | rfl | rfl
  · exact ⟨_, e6AdjData_valid, noG2_E6⟩
  · exact ⟨_, e7AdjData_valid, noG2_E7⟩
  · exact ⟨_, e8Data_valid, noG2_E8⟩

end EType

theorem eq_top_of_irrational_rootElt {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] (k : Subfield K) (hk : ∀ F : Subfield K, k ≤ F → F = k ∨ F = ⊤)
    (H : Subgroup ↥(adjointGroup τ K))
    (hrat : ∀ (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ H)
    (γ₀ : Fin τ.rank → ℤ) (hγ₀ : IsRoot τ γ₀) (t : K) (ht : t ∉ k)
    (hmem : xPar (rootOperatorFamily τ) γ₀ t ∈ H) : H = ⊤ := by
  have hw := weylElement_one_mem_of_rat k H hrat
  have hconn := cartanE_connected hτ
  have huniv := fun {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (u : K) =>
    xPar_mem_iff_of_roots H hw hconn hγ hδ u
  obtain ⟨D, hD, hG2⟩ := exists_adjData_valid_E hτ
  obtain ⟨i, l, hil, hli⟩ := exists_neighbour_E hτ
  obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_neighbour (K := K) hD hG2 hil hli
  let S : Subring K :=
    { carrier := {u | ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → xPar (rootOperatorFamily τ) γ u ∈ H}
      zero_mem' := fun γ _ => by simpa [xPar_zero] using H.one_mem
      one_mem' := fun γ hγ => hrat γ hγ 1 k.one_mem
      add_mem' := fun {a b} ha hb γ hγ => by
        rw [xPar_add]
        exact H.mul_mem (ha γ hγ) (hb γ hγ)
      neg_mem' := fun {a} ha γ hγ => by
        rw [← xPar_neg]
        exact H.inv_mem (ha γ hγ)
      mul_mem' := fun {a b} ha hb γ hγ => by
        have h1 := xPar_mul_mem_of_commutator H hε hcomm (ha _ (isRoot_single τ l)) (hb _ (isRoot_single τ i))
        exact (huniv (isRoot_single_add_single hil) hγ _).1 h1 }
  have hS : S = ⊤ := by
    refine eq_top_of_subring k hk S (fun c hc γ hγ => hrat γ hγ c hc) ht ?_
    intro γ hγ
    exact (huniv hγ₀ hγ t).1 hmem
  refine eq_top_of_forall_xPar_mem H fun γ hγ c => ?_
  have : c ∈ S := by rw [hS]; trivial
  exact this γ hγ

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
