module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QCov

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def FAt (X : Type) [Group X] (z : X) : Prop :=
  ∀ P : Subgroup X, P ≤ centralizer ({z} : Set X) → z ∈ P → Nat.card P = 8 →
    (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, ∀ g ∈ P, (k : X) * g = g * k) →
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = z) ∧
      ¬ ∀ q ∈ P, q * q = 1

theorem famF_of_fAt {t : StatedLieTag}
    (h : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (n p f : ℕ), p.Prime → p ≠ 2 →
      Blueprint.LieModel X t n p f → p ^ f ≠ 3 → ∀ z : X, orderOf z = 2 → FAt X z) :
    FamF t :=
  fun X _ _ _ n p f hp hp2 hX hq z hz => h X n p f hp hp2 hX hq z hz

theorem fAt_of_evenCent {X : Type} [Group X] {z : X} (hc : EvenCentComm X z)
    (hi : EvenCentInv X z) : FAt X z := by
  intro P hPC _ h8 hK
  refine ⟨fun ⟨⟨u, hu, v, hv, huv⟩, _⟩ => huv (hc u (hPC hu) v (hPC hv)
    (fun K h1 h2 k hk => hK K h1 h2 k hk u hu) (fun K h1 h2 k hk => hK K h1 h2 k hk v hv)),
    fun hall => ?_⟩
  have hsub : (P : Set X) ⊆ {1, z} := fun q hq => by
    rcases hi q (hPC hq) (fun K h1 h2 k hk => hK K h1 h2 k hk q hq) (hall q hq) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h2 : Nat.card P ≤ 2 :=
    calc Nat.card P = (P : Set X).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, z} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
