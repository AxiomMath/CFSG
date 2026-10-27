module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def KOk (a b a' b' d : Perm (Fin 5)) : Prop :=
  d ∉ Eset → (∀ g ∈ four a b, d * g * d⁻¹ ∈ four a b) → four a b ≠ {1} →
    (four a b).card * (fixOf a' b').card = 16 → (four a' b').card * (fixOf a b).card = 16 →
      four a b = Eset

instance (a b a' b' d : Perm (Fin 5)) : Decidable (KOk a b a' b' d) := by
  unfold KOk; infer_instance

theorem K_fin : ∀ a ∈ Eset, ∀ b ∈ Eset, ∀ a' ∈ Eset, ∀ b' ∈ Eset, ∀ d ∈ Dset,
    KOk a b a' b' d := by
  decide +kernel

theorem phi_two : ∀ g ∈ Dset, g ∉ Eset → ∀ w : Fin 5 → ZMod 2, isEven w →
    (∀ σ ∈ Eset, pact σ w = w) → pact g w + w = 0 ∨ pact g w + w = z0 := by
  decide +kernel

theorem even_Eset : ∀ g ∈ Eset, Perm.sign g = 1 → g = 1 ∨ g = swap 0 1 * swap 2 3 := by
  decide +kernel

theorem exists_not_mem_Eset (K : Subgroup (Perm (Fin 5)))
    (hev : ∀ g ∈ K, Perm.sign g = 1) (h3 : 3 ≤ Nat.card K) : ∃ g ∈ K, g ∉ Eset := by
  by_contra hcon
  push Not at hcon
  have hsub : ∀ g ∈ K, g = 1 ∨ g = swap 0 1 * swap 2 3 := fun g hg =>
    even_Eset g (hcon g hg) (hev g hg)
  have hle : Nat.card K ≤ Nat.card {g : Perm (Fin 5) // g = 1 ∨ g = swap 0 1 * swap 2 3} :=
    Nat.card_le_card_of_injective (fun g => ⟨g.1, hsub g.1 g.2⟩)
      (fun a b h => Subtype.ext (by simpa using h))
  have hc : Nat.card {g : Perm (Fin 5) // g = 1 ∨ g = swap 0 1 * swap 2 3} ≤ 2 := by
    have : {g : Perm (Fin 5) // g = 1 ∨ g = swap 0 1 * swap 2 3} ≃ ({1, swap 0 1 * swap 2 3} :
        Finset (Perm (Fin 5))) := Equiv.subtypeEquivRight (by intro g; simp)
    rw [Nat.card_congr this, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two
  omega

end CFSG.QuasithinUnique.AppCS2
