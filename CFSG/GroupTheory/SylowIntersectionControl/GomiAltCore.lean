module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

@[expose] def GomiAltCore : Prop :=
  ∀ n : ℕ, 7 ≤ n → (∀ m : ℕ, n ≠ 2 ^ m + 1) →
    ∀ X H : Subgroup (Equiv.Perm (Fin n)), alternatingGroup (Fin n) ≤ X → H ≠ ⊥ →
      IsPGroup 2 H → H ≤ X → IsPIsolatedOver 2 (normalizer (H : Set (Equiv.Perm (Fin n))) ⊓ X) H →
      ∃ Y : Subgroup (Equiv.Perm (Fin n)), Y ≠ ⊤ ∧ Odd Y.index ∧
        (∃ K : Subgroup (Equiv.Perm (Fin n)), H ≤ K ∧
          K ≤ normalizer (H : Set (Equiv.Perm (Fin n))) ⊓ X ∧
          (K.subgroupOf (normalizer (H : Set (Equiv.Perm (Fin n))) ⊓ X)).IsSubnormal ∧
          2 ∣ H.relIndex K ∧ K ≤ Y) ∧
        normalizer ((Y ⊓ alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))) :
          Set (Equiv.Perm (Fin n))) = Y ∧
        (Even n → CharTwo (Y ⊓ alternatingGroup (Fin n))) ∧
        (n % 4 = 3 → ∃ z : Equiv.Perm (Fin n), z.IsThreeCycle ∧
          twoResidual ((Y ⊓ alternatingGroup (Fin n)) ⊓
            centralizer (pCoreOf 2 (Y ⊓ alternatingGroup (Fin n)) : Set (Equiv.Perm (Fin n)))) ≤
            zpowers z)

end CFSG.GroupTheory
