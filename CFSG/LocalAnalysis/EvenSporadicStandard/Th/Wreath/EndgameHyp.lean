module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G]

structure QHyp (L A D : Subgroup G) (t : G) (Q : Subgroup G) : Prop where
  D_le : D ≤ Q
  le_centralizer : Q ≤ centralizer (D : Set G)
  pgroup : IsPGroup 2 Q
  comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  mem_of_sq_eq_one : ∀ x ∈ Q, x ^ 2 = 1 → x ∈ D
  conj_mem : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ Q, n * x * n⁻¹ ∈ Q
  conj_t_mem : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q
  maximal : ∀ Y : Subgroup G, Y ≤ centralizer (D : Set G) → IsPGroup 2 Y → Q ≤ Y → Y ≤ Q

structure THyp (S D Q : Subgroup G) (t : G) (T : Subgroup G) : Prop where
  pgroup : IsPGroup 2 T
  le_normalizer : T ≤ normalizer (D : Set G)
  Q_le : Q ≤ T
  S_le : S ≤ T
  t_mem : t ∈ T
  maximal : ∀ Y : Subgroup G, Y ≤ normalizer (D : Set G) → IsPGroup 2 Y → T ≤ Y → Y ≤ T

theorem THyp.inf_centralizer_eq {L A S D Q T : Subgroup G} {t : G} (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) : T ⊓ centralizer (D : Set G) = Q :=
  le_antisymm (hQ.maximal _ inf_le_right (hT.pgroup.to_le inf_le_left) (le_inf hT.Q_le
    hQ.le_centralizer)) (le_inf hT.Q_le hQ.le_centralizer)

end CFSG.EvenSporadicStandard.ThStd
