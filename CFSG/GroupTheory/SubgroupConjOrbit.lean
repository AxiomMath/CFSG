module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory

theorem ncard_conj_mul_card_inf_normalizer {G : Type*} [Group G] (N A : Subgroup G) :
    {B : Subgroup G | ∃ n ∈ N, A.map (MulAut.conj n).toMonoidHom = B}.ncard *
      Nat.card ↥(N ⊓ Subgroup.normalizer (A : Set G)) = Nat.card N := by
  let act : N → Subgroup G → Subgroup G :=
    fun n H => H.map (MulAut.conj (n : G)).toMonoidHom
  let _ : MulAction N (Subgroup G) :=
    { smul := act
      one_smul := by
        intro H
        change H.map (MulAut.conj ((1 : N) : G)).toMonoidHom = H
        rw [show ((1 : N) : G) = 1 from rfl, map_one]
        exact Subgroup.map_id H
      mul_smul := by
        intro m n H
        change H.map (MulAut.conj ((m * n : N) : G)).toMonoidHom =
          (H.map (MulAut.conj (n : G)).toMonoidHom).map
            (MulAut.conj (m : G)).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have hsmul : ∀ (n : N) (H : Subgroup G),
      n • H = H.map (MulAut.conj (n : G)).toMonoidHom := fun _ _ => rfl
  have horb : MulAction.orbit N A =
      {B : Subgroup G | ∃ n ∈ N, A.map (MulAut.conj n).toMonoidHom = B} := by
    ext B
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hstab : MulAction.stabilizer N A = (Subgroup.normalizer (A : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer N A)
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : N ⊓ Subgroup.normalizer (A : Set G) ≤ N)).toEquiv] at h1
  exact h1

end CFSG.GroupTheory
