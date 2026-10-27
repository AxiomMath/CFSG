module

public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas

public section

namespace CFSG.AGLEmbedding

theorem injective_map_conj_pow_of_forall_lt {G : Type*} [Group G] {L : Subgroup G} {t : G}
    {m : ℕ} (hmove : ∀ a : ℕ, 0 < a → a < m → t ^ a ∉ Subgroup.normalizer (L : Set G)) :
    Function.Injective fun i : Fin m => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom := by
  have hstep : ∀ i j : ℕ, i < j → j < m → L.map (MulAut.conj (t ^ i)).toMonoidHom =
      L.map (MulAut.conj (t ^ j)).toMonoidHom → False := by
    intro i j hij hjm he
    apply hmove (j - i) (by omega) (by omega)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hj : t ^ j = t ^ i * t ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj, map_conj_mul_eq] at he
    exact (Subgroup.map_injective (MulAut.conj (t ^ i)).injective he).symm
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact hstep i j hlt j.2 hij
  · exact hstep j i hlt i.2 hij.symm

end CFSG.AGLEmbedding
