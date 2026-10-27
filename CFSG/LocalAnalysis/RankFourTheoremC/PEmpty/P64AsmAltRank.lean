module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open Subgroup

section Blocks

variable (p : ℕ) [NeZero p]

@[expose] def blockPerm : Multiplicative (Fin 3 → ZMod p) →* Equiv.Perm (Fin 3 × ZMod p) where
  toFun v :=
    { toFun := fun q => (q.1, q.2 + Multiplicative.toAdd v q.1)
      invFun := fun q => (q.1, q.2 - Multiplicative.toAdd v q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  map_one' := by
    ext q <;> simp
  map_mul' v w := by
    ext q
    · simp
    · simp [add_assoc, add_comm (Multiplicative.toAdd v q.1)]

theorem blockPerm_injective : Function.Injective (blockPerm p) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  apply Multiplicative.toAdd.injective
  funext i
  have := congrArg (fun σ : Equiv.Perm (Fin 3 × ZMod p) => (σ (i, 0)).2) hv
  simpa [blockPerm] using this

theorem blockPerm_pow (v : Multiplicative (Fin 3 → ZMod p)) : (blockPerm p v) ^ p = 1 := by
  rw [← map_pow]
  have : v ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [nsmul_eq_mul]
  rw [this, map_one]

end Blocks

theorem exists_elemAbelian_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 3 * p ≤ n) :
    ∃ E : Subgroup (alternatingGroup (Fin n)), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι⟩ : Nonempty (Fin 3 × ZMod p ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa [ZMod.card] using hn)
  let Φ : Multiplicative (Fin 3 → ZMod p) →* Equiv.Perm (Fin n) :=
    (Equiv.Perm.viaEmbeddingHom ι).comp (blockPerm p)
  have hΦ : Function.Injective Φ :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp (blockPerm_injective p)
  have hpow : ∀ g, Φ g ^ p = 1 := fun g => by
    show (Equiv.Perm.viaEmbeddingHom ι) (blockPerm p g) ^ p = 1
    rw [← map_pow, blockPerm_pow, map_one]
  have heven : ∀ g, Φ g ∈ alternatingGroup (Fin n) := by
    intro g
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : Equiv.Perm.sign (Φ g) ^ p = 1 := by rw [← map_pow, hpow, map_one]
    obtain ⟨j, hj⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have h2 : Equiv.Perm.sign (Φ g) ^ (2 * j + 1) = Equiv.Perm.sign (Φ g) := by
      rw [pow_succ, pow_mul, Int.units_sq, one_pow, one_mul]
    rw [← h2, ← hj]
    exact h1
  let Φ' : Multiplicative (Fin 3 → ZMod p) →* alternatingGroup (Fin n) :=
    Φ.codRestrict _ heven
  have hΦ' : Function.Injective Φ' := fun a b h => hΦ (congrArg Subtype.val h)
  refine ⟨Φ'.range, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨g, rfl⟩
    apply Subtype.ext
    simpa [Φ'] using hpow g
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ').toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_pi]
    simp [ZMod.card]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
