module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p d e : ℕ} {M N : Type*} [Group M] [Group N]

private def piFinExtendHom (G : Type*) [Monoid G] (e d : ℕ) : (Fin e → G) →* (Fin d → G) where
  toFun f i := if h : (i : ℕ) < e then f ⟨i, h⟩ else 1
  map_one' := by funext i; dsimp; split_ifs <;> rfl
  map_mul' f g := by funext i; dsimp; split_ifs <;> simp

private theorem piFinExtendHom_injective (G : Type*) [Monoid G] (hed : e ≤ d) :
    Function.Injective (piFinExtendHom G e d) := by
  intro f g h
  funext i
  have hi : (i : ℕ) < d := lt_of_lt_of_le i.2 hed
  simpa [piFinExtendHom, i.2] using congrFun h ⟨i, hi⟩

theorem mem_elementaryAbelianRanks_of_le (hed : e ≤ d)
    (hd : d ∈ elementaryAbelianRanks p M) : e ∈ elementaryAbelianRanks p M := by
  obtain ⟨H, ⟨f⟩⟩ := mem_elementaryAbelianRanks.1 hd
  have hinj : Function.Injective
      ((H.subtype.comp f.symm.toMonoidHom).comp (piFinExtendHom _ e d)) :=
    (H.subtype_injective.comp f.symm.injective).comp (piFinExtendHom_injective _ hed)
  exact mem_elementaryAbelianRanks.2 ⟨_, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

theorem le_elementaryAbelianPRank_iff [Finite M] (hp : 1 < p) :
    d ≤ elementaryAbelianPRank p M ↔ d ∈ elementaryAbelianRanks p M :=
  ⟨fun h => mem_elementaryAbelianRanks_of_le h
      (elementaryAbelianPRank_mem_elementaryAbelianRanks hp),
    le_elementaryAbelianPRank hp⟩

def alphaPrimes (M : Type*) [Group M] : Set ℕ :=
  {p | p.Prime ∧ 3 ≤ elementaryAbelianPRank p M}

@[simp]
theorem mem_alphaPrimes :
    p ∈ alphaPrimes M ↔ p.Prime ∧ 3 ≤ elementaryAbelianPRank p M := Iff.rfl

theorem prime_of_mem_alphaPrimes (h : p ∈ alphaPrimes M) : p.Prime := h.1

theorem three_le_elementaryAbelianPRank_of_mem_alphaPrimes (h : p ∈ alphaPrimes M) :
    3 ≤ elementaryAbelianPRank p M := h.2

theorem mem_alphaPrimes_iff_exists_subgroup [Finite M] :
    p ∈ alphaPrimes M ↔
      p.Prime ∧ ∃ H : Subgroup M, Nonempty (H ≃* (Fin 3 → Multiplicative (ZMod p))) := by
  refine ⟨fun h => ⟨h.1, mem_elementaryAbelianRanks.1
    ((le_elementaryAbelianPRank_iff h.1.one_lt).1 h.2)⟩, fun ⟨hp, hH⟩ => ?_⟩
  exact ⟨hp, (le_elementaryAbelianPRank_iff hp.one_lt).2 (mem_elementaryAbelianRanks.2 hH)⟩

theorem alphaPrimes_subset_primeFactors [Finite M] :
    alphaPrimes M ⊆ (Nat.card M).primeFactors := fun _ hp =>
  Nat.mem_primeFactors.2 ⟨hp.1, (one_le_elementaryAbelianPRank_iff hp.1).1
    (le_trans (by norm_num) hp.2), Nat.card_pos.ne'⟩

theorem alphaPrimes_finite [Finite M] : (alphaPrimes M).Finite :=
  (Nat.card M).primeFactors.finite_toSet.subset alphaPrimes_subset_primeFactors

theorem alphaPrimes_mono_of_injective [Finite N] {f : M →* N} (hf : Function.Injective f) :
    alphaPrimes M ⊆ alphaPrimes N := fun _ hp =>
  ⟨hp.1, hp.2.trans (elementaryAbelianPRank_le_of_injective hp.1.one_lt hf)⟩

theorem alphaPrimes_subgroup_subset [Finite M] (H : Subgroup M) :
    alphaPrimes H ⊆ alphaPrimes M :=
  alphaPrimes_mono_of_injective H.subtype_injective

theorem alphaPrimes_eq_of_mulEquiv [Finite M] [Finite N] (e : M ≃* N) :
    alphaPrimes M = alphaPrimes N :=
  Set.Subset.antisymm (alphaPrimes_mono_of_injective (f := e.toMonoidHom) e.injective)
    (alphaPrimes_mono_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

theorem alphaPrimes_eq_empty_of_subsingleton [Subsingleton M] : alphaPrimes M = ∅ := by
  ext p
  simp only [mem_alphaPrimes, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp
  rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt]
  omega

end

end CFSG.FeitThompson
