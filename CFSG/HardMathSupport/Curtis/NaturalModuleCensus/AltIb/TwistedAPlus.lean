module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusA.Main

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding

@[expose] def IdxTwistedANoPlus (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q => q.p = 2 ∧ ¬ p ∣ q.card + 1
  | _ => False

theorem isLieOf_twistedA_cases {p : ℕ} (hp5 : 5 ≤ p) {X : Type} [Group X]
    (h : IsLieOf IdxTwistedA X) :
    IsLieOf (IdxPlusA p) X ∨ IsLieOf (IdxTwistedANoPlus p) X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d with
  | twistedA r q =>
    by_cases hpq : p ∣ q.card + 1
    · refine Or.inl ⟨⟨_, hv⟩, ⟨hd, fun h2 => ?_, hpq⟩, he⟩
      rw [h2] at hpq
      exact absurd (Nat.le_of_dvd (by norm_num) hpq) (by omega)
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, hpq⟩, he⟩
  | _ => exact hd.elim

theorem not_dvd_card_center_twistedA (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsLieOf (IdxTwistedANoPlus p) (A ⧸ Subgroup.center A)) :
    ¬ p ∣ Nat.card (Subgroup.center A) := by
  intro hdvd
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedA r q =>
    obtain ⟨hq2, hnp⟩ := hd
    rcases ToralCensus.prime_dvd_torus_of_dvd_card_center hGA ⟨.twistedA r q, hv⟩ hq2 e hp hp2
        hdvd with ⟨r', q', h, -⟩ | ⟨r', q', h, hdiv⟩
    · cases h
    · obtain ⟨-, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj h
      exact hnp hdiv
  | _ => exact hd.elim

section Plus


theorem false_of_plus_twistedA (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L J : Subgroup Y} (h : CompParabE L J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : Y} (hxL : x ∈ L) (hxp : x ^ p = 1) (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    (hX : IsLieOf (IdxPlusA p) (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨f, n, K, _, _, _, hf, hn, -, hK, hpq, ρ, hρs, hcompat, S₀, hS₀, hJtop⟩ :=
    exists_unitaryCoverPlus hGA h hX
  obtain ⟨t, ht, htJ⟩ := UnitaryLevi.exists_lift (J := J) ρ hρs hcompat
    (u := x) (Subgroup.mem_sup_left hxL) hxp hfix
  exact UnitaryLevi.false_of_pow_mem_scalars hK hf (by omega) hp hp2 hpq hS₀ hJtop t ht
    fun g hg => htJ g hg

theorem altIbCell_twistedA_plus (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L J : Subgroup Y} (hL : IsComponentOf L ⊤)
    (htype : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hpar : IsParabolicTwo L J) (hJL : J ≠ L)
    (hnB : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y))
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) {x : Y} (hxL : x ∈ L) (hxp : x ^ p = 1)
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J)
    (hX : IsLieOf (IdxPlusA p) (↥L ⧸ Subgroup.center ↥L)) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  exact false_of_plus_twistedA hGA ⟨hL, htype, hpar, hJL, hnB⟩ hp hp2 hxL hxp hfix hX

end Plus

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
