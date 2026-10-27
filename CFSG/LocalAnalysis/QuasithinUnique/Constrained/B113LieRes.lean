module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Open CFSG.QuasithinUnique

theorem ne_bot_of_two_dvd {S : Type*} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) (h2 : 2 ∣ Nat.card S) : U ≠ ⊥ := by
  intro hbot
  subst hbot
  have hidx : ¬ 2 ∣ (⊥ : Subgroup S).index := by
    have := hU.2.2
    rwa [show ((⊥ : Subgroup S).subgroupOf ⊤).index = (⊥ : Subgroup S).index from
      Subgroup.relIndex_top_right _] at this
  rw [Subgroup.index_bot] at hidx
  exact hidx h2

theorem pCoreOf_top_eq_pCore' {S : Type*} [Group S] :
    pCoreOf 2 (⊤ : Subgroup S) = CFSG.Open.pCore 2 S := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := S)).symm,
    Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := S)).symm.toMonoidHom =
      MonoidHom.id S := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem pCoreOf_top_eq_bot_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {U P : Subgroup S} (hU : IsSylowTwoOf U ⊤) (hUP : U ≤ P) (hP : P ≠ ⊤) :
    pCoreOf 2 (⊤ : Subgroup S) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pCoreOf_top_eq_pCore']
  have : (CFSG.Open.pCore 2 S).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 S) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 S := by
      have := CFSG.LieType.BorelTits.pCore_isPGroup (G := S) 2
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    have hidx : ¬ 2 ∣ U.index := by
      have := hU.2.2
      rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right _] at this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    have hdvd : U.index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card U
    obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hm0 : m = 0 := by
      by_contra hm0
      exact hidx (hmk ▸ dvd_pow_self 2 hm0)
    have h1 : U.index = 1 := by rw [hmk, hm0, pow_zero]
    have hUtop : U = ⊤ := Subgroup.index_eq_one.1 h1
    exact hP (top_le_iff.1 (hUtop ▸ hUP))

theorem sylowFacts_of_residualAt {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : IsSylowTwoOf U ⊤) (hU1 : U ≠ ⊥)
    (hR : Setup.X6.ResidualOvergroupsAt S U P) (hchar : ∀ j, CharTwo (P j)) :
    SylowFacts S U := by
  obtain ⟨hne, hUP, hmax, -, -, -⟩ := hR
  have hco : ∀ j, P j ⋖ ⊤ := fun j => (hmax (P j) (hUP j)).2 ⟨j, rfl⟩
  have hX : pCoreOf 2 (⊤ : Subgroup S) = ⊥ :=
    pCoreOf_top_eq_bot_of_simple hU (hUP 0) (hco 0).lt.ne
  refine (ParabolicData.of_coatoms (Ps := Set.range P) hU hU1 hX ?_ ?_ ?_ ?_).sylowFacts
  · rintro Q ⟨j, rfl⟩
    exact ⟨hco j, hUP j⟩
  · exact ⟨P 0, ⟨0, rfl⟩, P 1, ⟨1, rfl⟩, hne⟩
  · intro A hUA hA
    obtain ⟨M, hAM, hM⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hA)
    obtain ⟨j, hj⟩ := (hmax M (hUA.trans hAM)).1 hM
    exact ⟨P j, ⟨j, rfl⟩, hj ▸ hAM⟩
  · rintro Q ⟨j, rfl⟩
    exact hchar j

end CFSG.QuasithinUnique.B113Lie
