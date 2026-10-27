module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Shape
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroComp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}
  {Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p)}
  {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} {T₁ : Sylow p L}

theorem sylow_noncyclic (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁) :
    ¬ IsCyclic (T₁ : Subgroup L) := fun hc => h.noncyclic (by
  rw [← h.sylow]
  exact isCyclic_of_surjective _ (L.subtype.subgroupMap_surjective (T₁ : Subgroup L)))

theorem oneLieFacts (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁)
    (hK : KFactOneLie) : OneLieFacts p L T₁ :=
  hK L h.simple h.nonabelian h.catalog p h.red.prime h.red.ne_two T₁ h.sylow_noncyclic h.core_ne
    h.big

theorem exists_torusFacts [Fact p.Prime]
    (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁) (hT : KFactOneLieTorus) :
    ∃ n e : ℕ, OneLieTorusFacts p L T₁ n e :=
  hT L h.simple h.nonabelian h.catalog p h.red.ne_two T₁ h.sylow_noncyclic h.core_ne h.big

theorem glbCore_one_map_le [Fact p.Prime]
    (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁) {n e : ℕ}
    (hTF : OneLieTorusFacts p L T₁ n e) :
    (GLBCore p 1 (T₁ : Subgroup L)).map L.subtype ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have h2 := two_le_pRank_of_isPGroup_not_isCyclic h.red.prime h.red.ne_two T₁.isPGroup'
    h.sylow_noncyclic
  have hNle : Subgroup.normalizer ((T₁ : Subgroup L) : Set L) ≤ GLBCore p 1 (T₁ : Subgroup L) :=
    le_sSup ⟨(T₁ : Subgroup L), le_rfl, by omega, rfl⟩
  have heq : GLBCore p 1 (T₁ : Subgroup L) = Subgroup.normalizer ((T₁ : Subgroup L) : Set L) := by
    by_contra hne
    exact h.core_ne (hTF.borel_coatom.2 _ (lt_of_le_of_ne hNle (Ne.symm hne)))
  rw [heq]
  rintro _ ⟨x, hx, rfl⟩
  have hx' := coe_mem_normalizer_map hx
  rw [h.sylow] at hx'
  exact h.borel_le hx'

theorem toPhaseThree [Fact p.Prime]
    (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁) (hK : KFactOneLie) {n e : ℕ}
    (hTF : OneLieTorusFacts p L T₁ n e) :
    GLBPrimeCore p (H₁ ⊓ M) = GLBPrimeCore p H₁ ∧ D1PhaseThree p P' M H₁ S := by
  have hU : UPrimeHyp p (((H₁ ⊓ M).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :=
    uPrimeHyp_of_forall_kFact h.red.prime fun L' hL' hL'X => by
      by_cases hL'L : L' = L
      · subst hL'L
        exact ⟨(h.oneLieFacts hK).uPrime, T₁, h.glbCore_one_map_le hTF⟩
      · exact absurd (h.others L' hL' hL'L) hL'X
  have hcore := h.kzero.escape.primeCore_inf_eq_iff.mpr
    (h.red.primeComplementCore_eq_bot_of_uPrimeHyp hU)
  exact ⟨hcore, h.kzero.escape.toPhaseThreeU h.kzero.data.glob hcore⟩

end D1OneLieKZeroComp

end CFSG.AGLEmbedding
