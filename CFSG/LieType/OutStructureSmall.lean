module

public import CFSG.LieType.OutStructureA1
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycExc
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.LiteratureLocal.SmallRee
open CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_fieldPart_reeGamma
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) :
    ∃ F : Subgroup (MulAut (ReeTag.G2.reeGamma K a)),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (ReeTag.G2.reeGamma K a) ⊔ F).index ∧
      ∀ x : MulAut (ReeTag.G2.reeGamma K a), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K a) ⊔ F := by
  classical
  haveI : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  let Fr : MulAut (ReeTag.G2.reeGamma K a) := frobeniusΓ
  have hpow : Fr ^ (2 * a + 1) = 1 := frobeniusΓ_pow hK
  have hfinord : IsOfFinOrder Fr :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * a + 1, by omega, hpow⟩
  let F : Subgroup (MulAut (ReeTag.G2.reeGamma K a)) := Subgroup.zpowers Fr
  have hsup : inner (ReeTag.G2.reeGamma K a) ⊔ F = ⊤ := by
    refine le_antisymm le_top ?_
    intro α _
    obtain ⟨g, k, rfl⟩ := exists_eq_conj_mul_frobeniusΓ_pow ha hK α
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ (Subgroup.npow_mem_zpowers Fr k)
  have hbot : F ⊓ inner (ReeTag.G2.reeGamma K a) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨k, hk⟩ :=
      (Submonoid.mem_powers_iff x Fr).mp ((hfinord.mem_powers_iff_mem_zpowers).mpr hxF)
    rw [← hk] at hxI
    obtain ⟨g, hg⟩ := hxI
    obtain ⟨m, hm⟩ := dvd_of_frobeniusΓ_pow_eq_conj hK hg.symm
    rw [Subgroup.mem_bot, ← hk, hm, pow_mul, frobeniusΓ_pow hK, one_pow]
  refine ⟨F, ?_, Subgroup.isCyclic_zpowers Fr, hbot, ?_, ?_⟩
  · rw [hsup]; exact Subgroup.normal_top
  · rw [hsup, Subgroup.index_top]; exact hp.not_dvd_one
  · rw [hsup]; intro x _; exact Subgroup.mem_top x

theorem i713ClauseFor_lie_twistedG2
    (a : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 a).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.reeG2 a, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  have hmodel : CFSG.Blueprint.ReeTitsModel
      (TauCeti.CFSGIndex.lie ⟨.reeG2 a, hv⟩).Group .twistedG2 3 (2 * a + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 a ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨b, L, hLfield, hLfin, hLchar, hb, hLcard, ⟨eL⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel hmodel
  letI := hLfield
  letI := hLfin
  letI := hLchar
  haveI : Finite (ModGL ReeTag.G2.tag L) := finite_modGL
  haveI : Finite (ReeTag.G2.reeGamma L b) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_reeGamma hb hLcard hp)))

theorem i713ClauseFor_lie_Tits
    (hv : TauCeti.LieTypeIndex.tits.Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩) := by
  intro K _ _ hK hnab ⟨e⟩ p hp hp2 hpRank
  exact Or.inl (CFSG.AGLEmbedding.not_dvd_card_outer_tits hv e hp hp2)

end CFSG.LieType.OutStructure
