module

public import CFSG.LieType.OutStructureA1
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki

public section

namespace CFSG.LieType.OutStructure

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

theorem exists_fieldPart_suzukiGroup
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) :
    ∃ F : Subgroup (MulAut (suzukiGroup a K)),
      (inner (suzukiGroup a K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (suzukiGroup a K) = ⊥ ∧
      ¬ p ∣ (inner (suzukiGroup a K) ⊔ F).index ∧
      ∀ x : MulAut (suzukiGroup a K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (suzukiGroup a K) ⊔ F := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, ⟨e, he⟩, -, hbot, -, -, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  let F : Subgroup (MulAut (suzukiGroup a K)) := (szFieldAut a K).range
  have hsup : inner (suzukiGroup a K) ⊔ F = ⊤ := by
    refine le_antisymm le_top ?_
    intro α _
    obtain ⟨x, rfl⟩ := e.surjective α
    obtain ⟨g, σ⟩ := x
    rw [he g σ]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
  have hFcyc : IsCyclic ↥F := by
    haveI : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic Nat.prime_two K hK).2
    exact isCyclic_of_surjective (szFieldAut a K).rangeRestrict
      (MonoidHom.rangeRestrict_surjective (szFieldAut a K))
  refine ⟨F, ?_, hFcyc, hbot, ?_, ?_⟩
  · rw [hsup]; exact Subgroup.normal_top
  · rw [hsup, Subgroup.index_top]; exact hp.not_dvd_one
  · rw [hsup]; intro x _; exact Subgroup.mem_top x

theorem i713ClauseFor_lie_twistedB2
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩) := by
  intro K _ _ hK _habs ⟨eK⟩ p hp _hp2 _hpRank
  obtain ⟨-, a, ha, L, hLfield, hLfin, hf, hLcard, ⟨eL⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  letI : Field L := hLfield
  letI : Finite L := hLfin
  have hLcard' : Nat.card L = 2 ^ (2 * a + 1) := by rw [hLcard, hf]
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_suzukiGroup ha hLcard' hp)))

end CFSG.LieType.OutStructure
