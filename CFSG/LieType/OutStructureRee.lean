module

public import CFSG.LieType.OutStructureA1
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Ree

theorem exists_fieldPart_reeF4
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) :
    ∃ F : Subgroup (MulAut (ReeTag.F4.reeGamma K a)),
      (inner (ReeTag.F4.reeGamma K a) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ inner (ReeTag.F4.reeGamma K a) = ⊥ ∧
      ¬ p ∣ (inner (ReeTag.F4.reeGamma K a) ⊔ F).index ∧
      ∀ x : MulAut (ReeTag.F4.reeGamma K a), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (ReeTag.F4.reeGamma K a) ⊔ F := by
  classical
  have hNF :=
    (large_Ree_full_inner_field_automorphism_normal_form a ha K hK).2.1
  let G := ReeTag.F4.reeGamma K a
  let F : Subgroup (MulAut G) := ReeTag.F4.reeGammaFld K a
  have hFmem : ∀ β : K ≃+* K, ReeTag.F4.reeGammaFieldAut K a β ∈ F := fun β => ⟨β, rfl⟩
  have hImem : ∀ g : G, MulAut.conj g ∈ inner G := fun g => ⟨g, rfl⟩
  have hsup : inner G ⊔ F = ⊤ := by
    refine le_antisymm le_top ?_
    intro α _
    obtain ⟨q, hq, -⟩ := hNF α
    rw [hq]
    exact Subgroup.mul_mem_sup (hImem q.1) (hFmem q.2)
  have hbot : F ⊓ inner G = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨β, rfl⟩ := hxF
    change (ReeTag.F4.reeGammaFieldAut K a) β ∈ ⊥
    obtain ⟨g, hg⟩ := hxI
    change MulAut.conj g = (ReeTag.F4.reeGammaFieldAut K a) β at hg
    have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
      rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
    obtain ⟨q, -, huniq⟩ := hNF ((ReeTag.F4.reeGammaFieldAut K a) β)
    have h1 : (1, β) = q := by
      refine huniq (1, β) ?_
      dsimp only
      rw [map_one, one_mul]
    have h2 : (g, 1) = q := by
      refine huniq (g, 1) ?_
      dsimp only
      rw [hg, hone, mul_one]
    have hpair : (1, β) = (g, 1) := h1.trans h2.symm
    have hβ : β = 1 := congrArg Prod.snd hpair
    rw [hβ, hone]
    exact Subgroup.one_mem (⊥ : Subgroup (MulAut G))
  haveI : IsCyclic (K ≃+* K) := CFSG.LieType.Chevalley.ringAut_isCyclic
  have hcyc : IsCyclic ↥F :=
    isCyclic_of_surjective (f := (ReeTag.F4.reeGammaFieldAutHom K a).rangeRestrict)
      (ReeTag.F4.reeGammaFieldAutHom K a).rangeRestrict_surjective
  refine ⟨F, ?_, hcyc, hbot, ?_, ?_⟩
  · rw [hsup]; exact Subgroup.normal_top
  · rw [hsup, Subgroup.index_top]; exact hp.not_dvd_one
  · intro x _; rw [hsup]; exact Subgroup.mem_top x

theorem i713ClauseFor_lie_twistedF4
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  obtain ⟨X, hXfield, hXfin, hXchar, hm, hXcard, -, ⟨eL⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  letI := hXfield
  letI := hXfin
  letI := hXchar
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag X) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma X m) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_reeF4 hm hXcard hp)))

end CFSG.LieType.OutStructure
