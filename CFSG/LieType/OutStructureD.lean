module

public import CFSG.LieType.OutStructureA1
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.Adapters.CatalogueFieldBridges

theorem exists_fieldPart_graphFixedRootGroup_trialityD4
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (p ^ f)) →
    ∃ F : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ ∧
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊔ F) = ⊤ := by
  classical
  intro K _ _ hK σ hσ
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have key : ∀ (hNF : ∀ α : MulAut C, ∃! gδ : C × (K ≃+* K),
        α = MulAut.conj gδ.1 * fieldActor σ gδ.2)
      (Θ : MulAut C →* (K ≃+* K))
      (hΘ : ∀ (α : MulAut C) (g : C) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor σ δ → Θ α = δ)
      (hker : Θ.ker = MulAut.conj.range),
      ∃ F : Subgroup (MulAut C),
        (CFSG.ComponentClassification.OuterAutomorphisms.inner C ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner C = ⊥ ∧
        (CFSG.ComponentClassification.OuterAutomorphisms.inner C ⊔ F) = ⊤ := by
    intro hNF Θ hΘ hker
    let Φ : (K ≃+* K) →* MulAut C := fieldActorHom (t := TwistTag.D4) σ
    let F : Subgroup (MulAut C) := (⊤ : Subgroup (K ≃+* K)).map Φ
    have hΦinj : Function.Injective Φ := by
      intro δ ε hδε
      have h1 : Θ (Φ δ) = Θ (Φ ε) := congrArg Θ hδε
      have h2 : Θ (Φ δ) = δ := hΘ _ 1 δ (by rw [map_one, one_mul, fieldActorHom_apply])
      have h3 : Θ (Φ ε) = ε := hΘ _ 1 ε (by rw [map_one, one_mul, fieldActorHom_apply])
      rwa [h2, h3] at h1
    have hFcyc : IsCyclic ↥F := by
      have htop : IsCyclic ↥(⊤ : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
      exact (Subgroup.equivMapOfInjective (⊤ : Subgroup (K ≃+* K)) Φ hΦinj).isCyclic.mp htop
    have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner C = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxF, hxI⟩ := hx
      obtain ⟨δ, -, rfl⟩ := Subgroup.mem_map.mp hxF
      have h1 : Φ δ ∈ Θ.ker := by rw [hker]; exact hxI
      rw [MonoidHom.mem_ker] at h1
      have h2 : Θ (Φ δ) = δ := hΘ _ 1 δ (by rw [map_one, one_mul, fieldActorHom_apply])
      rw [h2] at h1
      rw [Subgroup.mem_bot, h1, map_one]
    have hsup : CFSG.ComponentClassification.OuterAutomorphisms.inner C ⊔ F = ⊤ := by
      refine le_antisymm le_top ?_
      intro α _
      obtain ⟨⟨g, δ⟩, hα, -⟩ := hNF α
      rw [hα]
      exact Subgroup.mul_mem_sup ⟨g, rfl⟩ (Subgroup.mem_map_of_mem Φ (Subgroup.mem_top δ))
    exact ⟨F, by rw [hsup]; exact Subgroup.normal_top, hFcyc, hFbot, hsup⟩
  ·
    have hNF : ∀ α : MulAut C, ∃! gδ : C × (K ≃+* K),
        α = MulAut.conj gδ.1 * fieldActor σ gδ.2 := by
      by_cases hp2 : p = 2
      · subst hp2
        have hK2 : Nat.card K = (2 ^ f) ^ 3 := hK
        exact (even_triality_exact_automorphism_normal_form hf K hK2 σ hσ).2.1
      · exact (odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ).2.1
    have hdata : ∃ Θ : MulAut C →* (K ≃+* K),
        (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
        Θ.ker = MulAut.conj.range := by
      by_cases hp2 : p = 2
      · subst hp2
        have hK2 : Nat.card K = (2 ^ f) ^ 3 := hK
        obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
          even_triality_exact_automorphism_normal_form hf K hK2 σ hσ
        exact ⟨Θ, hΘ, hker⟩
      · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
          odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
        exact ⟨Θ, hΘ, hker⟩
    obtain ⟨Θ, hΘ, hker⟩ := hdata
    exact key hNF Θ hΘ hker

theorem i713ClauseFor_lie_trialityD4
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let L := GaloisField q.p (3 * q.exponent)
  have hLcardp : Nat.card L = (q.p ^ q.exponent) ^ 3 := by
    rw [GaloisField.card q.p (3 * q.exponent)
      (Nat.mul_ne_zero (by norm_num) q.exponent_pos.ne'), ← pow_mul, mul_comm]
  have hLcard : Nat.card L = q.card ^ 3 := by
    rw [hLcardp, TauCeti.PrimePower.card_def]
  let σ : L ≃+* L := iterateFrobeniusEquiv L q.p q.exponent
  have hσdef : ∀ c : L, σ c = c ^ (q.p ^ q.exponent) := fun c =>
    iterateFrobeniusEquiv_def _ _ _ _
  have hσ : ∀ c : L, σ c = c ^ q.card := fun c => by
    rw [hσdef c, TauCeti.PrimePower.card_def]
  obtain ⟨e⟩ := nonempty_catEquiv_graphFixedRootGroup_trialityD4 (q := q) hv
    (K := L) hLcard σ hσ
  obtain ⟨F, hnorm, hcyc, hbot, htop⟩ :=
    exists_fieldPart_graphFixedRootGroup_trialityD4 (p := q.p) q.prime_p q.exponent_pos
      L hLcardp σ hσdef
  refine Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans e)
    ⟨F, ?_, hcyc, hbot, ?_, ?_⟩))
  · rw [htop]; exact Subgroup.normal_top
  · rw [htop, Subgroup.index_top]; exact hp.not_dvd_one
  · intro x hx
    rw [htop]
    exact Subgroup.mem_top x

end CFSG.LieType.OutStructure
