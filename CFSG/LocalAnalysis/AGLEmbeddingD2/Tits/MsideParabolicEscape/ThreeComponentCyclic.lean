module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.LayerOfNotConstrained
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
open scoped commutatorElement

theorem isPSolvable_three_of_hasPrimeConstraint_of_cyclic {B : Type} [Group B] [Finite B]
    (hcyc : ∀ X : Subgroup B, IsPGroup 3 X → IsCyclic X)
    (hc : HasPrimeConstraint (G := B) 3) : CFSG.HallHigman.IsPSolvable 3 B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hRn, hR3, hCR⟩ := hc
  obtain ⟨W, hW3, hWR⟩ :=
    CFSG.AGLEmbeddingD2.exists_isPGroup_map_mk_eq_of_isPGroup
      (primeComplementCore (G := B) 3) hR3
  haveI : IsCyclic W := hcyc W hW3
  have hRcyc : IsCyclic R := by
    rw [← hWR]
    exact isCyclic_of_surjective ((QuotientGroup.mk' (primeComplementCore (G := B) 3)).subgroupMap W)
      (MonoidHom.subgroupMap_surjective _ W)
  haveI := hRcyc
  have hsol : Group.IsSolvable (B ⧸ primeComplementCore (G := B) 3) := by
    haveI : Group.IsSolvable R := inferInstance
    apply isSolvable_of_commutatorElement_mem R
    intro a b
    have hcomm := commutator_centralizes_cyclic R (a := a⁻¹) (b := b⁻¹)
      (fun r hr => by simpa using hRn.conj_mem r hr a⁻¹)
      (fun r hr => by simpa using hRn.conj_mem r hr b⁻¹)
    apply hCR
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := hcomm r hr
    simp only [inv_inv, commutatorElement_def]
    simpa [mul_assoc] using this.symm
  exact isPSolvable_of_normal_coprime_quotient_solvable (primeComplementCore (G := B) 3)
    (primeComplementCore_coprime 3) hsol

theorem isPSolvable_three_of_coprime {K : Type} [Group K] [Finite K]
    (h : Nat.Coprime 3 (Nat.card K)) : CFSG.HallHigman.IsPSolvable 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isPSolvable_of_normal_coprime_quotient_solvable (⊤ : Subgroup K) ?_ ?_
  · rwa [Subgroup.card_top]
  · haveI : Subsingleton (K ⧸ (⊤ : Subgroup K)) := QuotientGroup.subsingleton_quotient_top
    infer_instance

theorem exists_three_component_of_cyclic {B : Type} [Group B] [Finite B]
    (hcyc : ∀ X : Subgroup B, IsPGroup 3 X → IsCyclic X)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 B) :
    ∃ L : Subgroup B, CFSG.IsPComponent 3 L ∧ 3 ∣ Nat.card L := by
  classical
  have hnc : ¬ HasPrimeConstraint (G := B) 3 := fun h =>
    hns (isPSolvable_three_of_hasPrimeConstraint_of_cyclic hcyc h)
  have hlayer := layer_ne_bot_of_not_hasPrimeConstraint hnc
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (B ⧸ primeComplementCore (G := B) 3), CFSG.IsComponent K := by
    by_contra h
    push Not at h
    apply hlayer
    have : {K : Subgroup (B ⧸ primeComplementCore (G := B) 3) | CFSG.IsComponent K} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr h
    simp only [CFSG.layer.eq_sSup]
    rw [this, sSup_empty]
  set π := QuotientGroup.mk' (primeComplementCore (G := B) 3) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hex : ∃ n : ℕ, ∃ J : Subgroup B, J.IsSubnormal ∧ J.map π = K ∧ Nat.card J = n :=
    ⟨_, K.comap π, hK.2.comap π, Subgroup.map_comap_eq_self_of_surjective hπs K, rfl⟩
  obtain ⟨J, hJsub, hJmap, hJcard⟩ : ∃ J : Subgroup B, J.IsSubnormal ∧ J.map π = K ∧
      Nat.card J = Nat.find hex := Nat.find_spec hex
  refine ⟨J, ⟨K, hK, hJsub, hJmap, fun J' hlt hsub hmap => ?_⟩, ?_⟩
  · have hle : Nat.find hex ≤ Nat.card J' := Nat.find_min' hex ⟨J', hsub, hmap, rfl⟩
    have hlt' : Nat.card J' < Nat.card J := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) fun heq => ?_
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le heq.ge)
    omega
  · have hnsK : ¬ CFSG.HallHigman.IsPSolvable 3 K :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.not_isPSolvable_of_isComponent
        (pPrimeCore_three_quotient_eq_bot B) hK
    have h3K : 3 ∣ Nat.card K := by
      by_contra h
      exact hnsK (isPSolvable_three_of_coprime ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h))
    have h3 : 3 ∣ Nat.card (J.map π) := by rw [hJmap]; exact h3K
    exact Nat.dvd_trans h3 (Subgroup.card_map_dvd π (H := J))

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
