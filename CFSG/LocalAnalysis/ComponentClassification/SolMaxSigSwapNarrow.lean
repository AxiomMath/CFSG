module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapAlt

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem card_le_two_of_centralizer_inf [Finite X] {K : Subgroup X} {t : X} (htK : t ∈ K)
    (ht : orderOf t = 2)
    (h : ∀ P : Subgroup X, P ≤ centralizer ({t} : Set X) ⊓ K → IsPGroup 2 P → Nat.card P ≤ 2)
    {P : Subgroup X} (hPK : P ≤ K) (hP2 : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 ((zpowers t).subgroupOf K) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])).comap_subtype
  obtain ⟨Q, hQ⟩ := hT.exists_le_sylow
  set F : Subgroup X := (Q : Subgroup ↥K).map K.subtype with hFdef
  have hFK : F ≤ K := map_subtype_le _
  have hFcard : Nat.card F = 2 ^ (Nat.card K).factorization 2 := by
    rw [hFdef, card_map_of_injective K.subtype_injective]
    exact Q.card_eq_multiplicity
  have hF2 : IsPGroup 2 F := Q.isPGroup'.map _
  have htF : t ∈ F := ⟨⟨t, htK⟩, hQ (mem_subgroupOf.mpr (mem_zpowers t)), rfl⟩
  set CF := F ⊓ centralizer ({t} : Set X) with hCFdef
  have hCF2 : Nat.card CF ≤ 2 :=
    h CF (le_inf inf_le_right (inf_le_left.trans hFK)) (hF2.to_le inf_le_left)
  have htCF : zpowers t ≤ CF :=
    zpowers_le.mpr (mem_inf.mpr ⟨htF, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hCFt : zpowers t = CF :=
    Subgroup.eq_of_le_of_card_ge htCF (by rw [Nat.card_zpowers, ht]; exact hCF2)
  have hF1 : F ≠ ⊥ := fun h0 => by
    have h1 := htF
    rw [h0, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    omega
  obtain ⟨z, hzF, hz2, hzc⟩ := Sol78H.exists_central_involution hF1 hF2
  have hzt : z ∈ zpowers t := by
    rw [hCFt]
    exact mem_inf.mpr ⟨hzF, mem_centralizer_singleton_iff.mpr (hzc t htF).symm⟩
  have hzz : zpowers z = zpowers t :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzt)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ht, hz2])
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hzz ▸ mem_zpowers t)
  have hFC : F ≤ CF := fun f hf => mem_inf.mpr ⟨hf, by
    rw [mem_centralizer_singleton_iff, ← hk]
    exact (Commute.zpow_right (hzc f hf) k).eq⟩
  calc Nat.card P ≤ 2 ^ (Nat.card K).factorization 2 := card_le_two_pow_of_le hPK hP2
    _ = Nat.card F := hFcard.symm
    _ ≤ Nat.card CF := Subgroup.card_le_of_le hFC
    _ ≤ 2 := hCF2

@[expose] def SignalizerSwapMemberNarrowInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      FooteLit.IsSolomonMember M

theorem signalizerSwapMemberInput_of_narrow (hR1 : SignalizerSwapMemberNarrowInput) :
    SignalizerSwapMemberInput := by
  intro X _ _ _ t J n e E D S hCH M hMH hMpc hne hJM eM hsmall
  by_cases hR : ∃ R : Subgroup X, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ∧
      R ≤ UnbalancedLayer.coreActionKernel M ∧
      centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)
  · obtain ⟨R, hR₁, hR₂, hRH, hRK, hCR⟩ := hR
    exact Sol78H.isSolomonMember_of_centralizer_le ⟨hMH, hMpc⟩ hR₁ hR₂ hRK hRH hCR
  · push Not at hR
    exact hR1 X t J n e E D S hCH M hMH hMpc hne hJM eM
      (fun P hPK hP2 =>
        card_le_two_of_centralizer_inf S.t_mem_coreActionKernel S.pair.1.1 hsmall hPK hP2)
      hR

theorem swapAltExclusion_of_narrow (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hR1 : SignalizerSwapMemberNarrowInput) :
    SignalizerSwapAltExclusion :=
  swapAltExclusion_of_member h33 h35 hT13 hML hSch (signalizerSwapMemberInput_of_narrow hR1)

end CFSG.ComponentClassification.SolMax
