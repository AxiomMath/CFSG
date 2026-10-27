module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharClassicalCover

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def P1OffCharCoverThreeNoInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ : Subgroup Y),
    ReducedNongeneration 3 Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        ((∃ q, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) ∨ (∃ q, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1)) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        3 ≠ d.1.characteristic → 3 ∣ Nat.card (Subgroup.center K) →
        (¬ ∃ E : Subgroup Y, E ≤ (Rb : Subgroup Y) ∧
            E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
            E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) →
        P1ThreeLieList 3 d

@[expose] def P1OffCharAlmostSimple : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      Subgroup.centralizer (K : Set Y) = ⊥ →
      (¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        p ≠ d.1.characteristic →
        P1ThreeLieList p d

namespace ReducedNongeneration

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y}

theorem centralizer_eq_bot (h : ReducedNongeneration p Y Rb Y₀) {K : Subgroup Y} (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hz : ¬ p ∣ Nat.card (Subgroup.center K)) : Subgroup.centralizer (K : Set Y) = ⊥ := by
  have hp : p.Prime := Fact.out
  have hcop : p.Coprime (Nat.card (Subgroup.centralizer (K : Set Y))) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hc' : orderOf (c : Y) = p := by rw [Subgroup.orderOf_coe, hc]
    have hexp : ∀ x ∈ Subgroup.zpowers (c : Y), x ^ p = 1 := by
      rintro _ ⟨k, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc', pow_orderOf_eq_one,
        one_zpow]
    obtain ⟨g, hg⟩ := exists_conj_le_sylow Rb hexp
    have hgR : (MulAut.conj g).toMonoidHom (c : Y) ∈ (Rb : Subgroup Y) :=
      hg ⟨(c : Y), Subgroup.mem_zpowers _, rfl⟩
    have hgC : (MulAut.conj g).toMonoidHom (c : Y) ∈ Subgroup.centralizer (K : Set Y) :=
      (Subgroup.normal_centralizer (H := K)).conj_mem _ c.2 g
    have hgo : orderOf ((MulAut.conj g).toMonoidHom (c : Y)) = p := by
      rw [orderOf_injective _ (MulAut.conj g).injective, hc']
    obtain ⟨z, hz', hzc⟩ := hcent _ ⟨hgR, hgC⟩ hgo
    apply hz
    have hzo : orderOf z = p := by
      rw [← orderOf_injective K.subtype K.subtype_injective z, hzc]
      exact hgo
    have := orderOf_dvd_natCard (⟨z, hz'⟩ : Subgroup.center K)
    rwa [Subgroup.orderOf_mk, hzo] at this
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore p
    (Subgroup.centralizer (K : Set Y)) (Subgroup.normal_centralizer (H := K)) hcop
  rw [h.core_eq_bot] at hle
  exact eq_bot_iff.2 hle

end ReducedNongeneration

section Covers


theorem p1OffCharNoInnerCube_of (hGA : GriessMultipliersAllModels)
    (hCov : P1OffCharCoverThreeNoInner) (hAS : P1OffCharAlmostSimple) : P1OffCharNoInnerCube := by
  intro p _ Y _ _ Rb Y₀ h hcat K hK huniq hnc hcent d hd hpd hno
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hnoK : ¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
    rintro ⟨E, hEK, hEa, hEc⟩
    obtain ⟨g, hg⟩ := exists_conj_le_sylow Rb hEa.2
    have hE'K : E.map (MulAut.conj g).toMonoidHom ≤ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hKn.conj_mem x (hEK hx) g
    refine hno ⟨E.map (MulAut.conj g).toMonoidHom, hg,
      hE'K.trans (Subgroup.normal_le_normalCore.2 le_sup_left),
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEa _, ?_, hE'K.trans le_sup_left⟩
    exact (Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm.trans
      hEc
  have hkill : ∀ E₁ : Subgroup K, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 3 → False :=
    fun E₁ hE₁a hE₁c => hnoK ⟨E₁.map K.subtype, by rintro _ ⟨x, -, rfl⟩; exact x.2,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁a K.subtype,
      (Nat.card_congr (E₁.equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm.trans
        hE₁c⟩
  by_cases hz : p ∣ Nat.card (Subgroup.center K)
  · by_contra hlist
    obtain ⟨e⟩ := hd
    by_cases hcl : IsClassicalIndex d.1
    · rcases classical_cover_cases hGA hK.2.2 d hcl e hp hp2 hpd hz with
        ⟨r, q, hdr, hpr, hpq⟩ | ⟨r, q, hdr, hpr, hpq⟩
      · by_cases hr : r = 2
        · subst hr
          obtain rfl : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpr
          exact hlist (hCov Y Rb Y₀ h hcat K hK huniq hnc hcent d (Or.inl ⟨q, hdr, hpq⟩) ⟨e⟩ hpd
            hz hno)
        · obtain ⟨dd, hv⟩ := d
          simp only at hdr
          subst hdr
          have hr1 : 1 ≤ r :=
            ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
              ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
          obtain ⟨E₁, hE₁a, hE₁c, -⟩ := exists_hyperGen_cover_linear
            (four_le_of_dvd_succ hp hp2 hr1 hr hpr) q hv hp hp2 hpq hK.2.2 e
          exact hkill E₁ hE₁a hE₁c
      · by_cases hr : r = 2
        · subst hr
          obtain rfl : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpr
          exact hlist (hCov Y Rb Y₀ h hcat K hK huniq hnc hcent d (Or.inr ⟨q, hdr, hpq⟩) ⟨e⟩ hpd
            hz hno)
        · obtain ⟨dd, hv⟩ := d
          simp only at hdr
          subst hdr
          have hr2 : 2 ≤ r :=
            ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
              ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
          obtain ⟨E₁, hE₁a, hE₁c, -⟩ :=
            hyperExCoverUnitary r q hv p hp hp2 hpq (by omega) hlist K hK.2.2 ⟨e⟩
          exact hkill E₁ hE₁a hE₁c
    · obtain ⟨E₁, hE₁a, hE₁c, -⟩ := hyperExCoverFor_exc hGA p hp hp2 K hK.2.2 d hcl ⟨e⟩ hpd hlist hz
      exact hkill E₁ hE₁a hE₁c
  · exact hAS p Y Rb Y₀ h hcat K hK huniq hnc (h.centralizer_eq_bot hKn hcent hz) hnoK d hd hpd

end Covers

section Cubes


theorem p1ThreeLieOffChar_of_cubesV9 (hX : ExcCubeResidualsV4) (hGA : GriessMultipliersAllModels)
    (h3 : P1OffCharCoverThree) (hCov : P1OffCharCoverThreeNoInner)
    (hAS : P1OffCharAlmostSimple) : P1ThreeLieOffChar :=
  p1ThreeLieOffChar_of_cubesV8 hX hGA h3 (p1OffCharNoInnerCube_of hGA hCov hAS)

end Cubes

end CFSG.AGLEmbedding
