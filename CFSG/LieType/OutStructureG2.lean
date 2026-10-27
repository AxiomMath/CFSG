module

public import CFSG.LieType.OutStructureA1
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog

theorem exists_fieldPart_adjointGroup_G2
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p₀ ^ f) (h3 : 3 ≤ p₀ ^ f) {p : ℕ} (hp : p.Prime) :
    ∃ F : Subgroup (MulAut (adjointGroup Tag.G2 K)),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) ⊔ F).index ∧
      ∀ x : MulAut (adjointGroup Tag.G2 K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) ⊔ F := by
  classical
  by_cases hchar3 : p₀ = 3
  ·
    have hK3 : Nat.card K = 3 ^ f := by rw [← hchar3]; exact hK
    haveI hchar : CharP K 3 :=
      finite_field_prime_power_characteristic Nat.prime_three hf hK3
    haveI : CharP K ReeTag.G2.prime := hchar
    let φ : MulAut (adjointGroup Tag.G2 K) := ReeTag.G2.finiteExceptionalAut K
    obtain ⟨hord, hNF, ⟨Θ, hΘform, -, hΘker⟩, -⟩ :=
      G2_three_exact_automorphism_normal_form hf K hK3
    have hordφ : orderOf φ = 2 * f := hord
    have hNF' : ∀ α : MulAut (adjointGroup Tag.G2 K),
        ∃! gk : adjointGroup Tag.G2 K × Fin (2 * f),
          α = MulAut.conj gk.1 * φ ^ (gk.2 : ℕ) := hNF
    have hΘform' : ∀ (α : MulAut (adjointGroup Tag.G2 K)) (g : adjointGroup Tag.G2 K)
        (k : ℕ), α = MulAut.conj g * φ ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f)) := hΘform
    have hΘker' : Θ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.G2 K) := hΘker
    let F : Subgroup (MulAut (adjointGroup Tag.G2 K)) := Subgroup.zpowers φ
    have hφ2f : φ ^ (2 * f) = 1 := by
      rw [← hordφ]
      exact pow_orderOf_eq_one φ
    have hfinord : IsOfFinOrder φ :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * f, by omega, hφ2f⟩
    have hsup : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) ⊔ F = ⊤ := by
      refine le_antisymm le_top ?_
      intro α _
      obtain ⟨⟨g, k⟩, hα, -⟩ := hNF' α
      rw [hα]
      exact Subgroup.mul_mem_sup ⟨g, rfl⟩ (Subgroup.npow_mem_zpowers φ (k : ℕ))
    refine ⟨F, ?_, Subgroup.isCyclic_zpowers φ, ?_, ?_, ?_⟩
    · rw [hsup]; exact Subgroup.normal_top
    ·
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxF, hxI⟩ := hx
      obtain ⟨k, hk⟩ :=
        (Submonoid.mem_powers_iff x φ).mp ((hfinord.mem_powers_iff_mem_zpowers).mpr hxF)
      rw [← hk] at hxI
      rw [Subgroup.mem_bot, ← hk]
      have hz : Θ (φ ^ k) = 1 := by
        have h1 : φ ^ k ∈ Θ.ker := hΘker'.symm ▸ hxI
        exact (MonoidHom.mem_ker).mp h1
      have hk0 : Θ (φ ^ k) = Multiplicative.ofAdd (k : ZMod (2 * f)) :=
        hΘform' (φ ^ k) 1 k (by rw [map_one, one_mul])
      rw [hk0] at hz
      have hdvd : 2 * f ∣ k :=
        (ZMod.natCast_eq_zero_iff k (2 * f)).mp (by
          simpa using congrArg Multiplicative.toAdd hz)
      obtain ⟨m, rfl⟩ := hdvd
      rw [pow_mul, hφ2f, one_pow]
    · rw [hsup, Subgroup.index_top]; exact hp.not_dvd_one
    · rw [hsup]; intro x _; exact trivial
  ·
    have hdata : ∃ Θ : MulAut (adjointGroup Tag.G2 K) →* (K ≃+* K),
        (∀ (α : MulAut (adjointGroup Tag.G2 K)) (g : adjointGroup Tag.G2 K) (σ : K ≃+* K),
          (∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
            Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) *
            (g : ModGL Tag.G2 K)⁻¹) → Θ α = σ) ∧
        Θ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) := by
      by_cases hp2 : p₀ = 2
      · have hK2 : Nat.card K = 2 ^ f := by rw [← hp2]; exact hK
        have hf2 : 2 ≤ f := by
          by_contra hlt
          have hf1 : f = 1 := by omega
          rw [hp2, hf1] at h3
          norm_num at h3
        obtain ⟨-, Θ, hΘform, -, hΘker, -⟩ :=
          even_G2_exact_automorphism_normal_form hf2 K hK2
        exact ⟨Θ, hΘform, hΘker⟩
      · obtain ⟨-, Θ, hΘform, -, hΘker, -⟩ :=
          odd_F4_and_nonexceptional_G2_automorphism_normal_form hp₀ hp2 hf K hK .G2
            (Or.inr ⟨rfl, hchar3⟩)
        exact ⟨Θ, hΘform, hΘker⟩
    obtain ⟨Θ, hΘform, hΘker⟩ := hdata
    haveI : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp₀ K hK).2
    let E : (K ≃+* K) →* MulAut (adjointGroup Tag.G2 K) :=
      { toFun := fun σ => exactNormalAut Tag.G2 K 1 σ 0
        map_one' := exactNormalAut_one_one_zero
        map_mul' := fun σ σ' => (exactNormalAut_one_zero_mul σ σ').symm }
    have hΘE : ∀ σ : K ≃+* K, Θ (E σ) = σ := by
      intro σ
      refine hΘform (E σ) 1 σ ?_
      intro h
      show (exactNormalAut Tag.G2 K 1 σ 0 h : ModGL Tag.G2 K) =
        ((1 : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) *
          (((1 : adjointGroup Tag.G2 K) : ModGL Tag.G2 K))⁻¹
      rw [Subgroup.coe_one, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one,
        mul_one]
    have hEinj : Function.Injective E := by
      intro σ σ' h
      have h' := congrArg Θ h
      simpa [hΘE] using h'
    let F : Subgroup (MulAut (adjointGroup Tag.G2 K)) :=
      (⊤ : Subgroup (K ≃+* K)).map E
    have hFcyc : IsCyclic ↥F := by
      have htop : IsCyclic ↥(⊤ : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
      exact (Subgroup.equivMapOfInjective (⊤ : Subgroup (K ≃+* K)) E hEinj).isCyclic.mp htop
    have hbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxF, hxI⟩ := hx
      obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hxF
      have h1 : σ = 1 := by
        have h2 : Θ (E σ) = 1 := by
          have h3 : E σ ∈ Θ.ker := hΘker.symm ▸ hxI
          exact (MonoidHom.mem_ker).mp h3
        rwa [hΘE] at h2
      rw [Subgroup.mem_bot, h1, map_one]
    have hsup : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) ⊔ F = ⊤ := by
      refine le_antisymm le_top ?_
      intro α _
      have hmem : α * (E (Θ α))⁻¹ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K) := by
        rw [← hΘker, MonoidHom.mem_ker, map_mul, map_inv, hΘE, mul_inv_cancel]
      have hEtop : E (Θ α) ∈ F := Subgroup.mem_map_of_mem E (by trivial)
      have hα : α = (α * (E (Θ α))⁻¹) * E (Θ α) :=
        (inv_mul_cancel_right α (E (Θ α))).symm
      rw [hα]
      exact Subgroup.mul_mem_sup hmem hEtop
    refine ⟨F, ?_, hFcyc, hbot, ?_, ?_⟩
    · rw [hsup]; exact Subgroup.normal_top
    · rw [hsup, Subgroup.index_top]; exact hp.not_dvd_one
    · rw [hsup]; intro x _; exact trivial

theorem i713ClauseFor_lie_G2
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    by_cases hq2 : q.p = 2
    · refine ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, ?_⟩
      exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 (MulEquiv.refl _)
    · exact CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv hq2
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .G2 hm.2
  letI := hLfield
  letI := hLfin
  haveI : Finite (adjointGroup Tag.G2 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_G2 q.prime_p q.exponent_pos L hLcard h3 hp)))

end CFSG.LieType.OutStructure
