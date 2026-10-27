module

public import CFSG.LieType.OutStructureA1
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeF4

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial

theorem exists_fieldPart_adjointGroup_F4
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p₀ ^ f) {p : ℕ} (hp : p.Prime) :
    ∃ F : Subgroup (MulAut (adjointGroup Tag.F4 K)),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) ⊔ F).index ∧
      ∀ x : MulAut (adjointGroup Tag.F4 K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) ⊔ F := by
  classical
  by_cases hchar2 : p₀ = 2
  ·
    have hK2 : Nat.card K = 2 ^ f := by rw [← hchar2]; exact hK
    haveI hchar : CharP K 2 :=
      finite_field_prime_power_characteristic Nat.prime_two hf hK2
    haveI : CharP K ReeTag.F4.prime := hchar
    let φ : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K
    obtain ⟨hord, hNF, ⟨Θ, hΘform, -, hΘker⟩, -, -, -, -⟩ :=
      even_F4_exact_automorphism_normal_form hf K hK2
    have hordφ : orderOf φ = 2 * f := hord
    have hNF' : ∀ α : MulAut (adjointGroup Tag.F4 K),
        ∃! gk : adjointGroup Tag.F4 K × Fin (2 * f),
          α = MulAut.conj gk.1 * φ ^ (gk.2 : ℕ) := hNF
    have hΘform' : ∀ (α : MulAut (adjointGroup Tag.F4 K)) (g : adjointGroup Tag.F4 K)
        (k : ℕ), α = MulAut.conj g * φ ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f)) := hΘform
    have hΘker' : Θ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.F4 K) := hΘker
    let F : Subgroup (MulAut (adjointGroup Tag.F4 K)) := Subgroup.zpowers φ
    have hφ2f : φ ^ (2 * f) = 1 := by
      rw [← hordφ]
      exact pow_orderOf_eq_one φ
    have hfinord : IsOfFinOrder φ :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * f, by omega, hφ2f⟩
    have hsup : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) ⊔ F = ⊤ := by
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
    obtain ⟨-, Θ, hΘform, -, hΘker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp₀ hchar2 hf K hK .F4
        (Or.inl rfl)
    have hΘker' : Θ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.F4 K) := hΘker
    haveI : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp₀ K hK).2
    let E : (K ≃+* K) →* MulAut (adjointGroup Tag.F4 K) :=
      { toFun := fun σ => exactNormalAut Tag.F4 K 1 σ 0
        map_one' := exactNormalAut_one_one_zero
        map_mul' := fun σ σ' => (exactNormalAut_one_zero_mul σ σ').symm }
    have hΘE : ∀ σ : K ≃+* K, Θ (E σ) = σ := by
      intro σ
      refine hΘform (E σ) 1 σ ?_
      intro h
      show (exactNormalAut Tag.F4 K 1 σ 0 h : ModGL Tag.F4 K) =
        ((1 : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.F4 K) *
          (((1 : adjointGroup Tag.F4 K) : ModGL Tag.F4 K))⁻¹
      rw [Subgroup.coe_one, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one,
        mul_one]
    have hEinj : Function.Injective E := by
      intro σ σ' h
      have h' := congrArg Θ h
      simpa [hΘE] using h'
    let F : Subgroup (MulAut (adjointGroup Tag.F4 K)) :=
      (⊤ : Subgroup (K ≃+* K)).map E
    have hFcyc : IsCyclic ↥F := by
      have htop : IsCyclic ↥(⊤ : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
      exact (Subgroup.equivMapOfInjective (⊤ : Subgroup (K ≃+* K)) E hEinj).isCyclic.mp htop
    have hbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxF, hxI⟩ := hx
      obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hxF
      have h1 : σ = 1 := by
        have h2 : Θ (E σ) = 1 := by
          have h3 : E σ ∈ Θ.ker := hΘker'.symm ▸ hxI
          exact (MonoidHom.mem_ker).mp h3
        rwa [hΘE] at h2
      rw [Subgroup.mem_bot, h1, map_one]
    have hsup : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) ⊔ F = ⊤ := by
      refine le_antisymm le_top ?_
      intro α _
      have hmem : α * (E (Θ α))⁻¹ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 K) := by
        rw [← hΘker', MonoidHom.mem_ker, map_mul, map_inv, hΘE, mul_inv_cancel]
      have hEtop : E (Θ α) ∈ F := Subgroup.mem_map_of_mem E (by trivial)
      have hα : α = (α * (E (Θ α))⁻¹) * E (Θ α) :=
        (inv_mul_cancel_right α (E (Θ α))).symm
      rw [hα]
      exact Subgroup.mul_mem_sup hmem hEtop
    refine ⟨F, ?_, hFcyc, hbot, ?_, ?_⟩
    · rw [hsup]; exact Subgroup.normal_top
    · rw [hsup, Subgroup.index_top]; exact hp.not_dvd_one
    · rw [hsup]; intro x _; exact trivial

theorem i713ClauseFor_lie_F4
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group .F4
      q.p q.exponent := by
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
      GaloisField.card q.p q.exponent q.exponent_pos.ne'
    have hqcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
      hcard.trans (TauCeti.PrimePower.card_def q).symm
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_F4 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .F4 hm.2
  letI := hLfield
  letI := hLfin
  haveI : Finite (adjointGroup Tag.F4 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_F4 q.prime_p q.exponent_pos L hLcard hp)))

end CFSG.LieType.OutStructure
