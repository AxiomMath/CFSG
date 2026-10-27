module

public import CFSG.LieType.OutStructureA1
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE8

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem exists_fieldPart_adjointGroup_E78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p₀ ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ F : Subgroup (MulAut (adjointGroup τ K)),
      (inner (adjointGroup τ K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (adjointGroup τ K) = ⊥ ∧
      ¬ p ∣ (inner (adjointGroup τ K) ⊔ F).index ∧
      ∀ x : MulAut (adjointGroup τ K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (adjointGroup τ K) ⊔ F := by
  classical
  set I : Subgroup (MulAut (adjointGroup τ K)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K)
  have hE1 : exactE τ = 1 := by
    rcases hτ with rfl | rfl <;> rfl
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨Θ, hΘsurj, hΘform, hΘker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions τ hτ' K
  let Θ₁ : MulAut (adjointGroup τ K) →* RingAut K :=
    (MonoidHom.fst (RingAut K) (Multiplicative (ZMod (exactE τ)))).comp Θ
  have hΘ₁surj : Function.Surjective Θ₁ := by
    intro σ
    obtain ⟨α, hα⟩ := hΘsurj (σ, 1)
    exact ⟨α, by simp [Θ₁, hα]⟩
  have hIker : I ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    rw [hΘker]
    refine ⟨g, 1, fun h => ?_⟩
    rw [MulAut.conj_apply, rootDiagUnit_one]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_one, inv_one]
  let E : RingAut K →* MulAut (adjointGroup τ K) :=
    { toFun := fun σ => exactNormalAut τ K 1 σ 0
      map_one' := exactNormalAut_one_one_zero
      map_mul' := fun σ σ' => (exactNormalAut_one_zero_mul σ σ').symm }
  have hΘE : ∀ σ : RingAut K, Θ₁ (E σ) = σ := by
    intro σ
    let ε : Fin (exactE τ) := ⟨0, by omega⟩
    have hε0 : (ε : ℕ) = 0 := rfl
    have hform : ∀ h : adjointGroup τ K,
        (E σ h : ModGL τ K) =
          ((1 : adjointGroup τ K) : ModGL τ K) *
            rootDiagUnit τ (1 : Fin τ.rank → Kˣ) * exactQ τ K ε *
            Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
            (exactQ τ K ε)⁻¹ * (rootDiagUnit τ (1 : Fin τ.rank → Kˣ))⁻¹ *
            (((1 : adjointGroup τ K)) : ModGL τ K)⁻¹ := by
      intro h
      change (exactNormalAut τ K 1 σ 0 h : ModGL τ K) = _
      rw [coe_exactNormalAut_zero]
      simp only [Subgroup.coe_one, rootDiagUnit_one, hε0, exactQ_zero, mul_one, inv_one]
    have h := hΘform (E σ) 1 1 σ ε hform
    exact congrArg Prod.fst h
  have hEinj : Function.Injective E := by
    intro σ σ' h
    have := congrArg Θ₁ h
    simpa [hΘE] using this
  have hcycAut : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hp₀ K hK).2
  haveI : IsCyclic (RingAut K) := hcycAut
  have hcardAut : Nat.card (RingAut K) = f := (card_ringAut_and_isCyclic hp₀ K hK).1
  let F : Subgroup (MulAut (adjointGroup τ K)) :=
    (⊤ : Subgroup (RingAut K)).map E
  have hFcyc : IsCyclic ↥F := by
    have htop : IsCyclic ↥(⊤ : Subgroup (RingAut K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (⊤ : Subgroup (RingAut K)) E hEinj).isCyclic.mp htop
  have hbot : F ⊓ I = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.1 hxF
    have hker : E σ ∈ Θ.ker := hIker hxI
    have h1 : Θ₁ (E σ) = 1 := by
      have := MonoidHom.mem_ker.1 hker
      simpa [Θ₁] using congrArg Prod.fst this
    rw [hΘE] at h1
    rw [Subgroup.mem_bot, h1, map_one]
  let π : MulAut (adjointGroup τ K) →* Outer (adjointGroup τ K) :=
    QuotientGroup.mk' (I)
  have hπker : π.ker = I := QuotientGroup.ker_mk' _
  have hcomp_inj : Function.Injective (π.comp E) := by
    intro σ σ' h
    have hmem : E σ * (E σ')⁻¹ ∈ I := by
      have h1 : π (E σ * (E σ')⁻¹) = 1 := by
        have h' : π (E σ) = π (E σ') := h
        rw [map_mul, map_inv, h', mul_inv_cancel]
      have hmem' : E σ * (E σ')⁻¹ ∈ π.ker := MonoidHom.mem_ker.2 h1
      rwa [hπker] at hmem'
    have hmem' : E (σ * σ'⁻¹) ∈ I := by
      rw [map_mul, map_inv]
      exact hmem
    have hker : E (σ * σ'⁻¹) ∈ Θ.ker := hIker hmem'
    have h1 : Θ₁ (E (σ * σ'⁻¹)) = 1 := by
      have := MonoidHom.mem_ker.1 hker
      simpa [Θ₁] using congrArg Prod.fst this
    rw [hΘE] at h1
    exact mul_inv_eq_one.mp h1
  have hcardF : Nat.card F = f := by
    rw [show F = (⊤ : Subgroup (RingAut K)).map E from rfl,
      Subgroup.card_map_of_injective hEinj, Subgroup.card_top, hcardAut]
  have hcardImage : Nat.card (F.map π) = Nat.card F := by
    rw [show F = (⊤ : Subgroup (RingAut K)).map E from rfl, Subgroup.map_map,
      Subgroup.card_map_of_injective hcomp_inj, Subgroup.card_top, hcardAut, hcardF]
  let H : Subgroup (MulAut (adjointGroup τ K)) := I ⊔ F
  have hrelH : (I).relIndex H = Nat.card F := by
    rw [show H = I ⊔ F from rfl, Subgroup.relIndex_sup_left,
      ← hπker, Subgroup.relIndex_ker]
    exact hcardImage
  have hHmul : Nat.card F * H.index = Nat.card (Outer (adjointGroup τ K)) := by
    have hmul := Subgroup.relIndex_mul_index
      (show I ≤ H from le_sup_left)
    rw [hrelH] at hmul
    simpa [I, Subgroup.index_eq_card] using hmul
  obtain ⟨Φ, hΦsurj, -, hΦdvd⟩ := exists_outer_hom_E (K := K) hτ'
  have hcardE : Nat.card (Multiplicative (ZMod (exactE τ))) = 1 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hE1]
  have hOut_eq : Nat.card (Outer (adjointGroup τ K)) = Nat.card Φ.ker * f := by
    have h := Subgroup.card_mul_index Φ.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj, Subgroup.card_top,
      Nat.card_prod, hcardAut, hcardE, mul_one] at h
    exact h.symm
  have hOut_dvd : Nat.card (Outer (adjointGroup τ K)) ∣ τ.cartan.det.natAbs * f := by
    rw [hOut_eq]
    exact Nat.mul_dvd_mul_right hΦdvd f
  have hHdvdDet : H.index ∣ τ.cartan.det.natAbs := by
    have h : Nat.card F * H.index ∣ τ.cartan.det.natAbs * f := by
      rwa [← hHmul] at hOut_dvd
    rw [hcardF] at h
    have h' : f * H.index ∣ f * τ.cartan.det.natAbs := by
      rwa [mul_comm (τ.cartan.det.natAbs) f] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h'
  have hdet2 : τ.cartan.det.natAbs ∣ 2 := by
    rcases hτ with rfl | rfl
    · rw [det_cartan_E7]
      norm_num
    · rw [det_cartan_E8]
      norm_num
  have hHdvd2 : H.index ∣ 2 := hHdvdDet.trans hdet2
  have hHnormal : H.Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hHdvd2 with h1 | h2
    · exact Subgroup.normal_of_index_eq_one h1
    · exact Subgroup.normal_of_index_eq_two h2
  have hpIndex : ¬ p ∣ H.index := by
    intro hpd
    have hp2d : p ∣ 2 := hpd.trans hHdvd2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2d)
  have hcover : ∀ x : MulAut (adjointGroup τ K),
      (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ H := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    haveI : H.Normal := hHnormal
    have hπx : QuotientGroup.mk' H x = 1 := by
      have hpow : (QuotientGroup.mk' H x) ^ (p ^ k) = 1 := by
        rw [← map_pow, hk, map_one]
      have hord_pow : orderOf (QuotientGroup.mk' H x) ∣ p ^ k :=
        orderOf_dvd_of_pow_eq_one hpow
      have hord_idx : orderOf (QuotientGroup.mk' H x) ∣ H.index := by
        simpa [Subgroup.index_eq_card] using orderOf_dvd_natCard (QuotientGroup.mk' H x)
      have hcop : Nat.Coprime (p ^ k) H.index :=
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpIndex).pow_left k
      have hone : orderOf (QuotientGroup.mk' H x) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hord_pow hord_idx
      exact orderOf_eq_one_iff.mp hone
    exact (QuotientGroup.eq_one_iff x).mp hπx
  refine ⟨F, ?_, hFcyc, ?_, ?_, ?_⟩
  · simpa [H, I] using hHnormal
  · simpa [I] using hbot
  · simpa [H, I] using hpIndex
  · intro x hx
    simpa [H, I] using hcover x hx

theorem exists_fieldPart_adjointGroup_E7
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p₀ ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ F : Subgroup (MulAut (adjointGroup Tag.E7 K)),
      (inner (adjointGroup Tag.E7 K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (adjointGroup Tag.E7 K) = ⊥ ∧
      ¬ p ∣ (inner (adjointGroup Tag.E7 K) ⊔ F).index ∧
      ∀ x : MulAut (adjointGroup Tag.E7 K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (adjointGroup Tag.E7 K) ⊔ F :=
  exists_fieldPart_adjointGroup_E78 (τ := .E7) (Or.inl rfl) hp₀ hf K hK hp hp2

theorem exists_fieldPart_adjointGroup_E8
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p₀ ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ F : Subgroup (MulAut (adjointGroup Tag.E8 K)),
      (inner (adjointGroup Tag.E8 K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (adjointGroup Tag.E8 K) = ⊥ ∧
      ¬ p ∣ (inner (adjointGroup Tag.E8 K) ⊔ F).index ∧
      ∀ x : MulAut (adjointGroup Tag.E8 K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (adjointGroup Tag.E8 K) ⊔ F :=
  exists_fieldPart_adjointGroup_E78 (τ := .E8) (Or.inr rfl) hp₀ hf K hK hp hp2

theorem i713ClauseFor_lie_E7
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hqcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    hcard.trans (TauCeti.PrimePower.card_def q).symm
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group .E7
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_E7 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .E7 hm.2
  letI := hLfield
  letI := hLfin
  haveI : Finite (adjointGroup Tag.E7 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_E7 q.prime_p q.exponent_pos L hLcard hp hp2)))

theorem i713ClauseFor_lie_E8
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hqcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    hcard.trans (TauCeti.PrimePower.card_def q).symm
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group .E8
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_E8 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .E8 hm.2
  letI := hLfield
  letI := hLfin
  haveI : Finite (adjointGroup Tag.E8 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_E8 q.prime_p q.exponent_pos L hLcard hp hp2)))

end CFSG.LieType.OutStructure
