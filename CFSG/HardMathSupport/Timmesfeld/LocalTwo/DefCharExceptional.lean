module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharClassical
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterTwisted
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterReeG2

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.HardMathSupport.Timmesfeld.DefChar
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

section E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Open

theorem exists_inner_of_bridge_E_lt {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (S : Type) [Group S]
    (e0 : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p = q.p) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D)
    (hlt : p < Nat.card D) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hq2 : q.p ≠ 2 := hpq ▸ hp2
  obtain ⟨eB⟩ := hbr q hv hq2 (GaloisField q.p q.exponent)
    (by rw [hKq]; simp [TauCeti.PrimePower.card_def])
  let e : S ≃* adjointGroup τ (GaloisField q.p q.exponent) :=
    e0.trans (eB.symm.trans adjointEquivQuotient.symm)
  have hndvd : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    intro h
    have h1 : p ∣ q.p ^ q.exponent := by
      rw [hpq]; exact dvd_pow_self _ q.exponent_pos.ne'
    rw [hKq] at h
    have h2 : p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h1 h
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    rw [Nat.sub_sub_self hpos] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_adjointE hτ hp hp2 hndvd D' hexp hc

theorem defCharOuterRankTwoFamE6 : DefCharOuterRankTwoFam .E6 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inl rfl) CFSG.TauCetiBridge.chevalleyBridges.e6 q hv S e0
    hp (ne_two_of_five_lt hp5) hpq D hD (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem defCharOuterRankTwoFamE7 : DefCharOuterRankTwoFam .E7 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inr (Or.inl rfl))
    CFSG.TauCetiBridge.chevalleyBridges.e7 q hv S e0 hp (ne_two_of_five_lt hp5) hpq D hD
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem defCharOuterRankTwoFamE8 : DefCharOuterRankTwoFam .E8 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inr (Or.inr rfl))
    CFSG.TauCetiBridge.chevalleyBridges.e8 q hv S e0 hp (ne_two_of_five_lt hp5) hpq D hD
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

end E

section F4G2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem defCharOuterRankTwoFamF4 : DefCharOuterRankTwoFam .F4 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := ne_two_of_five_lt hp5
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv K hK'
  let e : S ≃* adjointGroup .F4 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
    q.exponent_pos K hK .F4 (Or.inl rfl)
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  exact exists_inner_of_cyclic_quotient e Θ hker hp D hD.2
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem defCharOuterRankTwoFamG2 : DefCharOuterRankTwoFam .G2 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := ne_two_of_five_lt hp5
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : S ≃* adjointGroup .G2 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  have hlt : q.p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  have h3 : q.p ≠ 3 := by omega
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
    q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  exact exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt

end F4G2

section Twisted

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem defCharOuterRankTwoFamTrialityD4 : DefCharOuterRankTwoFam .trialityD4 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := ne_two_of_five_lt hp5
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  subst hpq
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, -, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hp2 hf K hK3 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx _ => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact this)
      D' hexp hc)

theorem defCharOuterRankTwoFamTwistedE6 : DefCharOuterRankTwoFam .twistedE6 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := ne_two_of_five_lt hp5
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  subst hpq
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hpK : ¬ q.p ∣ Nat.card K - 1 := by
    intro h
    have h1 : q.p ∣ Nat.card K := by
      rw [hK2]; exact dvd_pow (dvd_pow_self _ q.exponent_pos.ne') (by norm_num)
    have hpos : 1 ≤ Nat.card K := Nat.card_pos
    have h2 := (Nat.dvd_add_right h).1 (by rwa [Nat.sub_add_cancel hpos])
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx hxp => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact mem_inner_of_mem_inn_sup_diag_E6 σ hp hpK this hxp)
      D' hexp hc)

end Twisted

section Ree

open CFSG.Open CFSG.Blueprint
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ
  exists_eq_conj_mul_frobeniusΓ_pow)

theorem defCharOuterRankTwoFamReeG2 : DefCharOuterRankTwoFam .reeG2 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨d, hv⟩ := idx
  obtain ⟨m, rfl⟩ := hidx
  obtain ⟨e0⟩ := hS
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    ((e0.trans b.symm).trans e1).trans E
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_elemAbelian_of_outerCyclic
      (frobeniusΓ : MulAut (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m))
      (exists_eq_conj_mul_frobeniusΓ_pow hm1 hK) hp D' hexp hc)

end Ree

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
