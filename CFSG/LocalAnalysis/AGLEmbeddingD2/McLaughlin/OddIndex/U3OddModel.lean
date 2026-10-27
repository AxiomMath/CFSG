module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddMod4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddDefs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Assembly.LowTwoRank CFSG.Models TauCeti CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LinearGroups
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_mulEquiv_SU3 {K : Type} [Group K] {p f : ℕ}
    (h : StatedClassicalModel K .PSU 3 p f) (hq3 : (p ^ f) % 3 = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Fact p.Prime) (_ : CharP F p)
      (_ : Nat.card F = (p ^ f) ^ 2), Nonempty (K ≃* SU (unitaryInvolution F p f) 3) := by
  obtain ⟨hadm, F, hFfield, hFfin, hF, ⟨e1⟩⟩ := h
  let _ := hFfield
  have := hFfin
  have hp : p.Prime := hadm.1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2 * f)
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have hZ : (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ f) F) = ⊥ := by
    have hc := (unitary_scalar_kernel hp hF (n := 3) (by norm_num)).2.2
    have hcop : Nat.gcd 3 (p ^ f + 1) = 1 := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
      omega
    rw [hcop] at hc
    exact Subgroup.card_eq_one.1 hc
  have e2 : StatedProj (StatedSU 3 (p ^ f) F) ≃* StatedSU 3 (p ^ f) F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, hF,
    ⟨e1.trans (e2.trans (equivStatedSU hF 3).symm)⟩⟩

theorem overgroupL32Odd_of_u3OddCore
    (hU : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
      (hF : Nat.card F = (p ^ f) ^ 2), p ≠ 2 → (p ^ f) % 3 = 1 → U3OddCore F p f hF)
    (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hp2 : q.p ≠ 2) (hq3 : q.card % 3 = 1) (hd : d.1 = .twistedA 2 q)
    (e : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) : OvergroupL32Odd K := by
  obtain ⟨e⟩ := e
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have hmodel : StatedClassicalModel K .PSU 3 q.p q.exponent := by
    have := statedClassicalModel_of_lieModel' (by omega) (lieModel_twistedA 2 q hv e)
    rwa [hc, hf] at this
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨F, _, _, _, _, hF, ⟨e'⟩⟩ := exists_mulEquiv_SU3 hmodel (hq ▸ hq3)
  refine overgroupL32Odd_of_core e' ?_
  have hF3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h1 : (q.p ^ q.exponent) % 3 = 1 := hq ▸ hq3
    have h2 : (q.p ^ q.exponent) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h1]
    have h3 : 1 ≤ (q.p ^ q.exponent) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hF3
  have hcore := hU F q.p q.exponent hF hp2 (hq ▸ hq3) ω hω
  refine overgroupL32Core_of_A0 (A₀ := Subgroup.zpowers (tSU hF ω)) ?_ ?_
  · rw [Nat.card_zpowers, orderOf_injective (tSU hF) (tSU_injective hF) ω, hω]
  · intro W Y hNW hYW hAY hY
    exact hcore W Y hNW hYW hAY hY

theorem overgroupL32U3Odd_of_u3OddCore_mod4_three
    (hU : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
      (hF : Nat.card F = (p ^ f) ^ 2), p ≠ 2 → (p ^ f) % 3 = 1 → (p ^ f) % 4 = 3 →
        U3OddCore F p f hF) : OvergroupL32U3Odd := by
  intro K _ _ d q hp2 hq3 hd e
  refine overgroupL32Odd_of_u3OddCore ?_ K d q hp2 hq3 hd e
  intro F _ _ p f _ _ hF hp2' hq3'
  have hodd : (p ^ f) % 2 = 1 := by
    have : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2'
    exact Nat.odd_iff.1 (this.pow)
  by_cases h4 : (p ^ f) % 4 = 1
  · exact u3OddCore_of_mod4 hF hq3' h4
  · exact hU F p f hF hp2' hq3' (by omega)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
