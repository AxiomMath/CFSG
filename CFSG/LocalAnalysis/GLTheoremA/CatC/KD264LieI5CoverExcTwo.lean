module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.LieType.SemisimpleCentralizers.HeldLangUnitFix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LieType.SemisimpleCentralizers.HeldLang

section Certificates

theorem false_of_outer_three_twistedE6_two (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq2 : q.card = 2) {X : Type} [Group X]
    (eX : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hd⟩).Group) (γ : MulAut X) (hγ3 : γ ^ 3 = 1)
    (hout : γ ∉ innAutDerived X) : False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqc : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq2
  set F := GaloisField q.p (2 * q.exponent) with hF
  have hF2 : Nat.card F = q.card ^ 2 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  have hFt : Nat.card F = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := hF2
  let σ : F →+* F := iterateFrobenius F q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact iterateFrobenius_def q.p q.exponent x
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hd F hFt σ hσ
  have hTw : TwistedChevalleyModel X .E6 (q.p ^ q.exponent) :=
    ⟨F, inferInstance, inferInstance, by rw [hF2, TauCeti.PrimePower.card_def]; rfl, σ,
      fun x => by rw [hσ x, TauCeti.PrimePower.card_def], ⟨eX.trans b.symm⟩⟩
  have hE : ChevalleyExceptionalModel X .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, hTw⟩
  obtain ⟨K₂, _, _, σ₂, hK₂, hσ₂, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv q.prime_p q.exponent_pos hTw
  have hC := commutator_twistedE6RootGroup hE σ₂ e
  let ψ : MulAut (twistedE6RootGroup K₂ σ₂) := MulAut.congr e.symm γ
  have hψ3 : ψ ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K₂ hK₂ σ₂ hσ₂
  have hΘ3 : (Θ ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hK2e : Nat.card K₂ = 2 ^ 2 := by rw [hK₂, hqc]
  have hΘ2 : orderOf (Θ ψ) ∣ 2 := orderOf_dvd_of_card Nat.prime_two (by norm_num) hK2e (Θ ψ)
  have hΘ1 : Θ ψ = 1 := by
    have h3 : orderOf (Θ ψ) ∣ 3 := orderOf_dvd_of_pow_eq_one hΘ3
    have h1 : orderOf (Θ ψ) ∣ Nat.gcd 2 3 := Nat.dvd_gcd hΘ2 h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h1))
  have hψmem : ψ ∈ twistedE6Inn K₂ σ₂ ⊔ twistedE6Diag K₂ σ₂ := by
    rw [← hker]
    exact MonoidHom.mem_ker.2 hΘ1
  have hcomm := twistedE6Inndiag_le_commutator σ₂ hK₂ hσ₂ hC hψmem
  have h1 : ψ ∈ innAutDerived (twistedE6RootGroup K₂ σ₂) := commutator_le_innAutDerived _ hcomm
  have h2 : MulAut.congr e ψ ∈ innAutDerived X := (mem_innAutDerived_congr e).2 h1
  apply hout
  have h3 : MulAut.congr e ψ = γ := by
    refine MulEquiv.ext fun x => ?_
    simp [ψ, MulAut.congr_apply]
  rwa [h3] at h2

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
