module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
import CFSG.HardMathSupport.Timmesfeld.LangTorus.SubnormalTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUTorus
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDProved
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE


theorem exists_perfect_of_twistedE6_langFrame_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : ¬ 3 ∣ ℓ ^ f) (hq4 : 4 ≤ ℓ ^ f)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {w' : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
    (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) (ha3 : ∀ i, a i ^ 3 = 1)
    (hT : rootDiagUnit TwistTag.E6.tag a ∈ twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
      (twistHom TwistTag.E6 (AlgebraicClosure K) Fr))
    (ha1 : rootDiagUnit TwistTag.E6.tag a ≠ 1) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (hχ : rootChar a β = 1) (g₁ : ↥(twistedE6InndiagGL K σ))
    (hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (g₁ : ModGL TwistTag.E6.tag K) * g0 = rootDiagUnit TwistTag.E6.tag a) :
    ∃ P : Subgroup (twistedE6RootGroup K σ), P ≤ fixSubgroup (twistedE6InndiagConj K σ g₁) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι : K →+* L := algebraMap K L with hι
  let DL : LangDatum TwistTag.E6.tag L :=
    LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr w' hg0C hg0
  have hΦ : DL.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hfin := finite_model_twistedE6 hℓ hf hK hσ hFr DL hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L DL
  have hqpow : IsPrimePow DL.q ∧ ((DL.q : ℕ) : L) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), ?_⟩
    change ((ℓ ^ f : ℕ) : L) = 0
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  let S : LangSetup TwistTag.E6.tag L 3 :=
    DL.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow h3 hfin
  set φ : twistedE6RootGroup K σ ≃* S.Γ := twistedE6EquivΓ hℓ hf hK hσ hFr DL hΦ with hφdef
  have hφ : ∀ h : twistedE6RootGroup K σ, ((φ h : S.Γ) : ModGL TwistTag.E6.tag L) =
      g0⁻¹ * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * g0 :=
    fun h => coe_twistedE6EquivΓ hℓ hf hK hσ hFr DL hΦ h
  have hd3 : rootDiagUnit TwistTag.E6.tag a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun i => by simpa using ha3 i
    rw [this, rootDiagUnit_one]
  have hk : β ∈ kernelRoots (rootCharHom a) := ⟨hβ, hχ⟩
  let i : KernelComponent (rootCharHom a) := ⟦⟨β, hk⟩⟧
  obtain ⟨hRC, hRsn⟩ := langSubnormal_provedT TwistTag.E6.tag L 3 S a hT hd3 ha1 i
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hRdef
  have hRΓ : R ≤ S.Γ := hRC.trans inf_le_left
  have hbig : ¬ Nat.Coprime 3 (Nat.card R) := threeBigComponents_holds TwistTag.E6.tag L S a hT ha1 i
  have hq : CFSG.IsQuasisimple R := by
    cases hkind : twistKind S.ρ (rootCharHom a) i
    · exact langComponentsQuasisimple_inner_holdsT TwistTag.E6.tag L 3 S a hT hd3 ha1 i hkind hbig
    · exact langComponentsQuasisimpleT_suN_proved TwistTag.E6.tag L 3 S a hT hd3 ha1 i hkind hbig
    · exact langComponentsQuasisimpleT_twoD_proved TwistTag.E6.tag L 3 S a hT hd3 ha1 i hkind hbig
    · exact langComponentsQuasisimple_exc_provedT TwistTag.E6.tag L 3 S a hT hd3 ha1 i hkind hbig
  let ψ : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype)
  have hψ : ∀ y : twistedE6RootGroup K σ,
      ψ y = g0⁻¹ * baseChangeGL ι (y : ModGL TwistTag.E6.tag K) * g0 := fun y => by
    change (MulAut.conj g0⁻¹) (baseChangeGL ι (y : ModGL TwistTag.E6.tag K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective ι).comp Subtype.val_injective)
  have hRrange : R ≤ ψ.range := by
    intro r hr
    obtain ⟨y, hy⟩ := φ.surjective ⟨r, hRΓ hr⟩
    refine ⟨y, ?_⟩
    rw [hψ, ← hφ, hy]
  have hRperf : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥R := hq.1
    exact Subgroup.commutator_eq_self
  have hRcent : R ≤ Subgroup.centralizer ({rootDiagUnit TwistTag.E6.tag a} :
      Set (ModGL TwistTag.E6.tag L)) := fun r hr => (Subgroup.mem_inf.1 (hRC hr)).2
  refine ⟨R.comap ψ, ?_, ?_, ?_⟩
  · intro y hy
    rw [mem_fixSubgroup]
    apply hψinj
    have hyR : ψ y ∈ R := hy
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (hRcent hyR)
    rw [← hg₁, hψ y] at hcomm
    set G₁ := baseChangeGL ι (g₁ : ModGL TwistTag.E6.tag K) with hG₁
    set Y := baseChangeGL ι (y : ModGL TwistTag.E6.tag K) with hY
    have h1 : G₁ * Y = Y * G₁ := by
      calc G₁ * Y = g0 * (g0⁻¹ * G₁ * g0 * (g0⁻¹ * Y * g0)) * g0⁻¹ := by group
        _ = g0 * (g0⁻¹ * Y * g0 * (g0⁻¹ * G₁ * g0)) * g0⁻¹ := by rw [hcomm]
        _ = Y * G₁ := by group
    rw [hψ, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv, ← hG₁, ← hY, hψ, ← hY]
    calc g0⁻¹ * (G₁ * Y * G₁⁻¹) * g0 = g0⁻¹ * (Y * G₁ * G₁⁻¹) * g0 := by rw [h1]
      _ = g0⁻¹ * Y * g0 := by group
  · apply Subgroup.map_injective hψinj
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hRrange, hRperf]
  · have hcard : Nat.card (R.comap ψ) = Nat.card R := by
      rw [← Subgroup.card_map_of_injective hψinj (K := R.comap ψ),
        Subgroup.map_comap_eq_self hRrange]
    rw [hcard]
    exact (Nat.Prime.dvd_iff_not_coprime Nat.prime_three).2 hbig

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
