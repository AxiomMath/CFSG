module

import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2KillCycle
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwE6ModelIndex
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus

section KillRoot

set_option linter.unusedSectionVars false


theorem d4t2KernelRootUnip_holds :
    ∀ {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀),
      (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹) → S.IsAlgebraic →
      ∀ {l f : ℕ}, l.Prime → 0 < f → S.D.q = l ^ f → l ≠ 3 →
      ∀ A : Subgroup (ModGL Tag.E6 L), A ≤ S.D.torus →
      ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
        (∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 b ∈ A → rootChar b γ = 1) →
        ∃ u ∈ S.Γ, u ≠ 1 ∧ u ^ l = 1 ∧ ∀ x ∈ A, x * u = u * x := by
  intro L _ _ p₀ S hS hAlg l f hl hf hq hl3 A hA γ hγ hkill
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : ((l : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  haveI : CharP L l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  have hdiag : ∀ x : A, ∃ b : Fin Tag.E6.rank → Lˣ,
      (x : ModGL Tag.E6 L) = rootDiagUnit .E6 b :=
    fun x => exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 (hA x.2)).1
  choose b hb using hdiag
  have hbT : ∀ x : A, rootDiagUnit .E6 (b x) ∈ S.D.torus := fun x => by
    rw [← hb x]
    exact hA x.2
  have hγK : γ ∈ familyKernel b :=
    ⟨hγ, fun x => hkill (b x) (by rw [← hb x]; exact x.2)⟩
  obtain ⟨u, huM, hu1, hul, hcomm⟩ :=
    exists_unip_centralizing_familyKernel (Or.inr (Or.inl rfl)) S hq b hbT hγK
  refine ⟨u, ?_, hu1, hul, fun x hx => ?_⟩
  ·
    obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
    cases t with
    | D4 => exact absurd ht (by decide)
    | E6 =>
      have hΦ' : S.D.Φ = twistHom TwistTag.E6 L Fr :=
        MonoidHom.ext fun g => (hΦ g).trans rfl
      obtain ⟨k, hk⟩ := twE6_model_pow_mem_Γ S hAlg Fr hFr hΦ'
      have hgcd : (3 ^ k).gcd (orderOf u) = 1 := by
        rw [orderOf_eq_prime hul hu1]
        exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_three hl).2 (Ne.symm hl3))
      exact (Subgroup.zpowers_le.2 (hk u huM)) (mem_zpowers_pow_iff.2 hgcd)
  · have h := hcomm ⟨x, hx⟩
    rw [← hb ⟨x, hx⟩] at h
    exact h.symm

end KillRoot

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
