module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Unit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.SP
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.Open
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 renaming fixSub → fixSubO

set_option linter.unusedSectionVars false


theorem a2MinusCompsWith_holds {P : (X : Type) → [Group X] → Prop} (hP : IsComponentProperty P)
    {p f : ℕ}
    (hPquot : ∀ {F : Type} [Field F] [Finite F], Nat.card F = (p ^ f) ^ 2 →
      ∀ {Q : Type} [Group Q] [Finite Q] (g : ↥(StatedSU 3 (p ^ f) F) →* Q),
        Function.Surjective g → g.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F) → P Q) :
    A2MinusCompsWith P p f := by
  intro hp hp2 hp3 hf hq K _ _ hK σ hσ s hs
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, _, _, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  have hq5 : 5 ≤ p ^ f :=
    hp5.trans (Nat.le_self_pow (by omega) p)
  have hcore := compsWith_unitary_core hp2 hf hq hq5 hK₄ hσ₄ hε hb3 hb1 hs₄ hPquot
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have h1 : CompsWith P ↥(fixSubO (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) :=
    CompsWith.of_mulEquiv hP e hcore
  exact CompsWith.of_mulEquiv hP (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup _)) h1

theorem a2MinusComps_holds : A2MinusComps := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ s hs
  rw [compsFine_iff_compsWith]
  refine a2MinusCompsWith_holds (isComponentProperty_componentFactor p) ?_ hp hp2 hp3 hf hq hK hσ
    (s := s) hs
  intro F _ _ hF Q _ _ g hg hk
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = (p ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F p := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [hFc, ← pow_mul, mul_comm])
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  have hq5 : 5 ≤ p ^ f := hp5.trans (Nat.le_self_pow (by omega) p)
  exact componentFactor_statedSU_of_surjective hp hF hq5 g hg hk

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
