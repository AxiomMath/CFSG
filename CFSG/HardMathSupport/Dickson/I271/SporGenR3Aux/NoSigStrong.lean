module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen CFSG.RankThree.PartTwo.Sec4
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP

section NoSig

theorem noSig_of_noSig_model {p : ℕ} {S X : Type*} [Group S] [Group X] (f : S ≃* X)
    (hK : ∀ R Y : Subgroup (MulAut X), IsElemAbelian p R → Nat.card R = p ^ 2 →
      ¬ p ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥)
    (hp : p.Prime) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hE9 : Nat.card E = p ^ 2) : NoSig p E := by
  intro T hTcop hET
  set g : MulAut S ≃* MulAut X := MulAut.congr f with hg
  have hR : IsElemAbelian p (E.map g.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _
  have hRcard : Nat.card (E.map g.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective g.injective]
    exact hE9
  have hY3 : ¬ p ∣ Nat.card (T.map g.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective g.injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hTcop
  have hRY : E.map g.toMonoidHom ≤
      Subgroup.normalizer ((T.map g.toMonoidHom : Subgroup _) : Set _) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.le_normalizer_map g.toMonoidHom (Subgroup.mem_map_of_mem _ (hET he))
  have := hK _ _ hR hRcard hY3 hRY
  rwa [Subgroup.map_eq_bot_iff_of_injective _ g.injective] at this

theorem sporStrong_of_noSig_model (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnot : ¬ SporadicOnePair s p)
    {X : Type} [Group X] (bX : X ≃* Spor s)
    (hK : ∀ R Y : Subgroup (MulAut X), IsElemAbelian p R → Nat.card R = p ^ 2 →
      ¬ p ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥)
    {C : Type} [Group C] (bC : C ≃* Spor s) (hOff : OffPair s C) : SporStrong s p := by
  intro Y _ _ K B hC hN hS
  obtain ⟨e⟩ := hS
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  have hperf : commutator ↥K = ⊤ := hq.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab := exists_noncomm_of_isQuasisimple hq
  have hcen : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) ≤ 2 := hOut _ hq.2 hnab s ⟨e⟩
  have hR : AutRankLe2 p (↥K ⧸ Subgroup.center ↥K) :=
    autRankLe2_of_offPair hp hp2 hnot hOff (e.trans bC.symm) hcen hout
  have hAel : IsElemAbelian p (imgB B K) := isElemAbelian_imgB hC.elem
  have hAcard : Nat.card (imgB B K) = autOrderIn B K := card_imgB hperf
  have hA2 : Nat.card (imgB B K) = p ^ 2 := le_antisymm (hR _ hAel) (hAcard ▸ hN.2)
  exact isStronglyBalancedIn_of_noSig hperf (noSig_of_noSig_model (e.trans bX.symm) hK hp hAel hA2)

end NoSig

end CFSG.HardMathSupport.Dickson.I271
