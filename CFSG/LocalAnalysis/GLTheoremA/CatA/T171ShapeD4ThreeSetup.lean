module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcSmallD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151ExcDefs
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


private theorem inner_of_d4ExitAt_model {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    (hshape : ¬ I171.I171LieShapeAt 3 L) (hin : InducesInnerMod 3 L b)
    {M : Type} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥) (eM : PSimple 3 L ≃* M)
    (hExit : F151.D4ExitAt M 3)
    (hCatJ : catalogIs (PSimple 3 J) (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2))
    (hmem : MI.indAut 3 J b hS.b_norm ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple 3 J)) :
    InducesInnerMod 3 J b := by
  obtain ⟨x, w, Kc, hw, e, hx1, hxp, hwp, hxw, hKc, heq⟩ :=
    exists_model_component hS hshape hin hZ eM
  have hCat : catalogIs (↥Kc ⧸ Subgroup.center ↥Kc) (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) := by
    obtain ⟨j, hj, ⟨f⟩⟩ := hCatJ
    exact ⟨j, hj, ⟨e.symm.trans f⟩⟩
  have hmem' : centerQuotientHom ↥Kc
      (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (↥Kc ⧸ Subgroup.center ↥Kc) := by
    rw [← heq]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).2 hmem
  have hinner : centerQuotientHom ↥Kc
      (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (↥Kc ⧸ Subgroup.center ↥Kc) :=
    hExit x w hx1 hxp hwp hxw Kc hKc hCat hw hmem'
  have huniv : MulAut.congr e (MI.indAut 3 J b hS.b_norm) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (↥Kc ⧸ Subgroup.center ↥Kc) := by
    rw [heq]
    exact hinner
  have hmemInn : MI.indAut 3 J b hS.b_norm ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 J) :=
    (CFSG.HardMathSupport.Dickson.Sec6.I923.congr_mem_inner_iff_of_equiv e _).1 huniv
  exact (MI.indAut_mem_inner_iff Nat.prime_three hS.pcomp hS.b_norm).1 hmemInn

private theorem inducesInnerMod_of_untwistedBridge {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G}
    (h : F151.ExcAdjD4Inner) (hS : Setup 3 L J A d b)
    (hshape : ¬ I171.I171LieShapeAt 3 L) (hin : InducesInnerMod 3 L b)
    (hCatJ : catalogIs (PSimple 3 J) (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2))
    (hmem : MI.indAut 3 J b hS.b_norm ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple 3 J))
    {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    {q : TauCeti.PrimePower} (hv : (c q).Valid)
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hq2 : q.p = 2)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hE6 : τ = .E6 → ¬ 3 ∣ q.card - 1)
    (eCat : PSimple 3 L ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) :
    InducesInnerMod 3 J b := by
  obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  letI := hKf
  letI := hKfin
  haveI : CharP K 2 := by rw [← hq2]; exact hKchar
  exact inner_of_d4ExitAt_model hS hshape hin center_adjointGroup_eq_bot (eCat.trans eAd)
    (h hτ K 3 Nat.prime_three (by norm_num) fun h6 _ => by simpa [hKcard] using hE6 h6)
    hCatJ hmem

theorem smallExitD4AtThree_untw_of (h : F151.ExcAdjD4Inner) :
    SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2 := by
  intro G _ _ L J A d b hS hcatL hshape hin hCatJ hmem
  obtain ⟨i₀, hi₀, ⟨eCat⟩⟩ := hcatL
  cases i₀ with
  | cyclic _ _ => exact absurd hi₀ (by simp [onLie])
  | alternating _ _ => exact absurd hi₀ (by simp [onLie])
  | sporadic _ => exact absurd hi₀ (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hPexc, hPchar⟩ := hi₀
    cases idx with
    | G2 q =>
      exact inducesInnerMod_of_untwistedBridge h hS hshape hin hCatJ hmem hv
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
        (by rw [← TauCeti.LieTypeIndex.characteristic_G2]; exact hPchar)
        (Or.inl rfl) (fun h => absurd h (by decide)) eCat
    | F4 q =>
      exact inducesInnerMod_of_untwistedBridge h hS hshape hin hCatJ hmem hv
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
        (by rw [← TauCeti.LieTypeIndex.characteristic_F4]; exact hPchar)
        (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide)) eCat
    | E6 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E6]; exact hPchar
      exact inducesInnerMod_of_untwistedBridge h hS hshape hin hCatJ hmem hv
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 hq2
        (Or.inr (Or.inr (Or.inl rfl)))
        (fun _ h3 => hshape ⟨.lie ⟨.E6 q, hv⟩, ⟨rfl, hq2, h3⟩, ⟨eCat⟩⟩) eCat
    | E7 q =>
      exact inducesInnerMod_of_untwistedBridge h hS hshape hin hCatJ hmem hv
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
        (by rw [← TauCeti.LieTypeIndex.characteristic_E7]; exact hPchar)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun h => absurd h (by decide)) eCat
    | E8 q =>
      exact inducesInnerMod_of_untwistedBridge h hS hshape hin hCatJ hmem hv
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
        (by rw [← TauCeti.LieTypeIndex.characteristic_E8]; exact hPchar)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (fun h => absurd h (by decide)) eCat
    | _ => exact hPexc.elim

theorem smallExitD4AtThree_twE6_of (h : F151.TwE6D4Inner) :
    SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2 := by
  intro G _ _ L J A d b hS hcatL hshape hin hCatJ hmem
  obtain ⟨i₀, hi₀, ⟨eCat⟩⟩ := hcatL
  cases i₀ with
  | cyclic _ _ => exact absurd hi₀ (by simp [onLie])
  | alternating _ _ => exact absurd hi₀ (by simp [onLie])
  | sporadic _ => exact absurd hi₀ (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hex, hPchar⟩ := hi₀
    cases idx with
    | twistedE6 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_twistedE6]
        exact hPchar
      obtain ⟨K, hKf, σ, hKcard, hσ, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
      letI := hKf
      haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; positivity)
      haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
      haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
      have hnot3 : ¬ 3 ∣ q.p ^ q.exponent + 1 := by
        intro h3
        refine hshape ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨rfl, hq2, ?_⟩, ⟨eCat⟩⟩
        rw [TauCeti.PrimePower.card_def]
        exact h3
      have hExit : F151.D4ExitAt ↥(twistedE6RootGroup K σ) 3 :=
        h q hq2 K σ hKcard hσ 3 Nat.prime_three (by norm_num) (fun _ => hnot3)
      exact inner_of_d4ExitAt_model hS hshape hin
        (center_graphFixedRootGroup_eq_bot σ.surjective) (eCat.trans eAd) hExit hCatJ hmem
    | _ => exact absurd hex (by
        obtain ⟨q', hq'⟩ := hex
        exact absurd hq' (by simp))

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
