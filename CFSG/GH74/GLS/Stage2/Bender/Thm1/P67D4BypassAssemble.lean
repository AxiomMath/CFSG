module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ToralStage
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4VNormal
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.OddAut.FixedCore
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutAssemble
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def D4BadCase : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ (V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z →
      N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z →
    ∀ (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom → v ≠ 1 →
      v ^ 3 = 1 → MulAut.conj v ∈ V →
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom →
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom →
      (δ = σ ∨ δ = σ⁻¹) →
      MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ ∈ V →
      (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v → False

open CFSG.GH74.GLS.Stage2.OddAut in
theorem d4_false_of_outer_three_q1_of_bad (hA2 : D4OuterThreeA2Toral) (hBad : D4BadCase)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  classical
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hVc : Nat.card V = 3 ^ 2 := h2.2.2.2.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVp : IsPGroup 3 V := IsPGroup.of_card hVc
  obtain ⟨β, hβ⟩ := d4_exists_conj_le_B0 hp hp2 hf K hK σ hσ hq V hVp
  let e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (β⁻¹ :
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  have hconjapply : ∀ x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      MulAut.congr e x = β⁻¹ * x * β := fun x =>
    MulEquiv.ext fun y => rfl
  have h2' := h2.map_mulEquiv (MulAut.congr e)
  have h3' := N3Full.map_mulEquiv e h3
  have hmemV' : ∀ x' ∈ V.map (MulAut.congr e).toMonoidHom, ∃ x ∈ V, x' = β⁻¹ * x * β := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, hconjapply x⟩
  have hVe' : IsElementaryAbelian 3 (V.map (MulAut.congr e).toMonoidHom) := h2'.2.2.1
  have hVc' : Nat.card (V.map (MulAut.congr e).toMonoidHom) = 9 := by
    have := h2'.2.2.2.1
    simpa using this
  have hV0' : ∀ x ∈ V.map (MulAut.congr e).toMonoidHom,
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemV' x' hx'
    obtain ⟨g, δ, hg, hgδ⟩ := hβ x hx
    exact ⟨g, δ, hg, hgδ⟩
  obtain ⟨φ, hφV, hφout⟩ := hout
  have hout' : ∃ φ' ∈ V.map (MulAut.congr e).toMonoidHom, φ' ∉ (MulAut.conj :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* MulAut (graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom)).range := by
    refine ⟨MulAut.congr e φ, Subgroup.mem_map_of_mem _ hφV, ?_⟩
    rintro ⟨g, hg⟩
    apply hφout
    refine ⟨e.symm g, ?_⟩
    apply (MulAut.congr e).injective
    have h1 : MulAut.congr e (MulAut.conj (e.symm g)) = MulAut.conj g :=
      MulEquiv.ext fun y => by
        show e (e.symm g * e.symm y * (e.symm g)⁻¹) = g * y * g⁻¹
        rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply]
    rw [h1]
    exact hg
  rcases d4_weyl_cases hp hp2 hf K hK σ hσ _ hVe' hVc' hV0' hout' with
    ⟨φ', hφ'V, hφ'out, h, hh, hφ'⟩ | ⟨v, n, δ, hv, hv1, hv3, hvV, hn, hnT, hδ, heV, hev⟩
  · have hφ'3 : φ' ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian φ' hφ'V
    have hD := d4Out_of_toral hA2 hp hp2 hp3 hf hq K hK σ hσ φ' h hh hφ' hφ'3
    have hφ'1 : φ' ≠ 1 := fun h1 => hφ'out (h1 ▸ ⟨1, map_one _⟩)
    exact false_of_fixed_core hcen h2' h3' hφ'V hφ'1 hD.1 hD.2
  · exact hBad p f hp hp2 hp3 hf hq K hK σ hσ _ _ h2' h3' v n δ hv hv1 hv3 hvV hn hnT hδ heV hev

end CFSG.GH74.GLS.Stage2.Bender.Thm1
