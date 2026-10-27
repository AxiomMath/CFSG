module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv102Aux
public import CFSG.GH74.GLS.Prop27.LocBalFinal

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv102

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.E2 CFSG.Blueprint Subgroup Assembly.LowTwoRank
  CFSG.Assembly.Dichotomy CFSG.GH74.GLS.Prop27 CFSG.GH74.L5U5 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.TwoThin

theorem b_ivk_10_2_proved
    (hG : Generic.GenericKnownFacts) (hF : E2ComponentFacts) : B_ivk_10_2 := by
  intro G _ _ hGc x y K hlu
  obtain ⟨hpair, hy2, hyC, -, hnot⟩ := hlu
  have hx : orderOf x = 2 := hpair.1
  have hKb : CFSG.IsComponent (bar x K) := isComponent_bar hpair.2
  obtain ⟨e⟩ := kBar_equiv_bar hpair.2
  by_contra hnU
  have hnUb : ¬ InU2 ↥(bar x K) := fun h => hnU (inU2_of_mulEquiv e.symm h)
  have hC2 : InC2 ↥(bar x K) := (hGc.lt2o.2 x hx (bar x K) hKb).resolve_right hnUb
  have hno : ¬ HasL2Model ↥(bar x K) IsFM9 := by
    rintro ⟨p, f, hp, hf, hfm, hL⟩
    exact hnUb ⟨hC2.1, Or.inl ⟨p, f, hp, hf, isFM9_odd hfm, hL⟩⟩
  have hS : Shapes7 ↥(bar x K) :=
    shapes7_of_component hG hF (compData7_of_component hGc.gen4 hx hC2 hno) hC2.2.2.1
  have hTab : Prop27TableFacts := prop27TableFacts
  have hKn : (bar x K).Normal := ⟨fun n hn g => by
    have h1 : CFSG.IsComponent ((bar x K).map (MulAut.conj g).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hKb
    have e2 : ↥(bar x K) ≃* ↥((bar x K).map (MulAut.conj g).toMonoidHom) :=
      (MulAut.conj g).subgroupMap (bar x K)
    have hS2 : Shapes7 ↥((bar x K).map (MulAut.conj g).toMonoidHom) := shapes7_of_mulEquiv e2 hS
    have heq : (bar x K).map (MulAut.conj g).toMonoidHom = bar x K := by
      by_contra hne
      exact false_of_two_components7 hTab (gen4_centralizerBar hGc.gen4 x) (orderOf_xbar hx)
        (fun y => Generic.xbar_comm x y) h1 hKb hne hS2 hS
    have : g * n * g⁻¹ ∈ (bar x K).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [heq] at this⟩
  have hZ2 : IsPGroup 2 ↥(center ↥(bar x K)) := by
    have h := hC2.2.1
    rw [h]
    exact CFSG.pCore_isPGroup
  have hZc : Nat.card (center ↥(bar x K)) ≤ 2 := Shapes7.card_center_le_two hS
  have hZY := center_component_central (K := bar x K) hZc
  have hLB := locBal2_of_shapes7 prop27LocalBalance hS
  have hv2 : orderOf (sbar y hyC) = 2 := orderOf_sbar hy2 hyC
  have hcent := component_centralized (bar x K) hC2.1 hZ2 hZY hLB hv2
  apply hnot
  intro w hw
  have hwxy : w ∈ centralizer ({x, y} : Set G) := TwoThin.pPrimeCoreOf_le _ hw
  have hwC : w ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hwxy ⊢
    intro h hh
    exact hwxy h (by rw [Set.mem_singleton_iff.mp hh]; simp)
  have hmem := map_pPrimeCoreOf_le_involutionOddCore hy2 hyC hwC hw
  exact mem_centralizerSection_of_image hpair.2 hwC fun k hk => hcent _ hmem k hk

end CFSG.GH74.GLS.C3.Layer1.Iv102
