module

public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6
open scoped commutatorElement

theorem layer_le_oPrimePResidual (Q : Type) [Group Q] [Finite Q] : layer Q ≤ oPrimePResidual 2 Q := by
  refine sSup_le fun K hK => ?_
  have hperf : Group.IsPerfect ↥K := hK.1.1
  have hKY : K ≤ oPrimeResidual 2 Q := LayerFD.perfect_le_oPrimeResidual hperf
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf (oPrimeResidual 2 Q)) := by
    have e : ↥(K.subgroupOf (oPrimeResidual 2 Q)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKY
    exact Group.IsPerfect.ofSurjective (G := ↥K) (G' := ↥(K.subgroupOf (oPrimeResidual 2 Q)))
      (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 : K.subgroupOf (oPrimeResidual 2 Q) ≤ oResidual 2 ↥(oPrimeResidual 2 Q) :=
    Stage1.Main.perfect_le_oResidual _ hK'perf
  calc K = (K.subgroupOf (oPrimeResidual 2 Q)).map (oPrimeResidual 2 Q).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hKY).symm
    _ ≤ (oResidual 2 ↥(oPrimeResidual 2 Q)).map (oPrimeResidual 2 Q).subtype := Subgroup.map_mono h1

variable {G : Type} [Group G] [Finite G]

theorem em_le_LC (z : G) : Em (Cen z) ≤ LC z := by
  intro g hg
  have hg' : g ∈ (layer ↥(Cen z)).map (Cen z).subtype := hg
  obtain ⟨c, hc, rfl⟩ := hg'
  refine Stage1.Thm6.Prod.mem_LC_of_mem_layer z (layer_le_oPrimePResidual ↥(Cen z) hc) ?_
  have hX : (c : G) ∈ (layer ↥(Cen z)).map (Cen z).subtype := ⟨c, hc, rfl⟩
  exact CFSG.GH74.GLS.Stage2.Final.LayerFD.barOf_layer_le z ⟨c, hX, rfl⟩

omit [Finite G] in
theorem isCentralInvolution_of_conj' {z x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
    IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

omit [Finite G] in
theorem orderOf_eq_two_of_conj {z u : G} (hz : orderOf z = 2) (h : IsConj z u) : orderOf u = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
  rw [MulAut.conj_apply] at h1
  rw [← hc, h1]
  exact hz

theorem layer_conj_eq_of_two {z : G} (hz : IsCentralInvolution z) {S : Subgroup G}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {q : ℕ} {x : G} (hx : TwoClassData G z S L₁ L₂ q x) :
    ∀ u ∈ Em (Cen z), IsConj z u → u = z := by
  intro u hu hconj
  by_contra hne
  have hu2 : orderOf u = 2 := orderOf_eq_two_of_conj hz.1 hconj
  have hL : u ∈ LC z := em_le_LC z hu
  have hxu : IsConj x u := (hx.invol_L u hL hu2 hne).1
  have hzx : IsConj z x := hconj.trans hxu.symm
  exact hx.x_nonCentral (isCentralInvolution_of_conj' hz hzx)

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
