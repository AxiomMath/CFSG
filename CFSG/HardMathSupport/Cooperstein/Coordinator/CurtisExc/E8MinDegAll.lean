module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.NontrivialFactor
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8TypeBoundProof

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley TauCeti CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section MinDegAll


theorem baseChangeGL_mem_adjointGroup_E8 {R S : Type} [Field R] [Field S] (ι : R →+* S)
    {g : ModGL .E8 R} (hg : g ∈ adjointGroup .E8 R) : baseChangeGL ι g ∈ adjointGroup .E8 S := by
  have h : baseChangeGL ι g ∈ (adjointGroup .E8 R).map (baseChangeGL ι) := ⟨g, hg, rfl⟩
  rw [map_baseChangeGL_adjointGroup] at h
  refine (Subgroup.closure_le (adjointGroup .E8 S)).2 ?_ h
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact (xC .E8 S i (ι c)).2
  · exact (yC .E8 S i (ι c)).2

@[expose] def baseChangeAdjE8 {R S : Type} [Field R] [Field S] (ι : R →+* S) :
    adjointGroup .E8 R →* adjointGroup .E8 S :=
  ((baseChangeGL (τ := .E8) ι).comp (adjointGroup .E8 R).subtype).codRestrict (adjointGroup .E8 S)
    fun g => baseChangeGL_mem_adjointGroup_E8 ι g.2

theorem baseChangeAdjE8_injective {R S : Type} [Field R] [Field S] (ι : R →+* S) :
    Function.Injective (baseChangeAdjE8 ι) :=
  fun _ _ h => Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))

theorem e8MinDeg
    (K : Type) [Field K] [Finite K] [CharP K 2] : E8MinDeg K := by
  intro k _ _ _ _ m ρ hρ hinj
  let ρ' : Representation k (adjointGroup .E8 (ZMod 2)) (Fin m → k) :=
    ρ.comp (baseChangeAdjE8 (ιF K))
  have hnt : ∃ (g : adjointGroup .E8 (ZMod 2)) (v : Fin m → k), ρ' g v ≠ v := by
    by_contra hcon
    push Not at hcon
    have h1 : xC .E8 (ZMod 2) n8 1 = 1 := by
      apply baseChangeAdjE8_injective (ιF K)
      apply hinj
      refine LinearMap.ext fun v => ?_
      have := hcon (xC .E8 (ZMod 2) n8 1) v
      change ρ (baseChangeAdjE8 (ιF K) (xC .E8 (ZMod 2) n8 1)) v = v at this
      rw [this, map_one, map_one, Module.End.one_apply]
    exact xC_ne_one n8 1 h1
  obtain ⟨Q, _, _, _, σ, hσ, hσnt, hQ⟩ := exists_nontrivial_simple_subquotient
    (CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 (ZMod 2)).commutator_eq_top m (Fin m → k) ρ'
    (Module.finrank_fin_fun k) hnt
  have := e8_two_min_degree_of_nontrivial hσ hσnt
  omega

theorem noIrrFFOffender_E8_allq
    (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    (hq : q.p = 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.E8 q, hv⟩).Group :=
  noIrrFFOffender_E8_of_typeBound
    (fun K _ _ _ n hn hK => typeBound_of_minDeg hn hK (e8MinDeg K)) q hv hq

end MinDegAll

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
