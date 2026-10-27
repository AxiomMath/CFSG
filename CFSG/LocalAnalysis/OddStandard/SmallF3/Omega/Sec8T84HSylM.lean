module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HCompl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HQuot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

theorem omega1_hPm (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    omega1 (hPm hQ fr) = hPm hQ fr := by
  rw [omega1]
  refine le_antisymm ?_ ?_
  · exact (Subgroup.closure_le (hPm hQ fr)).mpr fun x hx => hx.1
  · calc hPm hQ fr = (ffP0 hQ fr).map (toProj Q) := rfl
      _ ≤ (Subgroup.closure {g : OGroup Q | g ∈ ffP0 hQ fr ∧ g * g = 1}).map
            (toProj Q) :=
          Subgroup.map_mono (ffP0_le_closure_involutions hQ fr)
      _ = Subgroup.closure ((toProj Q) '' {g : OGroup Q | g ∈ ffP0 hQ fr ∧ g * g = 1}) :=
          MonoidHom.map_closure (toProj Q) _
      _ ≤ Subgroup.closure {x : ProjOrth Q | x ∈ hPm hQ fr ∧ x ^ 2 = 1} := by
          apply Subgroup.closure_mono
          rintro y ⟨g, hg, rfl⟩
          exact ⟨(mem_hPm_iff hQ fr).mpr ⟨g, hg.1, rfl⟩,
            by rw [pow_two, ← map_mul, hg.2, map_one]⟩

theorem hPm_complement (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) {B : Subgroup (ProjOrth Q)}
    (hB : B ≤ hPm hQ fr) (hE : IsElemAb2 B 4) :
    ∃ D : Subgroup (ProjOrth Q), D ≤ hPm hQ fr ∧ B ⊓ D = ⊥ ∧ B ⊔ D = hPm hQ fr := by
  have hlift : IsLiftE16 hQ fr (B.comap (toProj Q)) :=
    isLiftE16_comap hQ hdim hsgn fr hB hE
  have hBmap : (B.comap (toProj Q)).map (toProj Q) = B :=
    Subgroup.map_comap_eq_self_of_surjective (f := toProj Q)
      (QuotientGroup.mk'_surjective (piGroup Q)) B
  rcases lift_cases hQ fr hlift with h | h
  · have hc := map_toProj_compl hQ fr (piOrth_mem_ffB0 fr) (hD1_le_ffP0 hQ fr)
      (hB0_inf_hD1 fr) (ffB0_le_ffP0 hQ fr) (fun g hg => ffP0_eq_B0_mul_D1 hQ fr hg)
    exact ⟨(hD1 fr).map (toProj Q), Subgroup.map_mono (hD1_le_ffP0 hQ fr),
      by rw [← hBmap, h]; exact hc.1, by rw [← hBmap, h]; exact hc.2⟩
  · have hc := map_toProj_compl hQ fr (piOrth_mem_hU2 fr) (hD2_le_ffP0 hQ fr)
      (hU2_inf_hD2 fr) (hU2_le_ffP0 hQ fr) (fun g hg => ffP0_eq_U2_mul_D2 hQ fr hg)
    exact ⟨(hD2 fr).map (toProj Q), Subgroup.map_mono (hD2_le_ffP0 hQ fr),
      by rw [← hBmap, h]; exact hc.1, by rw [← hBmap, h]; exact hc.2⟩

theorem sec8t84_modelSylow : Sec8T84ModelSylow := by
  intro V _ _ _ Q hQ hdim hsgn P hP
  haveI : Finite (ProjOrth Q) := by
    haveI hV : Finite V := Module.finite_of_finite (ZMod 3)
    haveI hE : Finite (V ≃ₗ[ZMod 3] V) :=
      Finite.of_injective (fun g : V ≃ₗ[ZMod 3] V => g.toEquiv)
        (fun g h hgh => LinearEquiv.ext fun x => by
          simpa using congrArg (fun e : V ≃ V => e x) hgh)
    exact Finite.of_surjective (toProj Q) (QuotientGroup.mk'_surjective (piGroup Q))
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨a, -, ha⟩ := IsSylow2Of.exists_conj_mem (hPm_sylow hQ hdim hsgn fr) hP
  refine ⟨omega1_eq_of_conj a ha (omega1_hPm hQ fr), ?_⟩
  intro B hB
  exact complement_of_conj a ha
    (fun B' hB' hE' => hPm_complement hQ hdim hsgn fr hB' hE') B hB.1 hB.2.1

end CFSG.OddStandard.SmallF3.Omega
