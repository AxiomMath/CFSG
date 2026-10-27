module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcFacts
public import CFSG.GH74.Generic.Front.OuterModels

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Universal
open CFSG.Open (StatedSp StatedLieAdmissible)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem comap_center_eq_center {K L : Type*} [Group K] [Group L] [Group.IsPerfect K]
    (π : K →* L) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) :
    (Subgroup.center L).comap π = Subgroup.center K := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have h2 : x ∈ Subgroup.upperCentralSeries K (1 + 1) := by
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro y
      rw [Subgroup.upperCentralSeries_one]
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hx (π y)).symm
    rwa [Group.IsPerfect.upperCentralSeries_eq_center K (by norm_num)] at h2
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro l
    obtain ⟨y, rfl⟩ := hπ l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]

private theorem outer_solvable_of_central_quotient {K L : Type*} [Group K] [Group L]
    [Group.IsPerfect K] (π : K →* L) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hK : Group.IsSolvable (Outer (K ⧸ Subgroup.center K))) : Group.IsSolvable (Outer L) := by
  have hL : Group.IsPerfect L := Group.IsPerfect.ofSurjective hπ
  let ψ : K →* L ⧸ Subgroup.center L := (QuotientGroup.mk' (Subgroup.center L)).comp π
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  have hker' : ψ.ker = Subgroup.center K := by
    rw [← comap_center_eq_center π hπ hker]
    ext x
    simp [ψ, QuotientGroup.eq_one_iff]
  let e : K ⧸ Subgroup.center K ≃* L ⧸ Subgroup.center L :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  haveI := hK
  haveI : Group.IsSolvable (Outer (L ⧸ Subgroup.center L)) := solvable_of_equiv e
  exact solvable_of_centerQuotient L

private theorem outer_solvable_of_sl4 {F : Type} [Field F] [Finite F] {L : Type} [Group L]
    (π : Matrix.SpecialLinearGroup (Fin 4) F →* L) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center _) : Group.IsSolvable (Outer L) := by
  obtain ⟨p, f, hp, hf, hF⟩ := CFSG.GH74.Generic.exists_prime_pow_card F
  have hadm : StatedLieAdmissible .PSL (3 + 1) p f :=
    ⟨hp, hf, by norm_num, by simp, by simp⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (SpecialLinear.isQuasisimple 3 F (by norm_num)).1
  have hmod := SpecialLinear.statedClassicalModel_center_quotient 3 F hadm hF
  have hs : Group.IsSolvable (Outer (Matrix.SpecialLinearGroup (Fin 4) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F))) :=
    (linear_higher_classical_model_schreier (by norm_num) hmod).2
  exact outer_solvable_of_central_quotient π hπ hker hs

private theorem outer_solvable_of_sp2 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {L : Type} [Group L] (π : ↥(StatedSp 2 F) →* L) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center _) : Group.IsSolvable (Outer L) := by
  obtain ⟨p, f, hp, hf, hcard⟩ := CFSG.GH74.Generic.exists_prime_pow_card F
  have hadm : StatedLieAdmissible .PSp 2 p f := ⟨hp, hf, le_rfl, by
    intro h
    have h2 : p ^ f = 2 := (Prod.mk.inj h).2
    rw [hcard, h2] at hF
    exact absurd hF (by decide)⟩
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (Symplectic.isQuasisimple_of_admissible 2 F hadm hcard).1
  have hmod := Symplectic.statedClassicalModel_center_quotient 2 F hadm hcard
  have hs : Group.IsSolvable (Outer (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))) :=
    (CFSG.ComponentClassification.CatalogueBSymplecticTwo.classical_model_two_schreier hmod).2
  exact outer_solvable_of_central_quotient π hπ hker hs

private theorem perfect_le_inner_of_outer_solvable {L : Type*} [Group L]
    [Group.IsSolvable (Outer L)] (Q : Subgroup (MulAut L)) (hQ : Group.IsPerfect ↥Q) :
    Q ≤ (MulAut.conj : L →* MulAut L).range := by
  intro q hq
  obtain ⟨g, hg⟩ := perfect_action_inner (A := ↥Q) Q.subtype ⟨q, hq⟩
  exact ⟨g, hg.symm⟩

theorem luOutFact : LuOutFact := by
  intro L _ _ hL Q hQ
  have hsolv : Group.IsSolvable (Outer L) := by
    rcases hL with ⟨φ, hφ, hker⟩ | ⟨φ, hφ, hker⟩
    · exact outer_solvable_of_sl4 φ hφ hker
    · refine outer_solvable_of_sp2 ?_ φ hφ hker
      rw [GaloisField.card 3 1 one_ne_zero]
      exact ⟨1, by norm_num⟩
  exact perfect_le_inner_of_outer_solvable Q hQ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
