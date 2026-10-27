module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGABlk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGALift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGADich
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClShape
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def Fj53 (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) : Prop :=
  ∀ (z : omegaGroup hQ) (K : Subgroup (omegaGroup hQ)), orderOf z = 2 →
    Sl23PocketIn ⊤ z K → K ≤ cOmega hQ s → (z : OGroup Q) ≠ piOrth Q → (z : OGroup Q) ≠ s →
    s ≠ piOrth Q * (z : OGroup Q) →
      (Module.finrank (ZMod 3) (fixSp s) = 5 → Module.finrank (ZMod 3) (commSp s) = 3 →
        K ≤ (fjOmegaInl hQ hs).range) ∧
      (Module.finrank (ZMod 3) (fixSp s) = 3 → Module.finrank (ZMod 3) (commSp s) = 5 →
        K ≤ (fjOmegaInr hQ hs).range)

theorem fj_53_of_le_seven (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 7)
    {s : OGroup Q} (hs : s * s = 1) : Fj53 hQ hs := by
  intro z K _ _ _ _ _ _
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) s
  exact ⟨fun h5 h3 => by omega, fun h3 h5 => by omega⟩

theorem fj_isFStarGroup_omegaGroup_of_five_le (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (h7 : Module.finrank (ZMod 3) V ≤ 7) :
    IsFStarGroup (omegaGroup hQ) := by
  rcases (by omega : Module.finrank (ZMod 3) V = 5 ∨ Module.finrank (ZMod 3) V = 6 ∨
      Module.finrank (ZMod 3) V = 7) with h | h | h
  · exact cl_isFStarGroup_omegaGroup_five hQ h
  · rcases Int.units_eq_one_or (quadSign Q) with hs | hs
    · exact cl_isFStarGroup_omegaGroup_six_plus hQ h hs
    · exact cl_isFStarGroup_omegaGroup_six_minus hQ h hs
  · exact cl_isFStarGroup_omegaGroup_seven hQ h

theorem fj_projAut_eq_conj (hQ : Q.Nondegenerate) (z : omegaGroup hQ) :
    projAut hQ (z : OGroup Q) = MulAut.conj (omegaToProj hQ z) := by
  ext p
  rw [MulAut.conj_apply, coe_projAut]
  rfl

theorem fj_projAut_piOrth_mul (hQ : Q.Nondegenerate) (x : OGroup Q) :
    projAut hQ (piOrth Q * x) = projAut hQ x := by
  unfold projAut
  rw [map_mul, toProj_piOrth, one_mul]

theorem fj_kga_engine (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 8)
    {s : OGroup Q} (hs : s * s = 1) (h53 : Fj53 hQ hs) (hσ : projAut hQ s ≠ 1)
    {y : omegaProj hQ} {B : Subgroup (omegaProj hQ)} (hy : orderOf y = 2)
    (hB : Sl23PocketIn ⊤ y B) (hfix : ∀ b ∈ B, projAut hQ s b = b)
    (hne : projAut hQ s ≠ MulAut.conj y) :
    ∃ J : Subgroup (omegaProj hQ), IsComponentIn J (fixSub (projAut hQ s)) ∧ InFStar J ∧
      B ≤ J := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) s
  have hU : 0 < Module.finrank (ZMod 3) (commSp s) := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 3) (commSp s)) with h | h
    · exfalso
      apply hσ
      have h1 : s = 1 := (invDim_eq_zero_iff hs).mp h
      rw [h1]
      simp [projAut]
    · exact h
  have hW : 0 < Module.finrank (ZMod 3) (fixSp s) := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 3) (fixSp s)) with h | h
    · exfalso
      apply hσ
      have h1 : s = piOrth Q := (invDim_eq_finrank_iff hs).mp (by unfold invDim; omega)
      have hπ1 : ((piOrth Q : OGroup Q) : ProjOrth Q) = 1 := toProj_piOrth
      rw [h1]
      simp [projAut, hπ1]
    · exact h
  obtain ⟨z, hzy, hz2, hzK⟩ := fj_lift_pocket_omega hQ hy hB
  have hKs : l34g_oddHull (omegaToProj hQ) B ≤ cOmega hQ s := fj_oddHull_le_cOmega hQ hs hfix
  have hKB : (l34g_oddHull (omegaToProj hQ) B).map (omegaToProj hQ) = B :=
    l34g_map_oddHull _ (omegaToProj_surjective hQ) hB.2.2.2
  have hzπ : (z : OGroup Q) ≠ piOrth Q := by
    intro h
    have h1 : omegaToProj hQ z = 1 := (omegaToProj_eq_one_iff hQ z).mpr (Or.inr h)
    rw [h1] at hzy
    rw [← hzy, orderOf_one] at hy
    exact absurd hy (by decide)
  have hconj : projAut hQ (z : OGroup Q) = MulAut.conj y := by
    rw [fj_projAut_eq_conj, hzy]
  have hzs : (z : OGroup Q) ≠ s := fun h => hne (by rw [← h]; exact hconj)
  have hzsπ : s ≠ piOrth Q * (z : OGroup Q) := fun h =>
    hne (by rw [h, fj_projAut_piOrth_mul]; exact hconj)
  obtain ⟨a, c, -, hcases⟩ := fj_pocket_dichotomy hQ hn hs hKs hzK.2.2.2 hzK.1 hz2 hzπ hzs hzsπ
  rcases hcases with ⟨-, h5⟩ | ⟨-, h5⟩
  · have hKblk : l34g_oddHull (omegaToProj hQ) B ≤ (fjOmegaInl hQ hs).range := by
      by_cases h3 : Module.finrank (ZMod 3) (commSp s) ≤ 2
      · exact fj_le_fixBlock_of_finrank_le_two hQ hs h3 hKs hzK.2.2.2
      · exact (h53 z _ hz2 hzK hKs hzπ hzs hzsπ).1 (by omega) (by omega)
    have hFS := fj_isFStarGroup_omegaGroup_of_five_le (nondegenerate_restrict_fixSp hQ hs) h5
      (by omega)
    have hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_fixSp hQ hs)) :=
      hFS.elim (fun h => h.1) (fun h => h.1)
    have hJ := fj_isComponentIn_clFixHom hQ hs hU hq
    refine ⟨(clFixHom hQ hs).range, hJ, cl_inFStar_of_isComponentIn_fix hQ hn hs hW hU hJ, ?_⟩
    intro b hb
    rw [← hKB] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    obtain ⟨p, hp⟩ := hKblk hk
    exact ⟨p, by rw [clFixHom_eq_comp, MonoidHom.comp_apply, hp]⟩
  · have hU2 : 2 ≤ Module.finrank (ZMod 3) (commSp s) := by omega
    have hKblk : l34g_oddHull (omegaToProj hQ) B ≤ (fjOmegaInr hQ hs).range := by
      by_cases h3 : Module.finrank (ZMod 3) (fixSp s) ≤ 2
      · exact fj_le_commBlock_of_finrank_le_two hQ hs h3 hKs hzK.2.2.2
      · exact (h53 z _ hz2 hzK hKs hzπ hzs hzsπ).2 (by omega) (by omega)
    have hFS := fj_isFStarGroup_omegaGroup_of_five_le (nondegenerate_restrict_commSp hQ hs) h5
      (by omega)
    have hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_commSp hQ hs)) :=
      hFS.elim (fun h => h.1) (fun h => h.1)
    have hJ := isComponentIn_omegaProjInr hQ hs hU2 hW hq
    refine ⟨(omegaProjInr hQ hs hU2).range, hJ,
      cl_inFStar_of_isComponentIn_fix hQ hn hs hW hU hJ, ?_⟩
    intro b hb
    rw [← hKB] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    obtain ⟨p, hp⟩ := hKblk hk
    exact ⟨p, by
      change omegaToProj hQ (omegaInr hQ hs hU2 p) = _
      rw [omegaInr_eq_fjOmegaInr, hp]⟩

theorem fj_kga_engine_le7 (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 7)
    {s : OGroup Q} (hs : s * s = 1) (hσ : projAut hQ s ≠ 1)
    {y : omegaProj hQ} {B : Subgroup (omegaProj hQ)} (hy : orderOf y = 2)
    (hB : Sl23PocketIn ⊤ y B) (hfix : ∀ b ∈ B, projAut hQ s b = b)
    (hne : projAut hQ s ≠ MulAut.conj y) :
    ∃ J : Subgroup (omegaProj hQ), IsComponentIn J (fixSub (projAut hQ s)) ∧ InFStar J ∧
      B ≤ J :=
  fj_kga_engine hQ (by omega) hs (fj_53_of_le_seven hQ hn hs) hσ hy hB hfix hne

end CFSG.OddStandard.SmallF3.Omega
