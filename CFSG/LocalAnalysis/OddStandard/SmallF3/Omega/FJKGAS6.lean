module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGALay
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureLayer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_exists_involution_of_simHasType (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {x : ProjSim Q} {r : ℕ} {a : ℤˣ}
    (h : SimHasType x r a) :
    ∃ s : OGroup Q, s * s = 1 ∧ ffSimOmegaAct hQ h2 x = projAut hQ s := by
  obtain ⟨y, hyx, -, t, ht, -, hty⟩ := h
  refine ⟨t, ht, ?_⟩
  rw [← hyx, ← hty, ffSimOmegaAct_projOrthToProjSim]
  rfl

theorem fj_kga_of_simHasType (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 7)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {x : ProjSim Q} {r : ℕ} {a : ℤˣ} (h : SimHasType x r a)
    {y : omegaProj hQ} {B : Subgroup (omegaProj hQ)} (hy : orderOf y = 2)
    (hB : Sl23PocketIn ⊤ y B) (hx1 : ffSimOmegaAct hQ h2 x ≠ 1)
    (hfix : ∀ b ∈ B, ffSimOmegaAct hQ h2 x b = b) (hne : ffSimOmegaAct hQ h2 x ≠ MulAut.conj y) :
    ∃ J : Subgroup (omegaProj hQ), IsComponentIn J (L34GFix (ffSimOmegaAct hQ h2 x)) ∧
      InFStar J ∧ B ≤ J := by
  obtain ⟨s, hs, hxs⟩ := fj_exists_involution_of_simHasType hQ h2 h
  rw [hxs] at hx1 hfix hne ⊢
  obtain ⟨J, hJ, hJF, hBJ⟩ := fj_kga_engine_le7 hQ hn hs hx1 hy hB hfix hne
  exact ⟨J, by rw [l34g_fix_eq_fixSub]; exact hJ, hJF, hBJ⟩

theorem fjKGAAt_omegaProj_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) : FJKGAAt ↥(omegaProj hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  haveI : Finite ↥(omegaProj hQ) :=
    Finite.of_surjective (omegaToProj hQ) (omegaToProj_surjective hQ)
  have hbij := ffSimOmegaAct_bijective_six_plus hQ hdim hs
  intro y B hy hB α hαα hα1 hfix hαy
  obtain ⟨x, rfl⟩ := hbij.2 α
  have hx2 : x * x = 1 := hbij.1 (by rw [map_mul, map_one]; exact hαα)
  have hBH : B ≤ ffFix hQ h2 x := fun b hb => hfix b hb
  have hBo := l34g_le_closure_odd hB.2.2.2
  have hiso : ∀ {r : ℕ} {a : ℤˣ}, SimHasType x r a → ∃ J : Subgroup ↥(omegaProj hQ),
      IsComponentIn J (L34GFix (ffSimOmegaAct hQ h2 x)) ∧ InFStar J ∧ B ≤ J := fun h =>
    fj_kga_of_simHasType hQ (by omega) h2 h hy hB hα1 hfix hαy
  have hlay : ∀ {t : CFSG.Open.StatedLieTag} {n k : ℕ},
      (∀ (E : Type) [Group E], LieModel E t n 3 k →
        IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E) →
      LayerModel ↥(ffFix hQ h2 x) t n k → ∃ J : Subgroup ↥(omegaProj hQ),
        IsComponentIn J (L34GFix (ffSimOmegaAct hQ h2 x)) ∧ InFStar J ∧ B ≤ J :=
    fun hsh hLM => by
      obtain ⟨J, hJ, hJF, hBJ⟩ := fj_exists_component_of_layerModel hsh hLM hBH hBo
      exact ⟨J, by rw [l34g_fix_eq_fixSub]; exact hJ, hJF, hBJ⟩
  rcases ff_model_classify hQ hdim hs hx2 with h | h | h | h | h | h
  · exact absurd (by rw [h, map_one]) hα1
  · exact hiso h
  · exact hiso h
  · obtain ⟨a, h⟩ := h
    exact hiso h
  · obtain ⟨a, h⟩ := h
    exact hiso h
  · rcases ff_K4_layerModel hQ hdim hs hx2 h with h' | h'
    · exact hlay fg_shape_psl3 h'
    · exact hlay fg_shape_psl2 h'

theorem fjKGAAt_omegaProj_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) : FJKGAAt ↥(omegaProj hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  haveI : Finite ↥(omegaProj hQ) :=
    Finite.of_surjective (omegaToProj hQ) (omegaToProj_surjective hQ)
  have hbij := ffSimOmegaAct_bijective_six_minus hQ hdim hs
  intro y B hy hB α hαα hα1 hfix hαy
  obtain ⟨x, rfl⟩ := hbij.2 α
  have hx2 : x * x = 1 := hbij.1 (by rw [map_mul, map_one]; exact hαα)
  have hBH : B ≤ ffFix hQ h2 x := fun b hb => hfix b hb
  have hBo := l34g_le_closure_odd hB.2.2.2
  have hiso : ∀ {r : ℕ} {a : ℤˣ}, SimHasType x r a → ∃ J : Subgroup ↥(omegaProj hQ),
      IsComponentIn J (L34GFix (ffSimOmegaAct hQ h2 x)) ∧ InFStar J ∧ B ≤ J := fun h =>
    fj_kga_of_simHasType hQ (by omega) h2 h hy hB hα1 hfix hαy
  have hlay : ∀ {t : CFSG.Open.StatedLieTag} {n k : ℕ},
      (∀ (E : Type) [Group E], LieModel E t n 3 k →
        IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E) →
      LayerModel ↥(ffFix hQ h2 x) t n k → ∃ J : Subgroup ↥(omegaProj hQ),
        IsComponentIn J (L34GFix (ffSimOmegaAct hQ h2 x)) ∧ InFStar J ∧ B ≤ J :=
    fun hsh hLM => by
      obtain ⟨J, hJ, hJF, hBJ⟩ := fj_exists_component_of_layerModel hsh hLM hBH hBo
      exact ⟨J, by rw [l34g_fix_eq_fixSub]; exact hJ, hJF, hBJ⟩
  rcases ff6m_model_classify hQ hdim hs hx2 with h | h | h | h | h | h | h
  · exact absurd (by rw [h, map_one]) hα1
  · exact hiso h
  · exact hiso h
  · obtain ⟨a, h⟩ := h
    exact hiso h
  · obtain ⟨a, h⟩ := h
    exact hiso h
  · exact hlay fg_shape_psu3 (ff6m_N2_layerModel hQ hdim hs h)
  · exact hlay fg_shape_psl2 (ff6m_K4_layerModel hQ hdim hs hx2 h)

theorem fjKGAAt_of_lieModel_psl {Y : Type} [Group Y] (h : LieModel Y .PSL 4 3 1) : FJKGAAt Y := by
  obtain ⟨W, i1, i2, i3, R, hR, hdim, hs, ⟨f⟩⟩ := isOmegaStar_of_lieModel_psl h
  letI := i1
  letI := i2
  letI := i3
  exact fjKGAAt_of_mulEquiv f.symm (fjKGAAt_omegaProj_six_plus hR hdim hs)

theorem fjKGAAt_of_lieModel_psu {Y : Type} [Group Y] (h : LieModel Y .PSU 4 3 1) : FJKGAAt Y := by
  obtain ⟨W, i1, i2, i3, R, hR, hdim, hs, ⟨f⟩⟩ := isOmegaStar_of_lieModel_psu h
  letI := i1
  letI := i2
  letI := i3
  exact fjKGAAt_of_mulEquiv f.symm (fjKGAAt_omegaProj_six_minus hR hdim hs)

end CFSG.OddStandard.SmallF3.Omega
