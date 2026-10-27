module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinHeld
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI Matrix

theorem i167CLin_split_model {K : Type} [Field K] [Finite K] {a : ℕ} (hKa : Nat.card K = 2 ^ a) (h2 : (2 : K) = 0)
    {d : ℕ} (A : GL (Fin d) K) (hord : ((orderOf A : ℕ) : K) ≠ 0) (M : Subgroup (GL (Fin d) K))
    (hM : CFSG.Open.IsComponentOf M (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K)) :
    ∃ b e : ℕ, StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e ∧ a ∣ e := by
  obtain ⟨b, E, hEfld, hEalg, hEfin, hb, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.held_linear_components_gl
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds A hord M hM
  letI : Field E := hEfld
  letI : Algebra K E := hEalg
  letI : Finite E := hEfin
  letI : Fintype E := Fintype.ofFinite E
  have h2E : (2 : E) = 0 := by
    have h := congrArg (algebraMap K E) h2
    rwa [map_ofNat (algebraMap K E) 2, map_zero] at h
  obtain ⟨q, hqchar, n, hqprime, hqcard⟩ := FiniteField.card' E
  haveI : CharP E q := hqchar
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff E q 2).mp h2E
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp hdvd
  subst hq2
  haveI : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.2.2
  have hEcard : Nat.card E = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hqcard]
  refine ⟨b, (n : ℕ),
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup hb hEcard φ, ?_⟩
  have hpow : 2 ^ (n : ℕ) = (2 ^ a) ^ Module.finrank K E := by
    rw [← hEcard, Module.natCard_eq_pow_finrank (K := K) (V := E), hKa]
  rw [← pow_mul] at hpow
  have heq : (n : ℕ) = a * Module.finrank K E :=
    Nat.pow_right_injective (by norm_num) hpow
  rw [heq]
  exact dvd_mul_right a _

theorem i167CLin_fixed_lt {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} (hg1 : g ≠ 1) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1))) < d := by
  have hle : Module.finrank K
      (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1))) ≤ d := by
    calc Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)))
        ≤ Module.finrank K (Fin d → K) := Submodule.finrank_le _
      _ = d := Module.finrank_fin_fun K
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply hg1
    have htop : LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_fin_fun K).symm)
    have hzero : Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1) = 0 :=
      LinearMap.ker_eq_top.mp htop
    have hmat : (g : Matrix (Fin d) (Fin d) K) - 1 = 0 := by
      apply Matrix.toLin'.injective
      simpa using hzero
    exact Units.ext (sub_eq_zero.mp hmat)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
