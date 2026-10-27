module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6Eight4
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.ClassicalInvolution.Upgrade
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

section Certs

local instance e6TwE6B14NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩


variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

theorem twE6_caseB_data (hn : 3 ≤ n) (hod : Odd n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {ω : (AlgebraicClosure F)ˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) :
    ∃ Jbar Sbar : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)),
      Jbar ≤ twE6C (iterateFrobenius (AlgebraicClosure F) 2 n) ∧
      CFSG.IsQuasisimple ↥Jbar ∧ TrivialMultiplierT ↥Jbar ∧ twE6BZero ω hω3 ≤ Jbar ∧
      Sbar ≤ twE6C (iterateFrobenius (AlgebraicClosure F) 2 n) ∧ IsPGroup 2 ↥Sbar ∧
      twE6BZero ω hω3 ≤
        Subgroup.normalizer (Sbar : Set (ModGL Tag.E6 (AlgebraicClosure F))) ∧
      twE6BZero ω hω3 ⊓
        Subgroup.centralizer (Sbar : Set (ModGL Tag.E6 (AlgebraicClosure F))) = ⊥ := by
  classical
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  have hf : 2 ≤ n := by omega
  have h3 : 3 ∣ 2 ^ n + 1 := three_dvd_pow_add_one hod
  obtain ⟨i⟩ := TwE6B.exists_kernelComponent_omega1 (Ω := Ω) hω3 hω1
  obtain ⟨S, hSR, hS2, hBS, hBSinf⟩ :=
    exists_twE6_eight_twoGroup (Ω := Ω) (q := 3) Fr (n := n) (by omega) hFr h3 ω hω3
  have hJle : twE6JStar (Fr := Fr) (q := 3) (ζ := ω) i ≤ twE6C Fr :=
    twE6JStar_le_twE6C (Fr := Fr) (q := 3) (ζ := ω) i
  have hJq : CFSG.IsQuasisimple ↥(twE6JStar (Fr := Fr) (q := 3) (ζ := ω) i) :=
    twE6_isQuasisimple_omega1 (K := F) (Ω := Ω) (Fr := Fr) hf hF hσ hFr
      Nat.prime_three (by norm_num) h3 hω3 hω1 i
  have hJmult : TrivialMultiplierT ↥(twE6JStar (Fr := Fr) (q := 3) (ζ := ω) i) :=
    (twE6_center_eq_bot_and_trivialMultiplierT (K := F) (Ω := Ω) (Fr := Fr) hf hF
      hσ hFr Nat.prime_three (by norm_num) h3 hω3 hω1 i).2
  have hB0J : twE6BZero ω hω3 ≤ twE6JStar (Fr := Fr) (q := 3) (ζ := ω) i :=
    twE6BZero_le_twE6JStar hf hF hσ hFr hod hω3 hω1 i
  have hSC : S ≤ twE6C Fr :=
    TwE6B.le_twE6C_of_isPGroup_two (K := F) (σ := σ.toRingHom) (Ω := Ω) (Fr := Fr) (n := n)
      (by omega) hF hσ hFr hSR hS2
  exact ⟨_, S, hJle, hJq, hJmult, hB0J, hSC, hS2, hBS, hBSinf⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
