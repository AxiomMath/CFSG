module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem s172FactC_of_models (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hexist : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (Q : QuadraticForm F V) (n p : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate →
      Module.finrank F V = 2 * n → ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q → 4 ≤ n → Even n →
      p.Prime → p ≠ 2 → p ∣ Nat.card F + 1 →
      (∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian p E →
        Nat.card E ≤ p ^ (n - 1)) →
      S172X.ModelExist p ↥(CFSG.RankThree.Classical2.orthDerived Q) (n - 1)
        (isUnA (n - 1) (Nat.card F)) (isOmPA (n - 1) (Nat.card F)) (isUnA (n - 2) (Nat.card F))) :
    S172FactC := by
  intro p n k heven hk hpk Ω _ _ S B D K x hcfg hS hK
  by_cases hn0 : n = 0
  · subst n
    exact absurd hK (S172C.not_catalogIs_isUnA_zero (PSimple p K) (2 ^ k))
  by_cases hn2 : n = 2
  · subst n
    exact absurd hK (S172B.not_catalogIs_isUnA_one (PSimple p K) (2 ^ k))
  have hn4 : 4 ≤ n := by
    obtain ⟨j, hj⟩ := heven
    omega
  obtain ⟨F, hFfield, hFfin, hFchar, V, hVadd, hVmod, hVfd, Q, hF, hQ, hdim, hminus, hθ⟩ :=
    S172C.exists_omegaMinus_model (n := n) (k := k) hn4 hk
  have hpq : p ∣ Nat.card F + 1 := by rw [hF]; exact hpk
  have hR : S172X.LiftableRank p ↥(CFSG.RankThree.Classical2.orthDerived Q) (n - 1) :=
    S172C.liftableRank_orthDerived_minus hQ hdim hminus (by omega) heven hcfg.prime hcfg.odd hpq
  have hBin := S172C.mem_sup_centralizer_of_innerDiagMarking hRig hcfg.qs hn4 hS hcfg.idiag
  have hM := hexist F V Q n p hQ hdim hminus hn4 heven hcfg.prime hcfg.odd hpq hR.1
  rw [hF] at hM
  exact S172X.exist_of_model_of_mem_sup hθ hR hM Ω S B D K x hcfg hBin hS hK

end CFSG.LocalAnalysis.GLTheoremA.S172

end
