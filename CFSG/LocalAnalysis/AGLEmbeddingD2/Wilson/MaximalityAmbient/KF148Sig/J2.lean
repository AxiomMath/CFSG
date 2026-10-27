module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.Cores
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.FiveSylow
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import Certificates.Kernel.Misc.Perm.J2Rel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofSig
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import Certificates.Certificate3029
public import Certificates.Certificate3086

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Asc83Table Subgroup
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem card_centralizer_xJ :
    Nat.card (centralizer ({xJ} : Set GJ)) = 36 := by
  rw [centralizer_x, card_subOf (by decide) enum45.1 gensCa_spec, enum45.2.1]

theorem card_centralizer_aJ
    (k : Fin 3) :
    Nat.card (centralizer ({aJ k} : Set GJ)) = 36 := by
  obtain ⟨-, hc⟩ := c_spec k
  rw [← card_centralizer_xJ, ← hc]
  have := card_centralizer_singleton_mulEquiv (MulAut.conj (cJ k)) xJ
  simpa [MulAut.conj_apply] using this

theorem centralizer_le_of_pow {G : Type*} [Group G] {y z : G} {n : ℕ} (h : y ^ n = z) :
    centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) := by
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg ⊢
  rw [← h]
  exact (Commute.pow_right (show Commute g y from hg) n).eq

theorem centralizer_eq_of_pow {G : Type*} [Group G] {y z : G} {n : ℕ} (hyz : y ^ n = z)
    (hy3 : y ^ 3 = 1) (hz1 : z ≠ 1) : centralizer ({y} : Set G) = centralizer ({z} : Set G) := by
  refine le_antisymm (centralizer_le_of_pow hyz) ?_
  have hn : ¬ 3 ∣ n := by
    rintro ⟨m, rfl⟩
    apply hz1
    rw [← hyz, pow_mul, hy3, one_pow]
  have hnn : n * n % 3 = 1 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hy : z ^ n = y := by
    rw [← hyz, ← pow_mul]
    conv_lhs => rw [← Nat.mod_add_div (n * n) 3, pow_add, pow_mul, hy3, one_pow, mul_one, hnn,
      pow_one]
  exact centralizer_le_of_pow hy

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig
