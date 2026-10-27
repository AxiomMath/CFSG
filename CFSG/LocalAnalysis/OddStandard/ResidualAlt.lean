module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.OddStandard.Glue

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace Residual

theorem center_eq_bot_of_mulEquiv_alternating {Q : Type*} [Group Q] {n : ℕ} (hn : 4 ≤ n)
    (e : Q ≃* alternatingGroup (Fin n)) : center Q = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcen : e y ∈ center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy w]
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hcen
  have : e y = e 1 := by rw [map_one]; exact Subgroup.mem_bot.mp hcen
  exact Subgroup.mem_bot.mpr (e.injective this)

theorem seven_dvd_card_alternatingGroup {n : ℕ} (hn : 7 ≤ n) :
    7 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h2
  have h7 : 7 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) hn
  rw [← h2] at h7
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 7 2) h7)

end Residual

section Branches

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem altStd_rankTwo
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hS : StandardSetting G L) {n : ℕ} (hn : 8 ≤ n) (e : L ≃* alternatingGroup (Fin n))
    (hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))) :
    Nonempty (G ≃* alternatingGroup (Fin (n + 4))) := by
  have hH : ComponentClassification.RankTwoStandard.RankTwoHyp G L :=
    ⟨hS.kProper, hS.standard, hS.not_normal, hrank⟩
  have hZ : center L = ⊥ := Residual.center_eq_bot_of_mulEquiv_alternating (by omega) e
  let θ : L ⧸ center L ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hXG : ComponentClassification.RankTwoStandard.rankTwoX L ≃* G :=
    (MulEquiv.subgroupCongr hS.normalClosure_eq_top).trans Subgroup.topEquiv
  rcases hRank2 G L hH hS.oddCore_eq_bot n (by omega) ⟨θ⟩ with he | ⟨h5, -⟩ | ⟨h5, -, -⟩
  · exact he.map fun e' => hXG.symm.trans e'
  · omega
  · omega

end Branches

end CFSG.OddStandard
