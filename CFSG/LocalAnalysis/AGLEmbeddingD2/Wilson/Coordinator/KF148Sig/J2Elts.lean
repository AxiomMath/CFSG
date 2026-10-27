module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Data
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import Certificates.Certificate12648
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2

set_option linter.unusedSectionVars false


@[expose] noncomputable def tJ (i : ℕ) : GJ :=
  if _h : i < 18 then Classical.choose Certificates.certificate12648 i else 1

theorem tJ_of_lt {i : ℕ} (hi : i < 18) :
    tJ i = Classical.choose Certificates.certificate12648 i :=
  dif_pos hi

theorem rep_tJ {i : ℕ} (hi : i < 18) : Rep 315 vA[i]! (tJ i).1 := by
  rw [tJ_of_lt hi]
  exact (Classical.choose_spec Certificates.certificate12648).1 i hi

theorem lt_six_of_mem_genSets {s j : ℕ} (hs : s < 4) (hj : j ∈ genSets.getD s []) : j < 6 := by
  have h : ∀ s < 4, ∀ j ∈ genSets.getD s [], j < 6 := by decide
  exact h s hs j hj

theorem lt_six_of_mem_twoSets {s j : ℕ} (hs : s < 6) (hj : j ∈ twoSets.getD s []) : j < 6 := by
  have h : ∀ s < 6, ∀ j ∈ twoSets.getD s [], j < 6 := by decide
  exact h s hs j hj

@[expose] noncomputable def wJ (k : ℕ) : GJ := zJ ^ k * xJ

@[expose] noncomputable def actJ (j : ℕ) : GJ := if j < 3 then zJ else xJ

set_option quotPrecheck false in
local notation "facts" =>
  (Classical.choose_spec Certificates.certificate12648).2 xJ zJ rep_x rep_z

theorem orb_spec {j p q : ℕ} (hj : j < 6) (hp : p < 3) (hq : q < 3) :
    ∃ e < 3, actJ j ^ e * tJ (3 * j + p) * (actJ j ^ e)⁻¹ = tJ (3 * j + q) := by
  rw [tJ_of_lt (i := 3 * j + p) (by omega), tJ_of_lt (i := 3 * j + q) (by omega)]
  exact facts.1 j hj p hp q hq

theorem pair_spec {p q : ℕ} (hpq : (p, q) ∈ pairA) (hp : p < 18) (hq : q < 18) :
    (tJ p * tJ q) ^ 3 = 1 ∧ tJ p * tJ q ≠ 1 := by
  rw [tJ_of_lt hp, tJ_of_lt hq]
  exact facts.2.1 (p, q) hpq

theorem gen_spec {K : Subgroup GJ} {s : ℕ} (hs : s < 4)
    (hK : ∀ j ∈ genSets.getD s [], ∀ q < 3, tJ (3 * j + q) ∈ K) : K = ⊤ := by
  refine facts.2.2.1 s hs K fun j hj q hq => ?_
  have h6 := lt_six_of_mem_genSets hs hj
  rw [← tJ_of_lt (i := 3 * j + q) (by omega)]
  exact hK j hj q hq

@[expose] noncomputable def S2 (s : ℕ) : Subgroup GJ :=
  Subgroup.closure {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3, g = tJ (3 * j + q)}

theorem card_S2 {s : ℕ} (hs : s < 6) : Nat.card (S2 s) = 64 := by
  have hset : {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3, g = tJ (3 * j + q)} =
      {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3,
        g = Classical.choose Certificates.certificate12648 (3 * j + q)} := by
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hj, q, hq, rfl⟩
      have h6 := lt_six_of_mem_twoSets hs hj
      exact ⟨j, hj, q, hq, tJ_of_lt (by omega)⟩
    · rintro ⟨j, hj, q, hq, rfl⟩
      have h6 := lt_six_of_mem_twoSets hs hj
      exact ⟨j, hj, q, hq, (tJ_of_lt (by omega)).symm⟩
  rw [S2, hset]
  exact facts.2.2.2.1 s hs

theorem cent_w {k : ℕ} (hk : k < 3) {g : GJ} (hg : g * wJ k = wJ k * g) (h3 : ¬ 3 ∣ orderOf g) :
    g = 1 ∨ ∃ p < 3, g = tJ (3 * k + p) :=
  (facts.2.2.2.2.1 k hk g hg h3).imp_right fun ⟨p, hp, h⟩ =>
    ⟨p, hp, h.trans (tJ_of_lt (i := 3 * k + p) (by omega)).symm⟩

theorem cent_z {g : GJ} (hg : g * zJ = zJ * g) (h3 : ¬ 3 ∣ orderOf g) :
    g = 1 ∨ (∃ j, 3 ≤ j ∧ j < 6 ∧ ∃ p < 3, g = tJ (3 * j + p)) ∨
      ∃ v ∈ Subgroup.closure ({g, xJ * g * xJ⁻¹, (xJ * xJ) * g * (xJ * xJ)⁻¹} : Set GJ),
        orderOf v = 3 :=
  (facts.2.2.2.2.2 g hg h3).imp_right <| Or.imp_left fun ⟨j, h3j, hj, p, hp, h⟩ =>
    ⟨j, h3j, hj, p, hp, h.trans (tJ_of_lt (i := 3 * j + p) (by omega)).symm⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2
