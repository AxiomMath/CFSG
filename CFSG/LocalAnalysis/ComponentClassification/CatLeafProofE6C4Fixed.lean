module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Edge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Comm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (blk spBlock edgeDown doubleBondDiagram_cartanC
  weylElement_sp_one)
open scoped MatrixGroups Matrix

variable {K : Type} [Field K]

theorem fin4_down_nadj : ∀ i j : Fin 4, i ≠ j → ¬ edgeDown 4 i j → ¬ edgeDown 4 j i →
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
      (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
  decide

theorem fin4_down_single : ∀ i j : Fin 4, edgeDown 4 i j → ¬ (i = 3 ∧ j = 2) →
    (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by
  decide

theorem rootGenerated_recognition
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(rootGenerated K) ∧
      LieModel (↥(rootGenerated K) ⧸ Subgroup.center ↥(rootGenerated K)) .PSp 4 p f := by
  obtain ⟨hf, hq3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSp 4 p f := ⟨hp, hf, by norm_num, fun h => by simp at h⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  obtain ⟨O'⟩ := Steinberg.nonempty_commOrder_ofCartan (Symplectic.rootDatum 4 K).isFiniteType
    (Dv := (Symplectic.rootDatum 4 K).divisible) rfl
  have hE' := Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ 4) O' Steinberg.Sp.commC
    (Steinberg.Sp.commutatorFormula O')
  have hsq : ∀ k : Fin 4,
      Steinberg.weylElement (Steinberg.Sp.x 4 K) k 1 ^ 2 ∈ Symplectic.torus 4 K k := by
    intro k
    rw [weylElement_sp_one]
    exact (Symplectic.isCTGroupDatum 4 K).sq_mem k
  obtain ⟨r1, r2, r3⟩ := e6C4Rho_eq_e6F4Rho K
  have hcR : ∀ i j : Fin 4, i ≠ j → ¬ edgeDown 4 i j → ¬ edgeDown 4 j i → ∀ A B : SL(2, K),
      Commute (e6C4Rho K i A) (e6C4Rho K j B) := by
    intro i j hne h1 h2 A B
    rcases fin4_down_nadj i j hne h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact commute_e6C4Rho_zero_two hK2 A B
    · exact (commute_e6C4Rho_zero_two hK2 B A).symm
    · exact commute_e6C4Rho_zero_three A B
    · exact (commute_e6C4Rho_zero_three B A).symm
    · rw [r1, r3]
      exact commute_e6F4Rho (i := 3) (j := 1) (by decide) (by decide) (by decide) A B
    · rw [r1, r3]
      exact commute_e6F4Rho (i := 1) (j := 3) (by decide) (by decide) (by decide) A B
  obtain ⟨Ψ, -, -, hqs, hlie, -⟩ := weakCT_of_frame_dl_subgroup
    (CurtisTits.curtisTitsConclusion_symplectic hadm hK (by norm_num))
    (leviConePresented_symplectic 4 K) hE' rfl (isQuasisimple_statedSp_two hq3)
    (Ring.two_ne_zero hK2)
    (doubleBondDiagram_cartanC (n := 4) (by norm_num) (a := 3) (b := 2) rfl rfl)
    (Symplectic.steinbergExtras 4 K).torus_iSupIndep hsq (U := fun k => (e6C4Rho K k).range)
    (fun i j hne h1 h2 u hu v hv => by
      obtain ⟨A, rfl⟩ := hu
      obtain ⟨B, rfl⟩ := hv
      exact (hcR i j hne h1 h2 A B).eq)
    (ρ := e6C4Rho K) (fun k => rfl) (by rw [r3]; exact simpleRootSL2_injective hK2 _)
    (fun i j hij hne => by
      rcases fin4_down_single i j hij hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact exists_e6C4_sl3_one_zero
      · rw [r1, r2]
        exact exists_e6F4_short_sl3)
    (by
      rw [r2, r3]
      exact exists_e6_sp4 hp hp2 hK (commute_e6_sl2_two_four K))
  let e := MulEquiv.subgroupCongr (iSup_e6C4Rho_range_eq hK2)
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e hqs,
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩

theorem oddLieCentralQuotient_rootGenerated
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    OddLieCentralQuotient p ↥(rootGenerated K) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  exact ⟨.PSp, 4, f, ⟨hp, hf, by norm_num, fun h => by simp at h⟩,
    (rootGenerated_recognition hp hp2 hK).2⟩

end CFSG.ComponentClassification.CatLeafProof
