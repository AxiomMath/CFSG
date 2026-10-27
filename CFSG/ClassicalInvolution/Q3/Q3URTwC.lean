module

public import CFSG.ClassicalInvolution.Q3.Q3URStd
public import CFSG.ClassicalInvolution.Q3.Q3URTwA
public import CFSG.ClassicalInvolution.Q3.Q3WASTLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Img

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem unitaryBlockStandardPair_locImg3 {x : G} (hP1 : LocalOddCentral Ω {x}) {A B : Subgroup G}
    (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x)
    (h : ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W A B) :
    ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x A) (locImg Ω x B) := by
  obtain ⟨W, hW⟩ := h
  have hWY : W ≤ locLayer Ω x :=
    (unitaryBlockStandardPair_le_sup card_gf9 (by norm_num) hW).trans (sup_le hA hB)
  have h1 := unitaryBlockStandardPair_subgroupOf hWY hW
  have h2 := unitaryBlockStandardPair_map3 h1 (locMk Ω x)
    (by rw [QuotientGroup.ker_mk']; exact hP1)
  exact ⟨_, h2⟩

variable [Finite G]

theorem unitary_of_chainSign_images3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {K β M : Subgroup G}
    (hKx : K ∈ centralizingMembers Ω {x}) (hβx : β ∈ centralizingMembers Ω {x})
    (hMx : M ∈ centralizingMembers Ω {x})
    (hs : ((∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x β) (locImg Ω x M)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x β) (locImg Ω x M)))
    (huni : ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β) :
    ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β M := by
  have h1 := unitaryBlockStandardPair_locImg3 hP1 (le_centralizingLayer hKx)
    (le_centralizingLayer hβx) huni
  rcases hs with ⟨hl, -⟩ | ⟨-, ⟨W, hW⟩⟩
  · exact (false_of_linear_of_unitary3 hl h1).elim
  · exact unitaryBlockStandardPair_of_locImg3 hΩ hex hP1 hO3 hβx hMx hW

end Img

section Partner

theorem exists_partner_two_su3 {R : Subgroup (Su (GaloisField 3 2) 3 1 (2 + 1))}
    {i : Su (GaloisField 3 2) 3 1 (2 + 1)}
    (h : IsLongRootSU2 (GaloisField 3 2) 3 1 (by omega : 2 ≤ 2 + 1) R i) :
    ∃ (R' : Subgroup (Su (GaloisField 3 2) 3 1 (2 + 1))) (i' : Su (GaloisField 3 2) 3 1 (2 + 1)),
      IsLongRootSU2 (GaloisField 3 2) 3 1 (by omega : 2 ≤ 2 + 1) R' i' ∧ Commute i i' ∧ i ≠ i' ∧
      ¬ Commutes R R' ∧ R ⊔ R' = ⊤ := by
  have h2 := two_ne_zero_gf9
  obtain ⟨g, hR, hi⟩ := h
  let T₀ : Pair (2 + 1) := nodePair 2 0 (by omega)
  let T₁ : Pair (2 + 1) := nodePair 2 1 (by omega)
  have hn : (2 : ℕ) ≤ 2 + 1 := by omega
  have hroot : rootSU2 (GaloisField 3 2) 3 1 hn = LcU (GaloisField 3 2) 3 1 T₀ := by
    rw [rootSU2_eq_longRootGroupSU h2, negBlock_eq_zMat (by omega : 0 + 2 ≤ 2 + 1)]
    rfl
  have hinv : rootInvSU (GaloisField 3 2) 3 1 hn = zEltU (GaloisField 3 2) 3 1 T₀ :=
    suMat_injective (by
      rw [suMat_rootInvSU, suMat_zEltU, negBlock_eq_zMat (by omega : 0 + 2 ≤ 2 + 1)]
      rfl)
  have hc : zEltU (GaloisField 3 2) 3 1 T₀ * zEltU (GaloisField 3 2) 3 1 T₁ =
      zEltU (GaloisField 3 2) 3 1 T₁ * zEltU (GaloisField 3 2) 3 1 T₀ :=
    signGroupU_comm (zEltU_mem_signGroupU T₀) (zEltU_mem_signGroupU T₁)
  have hT : T₀ ≠ T₁ := by
    intro h'
    have := (nodePair_eq_iff (m := 2) (a := 0) (b := 1) (by omega) (by omega)).mp h'
    omega
  refine ⟨(LcU (GaloisField 3 2) 3 1 T₁).map (MulAut.conj g).toMonoidHom,
    g * zEltU (GaloisField 3 2) 3 1 T₁ * g⁻¹, (isLongRootSU2_LcU h2 hn T₁).conj g, ?_, ?_, ?_, ?_⟩
  · rw [hi, hinv]
    show g * zEltU (GaloisField 3 2) 3 1 T₀ * g⁻¹ * (g * zEltU (GaloisField 3 2) 3 1 T₁ * g⁻¹) =
      g * zEltU (GaloisField 3 2) 3 1 T₁ * g⁻¹ * (g * zEltU (GaloisField 3 2) 3 1 T₀ * g⁻¹)
    calc g * zEltU (GaloisField 3 2) 3 1 T₀ * g⁻¹ * (g * zEltU (GaloisField 3 2) 3 1 T₁ * g⁻¹)
        = g * (zEltU (GaloisField 3 2) 3 1 T₀ * zEltU (GaloisField 3 2) 3 1 T₁) * g⁻¹ := by group
      _ = g * (zEltU (GaloisField 3 2) 3 1 T₁ * zEltU (GaloisField 3 2) 3 1 T₀) * g⁻¹ := by
        rw [hc]
      _ = g * zEltU (GaloisField 3 2) 3 1 T₁ * g⁻¹ *
          (g * zEltU (GaloisField 3 2) 3 1 T₀ * g⁻¹) := by group
  · intro h'
    rw [hi, hinv] at h'
    have h3 : zEltU (GaloisField 3 2) 3 1 T₀ = zEltU (GaloisField 3 2) 3 1 T₁ := by
      have := congrArg (fun y => g⁻¹ * y * g) h'
      simpa [mul_assoc] using this
    exact hT (typeU_zEltU_injective h2 h3)
  · rw [hR, hroot]
    intro hcm
    have h4 : Commutes (LcU (GaloisField 3 2) 3 1 T₀) (LcU (GaloisField 3 2) 3 1 T₁) :=
      (commutes_conjSub_iff g).mp hcm
    exact not_commutes_LcU_overlap card_gf9 (by norm_num) (by omega : 3 ≤ 2 + 1)
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (by simp) (by simp)
      (by simp) h4
  · rw [hR, hroot, ← Subgroup.map_sup, LcU_node_sup_eq_top3, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective

end Partner

end CFSG.ClassicalInvolution.Q3.Q3W
