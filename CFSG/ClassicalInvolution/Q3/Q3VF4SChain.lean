module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SAdapt
public import CFSG.ClassicalInvolution.Q3.Q3VF4CClose
public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.Q3.Q3VChainModel
public import CFSG.ClassicalInvolution.Q3.Q3TY5
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  planeGroup_stdPlane isHyperbolicPlane_stdPlane longBlock shortBlock
  commute_shortBlock_longBlock SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Q3.Q3V.Chain (exists_linearBlockStandardPair_shortSub
  exists_symplecticBlockStandardPair_shortSub shortSub_of_ne)

open scoped MatrixGroups

local notation "F₃" => GaloisField 3 1


variable {G : Type} [Group G]

theorem commutes_partner_of_perfect3' [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hP1 : LocalOddCentral Ω {z})
    (hO3 : LocalOddThreeFree3 Ω z) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hD : Nat.card ι ≤ 4)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t) {S : Subgroup G}
    (hS : ⁅S, S⁆ = S) (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) : Commutes β S := by
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 ht (hh ▸ hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj hΩ.conjInvariant h z hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]
    exact localOddThreeFree3_conj hΩ.conjInvariant h z hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  have hnorm := Q3TY.perfect_le_normalizer_of_involution3 (Gaps.fundNoncentral 3) hΩ hex hP1t
    hO3t Dt hD hSt hS hβ ht
  obtain ⟨e⟩ := ht.nonempty_equiv_sl2 (hex β hβ)
  have hcent := Q3TY.perfect_le_centralizer_of_normalizes_sl2 e hS hnorm
  intro b hb s hs
  exact Subgroup.mem_centralizer_iff.mp (hcent hs) b hb

theorem f4Chain3_of_nodes [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hP1 : LocalOddCentral Ω {z})
    (hO3 : LocalOddThreeFree3 Ω z) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hD : Nat.card ι ≤ 4)
    {β J : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t) (hJ : J ∈ Ω)
    (hβJ : ∃ W, WeakCT.LinearBlockStandardPair F₃ W β J) (Θ' : StatedSp 3 F₃ →* G)
    (hker : Θ'.ker ≤ Subgroup.center (StatedSp 3 F₃))
    (hJΘ : (longBlock F₃ 3 2).range.map Θ' = J)
    (hN₁ : (shortBlock F₃ (by decide : (1 : Fin 3) ≠ 2)).range.map Θ' ≤
      Subgroup.centralizer ({t} : Set G))
    (hN₂ : (shortBlock F₃ (by decide : (0 : Fin 3) ≠ 1)).range.map Θ' ≤
      Subgroup.centralizer ({t} : Set G)) :
    ∃ U : Fin 4 → Subgroup G, U 1 ∈ Ω ∧
      (∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
        ∃ W, WeakCT.LinearBlockStandardPair F₃ W (U i) (U j)) ∧
      (∃ W, SymplecticBlockStandardPair F₃ W (U 1) (U 2)) := by
  classical
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  obtain ⟨W₁₂, hW₁₂⟩ : ∃ W, WeakCT.LinearBlockStandardPair F₃ W
      ((shortBlock F₃ h12).range.map Θ') ((shortBlock F₃ h01).range.map Θ') := by
    obtain ⟨W, hW⟩ := exists_linearBlockStandardPair_shortSub Θ' hker h01 h12 h02
    rw [shortSub_of_ne h01, shortSub_of_ne h12] at hW
    exact ⟨W, hW.symm⟩
  have hjoin := Gaps.linear_eq_sup hW₁₂
  obtain ⟨θ, hθr, -, -, -⟩ := WeakCT.pair_normalize hW₁₂
  have hperf : Group.IsPerfect SL(3, F₃) := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
    (by norm_num)
  have hS : ⁅W₁₂, W₁₂⁆ = W₁₂ := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact W₁₂.mul_mem (W₁₂.mul_mem (W₁₂.mul_mem ha hb) (W₁₂.inv_mem ha)) (W₁₂.inv_mem hb)
    rw [← hθr]
    exact SpAdapt.range_le_commutator_aux θ
  have hSt : W₁₂ ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [hjoin]
    exact sup_le hN₁ hN₂
  have hc : Commutes β W₁₂ :=
    commutes_partner_of_perfect3' hΩ hex hz hsingle hP1 hO3 D hD hβ ht hS hSt
  have hcN₁ : Commutes β ((shortBlock F₃ h12).range.map Θ') := fun a ha b hb =>
    hc a ha b (by rw [hjoin]; exact Subgroup.mem_sup_left hb)
  have hcN₂ : Commutes β ((shortBlock F₃ h01).range.map Θ') := fun a ha b hb =>
    hc a ha b (by rw [hjoin]; exact Subgroup.mem_sup_right hb)
  have hJN₂ : Commutes J ((shortBlock F₃ h01).range.map Θ') := by
    rw [← hJΘ]
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩ _ ⟨_, ⟨s, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    have hc := commute_shortBlock_longBlock h01 (k := 2) (by decide) (by decide) s B
    exact congrArg Θ' hc.symm.eq
  obtain ⟨Wsp, hWsp⟩ := exists_symplecticBlockStandardPair_shortSub (K := F₃) (by norm_num) h12 Θ'
    hker
  rw [hJΘ, shortSub_of_ne h12] at hWsp
  refine ⟨![β, J, (shortBlock F₃ h12).range.map Θ', (shortBlock F₃ h01).range.map Θ'], hJ, ?_, ?_,
    ⟨Wsp, hWsp⟩⟩
  · intro i j hij a ha b hb
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact hcN₁ a ha b hb
      | exact hcN₂ a ha b hb
      | exact hJN₂ a ha b hb
  · intro i j hij hi
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact absurd rfl hi
      | exact hβJ
      | exact ⟨W₁₂, hW₁₂⟩

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
