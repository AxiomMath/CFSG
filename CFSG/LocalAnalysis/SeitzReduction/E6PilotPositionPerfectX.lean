module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionPerfect

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def oddDerivE6XFrame : List (Fin Tag.E6.rank → ℤ) :=
  [highRoot .E6]

@[expose] def oddDerivE6XDeriv :
    List ((Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)) := [
  (![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, -1, 0, 0]),
  (![0, 1, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 0, -1, 0, 0, 0]),
  (![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![0, 0, -1, 0, 0, 0]),
  (![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 0, -1, 0, 0, 0]),
  (![0, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 0, 0], ![-1, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![-1, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![-1, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 0], ![-1, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 1, 1], ![-1, 0, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 2, 1], ![-1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1], ![1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 0], ![1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 1, 1], ![1, 0, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 2, 1], ![0, 1, 1, 2, 2, 1], ![1, 0, 0, 0, 0, 0]),
  (![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 1, 0], ![0, 0, 1, 0, 0, 0]),
  (![1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 1, 1], ![0, 0, 1, 0, 0, 0]),
  (![1, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 1], ![0, 0, 1, 0, 0, 0]),
  (![1, 1, 2, 3, 2, 1], ![1, 1, 2, 2, 2, 1], ![0, 0, 0, 1, 0, 0]),
  (![1, 2, 2, 3, 2, 1], ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1])]

@[expose] def e6PosXPerpPos : List (Fin Tag.E6.rank → ℤ) := [
  ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
  ![1, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1]]

@[expose] def e6PosXPerp : List (Fin Tag.E6.rank → ℤ) :=
  e6PosXPerpPos ++ e6PosXPerpPos.map fun v => -v

theorem e6PosX_check :
    (oddDerivOK .E6 (oddDerivE6XDeriv.map Prod.fst) e6PosXPerp oddDerivE6XDeriv &&
      oddDerivFrameB .E6 oddDerivE6XFrame (oddDerivE6XDeriv.map Prod.fst ++ e6PosXPerp) &&
      E8Pilot.perpNegClosedB e6PosXPerp) = true := by
  decide +kernel

@[expose] def e6PosXCoverB : Bool :=
  Tag.E6.rootCertificate.roots.all fun c =>
    (!decide (0 < decodeVec (τ := .E6) c (highNode .E6)) ||
        oddDerivMemB (decodeVec c) (oddDerivE6XDeriv.map Prod.fst)) &&
      (!decide (decodeVec (τ := .E6) c (highNode .E6) = 0) ||
        oddDerivMemB (decodeVec c) e6PosXPerp)

theorem e6PosXCoverB_eq_true : e6PosXCoverB = true := by
  decide +kernel


theorem mem_e6PosX_of_isRoot {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    (0 < α (highNode .E6) → α ∈ oddDerivE6XDeriv.map Prod.fst) ∧
      (α (highNode .E6) = 0 → α ∈ e6PosXPerp) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hα
  have h1 := List.all_eq_true.1 e6PosXCoverB_eq_true _
    (List.getElem_mem (l := Tag.E6.rootCertificate.roots) hk)
  rw [← List.getD_eq_getElem _ 0 hk] at h1
  have e : Tag.E6.rootCertificate.root k =
      decodeVec (Tag.E6.rootCertificate.roots.getD k 0) := rfl
  rw [← e] at h1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h1
  obtain ⟨h1a, h1b⟩ := h1
  refine ⟨fun hpos => ?_, fun hzero => ?_⟩
  · rcases h1a with h | h
    · exact absurd hpos h
    · exact mem_of_oddDerivMemB h
  · rcases h1b with h | h
    · exact absurd hzero h
    · exact mem_of_oddDerivMemB h

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def e6PosXSpan : Subgroup (ModGL .E6 K) :=
  rootSpan .E6 K {γ | γ ∈ oddDerivE6XDeriv.map Prod.fst ∨ γ ∈ e6PosXPerp}

theorem commutator_e6PosXSpan [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅e6PosXSpan K, e6PosXSpan K⁆ = e6PosXSpan K := by
  have h := e6PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hD, -⟩, hneg⟩ := h
  exact E8Pilot.commutator_rootSpan_eq_self_of_oddDerivOK hq hD (oddDeriv_cov_map_fst _)
    (E8Pilot.neg_mem_of_perpNegClosedB hneg)

theorem e6PosXSpan_le_centralizer :
    e6PosXSpan K ≤ Subgroup.centralizer {pinnedX .E6 K (highRoot .E6) 1} := by
  have h := e6PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hD, hF⟩, -⟩ := h
  have hroots : ∀ γ ∈ oddDerivE6XDeriv.map Prod.fst ++ e6PosXPerp, IsRoot .E6 γ := by
    simp only [oddDerivOK, Bool.and_eq_true, List.all_eq_true] at hD
    exact fun γ hγ => isRoot_of_oddDerivIsRootB (hD.1.1 γ hγ)
  simp only [oddDerivFrameB, Bool.and_eq_true, List.all_eq_true] at hF
  obtain ⟨hFr, hFc⟩ := hF
  refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 : pinnedX .E6 K γ c * (oddDerivE6XFrame.map fun σ => pinnedX .E6 K σ 1).prod =
      (oddDerivE6XFrame.map fun σ => pinnedX .E6 K σ 1).prod * pinnedX .E6 K γ c :=
    (commute_pinnedX_list_prod_of_oddDerivCommB (hroots γ (List.mem_append.2 hγ))
      (fun σ hσ => isRoot_of_oddDerivIsRootB (hFr σ hσ))
      (List.all_eq_true.2 (hFc γ (List.mem_append.2 hγ))) c fun _ => (1 : K)).eq
  have h3 : (oddDerivE6XFrame.map fun σ => pinnedX .E6 K σ 1).prod =
      pinnedX .E6 K (highRoot .E6) 1 := by
    rw [oddDerivE6XFrame, List.map_singleton, List.prod_singleton]
  rw [h3] at h1
  exact h1

theorem centralizer_pinnedX_highRoot_inf_eq_e6PosXSpan :
    centralizer ({pinnedX .E6 K (highRoot .E6) 1} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K =
      e6PosXSpan K := by
  refine le_antisymm ?_ (le_inf e6PosXSpan_le_centralizer
    (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α))
  rw [EPilot.centralizer_pinnedX_highRoot_inf_eq (Or.inl rfl) one_ne_zero]
  have hgen : ∀ α, α ∈ oddDerivE6XDeriv.map Prod.fst ∨ α ∈ e6PosXPerp →
      rootSubgroup .E6 K α ≤ e6PosXSpan K := fun α hα =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ {γ | γ ∈ oddDerivE6XDeriv.map Prod.fst ∨
      γ ∈ e6PosXPerp}) => rootSubgroup .E6 K δ) α hα le_rfl
  refine sup_le (iSup₂_le fun α hα => hgen α (Or.inl ?_)) (iSup₂_le fun α hα => hgen α (Or.inr ?_))
  · obtain ⟨hr, hpos⟩ := EPilot.mem_parabolicRadicalRoots_perpNodes.1 hα
    exact (mem_e6PosX_of_isRoot hr).1 hpos
  · exact (mem_e6PosX_of_isRoot hα.1).2 hα.2

theorem commutator_centralizer_pinnedElt_highRoot_E6 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} : Set (adjointGroup .E6 K)),
        centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} :
          Set (adjointGroup .E6 K))⁆ =
      centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} : Set (adjointGroup .E6 K)) := by
  have hsub : e6PosXSpan K ≤ adjointGroup .E6 K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have h : centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} :
      Set (adjointGroup .E6 K)) = (e6PosXSpan K).subgroupOf (adjointGroup .E6 K) := by
    rw [F4Pilot.centralizer_eq_subgroupOf]
    exact congrArg (fun H => H.subgroupOf (adjointGroup .E6 K))
      centralizer_pinnedX_highRoot_inf_eq_e6PosXSpan
  rw [h]
  exact CFSG.SeitzReduction.commutator_subgroupOf_eq_self hsub (commutator_e6PosXSpan hq)

theorem commutator_centralizer_pinnedElt_highRoot_E6_of_one_le {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    ⁅centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} : Set (adjointGroup .E6 K)),
        centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} :
          Set (adjointGroup .E6 K))⁆ =
      centralizer ({EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)} : Set (adjointGroup .E6 K)) := by
  haveI := F4Pilot.finite_of_natCard_eq_two_pow hK
  haveI := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact E8Pilot.commutator_centralizer_pinnedElt_highRoot_two (Or.inl rfl) (by simpa using hK)
  · refine commutator_centralizer_pinnedElt_highRoot_E6 ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

end CFSG.SeitzReduction.E6Pilot
