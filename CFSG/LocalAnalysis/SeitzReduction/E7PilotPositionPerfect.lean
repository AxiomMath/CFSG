module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotOddCore
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def e7PosXPerpPos : List (Fin Tag.E7.rank → ℤ) := [
  ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1, 0],
  ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0, 0],
  ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0, 0],
  ![0, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 0], ![0, 1, 1, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 0],
  ![0, 1, 1, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 1]]

@[expose] def e7PosXPerp : List (Fin Tag.E7.rank → ℤ) :=
  e7PosXPerpPos ++ e7PosXPerpPos.map fun v => -v

theorem e7PosX_check :
    (oddDerivOK .E7 (oddDerivE7XDeriv.map Prod.fst) e7PosXPerp oddDerivE7XDeriv &&
      oddDerivFrameB .E7 oddDerivE7XFrame (oddDerivE7XDeriv.map Prod.fst ++ e7PosXPerp) &&
      E8Pilot.perpNegClosedB e7PosXPerp) = true := by
  decide +kernel

@[expose] def e7PosXCoverB : Bool :=
  Tag.E7.rootCertificate.roots.all fun c =>
    (!decide (0 < decodeVec (τ := .E7) c (highNode .E7)) ||
        oddDerivMemB (decodeVec c) (oddDerivE7XDeriv.map Prod.fst)) &&
      (!decide (decodeVec (τ := .E7) c (highNode .E7) = 0) ||
        oddDerivMemB (decodeVec c) e7PosXPerp)

theorem e7PosXCoverB_eq_true : e7PosXCoverB = true := by
  decide +kernel


theorem mem_e7PosX_of_isRoot {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) :
    (0 < α (highNode .E7) → α ∈ oddDerivE7XDeriv.map Prod.fst) ∧
      (α (highNode .E7) = 0 → α ∈ e7PosXPerp) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E7.rootCertificate_check hα
  have h1 := List.all_eq_true.1 e7PosXCoverB_eq_true _
    (List.getElem_mem (l := Tag.E7.rootCertificate.roots) hk)
  rw [← List.getD_eq_getElem _ 0 hk] at h1
  have e : Tag.E7.rootCertificate.root k =
      decodeVec (Tag.E7.rootCertificate.roots.getD k 0) := rfl
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
@[expose] noncomputable def e7PosXSpan : Subgroup (ModGL .E7 K) :=
  rootSpan .E7 K {γ | γ ∈ oddDerivE7XDeriv.map Prod.fst ∨ γ ∈ e7PosXPerp}

theorem commutator_e7PosXSpan [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅e7PosXSpan K, e7PosXSpan K⁆ = e7PosXSpan K := by
  have h := e7PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hD, -⟩, hneg⟩ := h
  exact E8Pilot.commutator_rootSpan_eq_self_of_oddDerivOK hq hD (oddDeriv_cov_map_fst _)
    (E8Pilot.neg_mem_of_perpNegClosedB hneg)

theorem e7PosXSpan_le_centralizer :
    e7PosXSpan K ≤ Subgroup.centralizer {pinnedX .E7 K (highRoot .E7) 1} := by
  have h := e7PosX_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hD, hF⟩, -⟩ := h
  have hroots : ∀ γ ∈ oddDerivE7XDeriv.map Prod.fst ++ e7PosXPerp, IsRoot .E7 γ := by
    simp only [oddDerivOK, Bool.and_eq_true, List.all_eq_true] at hD
    exact fun γ hγ => isRoot_of_oddDerivIsRootB (hD.1.1 γ hγ)
  simp only [oddDerivFrameB, Bool.and_eq_true, List.all_eq_true] at hF
  obtain ⟨hFr, hFc⟩ := hF
  refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 : pinnedX .E7 K γ c * (oddDerivE7XFrame.map fun σ => pinnedX .E7 K σ 1).prod =
      (oddDerivE7XFrame.map fun σ => pinnedX .E7 K σ 1).prod * pinnedX .E7 K γ c :=
    (commute_pinnedX_list_prod_of_oddDerivCommB (hroots γ (List.mem_append.2 hγ))
      (fun σ hσ => isRoot_of_oddDerivIsRootB (hFr σ hσ))
      (List.all_eq_true.2 (hFc γ (List.mem_append.2 hγ))) c fun _ => (1 : K)).eq
  have h3 : (oddDerivE7XFrame.map fun σ => pinnedX .E7 K σ 1).prod =
      pinnedX .E7 K (highRoot .E7) 1 := by
    rw [oddDerivE7XFrame, List.map_singleton, List.prod_singleton]
  rw [h3] at h1
  exact h1

theorem centralizer_pinnedX_highRoot_inf_eq_e7PosXSpan :
    centralizer ({pinnedX .E7 K (highRoot .E7) 1} : Set (ModGL .E7 K)) ⊓ adjointGroup .E7 K =
      e7PosXSpan K := by
  refine le_antisymm ?_ (le_inf e7PosXSpan_le_centralizer
    (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α))
  rw [EPilot.centralizer_pinnedX_highRoot_inf_eq (Or.inr (Or.inl rfl)) one_ne_zero]
  have hgen : ∀ α, α ∈ oddDerivE7XDeriv.map Prod.fst ∨ α ∈ e7PosXPerp →
      rootSubgroup .E7 K α ≤ e7PosXSpan K := fun α hα =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ {γ | γ ∈ oddDerivE7XDeriv.map Prod.fst ∨
      γ ∈ e7PosXPerp}) => rootSubgroup .E7 K δ) α hα le_rfl
  refine sup_le (iSup₂_le fun α hα => hgen α (Or.inl ?_)) (iSup₂_le fun α hα => hgen α (Or.inr ?_))
  · obtain ⟨hr, hpos⟩ := EPilot.mem_parabolicRadicalRoots_perpNodes.1 hα
    exact (mem_e7PosX_of_isRoot hr).1 hpos
  · exact (mem_e7PosX_of_isRoot hα.1).2 hα.2

theorem commutator_centralizer_pinnedElt_highRoot_E7 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({EPilot.pinnedElt .E7 (highRoot .E7) (1 : K)} : Set (adjointGroup .E7 K)),
        centralizer ({EPilot.pinnedElt .E7 (highRoot .E7) (1 : K)} :
          Set (adjointGroup .E7 K))⁆ =
      centralizer ({EPilot.pinnedElt .E7 (highRoot .E7) (1 : K)} : Set (adjointGroup .E7 K)) := by
  have hsub : e7PosXSpan K ≤ adjointGroup .E7 K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have h : centralizer ({EPilot.pinnedElt .E7 (highRoot .E7) (1 : K)} :
      Set (adjointGroup .E7 K)) = (e7PosXSpan K).subgroupOf (adjointGroup .E7 K) := by
    rw [F4Pilot.centralizer_eq_subgroupOf]
    exact congrArg (fun H => H.subgroupOf (adjointGroup .E7 K))
      centralizer_pinnedX_highRoot_inf_eq_e7PosXSpan
  rw [h]
  exact CFSG.SeitzReduction.commutator_subgroupOf_eq_self hsub (commutator_e7PosXSpan hq)

theorem map_conj_centralizer_singleton_E7 {G : Type*} [Group G] (n x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * x * n⁻¹} : Set G) := by
  ext g
  rw [mem_map_equiv, MulAut.conj_symm_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * (n * x * n⁻¹) = n * (n⁻¹ * g * n * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * g * n)) * n⁻¹ := by rw [h]
      _ = n * x * n⁻¹ * g := by group
  · intro h
    calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * x * n⁻¹ * g) * n := by rw [h]
      _ = x * (n⁻¹ * g * n) := by group

theorem commutator_centralizer_e7Rep_zero [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)),
        centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))⁆ =
      centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)) := by
  obtain ⟨n, hn⟩ := E8Pilot.exists_conj_pinnedElt_highRoot_eq (K := K) (Or.inr (Or.inl rfl))
    (e7RepFrames_isRoot 0 _ List.mem_cons_self)
  rw [e7Rep_zero_eq_pinnedElt, ← hn, ← map_conj_centralizer_singleton_E7, ← map_commutator,
    commutator_centralizer_pinnedElt_highRoot_E7 hq]

end CFSG.SeitzReduction.E7Pilot
