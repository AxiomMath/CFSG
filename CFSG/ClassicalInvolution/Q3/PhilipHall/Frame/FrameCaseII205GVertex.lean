module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205QVertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GRow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205MNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3


section Twins

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
  {a c : G} {d : Std20Frame K K' J S R R' W V z t}

theorem isUniqueInvolution_frameKa_of_vertex (hv : Vertex205 d a c) :
    IsUniqueInvolution (frameKa K c)
      (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) := by
  have hz : z ∈ tightCore (K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mp (z_mem_frameKa_of_vertex hv)
  exact isUniqueInvolution_subgroupOf (isUniqueInvolution_mono d.viol.hzK
    ((tightCore_le _).trans inf_le_left) hz) ((tightCore_le _).trans inf_le_right)

theorem isUniqueInvolution_frameKa'_of_vertex (hv : Vertex205 d a c) :
    IsUniqueInvolution (frameKa K' c)
      (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) := by
  have hz : z ∈ tightCore (K' ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mp (z_mem_frameKa'_of_vertex hv)
  exact isUniqueInvolution_subgroupOf (isUniqueInvolution_mono d.late_hzK'
    ((tightCore_le _).trans inf_le_left) hz) ((tightCore_le _).trans inf_le_right)

theorem isUniqueInvolution_map_of_odd_core {M : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    {u : ↥(Subgroup.centralizer ({c} : Set G))} (hu : IsUniqueInvolution M u) :
    IsUniqueInvolution
      (M.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)))))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G))) u) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  exact isUniqueInvolution_map_mk_of_odd
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)) hu

end Twins

section Block

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_aStar_of_twins {Ω : Set (Subgroup Y)} {M₁ M₂ : Subgroup Y} {u : Y} (h₂ : M₂ ∈ Ω)
    (hu₁ : IsUniqueInvolution M₁ u) (hu₂ : IsUniqueInvolution M₂ u) : M₂ ∈ aStar Ω M₁ := by
  by_cases h : M₂ = M₁
  · rw [h]
    exact self_mem_aStar _
  · exact Relation.ReflTransGen.single ⟨h₂, Or.inr (Or.inr ⟨⟨h₂, u, hu₁, hu₂⟩, h⟩)⟩

end Block

section Vertex

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
  {a c : G} {d : Std20Frame K K' J S R R' W V z t}

theorem frameKa_map_mem_aStar (hv : Vertex205 d a c)
    {M₀ : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    (hM₀ : M₀ = frameKa K c ∨ M₀ = frameKa K' c) :
    (frameKa K c).map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      aStar (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
        (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(Subgroup.centralizer ({c} : Set G))))) ∧
    (frameKa K' c).map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      aStar (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
        (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(Subgroup.centralizer ({c} : Set G))))) := by
  have h1 := isUniqueInvolution_map_of_odd_core (isUniqueInvolution_frameKa_of_vertex hv)
  have h2 := isUniqueInvolution_map_of_odd_core (isUniqueInvolution_frameKa'_of_vertex hv)
  have m1 : (frameKa K c).map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))) := ⟨_, frameKa_mem_omegaAFam_of_vertex hv, rfl⟩
  have m2 : (frameKa K' c).map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))) := ⟨_, frameKa'_mem_omegaAFam_of_vertex hv, rfl⟩
  rcases hM₀ with rfl | rfl
  · exact ⟨self_mem_aStar _, mem_aStar_of_twins m2 h1 h2⟩
  · exact ⟨mem_aStar_of_twins m1 h2 h1, self_mem_aStar _⟩

theorem oddQuotMk_t_mem (hv : Vertex205 d a c) {T : Subgroup (Balance.OddQuot c)}
    (h₁ : (frameKa K c).map (Balance.oddQuotMk c) ≤ T)
    (h₂ : (frameKa K' c).map (Balance.oddQuotMk c) ≤ T) :
    Balance.oddQuotMk c ⟨t, hv.t_cent⟩ ∈ T := by
  have hR : R.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ frameKa K c := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_tightCore_of_isPGroup (le_inf d.hR.1 hv.R_le) d.hR.2.1
      (Subgroup.mem_subgroupOf.mp hx))
  have hR' : R'.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ frameKa K' c := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_tightCore_of_isPGroup (le_inf d.hR'.1 hv.R'_le) d.hR'.2.1
      (Subgroup.mem_subgroupOf.mp hx))
  have hsup : (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      frameKa K c ⊔ frameKa K' c := by
    rw [Subgroup.subgroupOf_sup hv.R_le hv.R'_le]
    exact sup_le_sup hR hR'
  have ht : (⟨t, hv.t_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr (t_mem_sup_R_R' d)
  have hmap : (frameKa K c ⊔ frameKa K' c).map (Balance.oddQuotMk c) ≤ T := by
    rw [Subgroup.map_sup]
    exact sup_le h₁ h₂
  exact hmap (Subgroup.mem_map_of_mem _ (hsup ht))

theorem modOdd_B_le_sup_center (hv : Vertex205 d a c) {T : Subgroup (Balance.OddQuot c)}
    (hzT : Balance.oddQuotMk c ⟨z, hv.z_cent⟩ ∈ T)
    (htT : Balance.oddQuotMk c ⟨t, hv.t_cent⟩ ∈ T) :
    Balance.modOdd c (Subgroup.closure ({z, t, a} : Set G)) ≤
      T ⊔ Subgroup.center (Balance.OddQuot c) := by
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcS : Balance.oddQuotMk c ⟨c, hcC⟩ ∈ T ⊔ Subgroup.center (Balance.OddQuot c) := by
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ : ∃ w', Balance.oddQuotMk c w' = w :=
      QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w'.2)
  have hgen : Subgroup.closure ({z, t, a} : Set G) ≤
      ((T ⊔ Subgroup.center (Balance.OddQuot c)).comap (Balance.oddQuotMk c)).map
        (Subgroup.centralizer ({c} : Set G)).subtype := by
    rw [hv.gen]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with h | h | h
    · exact ⟨⟨z, hv.z_cent⟩, Subgroup.mem_comap.mpr (Subgroup.mem_sup_left hzT), h.symm⟩
    · exact ⟨⟨t, hv.t_cent⟩, Subgroup.mem_comap.mpr (Subgroup.mem_sup_left htT), h.symm⟩
    · exact ⟨⟨c, hcC⟩, Subgroup.mem_comap.mpr hcS, (Set.mem_singleton_iff.mp h).symm⟩
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Balance.mem_modOdd_iff.mp hx
  obtain ⟨s, hs, hsk⟩ := hgen hk
  have hsk' : s = k := Subtype.ext hsk
  rw [← hsk']
  exact Subgroup.mem_comap.mp hs

theorem hyp51At_of_moved_vertexG (hd : Frame205Data d a) (hv : Vertex205 d a c)
    {T : Subgroup (Balance.OddQuot c)}
    (hzT : Balance.oddQuotMk c ⟨z, hv.z_cent⟩ ∈ T)
    (htT : Balance.oddQuotMk c ⟨t, hv.t_cent⟩ ∈ T)
    (hU : ∀ L₁ L₂ : Subgroup (Balance.OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, Balance.oddQuotMk c ⟨z, hv.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hv.z_cent⟩) →
      (∃ y ∈ L₂, Balance.oddQuotMk c ⟨z, hv.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hv.z_cent⟩) →
        L₁ = L₂)
    (hAO : ∀ L : Subgroup (Balance.OddQuot c), CFSG.IsComponent L →
      (∃ y ∈ L, Balance.oddQuotMk c ⟨z, hv.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hv.z_cent⟩) →
        Q3NM.AutOddFree ↥L ∨ (Q3NM.AutOddFreeInner ↥L ∧
          ∀ y ∈ T, ∃ l ∈ L, ∀ w ∈ L, y * w * y⁻¹ = l * w * l⁻¹)) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hB := isElemAbelian_B_vertex hd
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have hBle := modOdd_B_le_sup_center hv hzT htT
  refine TL4.hyp51At_of_moved (fun b hb => (pow_two b).symm.trans (hB.2 b hb))
    (fun b hb b' hb' => congrArg Subtype.val
      (hB.1.is_comm.comm (⟨b, hb⟩ : Subgroup.closure ({z, t, a} : Set G)) ⟨b', hb'⟩))
    ⟨Balance.oddQuotMk c ⟨z, hv.z_cent⟩, Balance.oddQuotMk_mem_modOdd hzB hv.z_cent,
      Lemma52Proof.oddQuotMk_not_mem_zpowers hB hv.mem hv.ne_one hzB d.viol.hzK.ne_one hv.z_ne
        hv.z_cent, hU⟩ ?_
  intro L hL hm x hx hxN hxmv
  rcases hAO L hL (exists_not_comm_of_movedByAll_vertex hd hv hm) with h | ⟨hin, hact⟩
  · exact h.on _
  · obtain ⟨l, hlL, hl⟩ := exists_inner_of_mem_sup_center hact (hBle hx)
    exact hin.toOn.mono fun σ hσ => mem_innSubgroup_of_isInducedAut hσ hlL hl

end Vertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
