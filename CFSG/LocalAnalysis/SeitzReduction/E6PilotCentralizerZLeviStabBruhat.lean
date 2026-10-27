module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStabWeyl

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

local instance e6ZLeviStabBruhatNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem zHighLow_not_mem_zFrame :
    (∀ β ∈ zHigh, β ∉ zFrame) ∧ ∀ β ∈ zLow, β ∉ zFrame := by
  decide +kernel

@[expose] def zNegLeviRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {δ | IsRoot .E6 δ ∧ height δ < 0 ∧ δ 3 = 0}

variable {K : Type} [Field K]

@[expose] def zInvNeg (c : (Fin Tag.E6.rank → ℤ) → K) : Prop :=
  (∀ β ∈ zFrame, c β = 1) ∧ ∀ β ∈ zHigh, c β = 0

@[expose] def zInvPos (c₀ c : (Fin Tag.E6.rank → ℤ) → K) : Prop :=
  (∀ β ∈ zFrame, c β = c₀ β) ∧ ∀ β ∈ zLow, c β = 0


theorem zInvNeg_zCoeff : zInvNeg (zCoeff (K := K)) :=
  ⟨fun _ hβ => zCoeff_eq_one_of_mem hβ,
    fun β hβ => zCoeff_eq_zero_of_not_mem (zHighLow_not_mem_zFrame.1 β hβ)⟩

theorem rootSpan_zNegLeviRoots_le_zInvSubgroup [CharP K 2] :
    rootSpan .E6 K zNegLeviRoots ≤ zInvSubgroup K zInvNeg := by
  refine rootSpan_le_zInvSubgroup fun α hα t => ?_
  obtain ⟨hαr, hαneg, hα3⟩ := hα
  refine pinnedX_mem_zInvSubgroup (fun t c hc => ⟨_, conj_rootProd_zPsi hαr hα3.ge t c, ?_⟩) t
  have hfeed : ∀ ρ, (ρ ∈ zFrame ∨ ρ ∈ zHigh) → ρ ∈ zPsi → conjCoeff α t zPsi c ρ = c ρ :=
    fun ρ hρ hρΨ => conjCoeff_apply_of_forall zPsi_nodup t c hρΨ fun β hβ he =>
      hc.2 β (zHigh_closed hρ hβ ⟨IsRoot.neg hαr, by rw [height_neg]; omega⟩
        (by rw [Pi.neg_apply, hα3, neg_zero]) (by rw [neg_neg]; exact he))
  exact ⟨fun β hβ => by rw [hfeed β (Or.inl hβ) (mem_zPsi_of_mem_zFrame hβ)]; exact hc.1 β hβ,
    fun β hβ => by rw [hfeed β (Or.inr hβ) (mem_zPsi_of_mem_zHigh hβ)]; exact hc.2 β hβ⟩

theorem posUnipotent_le_zInvSubgroup_zInvPos [CharP K 2] (c₀ : (Fin Tag.E6.rank → ℤ) → K) :
    posUnipotent .E6 K ≤ zInvSubgroup K (zInvPos c₀) := by
  refine rootSpan_le_zInvSubgroup fun α hα t => pinnedX_mem_zInvSubgroup (fun t c hc =>
    ⟨_, conj_rootProd_zPsi hα.1 (level_nonneg_of_pos hα) t c, ?_⟩) t
  have hfeed : ∀ ρ, (ρ ∈ zFrame ∨ ρ ∈ zLow) → ρ ∈ zPsi → conjCoeff α t zPsi c ρ = c ρ :=
    fun ρ hρ hρΨ => conjCoeff_apply_of_forall zPsi_nodup t c hρΨ fun β hβ he =>
      hc.2 β (zLow_closed hρ hβ hα he)
  exact ⟨fun β hβ => by rw [hfeed β (Or.inl hβ) (mem_zPsi_of_mem_zFrame hβ)]; exact hc.1 β hβ,
    fun β hβ => by rw [hfeed β (Or.inr hβ) (mem_zPsi_of_mem_zLow hβ)]; exact hc.2 β hβ⟩

theorem commute_zAS_of_mem_torusGroup_mul [CharP K 2] {h u : ModGL .E6 K}
    (hh : h ∈ torusGroup .E6 K) (hu : u ∈ posUnipotent .E6 K)
    (hz : (h * u)⁻¹ * zAS K * (h * u) = zAS K) :
    h * zAS K = zAS K * h ∧ u * zAS K = zAS K * u := by
  have hr : ∀ β ∈ zPsi, IsRoot .E6 β := fun _ hβ => isRoot_of_mem_zPsi hβ
  set c₀ : (Fin Tag.E6.rank → ℤ) → K := fun β => torusRootChar h⁻¹ β * zCoeff β with hc₀def
  have hX : h⁻¹ * zAS K * h = rootProd .E6 K zPsi c₀ := by
    have := conj_rootProd_of_mem_torusGroup (inv_mem hh) hr (zCoeff (K := K))
    rw [inv_inv, rootProd_zPsi_zCoeff] at this
    exact this
  have hc₀ : zInvPos c₀ c₀ := ⟨fun _ _ => rfl, fun β hβ => by
    show torusRootChar h⁻¹ β * zCoeff β = 0
    rw [zInvB_zCoeff.2 β hβ, mul_zero]⟩
  obtain ⟨-, ⟨c'', e'', hc''⟩⟩ := posUnipotent_le_zInvSubgroup_zInvPos c₀ hu c₀ hc₀
  have hE : rootProd .E6 K zPsi c'' = rootProd .E6 K zPsi zCoeff := by
    rw [← e'', ← hX, rootProd_zPsi_zCoeff,
      show u⁻¹ * (h⁻¹ * zAS K * h) * u = (h * u)⁻¹ * zAS K * (h * u) by group]
    exact hz
  have hinj := rootProd_injective zPsi_nodup (fun _ hρ => pos_of_mem_zPsi hρ) hE
  have hX' : h⁻¹ * zAS K * h = zAS K := by
    rw [hX, ← rootProd_zPsi_zCoeff]
    refine rootProd_congr fun β hβ => ?_
    by_cases hF : β ∈ zFrame
    · rw [← hc''.1 β hF, hinj β hβ]
    · show torusRootChar h⁻¹ β * zCoeff β = zCoeff β
      rw [zCoeff_eq_zero_of_not_mem hF, mul_zero]
  have hhz : h * zAS K = zAS K * h := by
    calc h * zAS K = h * (h⁻¹ * zAS K * h) := by rw [hX']
      _ = zAS K * h := by group
  refine ⟨hhz, ?_⟩
  have huz : u⁻¹ * zAS K * u = zAS K := by
    calc u⁻¹ * zAS K * u = u⁻¹ * (h⁻¹ * zAS K * h) * u := by rw [hX']
      _ = (h * u)⁻¹ * zAS K * (h * u) := by group
      _ = zAS K := hz
  calc u * zAS K = u * (u⁻¹ * zAS K * u) := by rw [huz]
    _ = zAS K * u := by group

theorem canonicalRep_mul_zAS_mul_inv [CharP K 2] {w : WeylGroup .E6}
    (hF : ∀ β ∈ zFrame, w • β ∈ zFrame) :
    canonicalRep (coxeterSystem .E6) K w * zAS K * (canonicalRep (coxeterSystem .E6) K w)⁻¹ =
      zAS K := by
  have hr : ∀ β ∈ zFrame, IsRoot .E6 β := fun β hβ =>
    isRoot_of_mem_zPsi (mem_zPsi_of_mem_zFrame hβ)
  have hnd : (zFrame.map fun β => w • β).Nodup := zFrame_nodup.map (MulAction.injective w)
  have hsub : ∀ x ∈ zFrame.map (fun β => w • β), x ∈ zFrame := fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    exact hF β hβ
  have hperm : (zFrame.map fun β => w • β).Perm zFrame :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp)
  have hcomm' : RootCommFamily .E6 K (zFrame.map fun β => w • β) :=
    zPsi_comm.of_sublist fun x hx => mem_zPsi_of_mem_zFrame (hsub x hx)
  have e := rootProd_perm hcomm' hperm (fun _ => (1 : K))
  simp only [rootProd, List.map_map, Function.comp_def] at e
  rw [zAS, rootProd, canonicalRep_mul_list_prod_mul_inv_of_charTwo w hr]
  exact e

theorem exists_zBruhat_factors [CharP K 2] {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    (hgz : g * zAS K = zAS K * g) :
    ∃ w : WeylGroup .E6, w ∈ parabolicWeylGroup .E6 zNodes ∧ (∀ β ∈ zFrame, w • β ∈ zFrame) ∧
      ∃ h ∈ torusGroup .E6 K, ∃ u ∈ posUnipotent .E6 K, ∃ v ∈ rootSpan .E6 K (inversionSet w),
        h * zAS K = zAS K * h ∧ u * zAS K = zAS K * u ∧ v * zAS K = zAS K * v ∧
          g = h * u * canonicalRep (coxeterSystem .E6) K w * v := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hg
  obtain ⟨hwJ, hwF⟩ := smul_zFrame_of_commute_zAS hw hgz
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := (bijOn_bruhatCell (K := K) w).surjOn hw
  simp only at hbv
  have hb' : b ∈ (torusGroup .E6 K : Set (ModGL .E6 K)) *
      (posUnipotent .E6 K : Set (ModGL .E6 K)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ torusGroup_le_normalizer_posUnipotent]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  set n := canonicalRep (coxeterSystem .E6) K w with hn
  have hnz : n * zAS K * n⁻¹ = zAS K := canonicalRep_mul_zAS_mul_inv hwF
  have key : n * (v * zAS K * v⁻¹) * n⁻¹ = (h * u)⁻¹ * zAS K * (h * u) := by
    rw [← hbv] at hgz
    calc n * (v * zAS K * v⁻¹) * n⁻¹
        = (h * u)⁻¹ * (h * u * n * v * zAS K) * (h * u * n * v)⁻¹ * (h * u) := by group
      _ = (h * u)⁻¹ * (zAS K * (h * u * n * v)) * (h * u * n * v)⁻¹ * (h * u) := by rw [hgz]
      _ = (h * u)⁻¹ * zAS K * (h * u) := by group
  have hv' : n * v * n⁻¹ ∈ rootSpan .E6 K zNegLeviRoots := by
    have hS : ∀ α ∈ inversionSet w, IsRoot .E6 α := fun α hα => hα.1
    have h1 := canonicalRep_conj_mem_rootSpan (K := K) (w := w) hS hv
    refine rootSpan_mono ?_ h1
    rintro _ ⟨δ, hδ, rfl⟩
    have hδJ := inversionSet_subset_parabolicPosRoots hwJ hδ
    have hwδ := smul_mem_parabolicRoots hwJ hδJ.1
    exact ⟨hwδ.1, hδ.2.2.2, hwδ.2 3 (by simp [zNodes])⟩
  have hn' : n⁻¹ * zAS K * n = zAS K := by
    calc n⁻¹ * zAS K * n = n⁻¹ * (n * zAS K * n⁻¹) * n := by rw [hnz]
      _ = zAS K := by group
  have hv'eq : (n * v * n⁻¹) * zAS K * (n * v * n⁻¹)⁻¹ = (h * u)⁻¹ * zAS K * (h * u) := by
    calc (n * v * n⁻¹) * zAS K * (n * v * n⁻¹)⁻¹ = n * (v * (n⁻¹ * zAS K * n) * v⁻¹) * n⁻¹ := by
          group
      _ = n * (v * zAS K * v⁻¹) * n⁻¹ := by rw [hn']
      _ = _ := key
  obtain ⟨⟨cL, eL, hcL⟩, -⟩ :=
    rootSpan_zNegLeviRoots_le_zInvSubgroup (K := K) hv' zCoeff zInvNeg_zCoeff
  have hbB : h * u ∈ borelGroup .E6 K := mul_mem (mem_sup_left hh) (mem_sup_right hu)
  obtain ⟨-, ⟨cR, eR, hcR⟩⟩ := borelGroup_le_zInvSubgroup_zInvB (K := K) hbB zCoeff zInvB_zCoeff
  rw [rootProd_zPsi_zCoeff] at eL eR
  have hE : rootProd .E6 K zPsi cL = rootProd .E6 K zPsi cR := by rw [← eL, ← eR, hv'eq]
  have hinj := rootProd_injective zPsi_nodup (fun _ hρ => pos_of_mem_zPsi hρ) hE
  have hcLz : ∀ ρ ∈ zPsi, cL ρ = zCoeff ρ := by
    intro ρ hρ
    have hρ' : ρ ∈ zFrame ∨ ρ ∈ zHigh ∨ ρ ∈ zLow := by
      simp only [zPsi, zHigh, List.mem_append] at hρ ⊢
      tauto
    rcases hρ' with hF | hH | hL
    · rw [hcL.1 ρ hF, zCoeff_eq_one_of_mem hF]
    · rw [hcL.2 ρ hH, zCoeff_eq_zero_of_not_mem (zHighLow_not_mem_zFrame.1 ρ hH)]
    · rw [hinj ρ hρ, hcR.2 ρ hL, zCoeff_eq_zero_of_not_mem (zHighLow_not_mem_zFrame.2 ρ hL)]
  have hL : (n * v * n⁻¹) * zAS K * (n * v * n⁻¹)⁻¹ = zAS K := by
    rw [eL, rootProd_congr hcLz, rootProd_zPsi_zCoeff]
  have hR : (h * u)⁻¹ * zAS K * (h * u) = zAS K := by rw [← hv'eq, hL]
  obtain ⟨hhz, huz⟩ := commute_zAS_of_mem_torusGroup_mul hh hu hR
  have hvz : v * zAS K * v⁻¹ = zAS K := by
    have e : n * (v * zAS K * v⁻¹) * n⁻¹ = n * zAS K * n⁻¹ := by rw [key, hR, hnz]
    calc v * zAS K * v⁻¹ = n⁻¹ * (n * (v * zAS K * v⁻¹) * n⁻¹) * n := by group
      _ = n⁻¹ * (n * zAS K * n⁻¹) * n := by rw [e]
      _ = zAS K := by group
  have hvC : v * zAS K = zAS K * v := by
    calc v * zAS K = v * zAS K * v⁻¹ * v := by group
      _ = zAS K * v := by rw [hvz]
  exact ⟨w, hwJ, hwF, h, hh, u, hu, v, hv, hhz, huz, hvC, hbv.symm⟩

end CFSG.SeitzReduction.E6Pilot
