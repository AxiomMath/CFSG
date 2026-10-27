module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear pairEmbed)
open CFSG.SeitzReduction.SymplecticPilot (zThreeSL)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2E6ChainLongNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6ChainLongNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Frame

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def chainFrame (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K) :
    L ≃* adjointGroup .F4 K :=
  e.trans (MulAut.conj w)

theorem chainFrame_symm_apply (e : L ≃* adjointGroup .F4 K) (w m : adjointGroup .F4 K) :
    (chainFrame e w).symm m = e.symm (w⁻¹ * m * w) := by
  rw [chainFrame, MulEquiv.symm_trans_apply, MulAut.conj_symm_apply]

theorem coe_chainFrame_symm (e : L ≃* adjointGroup .F4 K) (w m : adjointGroup .F4 K) :
    (((chainFrame e w).symm m : L) : G) =
      ((e.symm w : L) : G)⁻¹ * ((e.symm m : L) : G) * ((e.symm w : L) : G) := by
  rw [chainFrame_symm_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem subgroupToG_chainFrame (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (Y : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (chainFrame e w) Y = subgroupToG e (Y.map (MulAut.conj w⁻¹).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨_, ⟨w⁻¹ * y * w, ⟨y, hy, ?_⟩, rfl⟩, ?_⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, chainFrame_symm_apply]
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      chainFrame_symm_apply, MulAut.conj_apply, inv_inv]

theorem subgroupToG_chainFrame_eq_map (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (Y : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (chainFrame e w) Y =
      (subgroupToG e Y).map (MulAut.conj ((e.symm w : L) : G)⁻¹).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, Subgroup.coe_subtype, coe_chainFrame_symm]
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, Subgroup.coe_subtype, coe_chainFrame_symm]

theorem map_conj_inv_eq_of_map_conj_eq_chain {M : Type*} [Group M] {H J : Subgroup M} {w : M}
    (h : H.map (MulAut.conj w).toMonoidHom = J) :
    J.map (MulAut.conj w⁻¹).toMonoidHom = H := by
  rw [← h, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id H]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Frame

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] noncomputable def conjParam (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (ΦA : e6ScLevi K e6A5Nodes →* G) : e6ScLevi K e6A5Nodes →* G :=
  (MulAut.conj ((e.symm w : L) : G)⁻¹).toMonoidHom.comp ΦA

theorem conjParam_apply (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (ΦA : e6ScLevi K e6A5Nodes →* G) (x : e6ScLevi K e6A5Nodes) :
    conjParam e w ΦA x = ((e.symm w : L) : G)⁻¹ * ΦA x * ((e.symm w : L) : G) := by
  rw [conjParam, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem levi6Hom_chainFrame (e : L ≃* adjointGroup .F4 K) (w : adjointGroup .F4 K)
    (s : StatedSp 3 K) :
    levi6Hom (chainFrame e w) (RingEquiv.refl K) s =
      ((e.symm w : L) : G)⁻¹ * levi6Hom e (RingEquiv.refl K) s * ((e.symm w : L) : G) := by
  simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  exact coe_chainFrame_symm e w _

theorem isLeviNormalizedA_conjParam {e : L ≃* adjointGroup .F4 K} (w : adjointGroup .F4 K)
    {ΦA : e6ScLevi K e6A5Nodes →* G} (hn : IsLeviNormalizedA e ΦA) :
    IsLeviNormalizedA (chainFrame e w) (conjParam e w ΦA) := by
  intro s
  rw [conjParam_apply, hn s, levi6Hom_chainFrame]

theorem range_conjParam {e : L ≃* adjointGroup .F4 K} (w : adjointGroup .F4 K)
    {ΦA : e6ScLevi K e6A5Nodes →* G} {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀)) :
    (conjParam e w ΦA).range = centralizerPerfectCore (subgroupToG (chainFrame e w) X₀) := by
  rw [conjParam, MonoidHom.range_comp, hr, map_centralizerPerfectCore,
    subgroupToG_chainFrame_eq_map]

theorem chainSL6_conjParam_injective {e : L ≃* adjointGroup .F4 K} (w : adjointGroup .F4 K)
    {ΦA : e6ScLevi K e6A5Nodes →* G} (hinj : Function.Injective (chainSL6 ΦA)) :
    Function.Injective (chainSL6 (conjParam e w ΦA)) := by
  intro x y hxy
  apply hinj
  have h := hxy
  rw [chainSL6_apply, chainSL6_apply, conjParam_apply, conjParam_apply] at h
  rw [chainSL6_apply, chainSL6_apply]
  exact mul_left_cancel (mul_right_cancel h)

theorem commute_rootSL2_rootR_centralizerPerfectCore_chain (hK : Nat.card K = 2)
    {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)} (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hinj : Function.Injective (chainSL6 ΦA)) (hn : IsLeviNormalizedA e ΦA)
    {a b : Fin 6} (hab : a ≠ b) {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hxn : ∀ (e₁ : L ≃* adjointGroup .F4 K) (Φ₁ : e6ScLevi K e6A5Nodes →* G),
      IsLeviNormalizedA e₁ Φ₁ → ∀ c : K,
        chainSL6 Φ₁ (SpecialLinearGroup.transvection hab c) =
          ((e₁.symm (Adjoint.f4Par K β c) : L) : G))
    (hxn' : ∀ (e₁ : L ≃* adjointGroup .F4 K) (Φ₁ : e6ScLevi K e6A5Nodes →* G),
      IsLeviNormalizedA e₁ Φ₁ → ∀ c : K,
        chainSL6 Φ₁ (SpecialLinearGroup.transvection hab.symm c) =
          ((e₁.symm (Adjoint.f4Par K (-β) c) : L) : G))
    (ω : List ℕ) (hω₁ : wordAct ω rootR = β) (hω₂ : wordAct ω β = rootR) :
    ∀ l ∈ rootSL2 K rootR, ∀ y ∈ centralizerPerfectCore
        (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))),
      Commute ((e.symm l : L) : G) y := by
  set w := wRep K ω with hw
  have hθβ : (rootSL2 K rootR).map (MulAut.conj w).toMonoidHom = rootSL2 K β := by
    rw [hw, map_wRep_rootSL2 ω isRoot_rootR, hω₁]
  have hβθ : (rootSL2 K β).map (MulAut.conj w).toMonoidHom = rootSL2 K rootR := by
    rw [hw, map_wRep_rootSL2 ω hβ, hω₂]
  set Z := zpowers (chainZ K β) with hZdef
  have hZ3 : Nat.card Z = 3 :=
    card_zpowers_chainZ hab hinj (hxn e ΦA hn) (hxn' e ΦA hn)
  have hZle : Z ≤ rootSL2 K β := zpowers_chainZ_le hβ
  have hX' : X₀.map (MulAut.conj w⁻¹).toMonoidHom = Z := by
    refine eq_of_le_rootSL2 hK hβ ?_ hZle ?_ hZ3
    · rw [← map_conj_inv_eq_of_map_conj_eq_chain hβθ]
      exact Subgroup.map_mono hXr
    · rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective, hX₀]
  have hZ' : Z.map (MulAut.conj w⁻¹).toMonoidHom = X₀ := by
    refine eq_of_le_rootSL2 hK isRoot_rootR ?_ hXr ?_ hX₀
    · rw [← map_conj_inv_eq_of_map_conj_eq_chain hθβ]
      exact Subgroup.map_mono hZle
    · rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective, hZ3]
  have H := commute_rootSL2_centralizerPerfectCore_chain hab hK (range_conjParam w hr)
    (chainSL6_conjParam_injective w hinj) hβ
    (hxn _ _ (isLeviNormalizedA_conjParam w hn)) (hxn' _ _ (isLeviNormalizedA_conjParam w hn))
  rw [subgroupToG_chainFrame, subgroupToG_chainFrame, hX', hZ', sup_comm] at H
  intro l hl y hy
  have hl' : w * l * w⁻¹ ∈ rootSL2 K β := by
    rw [← hθβ]
    exact ⟨l, hl, rfl⟩
  have h := H _ hl' y hy
  rwa [chainFrame_symm_apply, show w⁻¹ * (w * l * w⁻¹) * w = l by group] at h

omit [Finite G] [Finite K] [CharP K 2] in
theorem wordAct_rootR_a2 : wordAct [0, 2, 1, 2, 3, 2, 1, 0, 2] rootR = Pi.single 1 1 ∧
    wordAct [0, 2, 1, 2, 3, 2, 1, 0, 2] (Pi.single 1 1) = rootR := by
  decide +kernel

omit [Finite G] [Finite K] [CharP K 2] in
theorem wordAct_rootR_e1e2 : wordAct [0, 1, 2, 1, 0] rootR = rootE1mE2Align ∧
    wordAct [0, 1, 2, 1, 0] rootE1mE2Align = rootR := by
  decide +kernel

variable {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}
  {X₀ : Subgroup (adjointGroup .F4 K)}

theorem f4RootPairAlign_rootR_le_aligned_zero (hK : Nat.card K = 2)
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes)) (hn : IsLeviNormalizedA e ΦA) :
    f4RootPairAlign K rootR ≤ alignedSubgroup e
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range := by
  rw [f4RootPairAlign_eq_rootSL2 isRoot_rootR]
  intro l hl
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro y hy
  have hy' := le_centralizerPerfectCore_chain_of_le (show (2 : Fin 6) ≠ 5 by decide) hr
    (isRoot_single _ 1) (chainSL6_transvection_two_five hn) (chainSL6_transvection_five_two hn)
    (range_scLeviRestrict_zero_le ΦA) hy
  exact (commute_rootSL2_rootR_centralizerPerfectCore_chain hK hXr hX₀ hr
    (chainSL6_injective hK hker) hn (show (2 : Fin 6) ≠ 5 by decide) (isRoot_single _ 1)
    (fun _ _ h => chainSL6_transvection_two_five h) (fun _ _ h => chainSL6_transvection_five_two h)
    _ wordAct_rootR_a2.1 wordAct_rootR_a2.2 l hl y hy').symm.eq

theorem f4RootPairAlign_rootR_le_aligned_two (hK : Nat.card K = 2)
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3)
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes)) (hn : IsLeviNormalizedA e ΦA) :
    f4RootPairAlign K rootR ≤ alignedSubgroup e
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range := by
  rw [f4RootPairAlign_eq_rootSL2 isRoot_rootR]
  intro l hl
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro y hy
  have hy' := le_centralizerPerfectCore_chain_of_le (show (0 : Fin 6) ≠ 3 by decide) hr
    isRoot_rootE1mE2Align (chainSL6_transvection_zero_three hn)
    (chainSL6_transvection_three_zero hn) (range_scLeviRestrict_two_le ΦA) hy
  exact (commute_rootSL2_rootR_centralizerPerfectCore_chain hK hXr hX₀ hr
    (chainSL6_injective hK hker) hn (show (0 : Fin 6) ≠ 3 by decide) isRoot_rootE1mE2Align
    (fun _ _ h => chainSL6_transvection_zero_three h)
    (fun _ _ h => chainSL6_transvection_three_zero h)
    _ wordAct_rootR_e1e2.1 wordAct_rootR_e1e2.2 l hl y hy').symm.eq

end Param

end CFSG.SeitzReduction.F4Pilot
