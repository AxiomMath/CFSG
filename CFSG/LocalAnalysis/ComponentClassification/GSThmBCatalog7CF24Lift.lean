module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Mat
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndModel
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.ComponentClassification.GSThmB.CF24

open CFSG.F3.Native CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.Sporadic.Presentation.Suz CFSG.Sporadic.Recognition.CoverTransfer CFSG.CosetTable
  CFSG.Sporadic.SuzOddCore Subgroup
open scoped commutatorElement

local notation "zS" => CFSG.Sporadic.Recognition.SuzMultiplier.suzZ

@[expose] noncomputable def cf24XPerm : Equiv.Perm (Fin 1782) :=
  FreeGroup.lift (fun i : Fin gcS => suzGenP i) (FreeGroup.mk cf24X)

@[expose] noncomputable def cf24YPerm : Equiv.Perm (Fin 1782) :=
  FreeGroup.lift (fun i : Fin gcS => suzGenP i) (FreeGroup.mk cf24Y)

theorem commutatorElement_mul_mem_center {G : Type*} [Group G] {a b c d : G} (hc : c ∈ center G)
    (hd : d ∈ center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' : c * (b * d) = b * d * c := (mem_center_iff.mp hc (b * d)).symm
  have hd' : d * a⁻¹ = a⁻¹ * d := (mem_center_iff.mp hd a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ =
      a * (c * (b * d)) * c⁻¹ * a⁻¹ * (b * d)⁻¹ := by group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by rw [hc']; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hd']; group

section Lift


theorem ker_le_of_doubleCover (hTab : suzTabCheck = true) (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1) (hL1 : SuzIndexP2) (hL2 : SuzCardP2) {L : Type} [Group L]
    [Finite L] (q : L →* suzM) (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = zpowers t) (φ : SuzCover →* L) (hφ : Function.Surjective φ)
    (hcomp : q.comp φ = suzπ hTab) (φ₀ : SuzCover →* GL (Fin 12) (ZMod 3)) (hz : φ₀ zS = 1)
    (hd : φ₀ (PresentedGroup.mk _ (FreeGroup.mk (suzW [6, 6]))) ≠ 1) :
    ∀ k ∈ φ.ker, φ₀ k = 1 := by
  obtain ⟨hfin, -⟩ := card_suzCover_le hL0 hL1 hL2
  obtain ⟨hk3, hP⟩ := card_ker_eq_three_of_doubleCover hTab hRho0 hL0 hL1 hL2 q hq ht hker φ hφ
  set π := suzπ hTab with hπ
  have hπs : Function.Surjective π :=
    coverMap_surjective (isPresentation_suzGen hTab) (lift_suzCommW hTab)
  have hK6 : Nat.card π.ker = 6 := by
    have h := π.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hπs).toEquiv,
      suzM_card_chain, hP] at h
    omega
  have hzK : zS ∈ π.ker := suzπ_suzZ hTab
  have h3 : 3 ∣ orderOf zS := by
    have h1 := orderOf_map_dvd (suzRho0 hRho0) zS
    rwa [orderOf_suzRho0_suzZ] at h1
  have hd2K : (PresentedGroup.mk _ (FreeGroup.mk (suzW [6, 6])) : SuzCover) ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπ, suzπ_mk]
    exact lift_suzGen_eq_one hTab (by
      unfold suzTabWords
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hZK : zpowers zS ≤ π.ker := (zpowers_le).2 hzK
  have h6 : orderOf zS ∣ 6 := by
    have := orderOf_dvd_natCard (⟨zS, hzK⟩ : π.ker)
    rwa [Subgroup.orderOf_mk, hK6] at this
  have hoz : orderOf zS = 3 := by
    have hpos : 0 < orderOf zS := Nat.pos_of_dvd_of_pos h6 (by norm_num)
    have hle6 : orderOf zS ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    rcases (show orderOf zS = 3 ∨ orderOf zS = 6 by
      generalize orderOf zS = o at h3 hpos hle6
      interval_cases o <;> omega) with h | h
    · exact h
    · exfalso
      have hZeq : zpowers zS = π.ker :=
        Subgroup.eq_of_le_of_card_ge hZK (by rw [Nat.card_zpowers, h, hK6])
      rw [← hZeq] at hd2K
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hd2K
      exact hd (by rw [← hk, map_zpow, hz, one_zpow])
  have hidx : ((zpowers zS).subgroupOf π.ker).index = 2 := by
    have h1 := ((zpowers zS).subgroupOf π.ker).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv, Nat.card_zpowers, hoz, hK6] at h1
    omega
  intro k hk
  have hkπ : k ∈ π.ker := by
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [← hcomp, MonoidHom.comp_apply, hk, map_one]
  have hk3' : k ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : φ.ker)
    rw [hk3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hk2 : k ^ 2 ∈ zpowers zS := by
    have := Subgroup.sq_mem_of_index_two hidx (⟨k, hkπ⟩ : π.ker)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hk2
  have e : k = (k ^ 2)⁻¹ := by
    calc k = k ^ 3 * (k ^ 2)⁻¹ := by group
      _ = (k ^ 2)⁻¹ := by rw [hk3', one_mul]
  rw [e, map_inv, ← hm, map_zpow, hz, one_zpow, inv_one]

theorem commutator_eq_of_doubleCover (hTab : suzTabCheck = true)
    (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1) (hL1 : SuzIndexP2) (hL2 : SuzCardP2) {L : Type} [Group L]
    [Finite L] [Group.IsPerfect L] (q : L →* suzM) (hq : Function.Surjective q) {t : L}
    (ht : orderOf t = 2) (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) {u v : L}
    (hu : (q u : Equiv.Perm (Fin 1782)) = cf24XPerm)
    (hv : (q v : Equiv.Perm (Fin 1782)) = cf24YPerm)
    (hxy : cf24XPerm * cf24YPerm = cf24YPerm * cf24XPerm) : ⁅u, v⁆ = t := by
  have hkerc : q.ker ≤ center L := hker ▸ hcen
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_lift (isPresentation_suzGen hTab)
    suzCommW_mem_commutator (lift_suzCommW hTab) q hq hkerc
  obtain ⟨φ₀, hz, hd, hC⟩ := exists_hom_of_cf24MatCheck
  have hle := ker_le_of_doubleCover hTab hRho0 hL0 hL1 hL2 q hq ht hker φ hφ hcomp φ₀ hz hd
  set px : SuzCover := PresentedGroup.mk _ (FreeGroup.mk cf24X) with hpx
  set py : SuzCover := PresentedGroup.mk _ (FreeGroup.mk cf24Y) with hpy
  have hqx : q (φ px) = q u := by
    apply Subtype.ext
    rw [← MonoidHom.comp_apply, hcomp, hpx, suzπ_mk hTab, coe_lift_suzGen, hu]
    rfl
  have hqy : q (φ py) = q v := by
    apply Subtype.ext
    rw [← MonoidHom.comp_apply, hcomp, hpy, suzπ_mk hTab, coe_lift_suzGen, hv]
    rfl
  have hcx : (φ px)⁻¹ * u ∈ center L :=
    hkerc (by rw [MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel])
  have hcy : (φ py)⁻¹ * v ∈ center L :=
    hkerc (by rw [MonoidHom.mem_ker, map_mul, map_inv, hqy, inv_mul_cancel])
  have hcomm : ⁅u, v⁆ = φ (PresentedGroup.mk _ (FreeGroup.mk cf24C)) := by
    have e1 : u = φ px * ((φ px)⁻¹ * u) := by group
    have e2 : v = φ py * ((φ py)⁻¹ * v) := by group
    rw [e1, e2, commutatorElement_mul_mem_center hcx hcy, cf24C, mk_commWord,
      map_commutatorElement, map_commutatorElement]
  refine eq_of_mem_zpowers_of_ne_one ht ?_ ?_
  · rw [← hker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hu, hv]
    exact hxy
  · rw [hcomm]
    intro h1
    exact hC (hle _ h1)

end Lift

end CFSG.ComponentClassification.GSThmB.CF24
