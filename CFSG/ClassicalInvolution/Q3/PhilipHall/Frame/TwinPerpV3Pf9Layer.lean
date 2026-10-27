module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Closure
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGenSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf6Orth

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Count

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem twins_card_le_four' (hP : Q3CL.PartIHypG Ω) (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K)
    (hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W)
    (S : Finset (Subgroup G)) (hKS : K ∈ S) (hS : ∀ M ∈ S, M ∈ twinSet Ω K) : S.card ≤ 4 := by
  classical
  obtain ⟨W, hW, ρ, hρ⟩ := exists_reps_of_family' hd.hyp hd.hz S hKS hS
  have hnc' : ¬ DbarConnected Ω W := hnc W hW ⟨ρ K, hρ K hKS⟩
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  let g : Subgroup G → ↥(muGroup Ω W) := fun M => CFSG.ClassicalInvolution.Asc77.T7D.imgQ (ρ M)
  have hinj : Set.InjOn g (↑S : Set (Subgroup G)) := by
    intro M hM M' hM' e
    have := c.K_eq_of_img_eq (ρ M) (ρ M') (congrArg Subtype.val e)
    rwa [hρ M hM, hρ M' hM'] at this
  have hsub : (↑(S.image g) : Set ↥(muGroup Ω W)) ⊆
      Star3T.cent (muDelta Ω W) (g K) := by
    intro y hy
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    by_cases hMK : M = K
    · rw [hMK]
      exact Star3T.self_mem_cent (CFSG.ClassicalInvolution.Asc77.T7D.imgQ_mem _)
    · refine ⟨CFSG.ClassicalInvolution.Asc77.T7D.imgQ_mem _, (Subtype.ext (c.comm_of_omega (ρ K) (ρ M) ?_)).symm⟩
      rw [hρ K hKS, hρ M hM]
      exact adj_of_twins' hd hperp (hS K hKS) (hS M hM) hMK
  have hcard : S.card ≤ (Star3T.cent (muDelta Ω W) (g K)).ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at this
  rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc' (g K) (CFSG.ClassicalInvolution.Asc77.T7D.imgQ_mem _) with h1 | h1 | ⟨h1, -⟩
      <;> omega

theorem not_mem_trivialOnQuot_of_order4 (hΩ : HypOmegaGen Ω) {J L : Subgroup G} (hJ : J ∈ Ω)
    (hL : L ∈ Ω) (hLJ : L ≠ J) {z : G} (hzJ : IsUniqueInvolution J z)
    (hzL : IsUniqueInvolution L z)
    (hq8 : ∀ P : Subgroup G, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2)) {a b : G}
    (ha : a ∈ J) (ha4 : orderOf a = 4) (hb : b ∈ L) : a * b ∉ trivialOnQuot J := by
  intro hc
  have hb' : b ∈ trivialOnQuot J := A7T22.le_trivialOnQuot_of_twin hΩ hL hJ hLJ hzL hzJ hb
  have ha' : a ∈ trivialOnQuot J := by
    have := (trivialOnQuot J).mul_mem hc ((trivialOnQuot J).inv_mem hb')
    simpa using this
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ha4]; norm_num)
  obtain ⟨R₁, hR₁, hle⟩ := IsSylow2In.exists_ge ha2 (Subgroup.zpowers_le.mpr ha)
  have haR : a ∈ R₁ := hle (Subgroup.mem_zpowers a)
  obtain ⟨e⟩ := hq8 R₁ hR₁
  have hp4 : orderOf (e ⟨a, haR⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ha4
  have hq : ∀ p : QuaternionGroup 2, orderOf p = 4 → ∃ x : QuaternionGroup 2, p * x ≠ x * p := by
    intro p hp
    by_contra hcon
    push Not at hcon
    have key : ∀ q : QuaternionGroup 2, (∀ x : QuaternionGroup 2, q * x = x * q) → q * q = 1 := by
      decide
    have hsq : p * p = 1 := key p hcon
    have : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    rw [hp] at this
    omega
  obtain ⟨x', hx'⟩ := hq _ hp4
  set x : R₁ := e.symm x' with hxdef
  have hxJ : (x : G) ∈ J := hR₁.1 x.2
  have hax : a * (x : G) ≠ (x : G) * a := by
    intro h
    apply hx'
    have h1 : (⟨a, haR⟩ : R₁) * x = x * ⟨a, haR⟩ := Subtype.ext h
    have h2 := congrArg e h1
    rw [map_mul, map_mul, hxdef, MulEquiv.apply_symm_apply] at h2
    exact h2
  have h1 : ⁅a, (x : G)⁆ ∈ oddCoreOf J := ha'.2 _ hxJ
  have h2 : ⁅a, (x : G)⁆ ∈ R₁ := by
    rw [commutatorElement_def]
    exact R₁.mul_mem (R₁.mul_mem (R₁.mul_mem haR x.2) (R₁.inv_mem haR)) (R₁.inv_mem x.2)
  have h3 : ⁅a, (x : G)⁆ ∈ oddCoreOf R₁ := inf_oddCoreOf_le hR₁.1 ⟨h2, h1⟩
  rw [oddCoreOf_eq_bot_of_isPGroup hR₁.2.1, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h3
  exact hax h3

end Gen

section Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem not_mem_tq_K (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) :
    K ∉ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
      K' ∉ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  have hd := hStd.datum
  constructor
  · intro h
    exact not_mem_trivialOnQuot_of_order4 hd.hyp hd.mem hd.hK'.1 hd.hne hd.hz hd.hzK'
      (fun P hP => members_sylow_q8 hStd.perp K hd.mem P hP) hd.hu₁.1 hd.hu₁.2 hd.hu₂.1 h.2
  · intro h
    refine not_mem_trivialOnQuot_of_order4 hd.hyp hd.hK'.1 hd.mem hd.hne.symm hd.hzK' hd.hz
      (fun P hP => members_sylow_q8 hStd.perp K' hd.hK'.1 P hP) hd.hu₂.1 hd.hu₂.2 hd.hu₁.1 ?_
    rw [← hd.comm₁₂]
    exact h.2

theorem v3_perp_tq (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) {Kx Ky : Subgroup Y}
    (hKx : Kx ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hKy : Ky ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hxy : Kx ≠ Ky) (h1 : Kx ≠ K)
    (h2 : Kx ≠ K') (h3 : Ky ≠ K) (h4 : Ky ≠ K') :
    ∀ J₀ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      J₀ ∈ KPerp (CoreAssembly.conjClass (tightCore R)) Kx → J₀ = Kx ∨ J₀ = Ky := by
  classical
  intro J₀ hJ₀ hJ₀perp
  by_contra hcon
  push Not at hcon
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hP := hC.partIHypG
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hnc : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      (∃ ρ : Rep (CoreAssembly.conjClass (tightCore R)) W, ρ.K = K) →
        ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W :=
    fun W hW ⟨ρ₀, hρ₀⟩ => not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀ (hStd.wyl W hW)
  have hzx : IsUniqueInvolution Kx t := isUniqueInvolution_of_mem_twinSet hd.hz hKx
  have hK1 := kPerp_datum hStd.perp hKx.1 hzx
  rw [hK1, twinSet_eq_of_mem_twinSet hd.hz hKx] at hJ₀perp
  obtain ⟨hnK, hnK'⟩ := not_mem_tq_K hStd
  have h5 : J₀ ≠ K := fun h => hnK (h ▸ hJ₀)
  have h6 : J₀ ≠ K' := fun h => hnK' (h ▸ hJ₀)
  have hKt : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := mem_twinSet_self hd.mem hd.hz
  have hcard := twins_card_le_four' hP hd hperp hnc ({K, K', Kx, Ky, J₀} : Finset (Subgroup Y))
    (by simp) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl | rfl | rfl
      · exact hKt
      · exact hd.hK'
      · exact hKx
      · exact hKy
      · exact hJ₀perp)
  have hne : K ≠ K' := hd.hne.symm
  have h5' := hcon.1
  have h6' := hcon.2
  rw [Finset.card_insert_of_notMem (by simp [hne, h1.symm, h3.symm, h5.symm]),
    Finset.card_insert_of_notMem (by simp [h2.symm, h4.symm, h6.symm]),
    Finset.card_insert_of_notMem (by simp [hxy, h5'.symm]),
    Finset.card_pair_eq_two_iff.2 (Ne.symm h6')] at hcard
  omega

theorem v3_common_inv (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (h2' : ∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), IsPGroup 2 J) :
    ∃ z, IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) z ∧
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) z := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  obtain ⟨-, ⟨R₃, h3, c3⟩, ⟨R₄, h4, c4⟩⟩ := v3_layerBasics hStd hF
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hJ := secImg_mem_secFam hmem
  have hJ' := secImg_mem_secFam hmem4
  have e3 := secImgR_eq_secImg hc2 hmem h3 c3 (h2' _ hJ)
  have e4 := secImgR_eq_secImg hc2 hmem4 h4 c4 (h2' _ hJ')
  have hs3 : IsSylow2In R₃ (TwinADescent.coreAt (u₁ * u₂) K₃) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hmem.2).mpr ⟨h3, c3⟩
  have hs4 : IsSylow2In R₄ (TwinADescent.coreAt (u₁ * u₂) K₄) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hmem4.2).mpr ⟨h4, c4⟩
  have hR3H : R₃.subgroupOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := fun a ha =>
    le_coreHull hmem (Subgroup.mem_subgroupOf.mpr (hs3.1 (Subgroup.mem_subgroupOf.mp ha)))
  have hR4H : R₄.subgroupOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := fun a ha =>
    le_coreHull hmem4 (Subgroup.mem_subgroupOf.mpr (hs4.1 (Subgroup.mem_subgroupOf.mp ha)))
  have e8₃ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hd.hK₃.1 h3)
  have e8₄ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hF.1.1 h4)
  have hu3 : IsUniqueInvolution R₃ t := isUniqueInvolution_of_isSylow2In hd.hzK₃ h3 (by omega)
  have hu4 : IsUniqueInvolution R₄ t := isUniqueInvolution_of_isSylow2In hz4 h4 (by omega)
  obtain ⟨⟨z, hzJ⟩, -⟩ := hS.hyp.omega1 _ hJ
  obtain ⟨⟨z', hzJ'⟩, -⟩ := hS.hyp.omega1 _ hJ'
  have hzR3 : IsUniqueInvolution (secImgR (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) R₃) z := by
    rw [e3]; exact hzJ
  have hzR4 : IsUniqueInvolution (secImgR (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) R₄) z' := by
    rw [e4]; exact hzJ'
  have q3 := eq_of_isUniqueInvolution_secImgR c3 hR3H hu3.mem hu3.sq hu3.ne_one hzR3
  have q4 := eq_of_isUniqueInvolution_secImgR c4 hR4H hu4.mem hu4.sq hu4.ne_one hzR4
  have hzz : z' = z := q4.trans q3.symm
  subst hzz
  exact ⟨z', hzJ, hzJ'⟩

theorem v3LayerClosure_of_thm4 (h4 : Thm4RTwinBelow 3 n) : V3LayerClosure n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie M hM
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hJ := secImg_mem_secFam hmem
  have hJ' := secImg_mem_secFam hmem4
  obtain ⟨z, hz3, hz4⟩ := v3_common_inv hStd hF h2'
  have hK₄ := hF.1
  have hp3 := v3_perp_tq hStd hd.hK₃ hK₄ (Ne.symm hF.2.2.2.1) hd.hK₃K hd.hK₃K' hF.2.1 hF.2.2.1
  have hp4 := v3_perp_tq hStd hK₄ hd.hK₃ hF.2.2.2.1 hF.2.1 hF.2.2.1 hd.hK₃K hd.hK₃K'
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3 J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have hnb' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem4 hJq (K' := K₃)
      (fun J₀ hJ₀ hJ₀p => hp4 J₀ hJ₀ hJ₀p) hn
  exact TwinLayerGen.closure_of_twin_nbr h4 hlt hS hno hJ hJ' hz3 hz4 hnb hnb' M hM

theorem v3LayerTrans_of_thm4 (h4 : Thm4RTwinBelow 3 n) : V3LayerTrans n :=
  v3LayerTrans_of_closure h4 (v3LayerClosure_of_thm4 h4)

end Std

end Count

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
