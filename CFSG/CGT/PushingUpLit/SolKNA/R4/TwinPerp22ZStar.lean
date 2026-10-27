module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFusion
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpMainR

public section

namespace CFSG.ClassicalInvolution.T7F25

section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem not_le_centralizer_of_mem_USet_of_star (hΩ : HypOmegaMod Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hstar : ∀ J ∈ omegaStarNbr Ω K, J ∈ twinSet Ω K)
    {J : Subgroup G} (hJ : J ∈ Ω) (hJt : J ∉ twinSet Ω K) {V : Subgroup G} (hV : V ∈ USet Ω)
    (hVJ : V ≤ J) : ¬ V ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hVC
  have hKt : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hKJ : K ≠ J := fun h => hJt (h ▸ hKt)
  have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hV
  obtain ⟨-, -, -, -, -, -, -, -, hV4⟩ := hΩ.exists_data_of_mem_USet hV
  have hVN : V ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hz hVJ hV2 (by omega) hVC
  exact hJt (hstar J ⟨hJ, hKJ.symm, V, hV, hVJ, hVN⟩)

theorem not_commute_of_orderOf_four_of_star (hΩ : HypOmegaMod Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hstar : ∀ J ∈ omegaStarNbr Ω K, J ∈ twinSet Ω K)
    {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {x : G} (hx : x ∈ J) (hx4 : orderOf x = 4) : z * x ≠ x * z := by
  intro hxz
  obtain ⟨tJ, htJ⟩ := hΩ.exists_uniqueInvolution hJ
  have hxx : x * x = tJ := T7A.sq_eq_of_orderOf_four htJ hx hx4
  have hxC : x ∈ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hx4]
    norm_num
  obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2
    (Subgroup.zpowers_le.mpr hxC : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
  have hxVm : x ∈ V := hxV (Subgroup.mem_zpowers x)
  have htV : tJ ∈ V := hxx ▸ V.mul_mem hxVm hxVm
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  have hnot2 : V ≠ Subgroup.zpowers tJ := by
    intro hVt
    rw [hVt] at hxVm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxVm
    have h1 : x * x = 1 := by
      rw [← hk, ← zpow_add, ← two_mul, zpow_mul]
      have h2 : tJ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htJ.sq
      rw [h2, one_zpow]
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hx4] at h3
    omega
  rcases l6_2 G Ω hΩ K hK z hz J hJ hJt tJ htJ V hV htV with
    h | h | h | h
  · exact hnot2 h.1
  · exact hnot2 h.1
  · exact not_le_centralizer_of_mem_USet_of_star hΩ hK hz hstar hJ hJt h.1 hVJ hVC
  · have hVsyl : IsSylow2In V J := T7C.isSylow2In_of_mem_RSet_of_le hΩ hJ h.1 hVJ
    obtain ⟨U, hUV, hUc, hUcard⟩ := (hΩ.isQuatSub_of_mem_RSet h.1).exists_cyclic_index_two
    exact not_le_centralizer_of_mem_USet_of_star hΩ hK hz hstar hJ hJt
      (mem_USet_of_natCard hJ hVsyl hUV hUc hUcard) (hUV.trans hVJ) (hUV.trans hVC)

theorem not_commute_of_conj_of_star (hΩ : HypOmegaMod Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hstar : ∀ J ∈ omegaStarNbr Ω K, J ∈ twinSet Ω K)
    {J : Subgroup G} (hJ : J ∈ Ω) {a : G}
    (ha : IsUniqueInvolution J a) {y : G} (hya : y * z * y⁻¹ ≠ a) {x : G} (hx : x ∈ J)
    (hx4 : orderOf x = 4) : (y * z * y⁻¹) * x ≠ x * (y * z * y⁻¹) := by
  intro hc
  have hJ' : conjSub y⁻¹ J ∈ Ω := hΩ.conjInvariant y⁻¹ J hJ
  have ha' : IsUniqueInvolution (conjSub y⁻¹ J) (y⁻¹ * a * y⁻¹⁻¹) := ha.conj y⁻¹
  have hne : y⁻¹ * a * y⁻¹⁻¹ ≠ z := by
    intro h
    apply hya
    have : a = y * z * y⁻¹ := by
      have h2 : y * (y⁻¹ * a * y⁻¹⁻¹) * y⁻¹ = a := by group
      rw [← h2, h]
    exact this.symm
  have hx' : y⁻¹ * x * y ∈ conjSub y⁻¹ J := by
    have := conj_mem_conjSub (n := y⁻¹) hx
    simpa [mul_assoc] using this
  have hord : orderOf (y⁻¹ * x * y) = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj y⁻¹) x
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [h, hx4]
  have hcomm : z * (y⁻¹ * x * y) = (y⁻¹ * x * y) * z := by
    calc z * (y⁻¹ * x * y) = y⁻¹ * ((y * z * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * z * y⁻¹)) * y := by rw [hc]
      _ = (y⁻¹ * x * y) * z := by group
  exact not_commute_of_orderOf_four_of_star hΩ hK hz hstar hJ' (not_mem_twinSet_of_ne hz ha' hne) hx'
    hord hcomm

end T7ER
end Asc77
end
end CFSG.ClassicalInvolution.T7F25

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

section Main

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot trivialOnQuot_conjSub)

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_zStarOf_of_inO2_of_star {r : ℕ} (hr : 4 ≤ r) {Ω : Set (Subgroup Y)} {K₀ K : Subgroup Y}
    {z : Y} (hΩ : HypOmegaGen Ω) (hK₀ : K₀ ∈ Ω) (hz₀ : IsUniqueInvolution K₀ z)
    (hstar : ∀ J ∈ omegaStarNbr Ω K₀, J ∈ twinSet Ω K₀)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) {a : Y} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (haK : a ∈ trivialOnQuot K) (hzC : z ∈ Subgroup.centralizer ({a} : Set Y))
    (hin : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({a} : Set Y))) (⟨z, hzC⟩ : Subgroup.centralizer ({a} : Set Y)))) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set Y)) := by
  classical
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  set C := Subgroup.centralizer ({a} : Set Y) with hC
  rw [C25W.mem_zStarOf_iff]
  refine ⟨hzC, fun y hy => ?_⟩
  set c : Y := y⁻¹ with hc
  have hcC : c ∈ C := C.inv_mem hy
  set s : Y := c * z * c⁻¹ with hsdef
  have hsC : s ∈ C := C.mul_mem (C.mul_mem hcC hzC) (C.inv_mem hcC)
  have e : z⁻¹ * y⁻¹ * z * y = z⁻¹ * s := by simp only [hsdef, hc]; group
  rw [e]
  by_contra hcon
  have hKtq : K ∈ tqMembers3 Ω a := ⟨hK, haK⟩
  have hacomm : c * a * c⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc c * a * c⁻¹ = a * c * c⁻¹ := by rw [← this]
      _ = a := by group
  have hKctq : conjSub c K ∈ tqMembers3 Ω a := by
    refine ⟨hΩ.conjInvariant c K hK, ?_⟩
    have := trivialOnQuot_conjSub haK c
    rwa [hacomm] at this
  have hzs : IsUniqueInvolution (conjSub c K) s := hz.conj c
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := tightInO2_top hin
  have hsQ : centBarMk a hsC ∈ Q := by
    have h1 := hQn.conj_mem _ hzQ (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
      (topMk ⟨c, hcC⟩))
    have e1 : centBarMk a hsC = QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
        (topMk ⟨c, hcC⟩) * QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
        (topMk ⟨z, hzC⟩) * (QuotientGroup.mk' (classicalInvolutionOddCore (CentTop a))
        (topMk ⟨c, hcC⟩))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact h1
  obtain ⟨m, hmcore, hm4, hmc⟩ := exists_order_four_cent hr hΩ hc2 h2 hq hA hKtq hKctq hz hzs hzC
    hsC hQn hQ2 hzQ hsQ
  set N : Subgroup (CentTop a) := classicalInvolutionOddCore (CentTop a) with hN
  set π : CentTop a →* CentBar a := QuotientGroup.mk' N with hπ
  set sT : CentTop a := topMk (⟨s, hsC⟩ : ↥C) with hsT_def
  have hm2 : IsPGroup 2 (Subgroup.zpowers m) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hm4]; norm_num)
  have hsT : sT * sT = 1 :=
    Subtype.ext (Subtype.ext (by
      have : s * s = 1 := hzs.sq
      exact this))
  have hnorm : ∀ g : CentTop a, g ∈ Subgroup.normalizer (N : Set (CentTop a)) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => (inferInstance : N.Normal).conj_mem h hh g, fun hh => by
      have := (inferInstance : N.Normal).conj_mem _ hh g⁻¹
      simpa [mul_assoc] using this⟩
  have hcomm : ∀ r' ∈ Subgroup.zpowers m, ⁅sT, r'⁆ ∈ N := by
    intro r' hr'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr'
    have h1 : π ⁅sT, m ^ k⁆ = 1 := by
      rw [map_commutatorElement, map_zpow]
      have hc' : Commute (π sT) (π m) := hmc
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc'.zpow_right k).eq
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨n, hnN, hn⟩ := CFSG.ClassicalInvolution.Asc77.T7L.exists_conj_centralizes (N := N)
    (R := Subgroup.zpowers m) hsT (CFSG.ComponentClassification.OddCore.odd_card (CentTop a)) hm2
    (fun g _ => hnorm g) (hnorm _) hcomm
  have hm'c : sT * (n * m * n⁻¹) = (n * m * n⁻¹) * sT :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (hn (conj_mem_conjSub (Subgroup.mem_zpowers m)))).symm
  set ñ : Y := (((n : CentTop a) : ↥C) : Y) with hñ
  set x : Y := (((m : CentTop a) : ↥C) : Y) with hx
  have hx₁c : s * (ñ * x * ñ⁻¹) = (ñ * x * ñ⁻¹) * s := by
    have := congrArg (fun t : CentTop a => ((t : ↥C) : Y)) hm'c
    simpa [hsT_def, hñ, hx] using this
  have hxK : x ∈ K := TwinADescent.coreAt_le_left a K hmcore
  have hx₁mem : ñ * x * ñ⁻¹ ∈ conjSub ñ K := conj_mem_conjSub hxK
  have hx₁ord : orderOf (ñ * x * ñ⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj ñ) x
    simp only [MulAut.conj_apply] at h1
    rw [h1, hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hm4]
  have hñ' : ñ ∈ oddCoreOf C := Subgroup.mem_map.mpr ⟨(n : ↥C), mem_oddCore_of_top hnN, rfl⟩
  have hya : s ≠ ñ * z * ñ⁻¹ := by
    intro heq
    apply hcon
    have h1 := Balance.conj_mem_oddCoreIn (X := C) (x := z⁻¹) (C.inv_mem hzC) hñ'
    have h2 := (oddCoreOf C).mul_mem h1 ((oddCoreOf C).inv_mem hñ')
    have e2 : z⁻¹ * (ñ * z * ñ⁻¹) = z⁻¹ * ñ * z⁻¹⁻¹ * ñ⁻¹ := by group
    rw [heq, e2]
    exact h2
  have hJΩ : conjSub ñ K ∈ Ω := hΩ.conjInvariant ñ K hK
  exact CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.not_commute_of_conj_of_star hΩ hK₀ hz₀ hstar hJΩ
    (hz.conj ñ) (y := c) hya hx₁mem hx₁ord hx₁c

end Main

namespace Perp22

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

section NoSec

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem zStar_of_fourth_twin_noSec (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : PerpHypR r n Y R S t) {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h14 : K₄ ≠ K) (h24 : K₄ ≠ K') (h34 : K₄ ≠ K₃)
    (hμ : ¬ ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) :
    t ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)) := by
  push Not at hμ
  obtain ⟨W, hW, hnW⟩ := hμ
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := d.hyp
  have hcomp := TwinPerpV3.dstarComp_subset_twinSet_of_not_wyl h.partIHypG d
    (h.kPerp_datum d.mem d.hz) hW hnW
  have hstar : ∀ J ∈ omegaStarNbr Ω K, J ∈ twinSet Ω K := fun J hJ =>
    hcomp J (Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩)
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hzK₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hU hK₄
  have hzK₃ : IsUniqueInvolution K₃ t := d.hzK₃
  have hstd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hstd₀⟩ := hstd.core
  have hRc₀ : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hK₃Ω : K₃ ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc₀]; exact d.hK₃.1
  obtain ⟨S₃, hstd₃⟩ := exists_datum_atR hstd₀ hRc₀ hK₃Ω hzK₃
  have hRc₃ : tightCore K₃ = K₃ := TwinVtx.tightCore_eq_of_mem hRc₀ hK₃Ω
  have hcls : CoreAssembly.conjClass (tightCore K₃) = Ω := by
    rw [hRc₃, TwinVtx.conjClass_eq_of_mem d.hK₃.1]
  set c : Y := u₁ * u₂ with hc
  have hcB : c ∈ Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hc2 : c * c = 1 := d.hB.2 c hcB
  have hc1 : c ≠ 1 := by
    intro h1
    have hu₂ : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hu₂K : u₂ ∈ K := hu₂ ▸ K.inv_mem d.hu₁.1
    have h4dvd : 4 ∣ orderOf u₂ := by rw [d.hu₂.2]
    exact d.hne (eq_of_mem_inf_of_four_dvd hΩ d.hK'.1 d.mem d.hu₂.1 hu₂K h4dvd)
  have t13 : K ≤ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.mem d.hK₃.1 d.hK₃K.symm d.hz hzK₃
  have t23 : K' ≤ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' hzK₃
  have t14 : K ≤ Balance.Bootstrap.trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.mem hK₄.1 h14.symm d.hz hzK₄
  have t24 : K' ≤ Balance.Bootstrap.trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h24.symm d.hzK' hzK₄
  have hcq3 : c ∈ Balance.Bootstrap.trivialOnQuot K₃ :=
    Subgroup.mul_mem _ (t13 d.hu₁.1) (t23 d.hu₂.1)
  have hcq4 : c ∈ Balance.Bootstrap.trivialOnQuot K₄ :=
    Subgroup.mul_mem _ (t14 d.hu₁.1) (t24 d.hu₂.1)
  have hcm : c ∈ centralizerModOdd ⊤ K₃ :=
    TwinEdge.mem_centralizerModOdd_of_commutator hc2 fun x hx => hcq3.2 x hx
  have hK₄' : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore K₃)) (tightCore K₃) := by
    rw [hcls, hRc₃]
    exact ⟨hK₄.1, t, hzK₃, hzK₄⟩
  have hK₄ne : K₄ ≠ tightCore K₃ := by rw [hRc₃]; exact h34
  have hZ : Subgroup.center Y = ⊥ := h.center_eq_bot
  obtain ⟨htC, -⟩ := layer_mem d
  have hcent := inO2_cent_of_twin_R h4 hT hstd₃ hRc₃ hZ hc2 hc1 hcm htC hK₄' hK₄ne hcq4
  have h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass hstd₀.datum.twoGroup
  have hq := hstd₀.quat_sylow hRc₀
  have hA := h.aEmpty_all
  exact mem_zStarOf_of_inO2_of_star hr hΩ d.mem d.hz hstar h2 hq hA d.hK₃.1 hzK₃ hc2 hc1 hcq3 htC
    hcent

theorem muWylD4R_noSec (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4TwinSupplyR r n)
    (hE : ThmER r n) (h : PerpHypR r n Y R S t) (h3 : ¬ TwinPerp.TwoTwins R)
    (hge : 4 ≤ (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard) :
    ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W := by
  by_contra hW
  push Not at hW
  obtain ⟨W₀, hW₀, hnW⟩ := hW
  have hT : Thm1RTwinInO2 r n := thm1RTwinInO2_of_below hr hNo h.core.twinBelow
  have h4' : Thm4RTwinBelow r n := h4 h.core.below h.core.tbelow h.core.twinBelow
  refine false_of_not_wyl hE h h3 hW₀ hnW (fun {L L' L₃ x y w} d' => ?_)
    (fun {L L' L₃ x y w} d' => ?_)
  · obtain ⟨M, hM, h1, h2, h3'⟩ := exists_fourth_twin L L' L₃ hge
    exact hyp51B_of_fourth_twin h4' hT h d' hM h1 h2 h3'
  · obtain ⟨M, hM, h1, h2, h3'⟩ := exists_fourth_twin L L' L₃ hge
    exact zStar_of_fourth_twin_noSec hr h4' hT h d' hM h1 h2 h3' fun hall => hnW (hall W₀ hW₀)

end NoSec

end Perp22

section MainNoSec

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twoTwins_of_thmE (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4TwinSupplyR r n)
    (hE : Perp22.ThmER r n) (hT3 : Perp22.ThreeTwinsExclR r n) (hW : Perp22.WylD4ExclR r n)
    (h : PerpHypR r n Y R S t) : TwinPerp.TwoTwins R := by
  by_contra h3
  obtain ⟨K', K₃, u₁, u₂, u₃, hd⟩ := h.exists_hyp22G h3
  have h3le := Perp22.three_le_ncard_twinSet hd
  have hne3 : (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard ≠ 3 :=
    fun e => hT3 Y R S t h e
  exact hW Y R S t h h3 _ K' K₃ u₁ u₂ u₃ hd
    (Perp22.muWylD4R_noSec hr hNo h4 hE h h3 (by omega))

theorem twinPerpV3R_of_thmE (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4TwinSupplyR r n)
    (hE : Perp22.ThmER r n) (hT3 : Perp22.ThreeTwinsExclR r n) (hW : Perp22.WylD4ExclR r n) :
    TwinPerpV3R r n :=
  fun _ _ _ _ _ _ h h3 => h3 (twoTwins_of_thmE hr hNo h4 hE hT3 hW h)

end MainNoSec

end CFSG.CGT.PushingUpLit.SolKNA.R4
