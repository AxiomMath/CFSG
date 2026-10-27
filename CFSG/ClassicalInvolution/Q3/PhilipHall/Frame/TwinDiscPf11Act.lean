module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace TwinDisc

section Act

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

@[expose] noncomputable def secAct (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    ↥(Subgroup.centralizer ({c} : Set G)) →*
      MulAut (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  (CX.layerHom (coreHull Ω c) ⊤ (fun h _ => conjSub_coreHull hΩ hc2 h)).comp
    (Subgroup.topEquiv (G := ↥(Subgroup.centralizer ({c} : Set G)))).symm.toMonoidHom

theorem secAct_mk (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) (y : ↥(coreHull Ω c)) :
    secAct hΩ hc2 g (QuotientGroup.mk y) =
      QuotientGroup.mk (C25Y.conjOnSub (coreHull Ω c) (conjSub_coreHull hΩ hc2 g) y) := rfl

theorem coe_secAct_mk (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) (y : ↥(coreHull Ω c)) :
    ((C25Y.conjOnSub (coreHull Ω c) (conjSub_coreHull hΩ hc2 g) y : ↥(coreHull Ω c)) :
        ↥(Subgroup.centralizer ({c} : Set G))) = g * (y : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹ :=
  rfl

theorem secAct_of_mem (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {g : ↥(Subgroup.centralizer ({c} : Set G))} (hg : g ∈ coreHull Ω c) :
    secAct hΩ hc2 g = MulAut.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥(coreHull Ω c)) :
      ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) := by
  ext x
  refine QuotientGroup.induction_on x fun y => ?_
  rw [secAct_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem coe_mem_oddCoreOf_coreLayer {n : ↥(coreHull Ω c)}
    (hn : n ∈ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    (((n : ↥(Subgroup.centralizer ({c} : Set G))) : G)) ∈ oddCoreOf (coreLayer Ω c) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hiso : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
      (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective).toMonoidHom =
      classicalInvolutionOddCore ↥(coreLayer Ω c) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  have h2 : (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective) n ∈
      classicalInvolutionOddCore ↥(coreLayer Ω c) := by
    rw [← hiso]
    exact Subgroup.mem_map_of_mem _ hn
  exact ⟨_, h2, rfl⟩

theorem comm_mem_oddCoreOf_of_secAct_eq_one (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {g : G} (hg : g ∈ Subgroup.centralizer ({c} : Set G))
    (h1 : secAct hΩ hc2 ⟨g, hg⟩ = 1) :
    ∀ y ∈ coreLayer Ω c, g * y * g⁻¹ * y⁻¹ ∈ oddCoreOf (coreLayer Ω c) := by
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have h2 : C25Y.layerAut (coreHull Ω c) (conjSub_coreHull hΩ hc2 (⟨g, hg⟩ :
      ↥(Subgroup.centralizer ({c} : Set G)))) (QuotientGroup.mk ⟨y', hy'⟩) =
      QuotientGroup.mk ⟨y', hy'⟩ := by
    have : secAct hΩ hc2 ⟨g, hg⟩ (QuotientGroup.mk ⟨y', hy'⟩) = QuotientGroup.mk ⟨y', hy'⟩ := by
      rw [h1]; rfl
    exact this
  have h3 := (C5O.layerAut_mk_eq_iff (coreHull Ω c) (conjSub_coreHull hΩ hc2 (⟨g, hg⟩ :
      ↥(Subgroup.centralizer ({c} : Set G)))) ⟨y', hy'⟩).mp h2
  obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.mp h3
  have h4 := coe_mem_oddCoreOf_coreLayer (c := c) (Ω := Ω) (n := w) hw
  have e : (((w : ↥(Subgroup.centralizer ({c} : Set G))) : G)) =
      g * (y' : G) * g⁻¹ * (y' : G)⁻¹ := by
    have := congrArg (fun a : ↥(Subgroup.centralizer ({c} : Set G)) => (a : G)) hwn
    simpa [commutatorElement_def] using this
  rw [e] at h4
  exact h4

theorem secAct_fix_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} (h2 : IsPGroup 2 ↥(secImg Ω c J)) {x : G}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) (hxJ : x ∈ trivialOnQuot J) :
    ∀ a ∈ secImg Ω c J, secAct hΩ hc2 ⟨x, hxc⟩ a = a := by
  intro a ha
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp ha
  have hb : conjSub (⟨x, hxc⟩ : ↥(Subgroup.centralizer ({c} : Set G))) (coreHull Ω c) = coreHull Ω c := conjSub_coreHull hΩ hc2 _
  have hkJ : ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ TwinADescent.coreAt c J :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hk')
  set conj := C25Y.conjOnSub (coreHull Ω c) hb k' with hconj
  have hconjG : (((conj : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) = x * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) * x⁻¹ := rfl
  have hxk : x * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) * x⁻¹ ∈ TwinADescent.coreAt c J := by
    have h1 : x * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) * x⁻¹ ∈ conjSub x (TwinADescent.coreAt c J) :=
      Generic.conj_mem_conjSub hkJ
    rwa [TwinADescent.conjSub_coreAt hxc, conjSub_eq_of_mem_normalizer hxJ.1] at h1
  have hdmem : conj * k'⁻¹ ∈ ((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c) := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hk')
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hxk)
  have hcomm : x * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) * x⁻¹ * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G)⁻¹ ∈ Balance.oddCoreIn J :=
    hxJ.2 _ (TwinADescent.coreAt_le_left c J hkJ)
  set m := Nat.card (Balance.oddCoreIn J) with hmdef
  have hm : Odd m := Balance.odd_card_oddCoreIn J
  have hem : (x * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) * x⁻¹ * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G)⁻¹) ^ m = 1 := by
    have h3 : (⟨_, hcomm⟩ : ↥(Balance.oddCoreIn J)) ^ m = 1 := pow_card_eq_one'
    have h4 := congrArg Subtype.val h3
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h4
  have hdG : ((((conj * k'⁻¹ : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G)))) : G) =
      x * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) * x⁻¹ * ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G)⁻¹ := rfl
  have hdm : (conj * k'⁻¹) ^ m = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, hdG, hem]
    rfl
  set g : ↥(secImg Ω c J) :=
    ⟨QuotientGroup.mk (conj * k'⁻¹), Subgroup.mem_map_of_mem _ hdmem⟩ with hgdef
  have hg1 : g ^ m = 1 := by
    apply Subtype.ext
    show (QuotientGroup.mk (conj * k'⁻¹) : _) ^ m = 1
    rw [← QuotientGroup.mk_pow, hdm]
    rfl
  have hg : g = 1 := by
    obtain ⟨j, hj⟩ := h2 g
    have h1 : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one hg1
    have h2' : orderOf g ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have hcop : Nat.Coprime (orderOf g) m :=
      Nat.Coprime.coprime_dvd_left h2' ((Nat.coprime_two_left.mpr hm).pow_left j)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h1)
  have hmk : (QuotientGroup.mk (conj * k'⁻¹) : _) = 1 := congrArg Subtype.val hg
  show secAct hΩ hc2 ⟨x, hxc⟩ (QuotientGroup.mk k') = QuotientGroup.mk k'
  rw [secAct_mk]
  have e : conj = (conj * k'⁻¹) * k' := by group
  calc (QuotientGroup.mk conj : _) = QuotientGroup.mk ((conj * k'⁻¹) * k') := by rw [← e]
    _ = QuotientGroup.mk (conj * k'⁻¹) * QuotientGroup.mk k' := rfl
    _ = QuotientGroup.mk k' := by rw [hmk, one_mul]

end Act

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
