module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}

theorem core_h2 (h : TwinCoreHyp n G R S t₀) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
  TwinADescent3.isPGroup_two_quotient_conjClass
    (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.datum.twoGroup)

theorem core_hq (h : TwinCoreHyp n G R S t₀) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup G, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨g', rfl⟩
  apply forall_sylow_iso_of_exists
  obtain ⟨P, hP', ⟨e⟩⟩ := h.datum.exists_sylow_q8 h.q8
  exact ⟨conjSub g' P, hP'.conj g', ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g').toMonoidHom
    (MulAut.conj g').injective).symm.trans e⟩⟩

theorem core_hA (h : TwinCoreHyp n G R S t₀) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      AEmpty (CoreAssembly.conjClass (tightCore R)) M := by
  rintro J ⟨g, rfl⟩
  exact aEmpty_conj h.hyp.conjInvariant h.aEmpty g

theorem core_q8Section (h : TwinCoreHyp n G R S t₀) {c : G} (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    Q8Section (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c))
      (secFam (CoreAssembly.conjClass (tightCore R)) c) :=
  q8Section_secFam h.hyp (isPGroup_zpowers_of_mul_self_eq_one hc2 hc1) (core_h2 h) (core_hq h)
    (core_hA h)

theorem card_sec_lt (h : TwinCoreHyp n G R S t₀) {c : G} (hc1 : c ≠ 1) :
    Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c)) < n := by
  have hZ : Subgroup.center G = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hne : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
    intro htop
    apply hc1
    have : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have : g ∈ Subgroup.centralizer ({c} : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this
  have h1 : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) < n := by
    rw [← h.card]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
      hne ((Subgroup.card_eq_iff_eq_top _).mp heq)
  have h2 := Subgroup.card_le_card_group (coreHull (CoreAssembly.conjClass (tightCore R)) c)
  have h3 : Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c)) ≤
      Nat.card ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  omega

end Data

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_modOdd_iff_of_lift (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K : Subgroup G}
    {L : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))}
    (hK1 : ∀ k ∈ K, ∃ h : ↥(coreHull Ω c), (((h : ↥(Subgroup.centralizer ({c} : Set G)))) : G) = k ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h ∈ L)
    (hK2 : ∀ l ∈ L, ∃ h : ↥(coreHull Ω c), (((h : ↥(Subgroup.centralizer ({c} : Set G)))) : G) ∈ K ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h = l)
    {a : OddQuot c} :
    a ∈ modOdd c K ↔ ∃ l ∈ L, secMap Ω c hΩ hc2 l = a := by
  rw [mem_modOdd_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hhk, hhL⟩ := hK1 _ hk
    have : k = (h : ↥(Subgroup.centralizer ({c} : Set G))) := Subtype.ext hhk.symm
    subst this
    exact ⟨_, hhL, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨h, hhK, rfl⟩ := hK2 l hl
    exact ⟨(h : ↥(Subgroup.centralizer ({c} : Set G))), hhK, rfl⟩

theorem isPGroup_zpowers_conj {y : G} (hy : IsPGroup 2 (Subgroup.zpowers y)) (g : G) :
    IsPGroup 2 (Subgroup.zpowers (g * y * g⁻¹)) := by
  obtain ⟨k, hk⟩ := hy ⟨y, Subgroup.mem_zpowers y⟩
  have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hc : (g * y * g⁻¹) ^ (2 ^ k) = 1 := by rw [conj_pow, hk']; group
  intro w
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp w.2
  refine ⟨k, Subtype.ext ?_⟩
  show (w : G) ^ (2 ^ k) = 1
  rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

theorem conj_mem_tightCore {A : Subgroup G} {g : G} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) {y : G}
    (hy : y ∈ tightCore A) : g * y * g⁻¹ ∈ tightCore A := by
  have h1 : tightCore A ≤ (tightCore A).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    exact Subgroup.subset_closure ⟨hg y hy.1, isPGroup_zpowers_conj hy.2 g⟩
  exact h1 hy

theorem eq_one_of_odd_orderOf {X : Type*} [Group X] {P : Subgroup X} (hP : IsPGroup 2 P) {a : X}
    (ha : a ∈ P) (hodd : Odd (orderOf a)) : a = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
  have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm0 : m = 0 := by
    by_contra hne
    rw [hm] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hm0, pow_zero] at hm
  exact orderOf_eq_one_iff.mp hm

theorem secAut_fix_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} (hJ2 : IsPGroup 2 (secImg Ω c J)) {x : G}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) (hxJ : x ∈ centralizerModOdd ⊤ J) :
    ∀ j ∈ secImg Ω c J, secAut Ω c hΩ hc2 ⟨x, hxc⟩ j = j := by
  haveI := normal_coreHull hΩ hc2
  intro j hj
  obtain ⟨h, hh, rfl⟩ := hj
  have hhJ : (((h : ↥(Subgroup.centralizer ({c} : Set G)))) : G) ∈ TwinADescent.coreAt c J := hh
  set g : ↥(Subgroup.centralizer ({c} : Set G)) := ⟨x, hxc⟩ with hg
  set h' : ↥(coreHull Ω c) := ⟨g * (h : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹,
    this.conj_mem _ h.2 g⟩ with hh'
  rw [secAut_mk hΩ hc2 g h h' rfl]
  have hxJc : ∀ a ∈ J ⊓ Subgroup.centralizer ({c} : Set G),
      x * a * x⁻¹ ∈ J ⊓ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    ⟨(Subgroup.mem_normalizer_iff.mp hxJ.2.1 a).mp ha.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxc ha.2) (Subgroup.inv_mem _ hxc)⟩
  have hh'J : (((h' : ↥(Subgroup.centralizer ({c} : Set G)))) : G) ∈ TwinADescent.coreAt c J :=
    conj_mem_tightCore hxJc hhJ
  have hmem' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h' ∈ secImg Ω c J :=
    ⟨h', hh'J, rfl⟩
  have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h ∈ secImg Ω c J :=
    ⟨h, hhJ, rfl⟩
  set d : ↥(coreHull Ω c) := h' * h⁻¹ with hd
  have hdG : (((d : ↥(Subgroup.centralizer ({c} : Set G)))) : G) ∈ oddCoreOf J := by
    have : (((d : ↥(Subgroup.centralizer ({c} : Set G)))) : G) =
        ⁅x, (((h : ↥(Subgroup.centralizer ({c} : Set G)))) : G)⁆ := by
      simp only [hd, hh', hg, commutatorElement_def]
      rfl
    rw [this]
    exact hxJ.2.2.2 _ (TwinADescent.coreAt_le_left c J hhJ)
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (((d : ↥(Subgroup.centralizer ({c} : Set G)))) : G) ∣
        Nat.card (oddCoreOf J) := Subgroup.orderOf_dvd_natCard _ hdG
    have h2 := (oddCoreOf_odd_natCard J).of_dvd_nat h1
    rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h2
  have hmd : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) d ∈ secImg Ω c J := by
    rw [hd, map_mul, map_inv]
    exact Subgroup.mul_mem _ hmem' (Subgroup.inv_mem _ hmem)
  have h1 := eq_one_of_odd_orderOf hJ2 hmd
    (Odd.of_dvd_nat hodd (orderOf_map_dvd _ _))
  rw [hd, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
