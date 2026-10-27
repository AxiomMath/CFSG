module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam
import CFSG.ClassicalInvolution.SmallCases.A7Q1B
public import CFSG.ClassicalInvolution.Q3.Q3T6DConj
public import CFSG.ClassicalInvolution.Q3.Q3T7K00
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Twin

variable {G : Type} [Group G] [Finite G]

structure FrameTwins (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)
  card8 : ∀ L ∈ Ω, ∀ P : Subgroup G, IsSylow2In P L → Nat.card ↥P = 8
  mem : K ∈ Ω
  mem' : K' ∈ Ω
  ne : K' ≠ K
  hz : IsUniqueInvolution K z
  hz' : IsUniqueInvolution K' z
  twins : twinSet Ω K = {K, K'}

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem FrameTwins.K_le (d : FrameTwins Ω K K' z) : K ≤ Subgroup.normalizer (K' : Set G) :=
  Sec6Gen.le_normalizer_of_twin d.hyp d.mem d.mem' d.ne.symm d.hz d.hz'

theorem FrameTwins.K'_le (d : FrameTwins Ω K K' z) : K' ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_twin d.hyp d.mem' d.mem d.ne d.hz' d.hz

theorem FrameTwins.exists_of_aviol (hΩ : HypOmegaGen Ω)
    (two : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (card8 : ∀ L ∈ Ω, ∀ P : Subgroup G, IsSylow2In P L → Nat.card ↥P = 8)
    {M J' : Subgroup G} {zM zJ : G} (hM : M ∈ Ω) (hv : AViol Ω M J' zM zJ) :
    ∃ Ms : Subgroup G, FrameTwins Ω M Ms zM := by
  obtain ⟨v, Ms, hVU, hVJ, -, hMs, htw, hvv⟩ :=
    exists_hexagon_data3 hΩ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMsT : Ms ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  exact ⟨Ms, hΩ, two, card8, hM, hMsT.1, hMs, hv.hzK,
    isUniqueInvolution_of_mem_twinSet hv.hzK hMsT, htw⟩

end Twin

section Frame

variable {G : Type} [Group G] [Finite G] {K J : Subgroup G} {z t a g : G}

theorem FrameIIHyp.two_of_mem_conjClass (h : FrameIIHyp K J z t a g) :
    ∀ L ∈ CoreAssembly.conjClass K, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) :=
  TwinADescent3.isPGroup_two_quotient_conjClass h.twoGroup

theorem FrameIIHyp.card_sylow_of_mem_conjClass (h : FrameIIHyp K J z t a g) :
    ∀ L ∈ CoreAssembly.conjClass K, ∀ P : Subgroup G, IsSylow2In P L → Nat.card ↥P = 8 := by
  intro L hL P hP
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  rw [Sec6Gen.natCard_isSylow2In_eq h.hyp hL (CoreAssembly.mem_conjClass_self K) hP hR]
  exact h.sylow8 R hR

theorem FrameIIHyp.twin_facts (h : FrameIIHyp K J z t a g) :
    FrameTwins (CoreAssembly.conjClass K) K (conjSub a J) z := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := h.hyp
  obtain ⟨Ks, d⟩ := FrameTwins.exists_of_aviol hΩ h.two_of_mem_conjClass
    h.card_sylow_of_mem_conjClass (CoreAssembly.mem_conjClass_self K) h.viol
  have hzK' : IsUniqueInvolution (conjSub a J) z := by
    have := h.viol.hzJ.conj a
    rwa [h.haz] at this
  have hK'tw : conjSub a J ∈ twinSet (CoreAssembly.conjClass K) K :=
    ⟨hΩ.conjInvariant a J h.viol.mem, z, h.viol.hzK, hzK'⟩
  have hK's : conjSub a J = Ks := by
    rw [d.twins] at hK'tw
    rcases hK'tw with h1 | h1
    · exact absurd h1 h.hne
    · exact h1
  rw [hK's]
  exact d

theorem FrameIIHyp.twinPair_of_aviol (h : FrameIIHyp K J z t a g) {M J' : Subgroup G}
    {zM zJ : G} (hM : M ∈ CoreAssembly.conjClass K)
    (hv : AViol (CoreAssembly.conjClass K) M J' zM zJ) :
    ∃ Ms : Subgroup G, FrameTwins (CoreAssembly.conjClass K) M Ms zM :=
  FrameTwins.exists_of_aviol h.hyp h.two_of_mem_conjClass h.card_sylow_of_mem_conjClass hM hv

end Frame

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem FrameTwins.commutes_inf (d : FrameTwins Ω K K' z) {S : Subgroup G} (hS : IsPGroup 2 ↥S) :
    Commutes (K ⊓ S) (K' ⊓ S) :=
  Sec6Gen.commutes_of_twin_of_isPGroup d.hyp d.mem d.mem' d.ne.symm d.hz d.hz' inf_le_left
    inf_le_left (hS.to_le (sup_le inf_le_right inf_le_right))

theorem FrameTwins.isSylow2In_sup_inf (d : FrameTwins Ω K K' z) {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hR : IsSylow2In (K ⊓ S) K) (hR' : IsSylow2In (K' ⊓ S) K') :
    IsSylow2In ((K ⊓ S) ⊔ (K' ⊓ S)) (K ⊔ K') :=
  A7Q.Gen.isSylow2In_sup_of_twin d.hyp d.mem d.mem' d.ne d.hz d.hz' hR hR' (d.commutes_inf hS)

theorem FrameTwins.isSylow2In_inf_of_isSylow2In_sup (d : FrameTwins Ω K K' z) {P : Subgroup G}
    (hP : IsSylow2In P (K ⊔ K')) : IsSylow2In (K ⊓ P) K ∧ IsSylow2In (K' ⊓ P) K' := by
  have hKn : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer d.K'_le
  have hK'n : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) := sup_le d.K_le Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · rw [inf_comm]
    exact Sec7.isSylow2In_inf_of_normal hP le_sup_left hKn
  · rw [inf_comm]
    exact Sec7.isSylow2In_inf_of_normal hP le_sup_right hK'n

theorem FrameTwins.eq_sup_inf (d : FrameTwins Ω K K' z) {P : Subgroup G}
    (hP : IsSylow2In P (K ⊔ K')) : P = (K ⊓ P) ⊔ (K' ⊓ P) := by
  obtain ⟨hR, hR'⟩ := d.isSylow2In_inf_of_isSylow2In_sup hP
  exact (d.isSylow2In_sup_inf hP.2.1 hR hR').eq_of_le hP.2.1 hP.1
    (sup_le inf_le_right inf_le_right)

end Sylow

section Odd

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem eq_oddCoreOf_sup_of_isPGroup_quotient {L R : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hR : IsSylow2In R L) :
    L = oddCoreOf L ⊔ R := by
  refine le_antisymm (fun k hk => ?_) (sup_le (oddCoreOf_le_self L) hR.1)
  let f : ↥(R.subgroupOf L) →* ↥L ⧸ classicalInvolutionOddCore ↥L :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)).comp (R.subgroupOf L).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hwO : (w : ↥L) ∈ classicalInvolutionOddCore ↥L := (QuotientGroup.eq_one_iff _).mp hw
    have hwR : ((w : ↥L) : G) ∈ R := w.2
    have h2w : IsPGroup 2 (Subgroup.zpowers ((w : ↥L) : G)) :=
      hR.2.1.to_le (Subgroup.zpowers_le.mpr hwR)
    exact Subtype.ext (Subtype.ext (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L)
      (mem_oddCoreOf_iff.mpr ⟨(w : ↥L).2, hwO⟩) h2w))
  have hsurj : Function.Surjective f := by
    refine (hinj.bijective_of_nat_card_le ?_).2
    rw [TL4.natCard_quot_oddCore_eq h2 hR]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.1).toEquiv).symm.le
  obtain ⟨⟨p, hp⟩, hpk⟩ := hsurj (QuotientGroup.mk ⟨k, hk⟩)
  have hpR : (p : G) ∈ R := Subgroup.mem_subgroupOf.mp hp
  have hpk' : (QuotientGroup.mk p : ↥L ⧸ classicalInvolutionOddCore ↥L) =
      QuotientGroup.mk ⟨k, hk⟩ := hpk
  have ho : p⁻¹ * ⟨k, hk⟩ ∈ classicalInvolutionOddCore ↥L := QuotientGroup.eq.mp hpk'
  have hoO : (p : G)⁻¹ * k ∈ oddCoreOf L :=
    mem_oddCoreOf_iff.mpr ⟨L.mul_mem (L.inv_mem p.2) hk, by convert ho using 1⟩
  have hk' : k = (p : G) * ((p : G)⁻¹ * k) := by group
  rw [hk']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hpR) (Subgroup.mem_sup_left hoO)

theorem FrameTwins.sup_le_normalizer_left (d : FrameTwins Ω K K' z) :
    K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer d.K'_le

theorem FrameTwins.sup_le_normalizer_right (d : FrameTwins Ω K K' z) :
    K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) := sup_le d.K_le Subgroup.le_normalizer

theorem FrameTwins.sup_le_normalizer_oddProd (d : FrameTwins Ω K K' z) :
    K ⊔ K' ≤ Subgroup.normalizer ((oddCoreOf K ⊔ oddCoreOf K' : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup (oddCoreOf K) (oddCoreOf K')
    ⟨mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_left hg),
      mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_right hg)⟩

theorem oddProd_le_sup (K K' : Subgroup G) : oddCoreOf K ⊔ oddCoreOf K' ≤ K ⊔ K' :=
  sup_le ((oddCoreOf_le_self K).trans le_sup_left) ((oddCoreOf_le_self K').trans le_sup_right)

theorem FrameTwins.odd_oddProd (d : FrameTwins Ω K K' z) :
    Odd (Nat.card ↥(oddCoreOf K ⊔ oddCoreOf K')) := by
  have h1 : oddCoreOf K ≤ oddCoreOf (K ⊔ K') :=
    Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self K).trans le_sup_left)
      (fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_left hg))
      (oddCoreOf_odd_natCard K)
  have h2 : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') :=
    Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self K').trans le_sup_right)
      (fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_right hg))
      (oddCoreOf_odd_natCard K')
  exact (oddCoreOf_odd_natCard (K ⊔ K')).of_dvd_nat (Subgroup.card_dvd_of_le (sup_le h1 h2))

theorem FrameTwins.sup_eq_oddProd_sup (d : FrameTwins Ω K K' z) {P : Subgroup G}
    (hP : IsSylow2In P (K ⊔ K')) : K ⊔ K' = (oddCoreOf K ⊔ oddCoreOf K') ⊔ P := by
  obtain ⟨hR, hR'⟩ := d.isSylow2In_inf_of_isSylow2In_sup hP
  have h1 := eq_oddCoreOf_sup_of_isPGroup_quotient (d.two K d.mem) hR
  have h2 := eq_oddCoreOf_sup_of_isPGroup_quotient (d.two K' d.mem') hR'
  refine le_antisymm (sup_le ?_ ?_) (sup_le (oddProd_le_sup K K') hP.1)
  · exact h1.le.trans (sup_le (le_sup_of_le_left le_sup_left)
      (le_sup_of_le_right inf_le_right))
  · exact h2.le.trans (sup_le (le_sup_of_le_left le_sup_right)
      (le_sup_of_le_right inf_le_right))

theorem FrameTwins.exists_conj_oddProd (d : FrameTwins Ω K K' z) {P₁ P₂ : Subgroup G}
    (h₁ : IsSylow2In P₁ (K ⊔ K')) (h₂ : IsSylow2In P₂ (K ⊔ K')) :
    ∃ o ∈ oddCoreOf K ⊔ oddCoreOf K', conjSub o P₂ = P₁ := by
  refine Q3T7M.CentQ.exists_conjSub_of_le_sup_odd (h₂.1.trans d.sup_le_normalizer_oddProd)
    d.odd_oddProd ?_ h₂.2.1 h₁.2.1 (h₁.natCard_eq h₂) (h₁.1.trans (d.sup_eq_oddProd_sup h₂).le)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact eq_one_of_isPGroup_of_mem_odd d.odd_oddProd hx.2
    (h₂.2.1.to_le (Subgroup.zpowers_le.mpr hx.1))

end Odd

section AInv

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

@[expose] def IsAInv (Ω : Set (Subgroup G)) (M : Subgroup G) (zM u : G) : Prop :=
  ∃ J' : Subgroup G, AViol Ω M J' zM u

theorem IsAInv.mul_self_eq_one {u : G} (hu : IsAInv Ω K z u) : u * u = 1 := by
  obtain ⟨J', hv⟩ := hu
  exact hv.hzJ.sq

theorem IsAInv.ne_one {u : G} (hu : IsAInv Ω K z u) : u ≠ 1 := by
  obtain ⟨J', hv⟩ := hu
  exact hv.hzJ.ne_one

theorem IsAInv.ne_involution (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {u : G}
    (hu : IsAInv Ω K z u) : u ≠ z := by
  obtain ⟨J', hv⟩ := hu
  rintro rfl
  exact hv.not_nbr (Q3CL.T3.twin_mem_omegaNbr hΩ hK hv.mem hv.ne hv.hzK hv.hzJ)

theorem IsAInv.comm (hΩ : HypOmegaGen Ω) {u : G} (hu : IsAInv Ω K z u) : u * z = z * u := by
  obtain ⟨J', hv⟩ := hu
  exact (commute_of_mem_omegaStarNbr hΩ hv.star hv.hzK hv.hzJ).symm

theorem IsAInv.mem_sup (d : FrameTwins Ω K K' z) {u : G} (hu : IsAInv Ω K z u) :
    u ∈ K ⊔ K' := by
  obtain ⟨J', hv⟩ := hu
  obtain ⟨v, Ks, hVU, hVJ, -, hKs, htw, hvv⟩ :=
    exists_hexagon_data3 d.hyp d.mem hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hKsK' : Ks = K' := by
    have hm : Ks ∈ twinSet Ω K := by rw [htw]; exact Or.inr rfl
    rw [d.twins] at hm
    rcases hm with h | h
    · exact absurd h hKs
    · exact h
  rw [hKsK'] at hvv
  exact mem_sup_of_hexagon3 d.hyp hv.hzJ hVU hVJ hvv

theorem FrameTwins.isAInv_facts (d : FrameTwins Ω K K' z) {u : G} (hu : IsAInv Ω K z u) :
    u ∈ K ⊔ K' ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u :=
  ⟨hu.mem_sup d, hu.mul_self_eq_one, hu.ne_one, hu.ne_involution d.hyp d.mem, hu.comm d.hyp⟩

theorem IsAInv.conj_of_mem_normalizer (hΩ : ConjInvariant Ω) {u c : G} (hu : IsAInv Ω K z u)
    (hc : c ∈ Subgroup.normalizer (K : Set G)) : IsAInv Ω K z (c * u * c⁻¹) := by
  obtain ⟨J', hv⟩ := hu
  have hcK : conjSub c K = K := mem_normalizer_iff_conjSub_eq.mp hc
  have hcz : c * z * c⁻¹ = z := hv.hzK.conj_eq hcK
  have h := aviol_conj hΩ hv c
  rw [hcK, hcz] at h
  exact ⟨_, h⟩

theorem IsAInv.mul_involution (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {u : G}
    (hu : IsAInv Ω K z u) : IsAInv Ω K z (z * u) := by
  obtain ⟨J', hv⟩ := hu
  obtain ⟨r, hrK, -, hrj⟩ :=
    exists_mem_conj_eq_mul hΩ hK hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr
  have h := IsAInv.conj_of_mem_normalizer hΩ.conjInvariant ⟨J', hv⟩ (Subgroup.le_normalizer hrK)
  rwa [hrj] at h

theorem FrameTwins.isAInv_twin (d : FrameTwins Ω K K' z) {u : G} (hu : IsAInv Ω K z u) :
    IsAInv Ω K' z u := by
  obtain ⟨J', hv⟩ := hu
  obtain ⟨a', ha', ha'u, hΩ', hz'', hne⟩ := AViol.exists_twin d.hyp d.mem hv
  have hK' : conjSub a' J' = K' := by
    have hm : conjSub a' J' ∈ twinSet Ω K := ⟨hΩ', z, d.hz, hz''⟩
    rw [d.twins] at hm
    rcases hm with h | h
    · exact absurd h hne
    · exact h
  have hvs : AViol Ω J' K u z := aviol_symm_of_hypOmegaGen d.hyp d.mem hv
  have hc := aviol_conj d.hyp.conjInvariant hvs a'
  rw [hK', ha'u] at hc
  have hN : a' ∈ Subgroup.normalizer ((Subgroup.closure ({z, u} : Set G) : Subgroup G) : Set G) :=
    (sup_le inf_le_right inf_le_right : pairNormalizers K J' z u ≤ _) ha'
  have hzZ : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hwZ : a' * z * a'⁻¹ ∈ Subgroup.closure ({z, u} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hN z).mp hzZ
  have hzu : z * u = u * z := commute_of_mem_omegaStarNbr d.hyp hv.star hv.hzK hv.hzJ
  rcases (Sec71.mem_closure_pair_iff hv.hzK.sq hv.hzJ.sq hzu).mp hwZ with h | h | h | h
  · exact absurd (by simpa using h) hv.hzK.ne_one
  · have h1 : a' * z * a'⁻¹ = a' * u * a'⁻¹ := by rw [h, ha'u]
    have h2 : z = u := by simpa using h1
    exact absurd h2.symm (IsAInv.ne_involution d.hyp d.mem ⟨J', hv⟩)
  · rw [h] at hc
    exact ⟨_, hc⟩
  · rw [h] at hc
    have h3 := IsAInv.mul_involution d.hyp d.mem' (⟨_, hc⟩ : IsAInv Ω K' z (z * u))
    rwa [← mul_assoc, hv.hzK.sq, one_mul] at h3

end AInv

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
