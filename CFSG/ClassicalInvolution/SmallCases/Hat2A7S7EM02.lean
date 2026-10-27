module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM01
public import CFSG.ClassicalInvolution.Q3.Q3T7FUE2

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E

abbrev _root_.CFSG.ClassicalInvolution.Hat2A7E.Asc77.EtaAbelian :=
  @CFSG.ClassicalInvolution.Asc77.EtaAbelian

abbrev _root_.CFSG.ClassicalInvolution.Hat2A7E.Asc77.EtaMeet :=
  @CFSG.ClassicalInvolution.Asc77.EtaMeet

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def OddQuotHyp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HM Ω →
      ∀ (N : Subgroup G) [N.Normal], Odd (Nat.card N) → HM (quotFamily Ω N)

section Finite
variable [Finite G] {N : Subgroup G} [N.Normal]

theorem exists_conj_of_map_eq (hΩ : HM Ω)
    (hN : Odd (Nat.card N)) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K :=
  CFSG.ClassicalInvolution.T7FU.Asc77.exists_conj_of_map_eq (⟨hΩ, hΩ.toGen⟩) hN hK hL h

theorem exists_conj_omegaStarNbr (hΩ : HM Ω)
    (hΩ' : HM (quotFamily Ω N)) (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.exists_conj_omegaStarNbr (⟨hΩ, hΩ.toGen⟩) (⟨hΩ', hΩ'.toGen⟩)
    hN hK hJ h

theorem aEmpty_quotFamily (hΩ : HM Ω)
    (hΩ' : HM (quotFamily Ω N)) (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M :=
  CFSG.ClassicalInvolution.T7FU.Asc77.aEmpty_quotFamily (⟨hΩ, hΩ.toGen⟩) (⟨hΩ', hΩ'.toGen⟩) hN hA

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

structure E187Hyps : Prop where
  l67 : L6_7
  l69 : L6_9
  l611 : L6_11
  e6 : E18_6

theorem E187Hyps.toU (h : E187Hyps) : CFSG.ClassicalInvolution.T7FU.Asc77.E187Hyps :=
  ⟨h.l67, h.l69, h.l611⟩

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace E187Hyps
open CFSG.ClassicalInvolution.Asc77.E187Hyps

theorem etaAbelian (h : E187Hyps) (hΩ : HM Ω) :
    EtaAbelian Ω :=
  EtaAbelian.of_l6_9 h.l69 hΩ

theorem etaMeet (h : E187Hyps) (hΩ : HM Ω) :
    EtaMeet Ω :=
  EtaMeet.of_l6_11 h.l611 hΩ

end E187Hyps
section MinCex
variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.centralizer_ne_top (h6 : E18_6) (c : MinCex Ω K S R W H) {x : G}
    (hx : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.centralizer_ne_top (h6.atG c) c.toU hx

end MinCex
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def E189Sect : Prop :=
  ∀ n : ℕ, Hat2A7.CITBelow2A7 n →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
      ∀ Λ : Set (Subgroup Y), HM Λ → (⨆ L ∈ Λ, L) = ⊤ → (∀ L ∈ Λ, AEmpty Λ L) →
        ∀ K ∈ Λ, ∀ J ∈ Λ, ∀ z t : Y, IsUniqueInvolution K z → IsUniqueInvolution J t →
          z * t = t * z → conjSub t K ≠ K →
            (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧
                IsSylow2In R₂ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧
                  u * u = 1 ∧ x * u * x⁻¹ = z * t) ∨
            (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
                ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧
                  Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w)

section Apply
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
variable [Finite G]

theorem e189_sect_apply (hsect : E189Sect) {n : ℕ}
    (hbelow : Hat2A7.CITBelow2A7 n) (hΩ :
        HM Ω) (hAΩ : ∀ L ∈ Ω, AEmpty Ω L)
    {H K J : Subgroup G} (hHn : Nat.card H < n) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKH : K ≤ H)
    (hJH : J ≤ H) {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    (∃ K'' ∈ twinSet Ω K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ K ∧ R₂ ∈ RSet Ω ∧
        R₂ ≤ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : G, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧
          x * u * x⁻¹ = z * t) ∨
    (∃ x ∈ H, ∃ M' ∈ twinSet Ω (conjSub x K), M' ≠ conjSub x K ∧
        ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ conjSub x K ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ M' ∧
          Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w) := by
  classical
  set S₀ : Set (Subgroup G) := {L | L ∈ Ω ∧ L ≤ H} with hS₀
  set Y : Subgroup G := ⨆ L ∈ S₀, L with hYdef
  have hYH : Y ≤ H := iSup₂_le fun L hL => hL.2
  have hSY : ∀ L ∈ S₀, L ≤ Y := fun L hL =>
    le_iSup₂ (f := fun L (_ : L ∈ S₀) => L) L hL
  have hKY : K ≤ Y := hSY K ⟨hK, hKH⟩
  have hJY : J ≤ Y := hSY J ⟨hJ, hJH⟩
  have htY : t ∈ Y := hJY ht.mem
  have hzY : z ∈ Y := hKY hz.mem
  have hcard : Nat.card ↥Y < n := lt_of_le_of_lt (Subgroup.card_le_of_le hYH) hHn
  have hΛ : HM (restrictFamily Ω Y) := hΩ.restrict Y
  have hgen : (⨆ L ∈ restrictFamily Ω Y, L) = ⊤ := by
    have h1 : (⨆ L' ∈ restrictFamily Ω Y, L').map Y.subtype = Y := by
      apply le_antisymm (Subgroup.map_subtype_le _)
      refine iSup₂_le fun L hL => ?_
      have hLY := hSY L hL
      have hLmem : L.subgroupOf Y ∈ restrictFamily Ω Y :=
        subgroupOf_mem_restrictFamily hL.1 hLY
      calc L = (L.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hLY).symm
        _ ≤ _ := Subgroup.map_mono
            (le_iSup₂ (f := fun L' (_ : L' ∈ restrictFamily Ω Y) => L') _ hLmem)
    have h2 : (⊤ : Subgroup Y).map Y.subtype = Y := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective Y.subtype_injective (h1.trans h2.symm)
  have hAΛ : ∀ L' ∈ restrictFamily Ω Y, AEmpty (restrictFamily Ω Y) L' := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    exact AEmpty.restrict hΩ hLY (hAΩ L hL)
  have hKΛ := subgroupOf_mem_restrictFamily hK hKY
  have hJΛ := subgroupOf_mem_restrictFamily hJ hJY
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  have ht' := isUniqueInvolution_subgroupOf ht hJY
  have hzt' : (⟨z, hzY⟩ : Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  have hne' : conjSub (⟨t, htY⟩ : Y) (K.subgroupOf Y) ≠ K.subgroupOf Y := by
    intro h
    apply hne
    rw [conjSub_subgroupOf] at h
    have hle : conjSub t K ≤ Y := by
      have := conjSub_mono (n := t) hKY
      rwa [conjSub_eq_self_of_mem htY] at this
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this
  rcases hsect n hbelow ↥Y hcard _ hΛ hgen hAΛ _ hKΛ _ hJΛ _ _ hz' ht' hzt' hne' with
    ⟨K'', hK''tw, hK''ne, R₁, R₂, hR₁, hR₂, hRc, u, x, hu, hu1, hu2, hux⟩ |
      ⟨x, M', hM'tw, hM'ne, R₁, R₂, hR₁, hR₂, hRc, hcomm⟩
  · left
    have hRK : R₁.map Y.subtype ≤ K := by
      have := Subgroup.map_mono (f := Y.subtype) hR₁.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
    refine ⟨K''.map Y.subtype, map_mem_twinSet_restrict hKY hK''tw,
      map_ne_of_ne_subgroupOf hK''ne, R₁.map Y.subtype, R₂.map Y.subtype,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hKΛ hR₁), hRK,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hK''tw.1 hR₂), Subgroup.map_mono hR₂.1, ?_,
      (u : G), (x : G), ?_, fun h => hu1 (Subtype.ext h), congrArg Subtype.val hu2,
      by simpa using congrArg Subtype.val hux⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hRc a ha b hb)
    · have := Subgroup.mem_map_of_mem Y.subtype hu
      rwa [Subgroup.map_sup] at this
  · right
    have hMY : conjSub (x : G) K ≤ Y := by
      have := conjSub_mono (n := (x : G)) hKY
      rwa [conjSub_eq_self_of_mem x.2] at this
    have hxK : (conjSub (x : G) K).subgroupOf Y ∈ restrictFamily Ω Y :=
      subgroupOf_mem_restrictFamily (hΩ.conjInvariant (x : G) K hK) hMY
    rw [conjSub_subgroupOf] at hM'tw hM'ne hR₁
    have hM₂Y : M'.map Y.subtype ≤ Y := Subgroup.map_subtype_le M'
    refine ⟨(x : G), hYH x.2, M'.map Y.subtype, map_mem_twinSet_restrict hMY hM'tw,
      map_ne_of_ne_subgroupOf hM'ne, R₁.map Y.subtype, R₂.map Y.subtype,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hxK hR₁), ?_,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hM'tw.1 hR₂), Subgroup.map_mono hR₂.1, ?_,
      fun w hw => ?_⟩
    · have := Subgroup.map_mono (f := Y.subtype) hR₁.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hMY] at this
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hRc a ha b hb)
    · rw [← Subgroup.map_sup] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      simpa using congrArg Subtype.val (hcomm w' hw')

end Apply
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem dstarAdj_of_commutes [Finite G] (hΩ : HM Ω) {K J : Subgroup G}
    (hJ : J ∈ Ω) (hne : J ≠ K) (hc : Commutes J K) : dstarAdj Ω K J :=
  CFSG.ClassicalInvolution.T7FU.Asc77.dstarAdj_of_commutes (⟨hΩ, hΩ.toGen⟩) hJ hne hc

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G] {N : Subgroup G} [N.Normal]

theorem omega4_quot_odd (hΩ : HM Ω)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.omega4_quot_odd (⟨hΩ, hΩ.toGen⟩) hN hK hJ hne

theorem omega5_quot_odd (hΩ : HM Ω)
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∀ L' ∈ quotFamily Ω N, L ≠ L' → ∀ z : G ⧸ N, IsUniqueInvolution L z →
      ∀ v ∈ L', (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (L : Set (G ⧸ N)) :=
  T7FU.Asc77.omega5_quot_odd ⟨hΩ, hΩ.toGen⟩ hN

theorem classical_quot_odd (hΩ : HM Ω)
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∃ z : G ⧸ N, Generic.IsClassicalMember L z := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  obtain ⟨zc, hzc⟩ := hΩ.classical K hK
  obtain ⟨e'⟩ := AscQuot.nonempty_quotOddCoreEquiv (odd_natCard_inf hN K)
  refine ⟨QuotientGroup.mk' N z, ?_⟩
  refine
    { admissible := trivial
      orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one
      mem := hz'.mem
      perfect := fun hns => by
        have hKp : Group.IsPerfect ↥K := hzc.perfect hns
        rw [Subgroup.isPerfect_iff] at hKp ⊢
        rw [← Subgroup.map_commutator, hKp]
      subnormal := ?_
      witness := Uniform.MemberType.Witness.of_quotientEquiv e' hzc.witness }
  refine AscQuot.isSubnormal_centralizer ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hz.commute_of_mem hk]
  · intro c hc hne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
    rw [← AscQuot.map_conjSub] at hne ⊢
    have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    obtain ⟨h4, h4'⟩ := omega4_quot_odd hΩ hN hK hJ (Ne.symm hne)
    have hzJ : QuotientGroup.mk' N z ∈ (conjSub g K).map (QuotientGroup.mk' N) := by
      have h1 : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hz.mem
      refine ⟨g * z * g⁻¹, h1, ?_⟩
      rw [map_mul, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
    have hdvd : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        (conjSub g K).map (QuotientGroup.mk' N)) := by
      have := Subgroup.orderOf_dvd_natCard
        (K.map (QuotientGroup.mk' N) ⊓ (conjSub g K).map (QuotientGroup.mk' N))
        (x := QuotientGroup.mk' N z) ⟨hz'.mem, hzJ⟩
      rwa [orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one] at this
    have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
    exact (h4' (le_antisymm h4 h1)).trans inf_le_left

theorem oddQuotHyp : OddQuotHyp := by
  intro G _ _ Ω hΩ N _ hN
  refine
    { conjInvariant := AscQuot.conjInvariant_quot hΩ.conjInvariant N
      classical := classical_quot_odd hΩ hN
      omega4 := ?_
      omega5 := omega5_quot_odd hΩ hN }
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
  exact omega4_quot_odd hΩ hN hK hJ hne

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]

@[expose] def E187E4C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ A : Subgroup G, IsPGroup 2 A → (∃ w : G, w ≠ 1 ∧ w * w = 1 ∧ A = Subgroup.zpowers w) → R
            ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ →
          IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
            (Subgroup.centralizer (A : Set G)) → Subgroup.centralizer (A : Set G) ≤ H

section
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem E187E4C.atG (h4 : E187E4C) (c : MinCex Ω K S R W H) :
    CFSG.ClassicalInvolution.T7FU.Asc77.E187E4CAt .twoA7 G :=
  fun _ _ _ _ _ _ c₁ => h4 G _ _ _ _ _ _ (MinCex.ofU c₁ c)

end

section Finite
variable [Finite G] {Ω : Set (Subgroup G)}

theorem WSet.exists_normalized_sylow (hΩ : HM Ω)
    (S' : Sylow 2 G) :
    ∃ W' ∈ WSet Ω, W' ≤ (S' : Subgroup G) ∧ ∀ s ∈ (S' : Subgroup G), conjSub s W' = W' :=
  CFSG.ClassicalInvolution.T7FU.Asc77.WSet.exists_normalized_sylow (⟨hΩ, hΩ.toGen⟩) S'

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.of_sylow (c : MinCex Ω K S R W H) {S' : Sylow 2 G} {W' : Subgroup G}
    (hRS' : R ≤ (S' : Subgroup G)) {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S' : R' ≤ (S' : Subgroup G))
    (hW' : W' ∈ WSet Ω) (hW'S' : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') : MinCex Ω K S' R W' H :=
  MinCex.ofU
    (CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.of_sylow c.toU hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n)
    c

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G]
variable {Ω : Set (Subgroup G)}

theorem _root_.CFSG.ClassicalInvolution.Hat2A7E.HM.exists_orderOf_four_of_mem [Finite G] (hΩ :
    HM Ω)
    {K : Subgroup G} (hK : K ∈ Ω) : ∃ u ∈ K, orderOf u = 4 := by
  obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
  obtain ⟨u, huR, hu⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hR
  exact ⟨u, hRK.1 huR, hu⟩

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.conj_of_mem (c : MinCex Ω K S R W H) {x : G} (hx : x ∈ H) :
    MinCex Ω (conjSub x K) (conjSylow x S) (conjSub x R) (conjSub x W) H :=
  MinCex.ofU (CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.conj_of_mem c.toU hx) c

end Asc77
end
section
namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

section Finite
variable [Finite G]

omit [Finite G] in

theorem perfect_of_mem [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K := hΩ.oddGen hK

theorem exists_commuting_sylow_pair (hΩ : HM Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ R T : Subgroup G, IsSylow2In R K ∧ IsSylow2In T J ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      Commutes R T :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.exists_commuting_sylow_pair (⟨hΩ, hΩ.toGen⟩) hK hJ

end Finite
end Asc77.AscE186
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]

theorem map_ne_of_twin (hΩ : HM Ω)
    (hN : Odd (Nat.card N)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.map_ne_of_twin (⟨hΩ, hΩ.toGen⟩) hN hK hK' hne

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]

theorem endgame_all [Finite G] {Ω : Set (Subgroup G)} (hΩ : HM Ω) {H : Subgroup G} {t : G}
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (ht : IsUniqueInvolution K₁ t) (hbad : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (n₁ : conjSub d₁ K₁ = K₁) (n₂ : conjSub d₂ K₁ = K₁) : False :=
  CFSG.ClassicalInvolution.T7FU.Asc77.endgame_all (⟨hΩ, hΩ.toGen⟩) hK₁ ht hbad g₁ g₂ g₃ hc n₁ n₂

end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7E
