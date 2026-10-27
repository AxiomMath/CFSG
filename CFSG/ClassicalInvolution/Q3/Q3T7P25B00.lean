module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAE
public import CFSG.ClassicalInvolution.Q3.Q3T6AutUni
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A00
public import CFSG.ClassicalInvolution.Asc77.AscC25X4

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.ClassicalInvolution

abbrev HypOmegaModT {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  Uniform.HypOmegaModU (.sl2 3 1) Ω

instance coeHypOmegaModT {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} :
    Coe (HypOmegaModT Ω) (Disconnected.AschTight.HypOmegaGen Ω) :=
  ⟨Q3T7P25.hyp_of_modU⟩

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section TypedApi

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem HypOmegaModT.exists_uniqueInvolution [Finite G] (hΩ : HypOmegaModT Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution (Q3T7P25.hyp_of_modU hΩ) hK

theorem HypOmegaModT.isQuatSub_of_mem_RSet [Finite G] (hΩ : HypOmegaModT Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet (Q3T7P25.hyp_of_modU hΩ) hR

theorem HypOmegaModT.eight_le_of_mem_RSet [Finite G] (hΩ : HypOmegaModT Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet (Q3T7P25.hyp_of_modU hΩ) hR

theorem HypOmegaModT.center_two [Finite G] (hΩ : HypOmegaModT Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) →
      w = 1 ∨ w = z :=
  Sec6Gen.center_two (Q3T7P25.hyp_of_modU hΩ) hK hz

theorem HypOmegaModT.exists_noncentral [Finite G] (hΩ : HypOmegaModT Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A) (hA3 : 3 ≤ Nat.card A) :
    ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v :=
  Sec6Gen.exists_noncentral (Q3T7P25.hyp_of_modU hΩ) hJ hAJ hA2 hA3

theorem HypOmegaModT.card_le_two_of_le_inf [Finite G] (hΩ : HypOmegaModT Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 :=
  Sec6Gen.card_le_two_of_le_inf (Q3T7P25.hyp_of_modU hΩ) hK hJ hKJ hA hAK hAJ

theorem HypOmegaModT.eq_of_le_of_le [Finite G] (hΩ : HypOmegaModT Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J :=
  Sec6Gen.eq_of_le_of_le (Q3T7P25.hyp_of_modU hΩ) hK hJ hA h4 hAK hAJ

theorem HypOmegaModT.le_normalizer_of_le_centralizer [Finite G] (hΩ : HypOmegaModT Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_le_centralizer (Q3T7P25.hyp_of_modU hΩ) hK hJ hKJ hz hAJ hA2 hA3 hAc

theorem HypOmegaModT.comm_le_oddCore_of_twin [Finite G] (hΩ : HypOmegaModT Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
  Sec6Gen.comm_le_oddCore_of_twin (Q3T7P25.hyp_of_modU hΩ) hK hJ hKJ hzK hzJ

theorem HypOmegaModT.le_normalizer_of_twin [Finite G] (hΩ : HypOmegaModT Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) :=
  Sec6Gen.le_normalizer_of_twin (Q3T7P25.hyp_of_modU hΩ) hK hJ hKJ hzK hzJ

theorem HypOmegaModT.commutes_of_twin_of_isPGroup [Finite G] (hΩ : HypOmegaModT Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {A B : Subgroup G}
    (hA : A ≤ K) (hB : B ≤ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B :=
  Sec6Gen.commutes_of_twin_of_isPGroup (Q3T7P25.hyp_of_modU hΩ) hK hJ hKJ hzK hzJ hA hB hAB

theorem HypOmegaModT.exists_data_of_mem_USet [Finite G] (hΩ : HypOmegaModT Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U :=
  Sec6Gen.exists_data_of_mem_USet (Q3T7P25.hyp_of_modU hΩ) hU

theorem HypOmegaModT.isPGroup_of_mem_USet [Finite G] (hΩ : HypOmegaModT Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : IsPGroup 2 U :=
  Sec6Gen.isPGroup_of_mem_USet (Q3T7P25.hyp_of_modU hΩ) hU

theorem HypOmegaModT.exists_member_of_mem_USet [Finite G] (hΩ : HypOmegaModT Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : ∃ K ∈ Ω, U ≤ K :=
  Sec6Gen.exists_member_of_mem_USet (Q3T7P25.hyp_of_modU hΩ) hU

theorem HypOmegaModT.eq_of_mem_USet [Finite G] (hΩ : HypOmegaModT Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hUK : U ≤ K)
    (hUK' : U ≤ K') : K = K' :=
  Sec6Gen.eq_of_mem_USet (Q3T7P25.hyp_of_modU hΩ) hU hK hK' hUK hUK'

end TypedApi

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.ExactLayer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.ExactLayer (commutator_zpowers_le_iff)
open scoped commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {K K' : Subgroup G}

abbrev exactCore (c : G) (K : Subgroup G) : Subgroup G := exactCore3 c K

abbrev tqMembers (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) := tqMembers3 Ω c

abbrev exactFamily (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) := exactFamily3 Ω c

abbrev exactLayer (Ω : Set (Subgroup G)) (c : G) : Subgroup G := exactLayer3 Ω c

abbrev exactPair (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup ↥(exactLayer Ω c)) :=
  restrictFamily (exactFamily Ω c) (exactLayer Ω c)

theorem exactCore_def (c : G) (K : Subgroup G) :
    exactCore c K = K ⊓ Subgroup.centralizer ({c} : Set G) := rfl

theorem exactCore_le_left (c : G) (K : Subgroup G) : exactCore c K ≤ K := exactCore3_le_left c K

theorem exactCore_mem_exactFamily (hK : K ∈ tqMembers Ω c) : exactCore c K ∈ exactFamily Ω c :=
  exactCore3_mem_exactFamily3 hK

theorem centMembers_exactFamily (Ω : Set (Subgroup G)) (c : G) :
    centMembers (exactFamily Ω c) c = exactFamily Ω c := by
  ext K'
  exact ⟨fun h => h.1, fun h => ⟨h, le_centralizer_of_mem_exactFamily3 h⟩⟩

theorem exactCore_le_exactLayer (hK : K ∈ tqMembers Ω c) : exactCore c K ≤ exactLayer Ω c :=
  le_centralizingLayer ⟨exactCore3_mem_exactFamily3 hK, exactCore3_le_centralizer c K⟩

theorem exactLayer_le_centralizer (Ω : Set (Subgroup G)) (c : G) :
    exactLayer Ω c ≤ Subgroup.centralizer ({c} : Set G) :=
  centralizingLayer_le_centralizer _ _

theorem exactCore_conjSub (g c : G) (K : Subgroup G) :
    exactCore (g * c * g⁻¹) (conjSub g K) = conjSub g (exactCore c K) :=
  exactCore3_conjSub g c K

theorem conjSub_mem_tqMembers (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) (hK : K ∈ tqMembers Ω c) :
    conjSub n K ∈ tqMembers Ω c :=
  conjSub_mem_tqMembers3 hΩ hn hK

theorem exactLayer_eq_iSup (Ω : Set (Subgroup G)) (c : G) :
    exactLayer Ω c = ⨆ K' ∈ exactFamily Ω c, K' := by
  have h : centralizingMembers (exactFamily3 Ω c) {c} = exactFamily3 Ω c :=
    centMembers_exactFamily Ω c
  show centralizingLayer (exactFamily3 Ω c) {c} = _
  unfold centralizingLayer
  rw [h]

theorem card_exactLayer_lt (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) :
    Nat.card (exactLayer Ω c) < Nat.card G :=
  card_centralizingLayer_lt _ hnc

end Defs

section Layer2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {K : Subgroup G}

theorem mem_trivialOnQuot_exactCore {z : G} (hK : Generic.IsClassicalMember K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) {b : G}
    (hb : b ∈ trivialOnQuot K) (hbc : b ∈ Subgroup.centralizer ({c} : Set G)) :
    b ∈ trivialOnQuot (exactCore c K) :=
  mem_trivialOnQuot_exactCore3 (hK.toQ3 (by norm_num)) hc2 hcK hb hbc

theorem exactCore_cover {z : G} (hK : Generic.IsClassicalMember K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) :
    ∀ x ∈ K, ∃ i ∈ exactCore c K, ∃ n ∈ oddCoreIn K, x = i * n :=
  exactCore3_cover (hK.toQ3 (by norm_num)) hc2 hcK

theorem axisResidual_exactCore {z : G} (hK : Generic.IsClassicalMember K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) :
    AxisResidual K (Subgroup.zpowers c) (exactCore c K) z :=
  axisResidual_exactCore3 (hK.toQ3 (by norm_num)) hc2 hcK

theorem isSylow2In_exactCore_iff (_hΩ : HypOmegaMod Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (_hK : K ∈ Ω) (hcK : c ∈ trivialOnQuot K) {V : Subgroup G} :
    IsSylow2In V (exactCore c K) ↔ IsSylow2In V K ∧ V ≤ Subgroup.centralizer ({c} : Set G) :=
  Q3T7.isSylow2In_exactCore3_iff hc2 hcK

theorem mem_trivialOnQuot_iff_exists_sylow (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hK : K ∈ Ω) :
    c ∈ trivialOnQuot K ↔ ∃ R, IsSylow2In R K ∧ R ≤ Subgroup.centralizer ({c} : Set G) := by
  constructor
  · intro h
    obtain ⟨R, hR, hRc⟩ :=
      AscE184Sect.exists_isSylow2In_centralizer hc2 (commutator_zpowers_le_iff.mpr h)
    exact ⟨R, hR, by rwa [centralizer_zpowers_eq_singleton'] at hRc⟩
  · rintro ⟨R, hR, hRc⟩
    have hΩg := Q3T7P25.hyp_of_modU hΩ
    have hR8 : 8 ≤ Nat.card R := by
      rw [Q3T7P25.natCard_isSylow2In_member hΩ hK hR]
    have hRcomm : ∀ r ∈ R, r * c = c * r := fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
    have hRK : R ≤ conjSub c K := by
      intro r hr
      rw [mem_conjSub_iff]
      have : c⁻¹ * r * c = r := by
        calc c⁻¹ * r * c = c⁻¹ * (r * c) := by group
          _ = c⁻¹ * (c * r) := by rw [hRcomm r hr]
          _ = r := by group
      rw [this]
      exact hR.1 hr
    have hKc : conjSub c K = K :=
      hΩg.eq_of_le_of_le (hΩ.conjInvariant c K hK) hK hR.2.1 (by omega) hRK hR.1
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hKc
    have hcs : AscL62.CentSylow Ω := Q3T6.centSylow_three_of_memberU hΩ.classical
    have hVK : ∀ y ∈ Subgroup.zpowers c, conjSub y K = K := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr hcN) hy)
    have hcomm : ∀ r ∈ R, ∀ v ∈ Subgroup.zpowers c, r * v = v * r := by
      intro r hr v hv
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (hRcomm r hr) m).eq
    refine ⟨hcN, fun x hx => ?_⟩
    exact hcs hK hR hc2 hVK hcomm x hx c (Subgroup.mem_zpowers c)

theorem mem_tqMembers_iff_exists_sylow (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    K ∈ tqMembers Ω c ↔
      K ∈ Ω ∧ ∃ R, IsSylow2In R K ∧ R ≤ Subgroup.centralizer ({c} : Set G) :=
  and_congr_right fun hK => mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK

theorem conjSub_exactLayer (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) :
    conjSub n (exactLayer Ω c) = exactLayer Ω c := by
  have key : ∀ m ∈ Subgroup.centralizer ({c} : Set G),
      conjSub m (exactLayer Ω c) ≤ exactLayer Ω c := by
    intro m hm
    rw [exactLayer_eq_iSup Ω c]
    unfold conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun K' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK' => ?_
    exact le_iSup₂_of_le (conjSub m K') (conjSub_mem_exactFamily3 hΩ hm hK') le_rfl
  refine le_antisymm (key n hn) ?_
  have h := conjSub_mono (n := n) (key n⁻¹ (inv_mem hn))
  rwa [conjSub_conjSub_inv] at h

theorem exactLayer_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactLayer Ω (g * c * g⁻¹) = conjSub g (exactLayer Ω c) := by
  rw [exactLayer_eq_iSup, exactLayer_eq_iSup]
  have hfam : exactFamily Ω (g * c * g⁻¹) = conjSub g '' exactFamily Ω c := by
    ext K'
    constructor
    · rintro ⟨K, hK, rfl⟩
      obtain ⟨hKΩ, hKc⟩ := hK
      refine ⟨exactCore c (conjSub g⁻¹ K), ⟨conjSub g⁻¹ K, ⟨hΩ g⁻¹ K hKΩ, ?_⟩, rfl⟩, ?_⟩
      · have h := trivialOnQuot_conjSub hKc g⁻¹
        have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
        rwa [e] at h
      · rw [← exactCore_conjSub g c (conjSub g⁻¹ K), conjSub_conjSub_inv]
    · rintro ⟨_, ⟨K, hK, rfl⟩, rfl⟩
      obtain ⟨hKΩ, hKc⟩ := hK
      refine ⟨conjSub g K, ⟨hΩ g K hKΩ, trivialOnQuot_conjSub hKc g⟩, ?_⟩
      exact (exactCore_conjSub g c K).symm
  rw [hfam, iSup_image]
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_congr fun K' => ?_
  rw [Subgroup.map_iSup]

theorem exactPair_eq3 (Ω : Set (Subgroup G)) (c : G) : exactPair3 Ω c = exactPair Ω c := by
  have h : centralizingMembers (exactFamily3 Ω c) {c} = exactFamily3 Ω c :=
    centMembers_exactFamily Ω c
  show restrictFamily (centralizingMembers (exactFamily3 Ω c) {c}) (exactLayer3 Ω c) =
    restrictFamily (exactFamily3 Ω c) (exactLayer3 Ω c)
  rw [h]

theorem exactFamily_eq_empty_of_not_nonempty (hne : ¬ (tqMembers Ω c).Nonempty) :
    exactFamily Ω c = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨K, hK, _⟩ => hne ⟨K, hK⟩

theorem omega4_exactCore (hΩ : HypOmegaModT Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K₀ J₀ : Subgroup G} (hK₀ : K₀ ∈ tqMembers Ω c) (hJ₀ : J₀ ∈ tqMembers Ω c)
    (hKJ : K₀ ≠ J₀) :
    padicValNat 2 (Nat.card ↥(exactCore c K₀ ⊓ exactCore c J₀)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(exactCore c K₀ ⊓ exactCore c J₀)) = 1 →
        ⁅exactCore c K₀, exactCore c J₀⁆ ≤
          oddCoreOf (exactCore c K₀) ⊓ oddCoreOf (exactCore c J₀)) := by
  obtain ⟨h1, h2⟩ := hΩ.omega4 K₀ hK₀.1 J₀ hJ₀.1 hKJ
  obtain ⟨zK, hzK⟩ := hΩ.classical K₀ hK₀.1
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J₀ hJ₀.1
  have hK3 : IsClassicalMember3 K₀ zK := hzK.toQ3 (by norm_num)
  have hJ3 : IsClassicalMember3 J₀ zJ := hzJ.toQ3 (by norm_num)
  have hdvd : Nat.card ↥(exactCore c K₀ ⊓ exactCore c J₀) ∣ Nat.card ↥(K₀ ⊓ J₀) :=
    Subgroup.card_dvd_of_le (inf_le_inf (exactCore3_le_left c K₀) (exactCore3_le_left c J₀))
  have hle : padicValNat 2 (Nat.card ↥(exactCore c K₀ ⊓ exactCore c J₀)) ≤
      padicValNat 2 (Nat.card ↥(K₀ ⊓ J₀)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (dvd_trans pow_padicValNat_dvd hdvd)
  refine ⟨hle.trans h1, fun h => ?_⟩
  have hv : padicValNat 2 (Nat.card ↥(K₀ ⊓ J₀)) = 1 := le_antisymm h1 (h ▸ hle)
  have hcomm := h2 hv
  have hoK : oddCoreOf (exactCore c K₀) = exactCore c K₀ ⊓ oddCoreOf K₀ :=
    oddCoreIn_exactCore3 hK3 hc2 hK₀.2
  have hoJ : oddCoreOf (exactCore c J₀) = exactCore c J₀ ⊓ oddCoreOf J₀ :=
    oddCoreIn_exactCore3 hJ3 hc2 hJ₀.2
  rw [hoK, hoJ]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hab : ⁅a, b⁆ ∈ ⁅K₀, J₀⁆ :=
    Subgroup.commutator_mem_commutator (exactCore3_le_left c K₀ ha) (exactCore3_le_left c J₀ hb)
  have ho := hcomm hab
  have hac : a ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c K₀ ha
  have hbc : b ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c J₀ hb
  have hcc : ⁅a, b⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
    have h1 : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [h1]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hac hbc)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hac))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hbc)
  exact ⟨⟨⟨(Subgroup.map_subtype_le _) ho.1, hcc⟩, ho.1⟩,
    ⟨⟨(Subgroup.map_subtype_le _) ho.2, hcc⟩, ho.2⟩⟩

theorem secData_exactFamily (hΩ : HypOmegaModT Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers Ω c).Nonempty) : SecData3 c (exactFamily Ω c) := by
  refine ⟨?_, fun K' hK' => le_centralizer_of_mem_exactFamily3 hK',
    fun n hn K' hK' => conjSub_mem_exactFamily3 hΩ.conjInvariant hn hK', ?_⟩
  · obtain ⟨K, hK⟩ := hne
    exact ⟨exactCore3 c K, exactCore3_mem_exactFamily3 hK⟩
  · rintro K' ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical K hK.1
    exact ⟨z, isSectionMember3_exactCore3 (hz.toQ3 (by norm_num)) hc2 hK.2⟩

theorem hypOmegaModT_empty {H : Type} [Group H] : HypOmegaModT (∅ : Set (Subgroup H)) :=
  ⟨fun _ _ hK => absurd hK (Set.notMem_empty _), fun _ hL => absurd hL (Set.notMem_empty _),
    fun _ hK => absurd hK (Set.notMem_empty _), fun _ hK => absurd hK (Set.notMem_empty _)⟩

theorem hypOmegaMod_exactPair (hΩ : HypOmegaModT Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    HypOmegaModT (exactPair Ω c) := by
  by_cases hne : (tqMembers Ω c).Nonempty
  · rw [← exactPair_eq3]
    have hcl : InClass3 (exactPair3 Ω c) := (secData_exactFamily hΩ hc2 hne).inClass3
    refine ⟨hcl.conjInvariant, fun L hL => ?_, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hcl.classical L hL
      exact ⟨z, Uniform.IsClassicalMemberU.ofQ3 hz⟩
    · rintro _ ⟨Kc, hKc, hKcY, rfl⟩ _ ⟨Jc, hJc, hJcY, rfl⟩ hne'
      obtain ⟨⟨K₀, hK₀, rfl⟩, -⟩ := hKc
      obtain ⟨⟨J₀, hJ₀, rfl⟩, -⟩ := hJc
      have hKJ : K₀ ≠ J₀ := fun e => hne' (by rw [e])
      obtain ⟨h1, h2⟩ := omega4_exactCore hΩ hc2 hK₀ hJ₀ hKJ
      have hcard : Nat.card ↥((exactCore3 c K₀).subgroupOf (exactLayer3 Ω c) ⊓
          (exactCore3 c J₀).subgroupOf (exactLayer3 Ω c)) =
          Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀) := by
        rw [inf_subgroupOf_eq]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKcY)).toEquiv
      rw [hcard]
      refine ⟨h1, fun h => ?_⟩
      have hle := h2 h
      rw [oddCoreOf_subgroupOf hKcY, oddCoreOf_subgroupOf hJcY]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅exactCore3 c K₀, exactCore3 c J₀⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
          (Subgroup.mem_subgroupOf.mp hb)
      exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1,
        Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
    · rintro _ ⟨Kc, hKc, hKcY, rfl⟩ _ ⟨Jc, hJc, hJcY, rfl⟩ hne' z hz v hv hnc hv2 hvz
      obtain ⟨⟨K₀, hK₀, rfl⟩, -⟩ := hKc
      obtain ⟨⟨J₀, hJ₀, rfl⟩, -⟩ := hJc
      have hKJ : K₀ ≠ J₀ := fun e => hne' (by rw [e])
      obtain ⟨z₀, hz₀⟩ := hΩ.classical K₀ hK₀.1
      have hz₀3 : IsClassicalMember3 K₀ z₀ := hz₀.toQ3 (by norm_num)
      have hz₀U : IsUniqueInvolution K₀ z₀ :=
        hz₀.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1)
      have hz₀A : z₀ ∈ exactCore3 c K₀ := mem_exactCore3 hz₀3 hc2 hK₀.2
      have hzA : IsUniqueInvolution (exactCore3 c K₀) (z : G) :=
        isUniqueInvolution_of_subgroupOf hz hKcY
      have hzz : z₀ = (z : G) :=
        (hzA.unique z₀ hz₀A hz₀U.sq).resolve_left hz₀U.ne_one
      have hzK : IsUniqueInvolution K₀ (z : G) := hzz ▸ hz₀U
      have hvJ : (v : G) ∈ J₀ := exactCore3_le_left c J₀ (Subgroup.mem_subgroupOf.mp hv)
      have hnc' : ¬ ∀ w ∈ J₀, (v : G) * w = w * (v : G) := fun h => hnc (by
        rintro ⟨w, hw⟩ hw'
        exact Subtype.ext (h w (exactCore3_le_left c J₀ (Subgroup.mem_subgroupOf.mp hw'))))
      have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
      have hn := hΩ.omega5 K₀ hK₀.1 J₀ hJ₀.1 hKJ (z : G) hzK (v : G) hvJ hnc' hv2'
        (congrArg Subtype.val hvz)
      have hvc : (v : G) ∈ Subgroup.centralizer ({c} : Set G) :=
        exactLayer_le_centralizer Ω c v.2
      exact (mem_normalizer_subgroupOf_iff hKcY).mp
        (mem_normalizer_inf hn (Subgroup.le_normalizer hvc))
  · have h0 : exactFamily Ω c = ∅ := exactFamily_eq_empty_of_not_nonempty hne
    have h1 : exactPair Ω c = ∅ := by
      ext L
      simp [exactPair, h0, restrictFamily]
    rw [h1]
    exact hypOmegaModT_empty

theorem isUniqueInvolution_exactCore' (hΩ : HypOmegaModT Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G} (hJ : J ∈ tqMembers Ω c) {z : G}
    (hz : IsUniqueInvolution J z) : IsUniqueInvolution (exactCore c J) z := by
  obtain ⟨z₀, hz₀⟩ := hΩ.classical J hJ.1
  have hz₀3 : IsClassicalMember3 J z₀ := hz₀.toQ3 (by norm_num)
  have hz₀U : IsUniqueInvolution J z₀ :=
    hz₀.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1)
  have hzz : z₀ = z := (hz.unique z₀ hz₀U.mem hz₀U.sq).resolve_left hz₀U.ne_one
  have hzc : z ∈ exactCore c J := hzz ▸ mem_exactCore3 hz₀3 hc2 hJ.2
  exact { mem := hzc
          ne_one := hz.ne_one
          sq := hz.sq
          unique := fun y hy hy2 => hz.unique y (exactCore_le_left c J hy) hy2 }

theorem exists_of_mem_RSet_exactFamily {R₀ : Subgroup G} (hR₀ : R₀ ∈ RSet (exactFamily Ω c)) :
    ∃ J ∈ tqMembers Ω c, IsSylow2In R₀ (exactCore c J) := by
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR₀
  obtain ⟨J, hJ, rfl⟩ := hM
  exact ⟨J, hJ, hRM⟩

theorem mem_omegaNbr_of_exactFamily (hΩ' : HypOmegaModT Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G} (hK : K ∈ tqMembers Ω c)
    (hJ : J ∈ tqMembers Ω c)
    (h : exactCore c J ∈ omegaNbr (exactFamily Ω c) (exactCore c K)) : J ∈ omegaNbr Ω K := by
  have hΩ : HypOmegaGen Ω := Q3T7P25.hyp_of_modU hΩ'
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  obtain ⟨J', hJ', hTfix⟩ := exists_of_mem_RSet_exactFamily hT
  have hTfix' := (isSylow2In_exactCore_iff hΩ' hc2 hJ'.1 hJ'.2).mp hTfix
  have h8 : 8 ≤ Nat.card T :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'.1 hTfix'.1)
  have hTJG : T ≤ J := hTJ.trans (exactCore_le_left c J)
  have hJJ' : J = J' :=
    Sec6Gen.eq_of_le_of_le hΩ hJ.1 hJ'.1 hTfix'.1.2.1 (by omega) hTJG hTfix'.1.1
  subst hJJ'
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := isUniqueInvolution_exactCore' hΩ' hc2 hK hz
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hTN' : T ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 (Ne.symm hJK) hz hTJG hTfix'.1.2.1
      (by omega) hTc
  exact ⟨hJ.1, hJK, T, mem_RSet_of_isSylow2In hJ.1 hTfix'.1, hTJG, hTN'⟩

end Layer2

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.ExactLayer

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

theorem aEmpty_exactPair {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : HypOmegaModT Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    ∀ L ∈ restrictFamily (centralizingMembers (ExactLayer.exactFamily Ω c) {c})
        (ExactLayer.exactLayer Ω c),
      AEmpty (restrictFamily (centralizingMembers (ExactLayer.exactFamily Ω c) {c})
        (ExactLayer.exactLayer Ω c)) L := by
  have hΛ : HypOmegaModT (exactPair3 Ω c) := by
    rw [ExactLayer.exactPair_eq3]
    exact ExactLayer.hypOmegaMod_exactPair hΩ hc2
  exact Q3T7.aEmpty_exactPair3 (Q3T7P25.hyp_of_modU hΩ) (Q3T7P25.hyp_of_modU hΛ) hA hc2

abbrev LayerOrthType {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (c : G) (d : ℕ)
    (ε : Bool) : Prop :=
  CFSG.ClassicalInvolution.Asc77.SectionOrthType 3 1 (ExactLayer.exactFamily Ω c)
    (ExactLayer.exactLayer Ω c) d ε


namespace C25X

@[expose] def NC4Fact : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t k 3 1 →
    ((t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨
      (t = .POmegaMinus ∧ k = 4)) →
    CFSG.ClassicalInvolution.Asc77.C25X.NC4At 3 t k 1

end C25X

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
