module

public import CFSG.GH74.Uniqueness.SU.KI6BGroup
public import CFSG.GH74.Uniqueness.SU.KI6A
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CharacteristicCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.GH74.Uniqueness.SU.KI1r3Simple
public import CFSG.GH74.Uniqueness.SU.KI6BFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictionsFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicSetting

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

theorem pRank_coe_eq (K : Subgroup H) : CFSG.pRank 2 ↥K = Open.pRank 2 K :=
  CFSG.SectionRank.pRank_coe_eq_openPRank 2 K

theorem Cfg.pCore_rank_le_one (h : Cfg H T H₀) : Open.pRank 2 (pCore 2 H) ≤ 1 := by
  apply two_core_rank_le_one_of_proper_full_core T
  intro htop
  apply h.ne
  apply eq_top_iff.mpr
  rw [← htop]
  exact h.gamma

theorem Cfg.layer_ne_bot (h : Cfg H T H₀) : layer H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hlayer
  have hchar : IsCharacteristicP 2 H :=
    isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot H 2 h.odd hlayer
  have := characteristic_two_rank_three_full_core hchar h.rank T
  apply h.ne
  apply eq_top_iff.mpr
  rw [← this]
  exact h.gamma


theorem two_le_pRank_of_commuting_involutions {A : Subgroup H} {u v : H} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (hcomm : u * v = v * u) (huA : u ∈ A) (hvA : v ∈ A) :
    2 ≤ Open.pRank 2 A := by
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf_two hu
  have hv2 : v * v = 1 := mul_self_eq_one_of_orderOf_two hv
  have hu1 : u ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hu; omega
  have hnot : v ∉ zpowers u := by
    intro hmem
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 hmem with h1 | h1
    · rw [h1, orderOf_one] at hv; omega
    · exact huv h1.symm
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := u) (y := v)
    (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact hv2) hu1 hnot hcomm
  exact SU1.le_pRank (p := 2) (by norm_num)
    (sup_le (Subgroup.zpowers_le.mpr huA) (Subgroup.zpowers_le.mpr hvA)) hel (k := 2)
    (by simp [hcard])

theorem component_data (F : KI6BFacts) (h : Cfg H T H₀) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hr : Open.pRank 2 K ≤ 1) :
    t ∈ K ∧ (∀ y ∈ K, orderOf y = 2 → y = t) ∧
      (∀ x ∈ K, (∀ k ∈ K, x * k = k * x) → x ∈ zpowers t) ∧ (∃ y ∈ K, orderOf y = 4) := by
  have hq : CFSG.IsQuasisimple ↥K := hK.1
  have hrk : CFSG.pRank 2 ↥K ≤ 1 := (pRank_coe_eq K).trans_le hr
  have hZ := h.isPGroup_center_component hK
  obtain ⟨z, hz2, hzu, hzc, ⟨y, hy4⟩, -, -⟩ := F.rankOne ↥K hq hrk hZ
  have hzZ : z ∈ center ↥K := by rw [hzc]; exact Subgroup.mem_zpowers z
  have hzcomm : ∀ l ∈ K, (z : H) * l = l * (z : H) := fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨l, hl⟩).symm
  have hzp : (z : H) ∈ pCore 2 H := h.center_component_mem_pCore hK z.2 hzcomm
  have hz2' : orderOf (z : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hz2
  have hzt : (z : H) = t := by
    by_contra hne
    have := two_le_pRank_of_commuting_involutions hz2' ht2 hne
      (Subgroup.mem_center_iff.mp htc (z : H)) hzp (central_involution_mem_two_core t htc ht2)
    have := (this).trans (h.pCore_rank_le_one)
    omega
  refine ⟨hzt ▸ z.2, ?_, ?_, ?_⟩
  · intro y' hy' hy2'
    have : (⟨y', hy'⟩ : ↥K) = z :=
      hzu _ ((Subgroup.orderOf_coe (⟨y', hy'⟩ : ↥K)).symm.trans hy2')
    rw [← hzt, ← this]
  · intro x hx hxc
    have hxZ : (⟨x, hx⟩ : ↥K) ∈ center ↥K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hxc g g.2).symm
    rw [hzc] at hxZ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have := congrArg Subtype.val hn
    rw [← hzt]
    simpa using this
  · exact ⟨(y : H), y.2, by rw [Subgroup.orderOf_coe]; exact hy4⟩


theorem exists_sylow_component (T : Sylow 2 H) {K : Subgroup H} (hK : IsComponent K) :
    ∃ S : Sylow 2 ↥K, ∀ x : ↥K, x ∈ (S : Subgroup ↥K) ↔ (x : H) ∈ (T : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormE : (layer H).Normal := by
    have := layer_characteristic (G := H)
    infer_instance
  have hKE : K ≤ layer H := component_le_layer hK
  have hnormK : (K.subgroupOf (layer H)).Normal := (components_normal_in_layer hK).2
  let SN : Sylow 2 ↥(layer H) := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T (layer H)
  let SK : Sylow 2 ↥(K.subgroupOf (layer H)) :=
    CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal SN (K.subgroupOf (layer H))
  let e : ↥(K.subgroupOf (layer H)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKE
  have hesurj : Function.Surjective e.toMonoidHom := fun y => by
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, hx⟩
  refine ⟨SK.mapSurjective hesurj, fun x => ?_⟩
  rw [Sylow.coe_mapSurjective]
  have hx : x ∈ (SK : Subgroup ↥(K.subgroupOf (layer H))).map e.toMonoidHom ↔
      e.symm x ∈ (SK : Subgroup ↥(K.subgroupOf (layer H))) := by
    exact Subgroup.mem_map_equiv
  rw [hx]
  have h1 : e.symm x ∈ (SK : Subgroup ↥(K.subgroupOf (layer H))) ↔
      ((e.symm x : ↥(K.subgroupOf (layer H))) : ↥(layer H)) ∈ (SN : Subgroup ↥(layer H)) := by
    rw [CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]; rfl
  rw [h1]
  have h2 : ((e.symm x : ↥(K.subgroupOf (layer H))) : ↥(layer H)) ∈ (SN : Subgroup ↥(layer H)) ↔
      (((e.symm x : ↥(K.subgroupOf (layer H))) : ↥(layer H)) : H) ∈ (T : Subgroup H) := by
    rw [CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]; rfl
  rw [h2]
  rfl


theorem Cfg.pCore_comm_layer (h : Cfg H T H₀) {q l : H} (hq : q ∈ pCore 2 H) (hl : l ∈ layer H) :
    q * l = l * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqF : q ∈ fittingSubgroup H := by rw [Fitting_eq_pcore H 2 h.odd]; exact hq
  have hcomm : ⁅q, l⁆ ∈ ⁅fittingSubgroup H, layer H⁆ := Subgroup.commutator_mem_commutator hqF hl
  rw [fitting_layer_commute (G := H)] at hcomm
  have h1 : q * l * q⁻¹ * l⁻¹ = 1 := Subgroup.mem_bot.mp hcomm
  calc q * l = (q * l * q⁻¹ * l⁻¹) * (l * q) := by group
    _ = l * q := by rw [h1, one_mul]

theorem Cfg.pCore_inf_component_le (F : KI6BFacts) (h : Cfg H T H₀) {t : H}
    (htc : t ∈ center H) (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K)
    (hr : Open.pRank 2 K ≤ 1) {x : H} (hxQ : x ∈ pCore 2 H) (hxK : x ∈ K) : x ∈ zpowers t :=
  (component_data F h htc ht2 hK hr).2.2.1 x hxK
    (fun _ hk => h.pCore_comm_layer hxQ (component_le_layer hK hk))

theorem exists_orderFour_mem (F : KI6BFacts) (h : Cfg H T H₀) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hr : Open.pRank 2 K ≤ 1) :
    ∃ y ∈ K, y ∈ (T : Subgroup H) ∧ orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y₀, hy₀K, hy₀4⟩ := (component_data F h htc ht2 hK hr).2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_component T hK
  let y₀' : ↥K := ⟨y₀, hy₀K⟩
  have hord : orderOf y₀' = 4 := by rw [← Subgroup.orderOf_coe]; exact hy₀4
  have hp : IsPGroup 2 (zpowers y₀') := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S y₀' hp
  refine ⟨((g * y₀' * g⁻¹ : ↥K) : H), (g * y₀' * g⁻¹ : ↥K).2, (hS _).mp hg, ?_⟩
  rw [Subgroup.orderOf_coe]
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y₀'
  simpa [MulAut.conj_apply, hord] using this

end CFSG.GH74.Uniqueness.SU.K.R6
