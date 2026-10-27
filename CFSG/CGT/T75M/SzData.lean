module

public import CFSG.CGT.Timmesfeld75.Sec3L2
public import CFSG.CGT.Timmesfeld75.ConclusionIso
public import CFSG.CGT.Timmesfeld75.Sec3Odd
public import CFSG.CGT.Timmesfeld75.BenderInputs4
public import CFSG.CGT.Timmesfeld75.BenderInputsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import Certificates.Certificate113

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki

section MapIso

variable {K K' : Type*} [Group K] [Group K']

theorem StrongWC.map_mulEquiv (e : K ≃* K') {T : Subgroup K} (h : StrongWC T) :
    StrongWC (T.map e.toMonoidHom) := by
  refine ⟨isElemAbelian_map_mulEquiv e h.1, ?_⟩
  intro t' ht' ht'1 a' ha' g' hg'
  obtain ⟨t, ht, rfl⟩ := ht'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨g, rfl⟩ := e.surjective g'
  have ht1 : t ≠ 1 := fun h1 => ht'1 (by rw [h1]; exact map_one e)
  have hc : g⁻¹ * a * g ∈ Subgroup.centralizer ({t} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom] at hg'
    simp only [map_mul, map_inv]
    exact hg'
  refine ⟨g⁻¹ * a * g, h.2 t ht ht1 a ha g hc, ?_⟩
  simp [map_mul, map_inv]

end MapIso

section Bender

variable {K : Type} [Group K] [Finite K]

theorem eq_center_of_strongWC (hK : IsBenderGroup K) {T : Subgroup K} (hT : StrongWC T)
    (hT1 : T ≠ ⊥) (Q : Sylow 2 K) (hTQ : T ≤ (Q : Subgroup K)) :
    T = (Subgroup.center (Q : Subgroup K)).map (Q : Subgroup K).subtype := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  ext z
  constructor
  · intro hz
    refine ⟨⟨z, hTQ hz⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext
      (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q (hTQ hz)
        (by rw [← pow_two]; exact hT.1.2 z hz) q q.2).eq.symm
  · rintro ⟨⟨z, hzQ⟩, hzc, rfl⟩
    rw [SetLike.mem_coe] at hzc
    exact mem_of_commute_sylow_of_strongWC hK hT hx hx1' Q hTQ hzQ fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨q, hq⟩)

theorem card_eq_of_strongWC_sz {a : ℕ} (ha : 1 ≤ a) (e : K ≃* Sz a) {T : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) : Nat.card T = 2 ^ (2 * a + 1) := by
  have hK : IsBenderGroup K := isBenderGroup_of_mulEquiv_sz ha e
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
  have hQ := ((bender_suzuki_borel_full a ha).map_mulEquiv e.symm) Q
  have hcen : Nat.card (Subgroup.center (Q : Subgroup K)) = 2 ^ (2 * a + 1) := hQ.2.2.2.1
  have hTeq := eq_center_of_strongWC hK hT hT1 Q hTQ
  rw [hTeq, Subgroup.card_map_of_injective (Q : Subgroup K).subtype_injective]
  exact hcen

end Bender


section Quotient

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

theorem strongWC_map (hS : Sec3 T T₁) : StrongWC TQ := by
  have hTX : T ≤ T ⊔ T₁ := le_sup_left
  have hT₁X : T₁ ≤ T ⊔ T₁ := le_sup_right
  have c' := hS.cfg.subgroupOf_of_le hTX hT₁X
  have htop : T.subgroupOf (T ⊔ T₁) ⊔ T₁.subgroupOf (T ⊔ T₁) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTX hT₁X, Subgroup.subgroupOf_self]
  have hM : cfgM (T.subgroupOf (T ⊔ T₁)) (T₁.subgroupOf (T ⊔ T₁)) =
      (cfgM T T₁).subgroupOf (T ⊔ T₁) := cfgM_subgroupOf_eq hTX hT₁X
  have hN' : (cfgM (T.subgroupOf (T ⊔ T₁)) (T₁.subgroupOf (T ⊔ T₁))).Normal :=
    c'.normal_cfgM htop
  have hsw := c'.strongWC_map htop
  let e := QuotientGroup.quotientMulEquivOfEq hM
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (cfgM (T.subgroupOf (T ⊔ T₁))
      (T₁.subgroupOf (T ⊔ T₁)))) = QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    MonoidHom.ext fun g => rfl
  have := StrongWC.map_mulEquiv e hsw
  rwa [Subgroup.map_map, hcomp] at this

theorem card_map_sz (hS : Sec3 T T₁) {a : ℕ} (ha : 1 ≤ a) (e : XQ ≃* Sz a) :
    Nat.card TQ = 2 ^ (2 * a + 1) :=
  card_eq_of_strongWC_sz ha e (strongWC_map hS) hS.map_ne_bot

omit [Finite G] in
theorem card_eq_mul_of_card_map (hS : Sec3 T T₁) {k : ℕ} (hk : Nat.card TQ = k) :
    Nat.card T = Nat.card (normIn T T₁) * k := by
  let φ : ↥T →* XQ := (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))).comp
    (Subgroup.inclusion (le_sup_left : T ≤ T ⊔ T₁))
  have hrange : φ.range = TQ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Subgroup.inclusion le_sup_left t, Subgroup.mem_subgroupOf.2 t.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : φ.ker = (normIn T T₁).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hS.cfg.inf_cfgM, Subgroup.mem_inf]
    constructor
    · intro ht
      have h1 : (Subgroup.inclusion le_sup_left t : ↥(T ⊔ T₁)) ∈
          (cfgM T T₁).subgroupOf (T ⊔ T₁) := (QuotientGroup.eq_one_iff _).1 ht
      exact ⟨t.2, Subgroup.mem_subgroupOf.1 h1⟩
    · rintro ⟨-, hM⟩
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hM)
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (normIn_le T T₁)).toEquiv,
    hk] at h1
  exact h1.symm

theorem card_eq_mul_sz (hS : Sec3 T T₁) {a : ℕ} (ha : 1 ≤ a) (e : XQ ≃* Sz a) :
    Nat.card T = Nat.card (normIn T T₁) * 2 ^ (2 * a + 1) :=
  card_eq_mul_of_card_map hS (card_map_sz hS ha e)

end Quotient

section Conj

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

omit [Finite G] in
theorem exists_normIn_right_eq (hS : Sec3 T T₁) :
    ∃ x ∈ T ⊔ T₁, conjSubgroup x T = T₁ ∧ normIn T₁ T = conjSubgroup x (normIn T T₁) := by
  obtain ⟨x, hx, hx'⟩ := hS.conj
  refine ⟨x, hx, hx'.symm, ?_⟩
  have hne : conjSubgroup x T ≠ conjSubgroup 1 T := by
    rw [conjSubgroup_one, ← hx']
    exact hS.cfg.left_ne_right.symm
  have := hS.normIn_conj_eq hx (T ⊔ T₁).one_mem hne
  rw [conjSubgroup_one, ← hx'] at this
  exact this

omit [Finite G] in
theorem card_normIn_right (hS : Sec3 T T₁) :
    Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) := by
  obtain ⟨x, -, -, h⟩ := exists_normIn_right_eq hS
  rw [h, card_conjSubgroup]

end Conj

end CFSG.CGT.T75M
