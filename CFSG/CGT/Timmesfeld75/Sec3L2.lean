module

public import CFSG.CGT.Timmesfeld75.Sec3Odd
public import CFSG.CGT.Timmesfeld75.Lemma214Transfer
public import CFSG.CGT.Timmesfeld75.L2Swap
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.ZStarSmall
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section Normal

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem Cfg.normal_cfgM_subgroupOf (c : Cfg T T₁) :
    ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (cfgM_le_sup T T₁)).2 c.le_normalizer_cfgM

theorem Sec3.normal_cfgM_subgroupOf (hS : Sec3 T T₁) : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal :=
  hS.cfg.normal_cfgM_subgroupOf

end Normal

section Quotient

variable {G : Type} [Group G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

set_option quotPrecheck false in
local notation "T₁Q" =>
  (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

theorem Sec3.isElemAbelian_map (hS : Sec3 T T₁) : IsElemAbelian 2 TQ :=
  isElemAbelian_map_of_hom (isWC_subgroupOf hS.cfg.wc _ le_sup_left).1 _

theorem Sec3.map_ne_bot [Finite G] (hS : Sec3 T T₁) : TQ ≠ ⊥ := by
  intro h
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  refine hS.not_le_cfgM fun t ht => ?_
  exact Subgroup.mem_subgroupOf.1
    (h (Subgroup.mem_subgroupOf.2 (show t ∈ T from ht) : (⟨t, Subgroup.mem_sup_left ht⟩ :
      ↥(T ⊔ T₁)) ∈ T.subgroupOf (T ⊔ T₁)))

theorem Sec3.map_ne_map [Finite G] (hS : Sec3 T T₁) : T₁Q ≠ TQ := by
  intro heq
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  obtain ⟨y, hyc, hyM⟩ := IsConcreteLE.not_le_iff_exists.1 (hS.not_conj_le_cfgM hx₀X)
  have hyT₁ : y ∈ T₁ := hx₀ ▸ hyc
  have hyX : y ∈ T ⊔ T₁ := Subgroup.mem_sup_right hyT₁
  have hmem : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (⟨y, hyX⟩ : ↥(T ⊔ T₁)) ∈ T₁Q :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyT₁)
  rw [heq] at hmem
  obtain ⟨a', ha'T, ha'⟩ := hmem
  have h1 : (a' : G)⁻¹ * y ∈ cfgM T T₁ :=
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 ha')
  have haT : (a' : G) ∈ T := Subgroup.mem_subgroupOf.1 ha'T
  obtain ⟨l, hl, x, hx, hlx⟩ := hS.cfg.mem_cfgM_iff.1 h1
  have hxT₁ : x ∈ T₁ := normIn_le _ _ hx
  have hlT : l ∈ T := normIn_le _ _ hl
  have e : (a' : G) * l = y * x⁻¹ := by
    have : y = (a' : G) * (l * x) := by rw [← hlx]; group
    rw [this]
    group
  have hI : (a' : G) * l ∈ T ⊓ T₁ :=
    ⟨T.mul_mem haT hlT, by rw [e]; exact T₁.mul_mem hyT₁ (T₁.inv_mem hxT₁)⟩
  rw [hS.cfg.inf, Subgroup.mem_bot, e, mul_inv_eq_one] at hI
  exact hyM (hI ▸ Cfg.normIn_le_cfgM_right T T₁ hx)

theorem Sec3.isWC_map [Finite G] (hS : Sec3 T T₁) : IsWC TQ := by
  have hTX : T ≤ T ⊔ T₁ := le_sup_left
  have hT₁X : T₁ ≤ T ⊔ T₁ := le_sup_right
  have c' := hS.cfg.subgroupOf_of_le hTX hT₁X
  have htop : T.subgroupOf (T ⊔ T₁) ⊔ T₁.subgroupOf (T ⊔ T₁) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTX hT₁X, Subgroup.subgroupOf_self]
  have hM : cfgM (T.subgroupOf (T ⊔ T₁)) (T₁.subgroupOf (T ⊔ T₁)) =
      (cfgM T T₁).subgroupOf (T ⊔ T₁) := cfgM_subgroupOf_eq hTX hT₁X
  have hN' : (cfgM (T.subgroupOf (T ⊔ T₁)) (T₁.subgroupOf (T ⊔ T₁))).Normal :=
    c'.normal_cfgM htop
  have hwc := (c'.strongWC_map htop).isWC
  let e := QuotientGroup.quotientMulEquivOfEq hM
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (cfgM (T.subgroupOf (T ⊔ T₁))
      (T₁.subgroupOf (T ⊔ T₁)))) = QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    MonoidHom.ext fun g => rfl
  have := IsWC.map_mulEquiv e hwc
  rwa [Subgroup.map_map, hcomp] at this

theorem Sec3.isL2Pair_quotient [Finite G] (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (XQ ≃* PSL(2, GaloisField 2 f))) : IsL2Pair XQ TQ (2 ^ f) := by
  have hT2 : IsPGroup 2 TQ := isPGroup_two_of_isElemAbelian hS.isElemAbelian_map
  obtain ⟨Q, hQ⟩ := hT2.exists_le_sylow
  have hpair := IsL2Pair.of_psl_sylow hf h Q
  have heq : TQ = (Q : Subgroup XQ) := hpair.eq_of_isWC hQ hS.map_ne_bot hS.isWC_map
  rw [heq]
  exact hpair

theorem Sec3.card_map [Finite G] (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (XQ ≃* PSL(2, GaloisField 2 f))) : Nat.card TQ = 2 ^ f :=
  (hS.isL2Pair_quotient hf h).card_eq

theorem Sec3.card_eq_mul [Finite G] (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (XQ ≃* PSL(2, GaloisField 2 f))) :
    Nat.card T = Nat.card (normIn T T₁) * 2 ^ f := by
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
    hS.card_map hf h] at h1
  exact h1.symm

end Quotient

end CFSG.CGT.Timmesfeld75
