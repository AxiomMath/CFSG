module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step18G24
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Embed
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1TwoCDefs
public import CFSG.Sporadic.Co1Patterson.GenerationClasses
public import CFSG.Sporadic.Co1Patterson.GenerationCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)
open CFSG.Blueprint

local notation "Co₁" => CFSG.Blueprint.NativeSporadic.Co1

variable {G : Type} [Group G] [Finite G]

theorem rightConjugate_eq_of_centralizer_le_of_fus {L : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G))
    (hfus : ∀ g : G, z ∈ normalizer (rightConjugate L g : Set G) → rightConjugate L g = L)
    {y : G} (hy : orderOf y = 2) (hyN : centralizer ({y} : Set G) ≤ normalizer (L : Set G))
    {c : G} (hc : y ∈ normalizer (rightConjugate L c : Set G)) : rightConjugate L c = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := normalizer (rightConjugate L c : Set G) with hN'
  have hSc : rightConjugate S c ≤ N' :=
    rightConjugate_le_normalizer_rightConjugate (hSz.trans hzL) c
  have hScG : IsSylowOf 2 (rightConjugate S c) ⊤ := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hS c
    rwa [rightConjugate_top] at h
  have hNodd : ¬ 2 ∣ N'.relIndex ⊤ := by
    have h1 := hScG
    rw [isSylowOf_iff] at h1
    intro h2
    apply h1.2.2
    rw [← relIndex_mul_relIndex _ N' ⊤ hSc le_top]
    exact h2.mul_left _
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 N'
  obtain ⟨a, haN, hay⟩ := AS76b.exists_conj_mem_of_isSylowOf hQ hc (n := 1)
    (by rw [pow_one, ← hy, pow_orderOf_eq_one])
  have hPN : IsSylowOf 2 (rightConjugate Q a) N' := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hQ a
    rwa [(rightConjugate_eq_self_iff N' a).mpr (le_normalizer haN)] at h
  have hyP : y ∈ rightConjugate Q a := (mem_rightConjugate_iff _ _ _).mpr hay
  have hPG : IsSylowOf 2 (rightConjugate Q a) ⊤ := by
    rw [isSylowOf_iff] at hPN ⊢
    refine ⟨le_top, hPN.2.1, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex _ N' ⊤ hPN.1 le_top] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hPN.2.2 h
    · exact hNodd h
  obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hPG
  have hzS : z ∈ S := (mem_centerIn_of_le_centralizer hS hz hSz).1
  have hz'P : k * z * k⁻¹ ∈ rightConjugate Q a :=
    (hk _).mpr (by rwa [show k⁻¹ * (k * z * k⁻¹) * k = z by group])
  have hz'y : k * z * k⁻¹ ∈ centralizer ({y} : Set G) := by
    have h1 := mem_centralizer_singleton_iff.mp (hSz ((hk y).mp hyP))
    rw [mem_centralizer_singleton_iff]
    calc k * z * k⁻¹ * y = k * (z * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * (k⁻¹ * y * k * z) * k⁻¹ := by rw [h1]
      _ = y * (k * z * k⁻¹) := by group
  have hkN : k ∈ normalizer (L : Set G) :=
    (rightConjugate_eq_self_iff L k).mp (hfus k (mem_normalizer_rightConjugate_iff.mpr (hyN hz'y)))
  have h3 : rightConjugate (rightConjugate L c) k = L := by
    have h4 : z ∈ normalizer (rightConjugate (rightConjugate L c) k : Set G) :=
      mem_normalizer_rightConjugate_iff.mpr (hPN.le hz'P)
    rw [rightConjugate_mul] at h4 ⊢
    exact hfus _ h4
  calc rightConjugate L c = rightConjugate (rightConjugate (rightConjugate L c) k) k⁻¹ :=
        (rightConjugate_rightConjugate_inv_cancel _ _).symm
    _ = rightConjugate L k⁻¹ := by rw [h3]
    _ = L := (rightConjugate_eq_self_iff L k⁻¹).mpr (inv_mem hkN)

omit [Finite G] in
theorem card_centralizer_conj_mul {Y : Type*} [Group Y] (c σ : Y) :
    Nat.card (centralizer ({c * σ * c⁻¹} : Set Y)) = Nat.card (centralizer ({σ} : Set Y)) := by
  have e : (centralizer ({σ} : Set Y)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * σ * c⁻¹} : Set Y) := by
    ext w
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      calc c * v * c⁻¹ * (c * σ * c⁻¹) = c * (v * σ) * c⁻¹ := by group
        _ = c * (σ * v) * c⁻¹ := by rw [hv]
        _ = c * σ * c⁻¹ * (c * v * c⁻¹) := by group
    · intro hw
      refine ⟨c⁻¹ * w * c, ?_, by group⟩
      calc c⁻¹ * w * c * σ = c⁻¹ * (w * (c * σ * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * σ * c⁻¹ * w) * c := by rw [hw]
        _ = σ * (c⁻¹ * w * c) := by group
  rw [← e, card_map_of_injective (MulAut.conj c).injective]

section Classes


theorem centralizer_le_normalizer_of_co1TwoC (h2C : RankTwoExceptional.Co1TwoCControl)
    {L : Subgroup G} {φ : normalizer (L : Set G) →* Co₁} (hφ : IsActionHom L ⊤ φ)
    (hZodd : Odd (Nat.card (center ↥L))) (hCL : Odd (Nat.card (centralizer (L : Set G))))
    {z : G} (hz : orderOf z = 2) (hzLm : z ∈ L)
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G))
    (huniq : ∀ k : G, k * z * k⁻¹ ∈ L → k ∈ normalizer (L : Set G))
    {r : G} (hro : orderOf r = 2) (hrL : r ∈ L) (hrz : ∀ l ∈ L, r ≠ l * z * l⁻¹)
    (hrN : centralizer ({r} : Set G) ≤ normalizer (L : Set G))
    (hr7 : 7 ∣ Nat.card (centralizer ({φ ⟨r, le_normalizer hrL⟩} : Set Co₁)))
    {y : G} (hyL : y ∈ L) (hy : orderOf y = 2) :
    centralizer ({y} : Set G) ≤ normalizer (L : Set G) := by
  have sq2 : ∀ {a : G}, orderOf a = 2 → a ^ 2 = 1 := fun h => by rw [← h, pow_orderOf_eq_one]
  have hcls₀ :=
    CFSG.Sporadic.Co1Patterson.exists_involution_classes (Y := Co₁) (MulEquiv.refl Co₁)
  obtain ⟨a₀, b₀, c₀, hcls, -, -, -, -, -, -, hCa, hCb, hCc⟩ := hcls₀
  have hcardCo1 : Nat.card Co₁ = 4157776806543360000 :=
    CFSG.Sporadic.Co1Patterson.card_eq_of_mulEquiv_co1 (Y := Co₁) (MulEquiv.refl Co₁)
  have hcardconj : ∀ {σ τ : Co₁}, IsConj σ τ →
      Nat.card (centralizer ({τ} : Set Co₁)) =
        Nat.card (centralizer ({σ} : Set Co₁)) := fun h => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp h
    exact card_centralizer_conj_mul c _
  have hrange : φ.range = ⊤ := eq_top_iff.mpr (le_range_actionHom hφ)
  have hz2c : ¬ 2 ∣ (centralizer ({φ ⟨z, le_normalizer hzLm⟩} :
      Set Co₁)).index := by
    have h := not_two_dvd_relIndex_of_sylow (φ := φ) hzL hS hSz
    rwa [hrange, relIndex_top_right] at h
  have hφz := orderOf_actionHom hφ hCL (r := ⟨z, le_normalizer hzLm⟩) hz
  have hza : IsConj a₀ (φ ⟨z, le_normalizer hzLm⟩) := by
    have hidx := (centralizer ({φ ⟨z, le_normalizer hzLm⟩} : Set Co₁)).index_mul_card
    rw [hcardCo1] at hidx
    rcases hcls _ hφz with h | h | h
    · exact h
    · rw [hcardconj h, hCb] at hidx
      exact absurd (by omega : 2 ∣ _) hz2c
    · rw [hcardconj h, hCc] at hidx
      exact absurd (by omega : 2 ∣ _) hz2c
  have hφr := orderOf_actionHom hφ hCL (r := ⟨r, le_normalizer hrL⟩) hro
  have hrb : IsConj b₀ (φ ⟨r, le_normalizer hrL⟩) := by
    rcases hcls _ hφr with h | h | h
    · obtain ⟨m, hm⟩ := isConj_iff.mp (hza.symm.trans h)
      obtain ⟨l, hl, hlr⟩ := exists_conj_of_map_conj hφ hZodd hzLm hrL (sq2 hz) (sq2 hro)
        (mem_top m) hm.symm
      exact absurd hlr (hrz l hl)
    · exact h
    · rw [hcardconj h, hCc] at hr7
      norm_num at hr7
  have hφy := orderOf_actionHom hφ hCL (r := ⟨y, le_normalizer hyL⟩) hy
  rcases hcls _ hφy with h | h | h
  · obtain ⟨m, hm⟩ := isConj_iff.mp (hza.symm.trans h)
    obtain ⟨l, hl, rfl⟩ := exists_conj_of_map_conj hφ hZodd hzLm hyL (sq2 hz) (sq2 hy)
      (mem_top m) hm.symm
    exact centralizer_conj_le_normalizer (le_normalizer hl) hzL
  · obtain ⟨m, hm⟩ := isConj_iff.mp (hrb.symm.trans h)
    obtain ⟨l, hl, rfl⟩ := exists_conj_of_map_conj hφ hZodd hrL hyL (sq2 hro) (sq2 hy)
      (mem_top m) hm.symm
    exact centralizer_conj_le_normalizer (le_normalizer hl) hrN
  · have hcy : Nat.card (centralizer ({φ ⟨y, le_normalizer hyL⟩} : Set Co₁)) =
        389283840 := by rw [hcardconj h, hCc]
    exact h2C G L φ hφ hZodd hCL z hzLm hz hz2c huniq y hyL hy hcy

end Classes

section Main


theorem false_of_co1TwoC_g24
    (h2C : RankTwoExceptional.Co1TwoCControl) {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
    {x : G} (hSt : Sec3Setting G A A₁ R g E F x)
    (hHA : normalClosure (A : Set G) = CFSG.generalizedFitting G)
    (hFs : IsSimpleGroup (CFSG.generalizedFitting G)) {z : G} (hz : orderOf z = 2)
    (hzA₁ : z ∈ A₁) (hnp : ∀ h : G, z ∉ rightConjugate R h) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G))
    (hRz : R ≤ centralizer ({z} : Set G)) {L : Subgroup G} {φ : normalizer (L : Set G) →* Co₁}
    (hφ : IsActionHom L ⊤ φ) (hZodd : Odd (Nat.card (center ↥L)))
    (hCL : Odd (Nat.card (centralizer (L : Set G))))
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hLH : L ≤ CFSG.generalizedFitting G) (hAL : A ≤ L) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWL : W ≤ centralizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hFs
  have hB := hSt.base
  have hstd := hB.hyp.standard
  have hq : Open.IsQuasisimple ↥A := hstd.1
  have hK := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRK : R ≤ centralizer (A : Set G) := hSt.sylowR.le
  have hAH : A ≤ CFSG.generalizedFitting G := hHA ▸ subset_normalClosure
  have hHn : (CFSG.generalizedFitting G).Normal := hHA ▸ normalClosure_normal
  have hD := Co1Fusion.co1_fusionModel
  have hφT : φ.range ≤ ⊤ := le_top
  have hA₁A : A₁ ≤ A := hSt.le
  have hzLm : z ∈ L := hAL (hA₁A hzA₁)
  have hzH : z ∈ CFSG.generalizedFitting G := hLH hzLm
  have hzN : z ∈ normalizer (L : Set G) := hzL (mem_centralizer_singleton_iff.mpr rfl)
  have hfus : ∀ c : G, z ∈ normalizer (rightConjugate L c : Set G) → rightConjugate L c = L :=
    fun c hc => rightConjugate_eq_of_fusionModel_odd hD hφ hφT hZodd hCL hz hzL hS hSz hc
  have huniq : ∀ k : G, k * z * k⁻¹ ∈ L → k ∈ normalizer (L : Set G) := fun k hk =>
    (rightConjugate_eq_self_iff L k).mp
      (hfus k (le_normalizer ((mem_rightConjugate_iff L k z).mpr hk)))
  have hNAL : normalizer (A : Set G) ≤ normalizer (L : Set G) := fun k hk =>
    huniq k (hAL ((mem_normalizer_iff.mp hk z).mp (hA₁A hzA₁)))
  have hRN : R ≤ normalizer (L : Set G) := hRz.trans hzL
  obtain ⟨r, ⟨hrR, hrL⟩, hr1⟩ :=
    exists_mem_inf_of_fusionModel hD hφ hφT hCL hRN hSt.elemR hSt.frame.cardR
  have hr2 : r ^ 2 = 1 := hSt.elemR.2 r hrR
  have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
  have hrA : ∀ a ∈ A, a * r = r * a := fun a ha => mem_centralizer_iff.mp (hRK hrR) a ha
  have hCr : centralizer ({r} : Set G) ≤ normalizer (A : Set G) := by
    intro c hc
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hK (hRK hrR) hr1 hr2
      (mem_centralizer_singleton_iff.mp hc)
  have hrz : ∀ l ∈ L, r ≠ l * z * l⁻¹ := fun l _ h =>
    hnp l ((mem_rightConjugate_iff R l z).mpr (h ▸ hrR))
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7A : 7 ∣ Nat.card A₁ := by rw [Sec3.card_A₁ hSt]; norm_num
  obtain ⟨⟨s, hsA₁⟩, hs7⟩ := exists_prime_orderOf_dvd_card' (G := ↥A₁) 7 h7A
  rw [Subgroup.orderOf_mk] at hs7
  have hsL : s ∈ L := hAL (hA₁A hsA₁)
  have hφs : φ ⟨s, le_normalizer hsL⟩ ∈
      centralizer ({φ ⟨r, le_normalizer hrL⟩} : Set Co₁) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hrA s (hA₁A hsA₁))
  have hord : orderOf (φ ⟨s, le_normalizer hsL⟩) = 7 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow]
      have : (⟨s, le_normalizer hsL⟩ : normalizer (L : Set G)) ^ 7 = 1 :=
        Subtype.ext (by rw [coe_pow, ← hs7, pow_orderOf_eq_one, coe_one])
      rw [this, map_one]
    · have hsC := (hφ.eq_one_iff _).mp h1
      have hsZ : s ∈ centerIn A₁ :=
        ⟨hsA₁, fun a ha => mem_centralizer_iff.mp hsC a (hAL (hA₁A ha))⟩
      rw [hSt.center_A₁] at hsZ
      have h3 := orderOf_dvd_of_mem_zpowers hsZ
      rw [hs7, hSt.order_x] at h3
      norm_num at h3
  have hr7 : 7 ∣ Nat.card (centralizer ({φ ⟨r, le_normalizer hrL⟩} : Set Co₁)) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hφs
  have hcentL : ∀ y ∈ L, orderOf y = 2 → centralizer ({y} : Set G) ≤ normalizer (L : Set G) :=
    fun y hy hy2 => centralizer_le_normalizer_of_co1TwoC h2C hφ hZodd hCL hz hzLm hzL hS hSz
      huniq hro hrL hrz (hCr.trans hNAL) hr7 hy hy2
  have hinv : ∀ y ∈ L, orderOf y = 2 → ∀ c : G, y ∈ normalizer (rightConjugate L c : Set G) →
      rightConjugate L c = L := fun y hy hy2 _ hc =>
    rightConjugate_eq_of_centralizer_le_of_fus hz hzL hS hSz hfus hy2 (hcentL y hy hy2) hc
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZ : center ↥A = ⊤ := eq_top_iff.mpr fun x _ =>
      mem_center_iff.mpr fun y => Subtype.ext (hcon y y.2 x x.2)
    have : Nontrivial (↥A ⧸ center ↥A) := hq.2.toNontrivial
    obtain ⟨u, hu⟩ := exists_ne (1 : ↥A ⧸ center ↥A)
    apply hu
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    rw [QuotientGroup.eq_one_iff, hZ]
    exact mem_top a
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x :=
    ⟨⟨a, hAH ha⟩, ⟨b, hAH hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hZH : center ↥(CFSG.generalizedFitting G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(CFSG.generalizedFitting G))
      with h | h
    · exact h
    · obtain ⟨x, y, hxy⟩ := hnab
      exact absurd (mem_center_iff.mp (h ▸ mem_top y) x) hxy
  set NH : Subgroup ↥(CFSG.generalizedFitting G) :=
    (normalizer (L : Set G)).subgroupOf (CFSG.generalizedFitting G) with hNHdef
  have hNH : NH ≠ ⊤ := by
    intro htop
    have hLn : (L.subgroupOf (CFSG.generalizedFitting G)).Normal := by
      refine ⟨fun n hn h => ?_⟩
      have hh : (h : G) ∈ normalizer (L : Set G) := by
        have : h ∈ NH := htop ▸ mem_top h
        exact this
      rw [mem_subgroupOf] at hn ⊢
      have := (mem_normalizer_iff.mp hh n).mp hn
      simpa using this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf (CFSG.generalizedFitting G))
      with h | h
    · have hz1 : z = 1 := Subgroup.disjoint_def.mp (subgroupOf_eq_bot.mp h) hzLm hzH
      rw [hz1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · have hHL : CFSG.generalizedFitting G ≤ L := subgroupOf_eq_top.mp h
      apply hW
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ centralizer (CFSG.generalizedFitting G : Set G) :=
        centralizer_le hHL (hWL hw)
      have hwH : w ∈ CFSG.generalizedFitting G := CFSG.centralizer_generalizedFitting_le G hwC
      have hwZ : (⟨w, hwH⟩ : ↥(CFSG.generalizedFitting G)) ∈
          center ↥(CFSG.generalizedFitting G) :=
        mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hwC y y.2)
      rw [hZH, mem_bot] at hwZ
      exact (mem_bot).mpr (congrArg Subtype.val hwZ)
  have hSH : IsSylowOf 2 (S ⊓ CFSG.generalizedFitting G) (CFSG.generalizedFitting G) :=
    hS.inf_of_le_normalizer le_top (fun x _ => by
      rw [mem_normalizer_iff]
      intro y
      exact ⟨fun hy => hHn.conj_mem y hy x, fun hy => by
        have := hHn.conj_mem _ hy x⁻¹
        simpa [mul_assoc] using this⟩)
  have hinvL : ∀ x ∈ CFSG.generalizedFitting G, x ∈ normalizer (L : Set G) → orderOf x = 2 →
      x ∈ L := fun x hxH hxN hx =>
    mem_of_mem_normalizer hFs hnab hD hφ hφT hCL hSH (hSz.trans hzL) hinv hxH hxN hx
  have hSE : CFSG.IsStronglyEmbedded NH := by
    refine AS81.HeSE.isStronglyEmbedded_of_fusion NH hNH ?_ ?_ ?_
    · have hzNH : (⟨z, hzH⟩ : ↥(CFSG.generalizedFitting G)) ∈ NH := hzN
      have h2 := Subgroup.orderOf_dvd_natCard NH hzNH
      rw [Subgroup.orderOf_mk, hz] at h2
      exact even_iff_two_dvd.mpr h2
    · intro u hu hu2 k hk
      refine ⟨k, ?_, rfl⟩
      have hu2' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
      have huL := hinvL _ u.2 hu hu2'
      have hk2 : orderOf ((k * u * k⁻¹ : ↥(CFSG.generalizedFitting G)) : G) = 2 := by
        rw [Subgroup.orderOf_coe, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hu2
      have hkuL := hinvL _ (k * u * k⁻¹).2 hk hk2
      have hmem : (u : G) ∈ rightConjugate L (k : G) :=
        (mem_rightConjugate_iff L (k : G) (u : G)).mpr (by simpa using hkuL)
      exact (rightConjugate_eq_self_iff L (k : G)).mp (hinv _ huL hu2' k (le_normalizer hmem))
    · intro u hu hu2 c hc
      have hu2' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
      have huL := hinvL _ u.2 hu hu2'
      have hcG : (c : G) ∈ centralizer ({(u : G)} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
      exact hcentL _ huL hu2' hcG
  have hsol : Group.IsSolvable ↥NH :=
    AschbacherStrongEmbedding.strongly_embedded_solvable ↥(CFSG.generalizedFitting G) NH hSE
      (two_le_twoRank_of_sec3 hSt hAH)
  have hANH : ∀ a : ↥A, (⟨(a : G), hAH a.2⟩ : ↥(CFSG.generalizedFitting G)) ∈ NH := fun a =>
    le_normalizer (hAL a.2)
  let f : ↥A →* ↥NH :=
    { toFun := fun a => ⟨⟨a, hAH a.2⟩, hANH a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun y : ↥NH => ((y : ↥(CFSG.generalizedFitting G)) : G)) h)
  have : Group.IsSolvable ↥A := Group.isSolvable_of_isSolvable_injective hinj
  exact not_isSolvable_of_isQuasisimple hq this

theorem oddCoreIn_centralizer_eq_bot_of_sec3Suz_of_co1TwoC (h17 : Step17G24Odd)
    (h2C : RankTwoExceptional.Co1TwoCControl)
    {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
    {Zs P T Q B₀ : Subgroup G} {z₀ y : G} (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z₀ y)
    {z : G} (hzE : z ∈ E) (hz : orderOf z = 2)
    (hS2 : ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ centralizer ({z} : Set G))
    (hnp : ∀ h : G, z ∉ rightConjugate R h) :
    AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨S, -, hSzS⟩ := hS2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hW
  have hSt := hSz.setting
  have hFr := hSt.frame
  have hB := hSt.base
  have hstd := hB.hyp.standard
  obtain ⟨hHA, hFs⟩ := AS76b.asc08Lemma34 G A hB.hyp31
  obtain ⟨hNtop, hAW, hzW, hH⟩ := rankTwoHyp_normalizer_of_sec3Suz h17 hSz hzE hnp hW
  set W := AS76b.oddCoreIn (centralizer ({z} : Set G)) with hWdef
  set N := normalizer (W : Set G) with hNdef
  have hcard : Nat.card N < Nat.card G := by
    have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNtop)
    rwa [card_top] at this
  have hAN : A ≤ N := hAW.trans (centralizer_le_normalizer _)
  let eA : ↥(A.subgroupOf N) ≃* ↥A := subgroupOfEquivOfLe hAN
  have hT₁ : TypeG24 (rankTwoQuot (A.subgroupOf N)) :=
    SectionRank.chevalleyExceptionalModel_of_mulEquiv
      (QuotientGroup.congr (center _) (center _) eA (Subgroup.map_center_eq eA)) hSt.type
  obtain ⟨hHq, hOq, ⟨eq⟩⟩ := rankTwoHyp_map_quotient hH
  have hcardq : Nat.card (↥N ⧸ standardComponentOddCore ↥N) < Nat.card G :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hcard
  obtain ⟨-, ⟨eCo⟩⟩ := (hSt.below _ _ hcardq).2 hHq hOq
    (Or.inl ⟨2, le_rfl, SectionRank.chevalleyExceptionalModel_of_mulEquiv eq.symm hT₁⟩)
  have hZq : center ↥(rankTwoX ((A.subgroupOf N).map
      (QuotientGroup.mk' (standardComponentOddCore ↥N)))) = ⊥ := by
    rw [← map_center_eq eCo.symm, center_eq_bot_of_autModel RankTwoSporadic.Co1.co1AutModel,
      Subgroup.map_bot]
  obtain ⟨⟨eX⟩, hXodd⟩ := quotCenter_equiv_map_of_center_eq_bot hH.standard hH.rank hZq
  have hCL := odd_card_centralizer_closureIn hstd hAN hH.not_normal
  have hzL := hzW.trans (le_normalizer_closureIn A N)
  have hLH : closureIn A N ≤ CFSG.generalizedFitting G := hHA ▸ closureIn_le_normalClosure A _
  have hWL : W ≤ centralizer (closureIn A N : Set G) :=
    le_centralizer_iff.mp (closureIn_le_centralizer hAW)
  have hRz : R ≤ centralizer ({z} : Set G) := fun r hr => by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hFr.elemE.1.is_comm.comm ⟨r, hFr.R_le_E hr⟩ ⟨z, hzE⟩)
  have hS : IsSylowOf 2 (S : Subgroup G) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  let eL : ↥(closureIn A N) ≃* ↥(rankTwoX (A.subgroupOf N)) :=
    ((rankTwoX _).equivMapOfInjective _ N.subtype_injective).symm
  have hperf : commutator ↥(closureIn A N) = ⊤ :=
    commutator_eq_top_of_mulEquiv eL.symm
      (RankTwoL3Four.commutator_rankTwoX_eq_top
        (commutator_eq_top_of_mulEquiv eA.symm hstd.1.1))
  have hZodd : Odd (Nat.card (center ↥(closureIn A N))) := by
    rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv]
    exact hXodd
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoSporadic.Co1.co1AutModel hperf
    ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans (eX.trans eCo))
  exact false_of_co1TwoC_g24 h2C hSt hHA hFs hz (hSz.mem_A₁_of_forall_not_mem hzE hnp) hnp hS
    hSzS hRz hψ hZodd hCL hzL hLH (le_closureIn hAN) hW hWL

theorem step18G24_of_co1TwoC (h17 : Step17G24Odd) (h2C : RankTwoExceptional.Co1TwoCControl) :
    Step18G24 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSz _ hzE hz hS2 hnp =>
    oddCoreIn_centralizer_eq_bot_of_sec3Suz_of_co1TwoC h17 h2C hSz hzE hz hS2 hnp

end Main

end CFSG.ComponentClassification.AS81
