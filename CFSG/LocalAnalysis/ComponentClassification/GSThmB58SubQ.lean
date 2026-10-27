module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

variable (h : Hyp52 X) (y : X)

abbrev subQuot : Type := ↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y)

@[expose] def subMk : ↥(h.secSub y) →* ↥(h.secSubImg y) :=
  ((h.secMk y).comp (inclusion (h.secSub_le_G0 y))).codRestrict (h.secSubImg y) fun g =>
    mem_map_of_mem _ (show inclusion (h.secSub_le_G0 y) g ∈ (h.secSub y).subgroupOf (h.secG0 y)
      from g.2)

abbrev subQ : ↥(h.secSub y) →* h.subQuot y :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))).comp (h.subMk y)

theorem subMk_coe (g : ↥(h.secSub y)) :
    ((h.subMk y g : ↥(h.secSubImg y)) : h.secBar y) = h.secMk y ⟨g, h.secSub_le_G0 y g.2⟩ :=
  rfl

theorem subMk_surjective : Function.Surjective (h.subMk y) := by
  rintro ⟨z, hz⟩
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hz
  exact ⟨⟨g, mem_subgroupOf.mp hg⟩, Subtype.ext rfl⟩

theorem subQ_surjective : Function.Surjective (h.subQ y) :=
  (QuotientGroup.mk'_surjective _).comp (h.subMk_surjective y)

theorem ker_subMk : (h.subMk y).ker = (h.secB0 y).subgroupOf (h.secSub y) := by
  ext g
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hg
    have h1 : (⟨g, h.secSub_le_G0 y g.2⟩ : ↥(h.secG0 y)) ∈ (h.secMk y).ker := by
      rw [MonoidHom.mem_ker, ← subMk_coe, hg, OneMemClass.coe_one]
    rw [h.ker_secMk] at h1
    exact mem_subgroupOf.mp h1
  · intro hg
    apply Subtype.ext
    rw [subMk_coe, OneMemClass.coe_one, ← MonoidHom.mem_ker, h.ker_secMk]
    exact mem_subgroupOf.mpr hg

theorem S_inf_le_secSub : h.S ⊓ h.secG0 y ≤ h.secSub y :=
  (h.S_inf_le_secC0 y).trans (h.secC0_le_secSub y)

theorem P_inf_le_secSub : h.P ⊓ h.secG0 y ≤ h.secSub y :=
  (inf_le_inf_right _ inf_le_left).trans (h.S_inf_le_secSub y)

variable {h y}

theorem subQ_eq_one_of_mem_secB0 {w : ↥(h.secSub y)} (hw : (w : X) ∈ h.secB0 y) :
    h.subQ y w = 1 := by
  have h1 : h.subMk y w = 1 := by
    rw [← MonoidHom.mem_ker, ker_subMk]
    exact mem_subgroupOf.mpr hw
  show QuotientGroup.mk' _ (h.subMk y w) = 1
  rw [h1, map_one]

theorem map_subMk {Y : Subgroup X} (hY : Y ≤ h.secSub y) :
    (Y.subgroupOf (h.secSub y)).map (h.subMk y) = (h.secImage y Y).subgroupOf (h.secSubImg y) := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_subgroupOf.mpr (mem_map_of_mem _ (show (⟨g, h.secSub_le_G0 y g.2⟩ : ↥(h.secG0 y)) ∈
      Y.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr (mem_subgroupOf.mp hg)))
  · intro hz
    obtain ⟨g, hg, hgz⟩ := mem_map.mp (mem_subgroupOf.mp hz)
    exact ⟨⟨g, hY (mem_subgroupOf.mp hg)⟩, mem_subgroupOf.mpr (mem_subgroupOf.mp hg),
      Subtype.ext hgz⟩

theorem map_subQ {Y : Subgroup X} (hY : Y ≤ h.secSub y) :
    (Y.subgroupOf (h.secSub y)).map (h.subQ y) =
      ((h.secImage y Y).subgroupOf (h.secSubImg y)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) := by
  rw [← map_subMk hY, Subgroup.map_map]

theorem map_subQ_secJ0 : ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) =
    (h.subJ y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) :=
  map_subQ (h.secJ0_le_secSub y)

theorem map_subQ_S : ((h.S ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) =
    (h.subS y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) := by
  rw [map_subQ (h.S_inf_le_secSub y), secImage_W_inf]

theorem map_subQ_P : ((h.P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) =
    ((h.secImage y h.P).subgroupOf (h.secSubImg y)).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) := by
  rw [map_subQ (h.P_inf_le_secSub y), secImage_W_inf]

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem subQ_a : h.subQ y ⟨h.a, hc.a_mem_secSub⟩ =
    QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subA :=
  rfl

theorem subQ_y : h.subQ y ⟨y, hc.y_mem_secSub⟩ =
    QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subX :=
  rfl

theorem map_subQ_B : (h.B.subgroupOf (h.secSub y)).map (h.subQ y) =
    (h.subB y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) :=
  map_subQ hc.B_le_secSub

theorem map_subQ_K : (h.K.subgroupOf (h.secSub y)).map (h.subQ y) =
    (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) :=
  map_subQ (K_le_secSub hc)

theorem Q_le_secSub : h.Q ≤ h.secSub y := hc.Q_le_secC0.trans (h.secC0_le_secSub y)

theorem T_le_secSub : h.T ≤ h.secSub y := (inf_le_left : h.T ≤ h.Q).trans hc.Q_le_secSub

theorem map_subQ_Q : (h.Q.subgroupOf (h.secSub y)).map (h.subQ y) =
    ((h.secImage y h.Q).subgroupOf (h.secSubImg y)).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) :=
  map_subQ hc.Q_le_secSub

theorem map_subQ_T : (h.T.subgroupOf (h.secSub y)).map (h.subQ y) =
    ((h.secImage y h.T).subgroupOf (h.secSubImg y)).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) :=
  map_subQ hc.T_le_secSub

end SecCond

theorem subQ_eq_one_of_two {w : ↥(h.secSub y)} {k : ℕ} (hw : (w : X) ^ 2 ^ k = 1)
    (h1 : h.subQ y w = 1) : (w : X) ∈ h.secB0 y := by
  have h2 : h.subMk y w ∈ pPrimeCore 2 ↥(h.secSubImg y) := by
    have : QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) (h.subMk y w) = 1 := h1
    exact (QuotientGroup.eq_one_iff _).mp this
  have hw' : w ^ 2 ^ k = 1 := Subtype.ext hw
  have hd1 : orderOf (h.subMk y w) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hw', map_one]
  have hd2 : orderOf (h.subMk y w) ∣ Nat.card (pPrimeCore 2 ↥(h.secSubImg y)) := by
    have := orderOf_dvd_natCard (⟨h.subMk y w, h2⟩ : pPrimeCore 2 ↥(h.secSubImg y))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥(h.secSubImg y))) :=
    Nat.Coprime.pow_left k (pPrimeCore_coprime_card (p := 2) (G := ↥(h.secSubImg y)))
  have h3 : orderOf (h.subMk y w) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  rw [orderOf_eq_one_iff] at h3
  have h4 : w ∈ (h.subMk y).ker := h3
  rw [ker_subMk] at h4
  exact mem_subgroupOf.mp h4

theorem subQ_injOn {Y : Subgroup X} (hY : IsPGroup 2 Y) (hYB : Y ⊓ h.secB0 y = ⊥) :
    Set.InjOn (h.subQ y) ((Y.subgroupOf (h.secSub y) : Subgroup _) : Set ↥(h.secSub y)) := by
  intro v hv w hw hvw
  have hm : v⁻¹ * w ∈ Y.subgroupOf (h.secSub y) := mul_mem (inv_mem hv) hw
  obtain ⟨k, hk⟩ := hY ⟨((v⁻¹ * w : ↥(h.secSub y)) : X), mem_subgroupOf.mp hm⟩
  have hk' : ((v⁻¹ * w : ↥(h.secSub y)) : X) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : h.subQ y (v⁻¹ * w) = 1 := by rw [map_mul, map_inv, hvw, inv_mul_cancel]
  have h3 : ((v⁻¹ * w : ↥(h.secSub y)) : X) ∈ Y ⊓ h.secB0 y :=
    mem_inf.mpr ⟨mem_subgroupOf.mp hm, subQ_eq_one_of_two hk' h1⟩
  rw [hYB, mem_bot] at h3
  have h4 : v⁻¹ * w = 1 := Subtype.ext h3
  exact inv_mul_eq_one.mp h4

theorem card_map_subQ_of_inf {Y : Subgroup X} (hY : IsPGroup 2 Y) (hYH : Y ≤ h.secSub y)
    (hYB : Y ⊓ h.secB0 y = ⊥) :
    Nat.card ↥((Y.subgroupOf (h.secSub y)).map (h.subQ y)) = Nat.card Y := by
  have hinj : Function.Injective ((h.subQ y).subgroupMap (Y.subgroupOf (h.secSub y))) := by
    intro v w hvw
    exact Subtype.ext (subQ_injOn hY hYB v.2 w.2 (congrArg Subtype.val hvw))
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, (h.subQ y).subgroupMap_surjective _⟩)]
  exact Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv

theorem subQ_mem_map_iff {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (hYP : Y ≤ h.P)
    {w : ↥(h.secSub y)} (hwP : (w : X) ∈ h.P) :
    h.subQ y w ∈ (Y.subgroupOf (h.secSub y)).map (h.subQ y) ↔ (w : X) ∈ Y := by
  constructor
  · intro hw
    obtain ⟨v, hvY, hvw⟩ := mem_map.mp hw
    have hP2 : IsPGroup 2 ((h.secImage y h.P).subgroupOf (h.secSubImg y)) :=
      (((h.isPGroup_S.to_le inf_le_left).comap_subtype).map _).comap_subtype
    have hv : h.subMk y v ∈ (h.secImage y h.P).subgroupOf (h.secSubImg y) :=
      mem_subgroupOf.mpr (mem_map_of_mem _ (show (⟨v, h.secSub_le_G0 y v.2⟩ : ↥(h.secG0 y)) ∈
        h.P.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr (hYP (mem_subgroupOf.mp hvY))))
    have hw' : h.subMk y w ∈ (h.secImage y h.P).subgroupOf (h.secSubImg y) :=
      mem_subgroupOf.mpr (mem_map_of_mem _ (show (⟨w, h.secSub_le_G0 y w.2⟩ : ↥(h.secG0 y)) ∈
        h.P.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr hwP))
    have h1 : h.subMk y v = h.subMk y w := OddQuot.injOn_of_isPGroup hP2 hv hw' hvw
    have h2 : h.secMk y ⟨w, h.secSub_le_G0 y w.2⟩ ∈ h.secImage y Y := by
      rw [← subMk_coe, ← h1, subMk_coe]
      exact mem_map_of_mem _ (show (⟨v, h.secSub_le_G0 y v.2⟩ : ↥(h.secG0 y)) ∈
        Y.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr (mem_subgroupOf.mp hvY))
    exact (Hyp52.secMk_mem_secImage_iff hBY _).mp h2
  · intro hw
    exact mem_map_of_mem _ (show w ∈ Y.subgroupOf (h.secSub y) from mem_subgroupOf.mpr hw)

theorem card_map_subQ_mul {Y : Subgroup X} (hY : IsPGroup 2 Y) (hBY : h.secB0 y ≤ Y)
    (hYH : Y ≤ h.secSub y) :
    Nat.card ↥((Y.subgroupOf (h.secSub y)).map (h.subQ y)) * Nat.card (h.secB0 y) =
      Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYI : h.secImage y Y ≤ h.secSubImg y := secImage_mono hYH
  have h2 : IsPGroup 2 ((h.secImage y Y).subgroupOf (h.secSubImg y)) :=
    (hY.comap_subtype.map _).comap_subtype
  rw [map_subQ hYH, OddQuot.card_map_of_isPGroup h2,
    Nat.card_congr (subgroupOfEquivOfLe hYI).toEquiv]
  exact Hyp52.card_secImage hBY (hYH.trans (h.secSub_le_G0 y))

theorem isKGroupCat_subQuot [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) (hB0 : h.secB0 y ≠ ⊥) :
    SectionRank.IsKGroupCat (h.subQuot y) := by
  have hne : h.secG0 y ≠ ⊤ := normalizer_ne_top_of_simple hnonab hB0 (h.isPGroup_secB0 y)
  have hG : SectionRank.IsKGroupCat ↥(h.secG0 y) :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK _ hne
  exact ((hG.quotient _).subgroup _).quotient _

theorem SecCond.kappa_of_secL0_inf_eq_bot (hc : h.SecCond y) (hL : h.secL0 y ⊓ h.secB0 y = ⊥) :
    ∀ l ∈ layerIn (centralizer (h.secB0 y : Set X)),
      l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y → l * h.a = h.a * l := by
  intro l hl _ hlB
  have haN : h.a ∈ normalizer (h.secL0 y : Set X) := h.G0_le_normalizer_secL0 y hc.a_mem_G0
  have h1 : h.a * l⁻¹ * h.a⁻¹ ∈ h.secL0 y := (mem_normalizer_iff.mp haN l⁻¹).mp (inv_mem hl)
  have h2 : l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secL0 y := by
    rw [show l * h.a * l⁻¹ * h.a⁻¹ = l * (h.a * l⁻¹ * h.a⁻¹) by group]
    exact mul_mem hl h1
  have h3 : l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secL0 y ⊓ h.secB0 y := mem_inf.mpr ⟨h2, hlB⟩
  rw [hL, mem_bot] at h3
  calc l * h.a = l * h.a * l⁻¹ * h.a⁻¹ * (h.a * l) := by group
    _ = h.a * l := by rw [h3, one_mul]

end Hyp52

end CFSG.ComponentClassification.GSThmB
