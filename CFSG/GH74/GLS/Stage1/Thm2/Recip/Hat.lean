module

public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.GLS.TwoThin.Cover
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev Hat (K : Subgroup G) : Type := ↥K ⧸ pPrimeCore 2 ↥K

abbrev hatMk (K : Subgroup G) : ↥K →* Hat K := QuotientGroup.mk' (pPrimeCore 2 ↥K)

theorem odd_card_ker_hatMk (K : Subgroup G) : Odd (Nat.card (hatMk K).ker) :=
  TwoThin.odd_card_ker_barMk (Y := ↥K)

omit [Finite G] in
theorem hatMk_surjective (K : Subgroup G) : Function.Surjective (hatMk K) :=
  QuotientGroup.mk'_surjective _

theorem eq_of_hatMk_eq {K S : Subgroup G} (hSK : S ≤ K) (hS : IsPGroup 2 ↥S) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) (h : hatMk K ⟨a, hSK ha⟩ = hatMk K ⟨b, hSK hb⟩) : a = b := by
  have hS' : IsPGroup 2 ↥(S.subgroupOf K) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hinj := ComponentClassification.OddKernel.image_injective_on_two (hatMk K)
    (odd_card_ker_hatMk K) (S.subgroupOf K) hS'
  have h2 := @hinj ⟨⟨a, hSK ha⟩, ha⟩ ⟨⟨b, hSK hb⟩, hb⟩ h
  exact congrArg (fun z : ↥(S.subgroupOf K) => ((z : ↥K) : G)) h2

theorem orderOf_hatMk {K S : Subgroup G} (hSK : S ≤ K) (hS : IsPGroup 2 ↥S) {a : G} (ha : a ∈ S) :
    orderOf (hatMk K ⟨a, hSK ha⟩) = orderOf a := by
  have hS' : IsPGroup 2 ↥(S.subgroupOf K) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hinj := ComponentClassification.OddKernel.image_injective_on_two (hatMk K)
    (odd_card_ker_hatMk K) (S.subgroupOf K) hS'
  have h1 := orderOf_injective ((hatMk K).domRestrict (S.subgroupOf K)) hinj
    ⟨⟨a, hSK ha⟩, ha⟩
  have h2 : orderOf (hatMk K ⟨a, hSK ha⟩) = orderOf (⟨⟨a, hSK ha⟩, ha⟩ : ↥(S.subgroupOf K)) := h1
  have h3 : orderOf (⟨⟨a, hSK ha⟩, ha⟩ : ↥(S.subgroupOf K)) = orderOf a :=
    (Subgroup.orderOf_mk (⟨a, hSK ha⟩ : ↥K) ha).trans (Subgroup.orderOf_mk a (hSK ha))
  rw [h2, h3]

def hatImg (K S : Subgroup G) : Subgroup (Hat K) := (S.subgroupOf K).map (hatMk K)

omit [Finite G] in
theorem mem_hatImg {K S : Subgroup G} {x : Hat K} :
    x ∈ hatImg K S ↔ ∃ a : ↥K, (a : G) ∈ S ∧ hatMk K a = x := by
  unfold hatImg
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

omit [Finite G] in
theorem hatMk_mem_hatImg {K S : Subgroup G} {a : G} (hSK : S ≤ K) (ha : a ∈ S) :
    hatMk K ⟨a, hSK ha⟩ ∈ hatImg K S :=
  mem_hatImg.mpr ⟨⟨a, hSK ha⟩, ha, rfl⟩

omit [Finite G] in
theorem isSylow2In_hatImg {K S : Subgroup G} (hS : IsSylow2In S K) :
    IsSylow2In (hatImg K S) (⊤ : Subgroup (Hat K)) := by
  obtain ⟨hSK, hSp, hSi⟩ := hS
  refine ⟨le_top, ?_, ?_⟩
  · have hS' : IsPGroup 2 ↥(S.subgroupOf K) :=
      hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    exact hS'.map (hatMk K)
  · rw [Subgroup.relIndex_top_right, hatImg, Subgroup.index_map]
    have hr : (hatMk K).range.index = 1 := by
      rw [MonoidHom.range_eq_top.mpr (hatMk_surjective K)]
      exact Subgroup.index_top
    rw [hr, mul_one]
    intro hd
    apply hSi
    exact hd.trans (Subgroup.index_dvd_of_le le_sup_left)

noncomputable abbrev phi (K : Subgroup G) (s : G) (hs : s ∈ normalizer (K : Set G)) :
    MulAut (Hat K) :=
  inducedQuotAut K (pPrimeCore 2 ↥K) ⟨s, hs⟩

omit [Finite G] in
theorem phi_mk (K : Subgroup G) {s : G} (hs : s ∈ normalizer (K : Set G)) (k : ↥K) :
    phi K s hs (hatMk K k) =
      hatMk K ⟨s * k * s⁻¹, (mem_normalizer_iff.mp hs k).mp k.2⟩ := by
  rfl

omit [Finite G] in
theorem phi_mul (K : Subgroup G) {s t : G} (hs : s ∈ normalizer (K : Set G))
    (ht : t ∈ normalizer (K : Set G)) :
    phi K (s * t) (mul_mem hs ht) = phi K s hs * phi K t ht := by
  ext x
  obtain ⟨k, rfl⟩ := hatMk_surjective K x
  rw [MulAut.mul_apply, phi_mk, phi_mk, phi_mk]
  congr 1
  apply Subtype.ext
  simp [mul_assoc]

omit [Finite G] in
theorem phi_mul_self (K : Subgroup G) {s : G} (hs : s ∈ normalizer (K : Set G)) (hss : s * s = 1) :
    phi K s hs * phi K s hs = 1 := by
  ext x
  obtain ⟨k, rfl⟩ := hatMk_surjective K x
  rw [MulAut.mul_apply, phi_mk, phi_mk]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have : s * (s * (k : G) * s⁻¹) * s⁻¹ = k := by
    calc s * (s * (k : G) * s⁻¹) * s⁻¹ = (s * s) * k * (s⁻¹ * s⁻¹) := by group
      _ = k := by rw [hss, hsinv, hss]; simp
  simp only [MulAut.one_apply]
  congr 1
  apply Subtype.ext
  exact this

omit [Finite G] in
theorem phi_of_mem (K : Subgroup G) {t : G} (ht : t ∈ K) :
    phi K t (le_normalizer ht) = MulAut.conj (hatMk K ⟨t, ht⟩) := by
  ext x
  obtain ⟨k, rfl⟩ := hatMk_surjective K x
  rw [phi_mk, MulAut.conj_apply]
  rw [← map_mul, ← map_inv, ← map_mul]
  rfl

omit [Finite G] in
theorem phi_mem_hatImg {K S : Subgroup G} {s : G} (hs : s ∈ normalizer (K : Set G))
    (hSs : ∀ a ∈ S, s * a * s⁻¹ ∈ S) {x : Hat K} (hx : x ∈ hatImg K S) :
    phi K s hs x ∈ hatImg K S := by
  obtain ⟨a, haS, rfl⟩ := mem_hatImg.mp hx
  rw [phi_mk]
  exact mem_hatImg.mpr ⟨_, hSs a haS, rfl⟩

omit [Finite G] in
theorem phi_congr (K : Subgroup G) {s t : G} (h : s = t) (hs : s ∈ normalizer (K : Set G))
    (ht : t ∈ normalizer (K : Set G)) : phi K s hs = phi K t ht := by
  subst h
  rfl

omit [Finite G] in
theorem hatMk_eq_one_iff (K : Subgroup G) (a : ↥K) :
    hatMk K a = 1 ↔ (a : G) ∈ pPrimeCoreOf 2 K :=
  TwoThin.hatMap_eq_one_iff (le_refl K) a

omit [Finite G] in
theorem phi_eq_one_iff (K : Subgroup G) {s : G} (hs : s ∈ normalizer (K : Set G)) :
    phi K s hs = 1 ↔ s ∈ cSec K := by
  constructor
  · intro h
    refine ⟨hs, TwoThin.mem_normalizer_pPrimeCoreOf hs, fun k hk => ?_⟩
    have hk1 : s * k⁻¹ * s⁻¹ ∈ K := (mem_normalizer_iff.mp hs k⁻¹).mp (inv_mem hk)
    have hcomm : ⁅k, s⁆ ∈ K := by
      have : ⁅k, s⁆ = k * (s * k⁻¹ * s⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact mul_mem hk hk1
    refine (hatMk_eq_one_iff K ⟨⁅k, s⁆, hcomm⟩).mp ?_
    have e : (⟨⁅k, s⁆, hcomm⟩ : ↥K) = ⟨k, hk⟩ * ⟨s * k⁻¹ * s⁻¹, hk1⟩ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    rw [e, map_mul]
    have h2 := phi_mk K hs ⟨k⁻¹, inv_mem hk⟩
    rw [h, MulAut.one_apply] at h2
    rw [← h2, ← map_mul]
    have : (⟨k, hk⟩ * ⟨k⁻¹, inv_mem hk⟩ : ↥K) = 1 := by
      apply Subtype.ext
      simp
    rw [this, map_one]
  · rintro ⟨-, -, hc⟩
    ext x
    obtain ⟨k, rfl⟩ := hatMk_surjective K x
    rw [phi_mk, MulAut.one_apply]
    have h1 := hc (k : G)⁻¹ (inv_mem k.2)
    have hmem : ⁅(k : G)⁻¹, s⁆ ∈ K := TwoThin.pPrimeCoreOf_le K h1
    have e : (⟨s * k * s⁻¹, (mem_normalizer_iff.mp hs k).mp k.2⟩ : ↥K) =
        k * ⟨⁅(k : G)⁻¹, s⁆, hmem⟩ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    rw [e, map_mul, (hatMk_eq_one_iff K ⟨_, hmem⟩).mpr h1, mul_one]

omit [Finite G] in
theorem phi_mem_inn_iff (K : Subgroup G) {s : G} (hs : s ∈ normalizer (K : Set G)) :
    phi K s hs ∈ innOf (Hat K) ↔ InducesInner s K := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨k₀, rfl⟩ := hatMk_surjective K q
    refine ⟨k₀, k₀.2, ?_⟩
    have hsk : s * (k₀ : G)⁻¹ ∈ normalizer (K : Set G) :=
      mul_mem hs (inv_mem (le_normalizer k₀.2))
    refine (phi_eq_one_iff K hsk).mp ?_
    rw [phi_mul K hs (inv_mem (le_normalizer k₀.2))]
    have h1 : phi K (k₀ : G)⁻¹ (inv_mem (le_normalizer k₀.2)) =
        MulAut.conj (hatMk K ⟨(k₀ : G)⁻¹, inv_mem k₀.2⟩) :=
      phi_of_mem K (inv_mem k₀.2)
    rw [h1, ← hq]
    have h2 : (hatMk K ⟨(k₀ : G)⁻¹, inv_mem k₀.2⟩) = (hatMk K k₀)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h2]
    show MulAut.conj (hatMk K k₀) * MulAut.conj (hatMk K k₀)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]
  · rintro ⟨k, hk, hc⟩
    have hsk : s * k⁻¹ ∈ normalizer (K : Set G) := hc.1
    have h1 : phi K (s * k⁻¹) hsk = 1 := (phi_eq_one_iff K hsk).mpr hc
    have h2 : phi K s hs = phi K (s * k⁻¹) hsk * phi K k (le_normalizer hk) := by
      rw [← phi_mul K hsk (le_normalizer hk)]
      exact phi_congr K (by group) hs _
    refine ⟨hatMk K ⟨k, hk⟩, ?_⟩
    rw [h2, h1, one_mul, phi_of_mem K hk]

end CFSG.GH74.GLS.Stage1.Thm2.Recip
