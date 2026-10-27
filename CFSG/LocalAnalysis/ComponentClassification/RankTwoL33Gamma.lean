module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Gen
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.ComponentClassification.RankTwoL33

open Subgroup CFSG.GH74 CFSG.GH74.E2 CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding

variable {H : Type} [Group H]

theorem normalizerMonoidHom_apply_coe {B : Subgroup H} (g : normalizer (B : Set H)) (b : B) :
    ((B.normalizerMonoidHom g b : B) : H) = (g : H) * b * (g : H)⁻¹ := rfl

theorem le_sup_inf_centralizer {B : Subgroup H} (hB : ShapeL33 ↥B) {u v : H}
    (hu : u ∈ normalizer (B : Set H)) (hv : v ∈ normalizer (B : Set H)) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (huv : u * v = v * u) (hu' : u ∉ centralizer (B : Set H))
    (hv' : v ∉ centralizer (B : Set H)) (huv' : u * v ∉ centralizer (B : Set H)) :
    B ≤ (B ⊓ centralizer ({u} : Set H)) ⊔ (B ⊓ centralizer ({v} : Set H)) ⊔
      (B ⊓ centralizer ({u * v} : Set H)) := by
  set f := B.normalizerMonoidHom
  set U : normalizer (B : Set H) := ⟨u, hu⟩
  set V : normalizer (B : Set H) := ⟨v, hv⟩
  have hker : ∀ g : normalizer (B : Set H), f g = 1 → (g : H) ∈ centralizer (B : Set H) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro b hb
    have h := congrArg (fun φ : MulAut B => ((φ ⟨b, hb⟩ : B) : H)) hg
    simp only [MulAut.one_apply] at h
    rw [normalizerMonoidHom_apply_coe] at h
    calc b * (g : H) = (g : H) * b * (g : H)⁻¹ * (g : H) := by rw [h]
      _ = (g : H) * b := by group
  have hU2 : f U ^ 2 = 1 := by
    rw [← map_pow]
    have : U ^ 2 = 1 := Subtype.ext (by simpa using hu2)
    rw [this, map_one]
  have hV2 : f V ^ 2 = 1 := by
    rw [← map_pow]
    have : V ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [this, map_one]
  have hU1 : f U ≠ 1 := fun h => hu' (hker U h)
  have hV1 : f V ≠ 1 := fun h => hv' (hker V h)
  have hUV : f U ≠ f V := by
    intro h
    apply huv'
    have h1 : f (U * V) = 1 := by
      rw [map_mul, h, ← sq, hV2]
    exact hker (U * V) h1
  have hcomm : f U * f V = f V * f U := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext huv
  have htop := sup_fixSubgroup_eq_top hB hU2 hV2 hU1 hV1 hUV hcomm
  have hfix : ∀ (g : normalizer (B : Set H)),
      (fixSubgroup (f g)).map B.subtype ≤ B ⊓ centralizer ({(g : H)} : Set H) := by
    rintro g _ ⟨b, hb, rfl⟩
    refine ⟨b.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h := congrArg (fun x : B => (x : H)) (mem_fixSubgroup.1 hb)
    rw [normalizerMonoidHom_apply_coe] at h
    calc (b : H) * (g : H) = (g : H) * b * (g : H)⁻¹ * (g : H) := by rw [h]
      _ = (g : H) * b := by group
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ fixSubgroup (f U) ⊔ fixSubgroup (f V) ⊔ fixSubgroup (f U * f V) := by
    rw [htop]
    exact mem_top _
  have hmap := mem_map_of_mem B.subtype hx'
  rw [Subgroup.map_sup, Subgroup.map_sup, ← map_mul] at hmap
  exact sup_le_sup (sup_le_sup (hfix U) (hfix V)) (hfix (U * V)) hmap

theorem exists_two_ne_one {T : Subgroup H} (hT : 4 ≤ Nat.card T) :
    ∃ u ∈ T, ∃ v ∈ T, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype T := Fintype.ofFinite T
  have h3 : 2 < (Finset.univ.erase (1 : T)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.1 (by omega : 1 < (Finset.univ.erase (1 : T)).card)
  rw [Finset.mem_erase] at ha hb
  refine ⟨a, a.2, b, b.2, fun h => ha.1 (Subtype.ext h), fun h => hb.1 (Subtype.ext h),
    fun h => hab (Subtype.ext h)⟩

theorem commute_of_elemAbelian {T : Subgroup H} (hT : IsElemAbelian 2 T) {u v : H} (hu : u ∈ T)
    (hv : v ∈ T) : u * v = v * u := CFSG.Open.IsElemAbelian.comm hT hu hv

theorem shapeL33_simple {B : Type} [Group B] (hB : ShapeL33 B) :
    IsSimpleGroup B ∧ Nat.card B = 5616 := by
  refine ⟨(ShapeL33.facts hB).1, ?_⟩
  obtain ⟨e⟩ := KGroups.L33.equiv_of_lieModel hB
  rw [KGroups.L33.card_K e]
  norm_num

theorem not_le_of_isTwoNilpotent {B X : Subgroup H} (hB : ShapeL33 ↥B)
    (hX : AS76b.IsTwoNilpotent X) (hBX : B ≤ X) : False := by
  obtain ⟨hsimple, hcard⟩ := shapeL33_simple hB
  obtain ⟨N, hNX, hNn, hNodd, k, hk⟩ := hX
  let φ : B →* X ⧸ N.subgroupOf X := (QuotientGroup.mk' (N.subgroupOf X)).comp (inclusion hBX)
  rcases (inferInstance : φ.ker.Normal).eq_bot_or_eq_top with h | h
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have hdvd := Subgroup.card_dvd_of_injective φ hinj
    have hq : Nat.card (X ⧸ N.subgroupOf X) = 2 ^ k := by
      rw [← hk, Subgroup.relIndex]
      rfl
    rw [hcard, hq] at hdvd
    have h3 : 3 ∣ 2 ^ k := dvd_trans (by norm_num) hdvd
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
    omega
  · have hBN : B ≤ N := by
      intro b hb
      have hm : (⟨b, hb⟩ : B) ∈ φ.ker := h ▸ mem_top _
      rw [MonoidHom.mem_ker] at hm
      have := (QuotientGroup.eq_one_iff _).1 hm
      exact (mem_subgroupOf.1 this)
    have hdvd := card_dvd_of_le hBN
    rw [hcard] at hdvd
    obtain ⟨j, hj⟩ := hNodd
    omega

theorem l33_hypII (A : Type) [Group A] (hA : ShapeL33 A) : AS76b.HypII A := by
  intro H _ _ B T ⟨eB⟩ hNF hST
  exfalso
  have hB : ShapeL33 ↥B := lieModel_of_mulEquiv eB.symm hA
  obtain ⟨hsimple, hcard⟩ := shapeL33_simple hB
  obtain ⟨hTel, hT4, hTN, hTC⟩ := hNF
  obtain ⟨X, hXle, hTX, hX2, hXt⟩ := hST
  have hTX' : T ≤ X := by
    obtain ⟨Q, hQ⟩ := hTX
    rw [← hQ]
    exact map_subtype_le _
  have hfaith : ∀ t ∈ T, t ≠ 1 → t ∉ centralizer (B : Set H) := fun t ht h1 hC => h1 (by
    have : t ∈ T ⊓ centralizer (B : Set H) := ⟨ht, hC⟩
    rwa [hTC, mem_bot] at this)
  obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := exists_two_ne_one hT4
  have huv1 : u * v ≠ 1 := fun h => huv (by
    have h' := eq_inv_of_mul_eq_one_left h
    rw [h', inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hTel.2 v hv)])
  have hYB : B ≤ T ⊔ B := le_sup_right
  have hYT : T ≤ T ⊔ B := le_sup_left
  have hCN : ∀ t ∈ T, t ≠ 1 → B ⊓ centralizer ({t} : Set H) ≤ normalizer (X : Set H) := by
    intro t ht ht1 y hy
    have hyY : y ∈ T ⊔ B := hYB hy.1
    have htY : t ∈ T ⊔ B := hYT ht
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 hy.2
    have hnorm : (⟨y, hyY⟩ : ↥(T ⊔ B)) ∈
        normalizer ((X.subgroupOf (T ⊔ B) : Subgroup ↥(T ⊔ B)) : Set ↥(T ⊔ B)) := by
      by_contra hn
      have hodd := hXt.2 _ hn
      have htmem : (⟨t, htY⟩ : ↥(T ⊔ B)) ∈ X.subgroupOf (T ⊔ B) ⊓
          rightConjugate (X.subgroupOf (T ⊔ B)) ⟨y, hyY⟩ := by
        refine Subgroup.mem_inf.2 ⟨mem_subgroupOf.2 (hTX' ht), ?_⟩
        rw [mem_rightConjugate_iff, mem_subgroupOf]
        simp only [coe_mul, coe_inv]
        rw [hyt, mul_inv_cancel_right]
        exact hTX' ht
      have hord : orderOf (⟨⟨t, htY⟩, htmem⟩ : ↥(X.subgroupOf (T ⊔ B) ⊓
          rightConjugate (X.subgroupOf (T ⊔ B)) ⟨y, hyY⟩)) = 2 := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
        exact orderOf_eq_prime (hTel.2 t ht) ht1
      have h2 := orderOf_dvd_natCard (⟨⟨t, htY⟩, htmem⟩ : ↥(X.subgroupOf (T ⊔ B) ⊓
          rightConjugate (X.subgroupOf (T ⊔ B)) ⟨y, hyY⟩))
      rw [hord] at h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxY : x ∈ T ⊔ B := hXle hx
      have := (mem_normalizer_iff.1 hnorm ⟨x, hxY⟩).1 (mem_subgroupOf.2 hx)
      simpa [mem_subgroupOf] using this
    · intro hx
      have hxY : x ∈ T ⊔ B := by
        have h1 : y * x * y⁻¹ ∈ T ⊔ B := hXle hx
        have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem hyY) h1) hyY
      have := (mem_normalizer_iff.1 hnorm ⟨x, hxY⟩).2 (by
        rw [mem_subgroupOf]
        simpa using hx)
      exact mem_subgroupOf.1 this
  have hgen := le_sup_inf_centralizer hB (hTN hu) (hTN hv) (hTel.2 u hu) (hTel.2 v hv)
    (commute_of_elemAbelian hTel hu hv) (hfaith u hu hu1) (hfaith v hv hv1)
    (hfaith (u * v) (mul_mem hu hv) huv1)
  have hBN : B ≤ normalizer (X : Set H) := hgen.trans (sup_le (sup_le (hCN u hu hu1)
    (hCN v hv hv1)) (hCN (u * v) (mul_mem hu hv) huv1))
  have hnormal : ((X ⊓ B).subgroupOf B).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    exact ⟨(mem_normalizer_iff.1 (hBN g.2) n).1 hn.1, mul_mem (mul_mem g.2 hn.2) (inv_mem g.2)⟩⟩
  rcases hnormal.eq_bot_or_eq_top with h | h
  ·
    apply hfaith u hu hu1
    rw [mem_centralizer_iff]
    intro b hb
    have hc : b * u * b⁻¹ * u⁻¹ ∈ X ⊓ B := by
      refine Subgroup.mem_inf.2
        ⟨mul_mem ((mem_normalizer_iff.1 (hBN hb) u).1 (hTX' hu)) (inv_mem (hTX' hu)), ?_⟩
      have : b * u * b⁻¹ * u⁻¹ = b * (u * b⁻¹ * u⁻¹) := by group
      rw [this]
      exact mul_mem hb ((mem_normalizer_iff.1 (hTN hu) b⁻¹).1 (inv_mem hb))
    have hc' : (⟨_, (Subgroup.mem_inf.1 hc).2⟩ : B) ∈ (X ⊓ B).subgroupOf B :=
      mem_subgroupOf.2 hc
    rw [h, mem_bot] at hc'
    have h1 : b * u * b⁻¹ * u⁻¹ = 1 := congrArg Subtype.val hc'
    calc b * u = b * u * b⁻¹ * u⁻¹ * (u * b) := by group
      _ = u * b := by rw [h1, one_mul]
  ·
    have hBX : B ≤ X := fun b hb => by
      have : (⟨b, hb⟩ : B) ∈ (X ⊓ B).subgroupOf B := h ▸ mem_top _
      exact (Subgroup.mem_inf.1 (mem_subgroupOf.1 this)).1
    exact not_le_of_isTwoNilpotent hB hX2 hBX

end CFSG.ComponentClassification.RankTwoL33
