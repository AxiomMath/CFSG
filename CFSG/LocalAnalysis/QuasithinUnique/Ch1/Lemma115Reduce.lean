module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Datum
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionQuotient
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog
open scoped commutatorElement

section Transport

variable {G : Type*} [Group G]

theorem charTwo_subgroupOf {X L : Subgroup G} (hXL : X ≤ L) (h : CharTwo X) :
    CharTwo (X.subgroupOf L) := by
  rw [charTwo_iff_internal] at h ⊢
  exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
    (Subgroup.subgroupOfEquivOfLe hXL).symm h

theorem eq_commutator_of_central_aux {z a d : G} (hzz : z * z = 1)
    (hd : d = (a⁻¹ * (z⁻¹ * a * z))⁻¹) (hcen : a * d = d * a) : d = ⁅a, z⁆ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have h1 : a * d * a⁻¹ = d := by rw [hcen, mul_inv_cancel_right]
  have h2 : a * d * a⁻¹ = a * z * a⁻¹ * z⁻¹ := by
    rw [hd]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [hzinv]
    group
  rw [commutatorElement_def, ← h1, h2]

end Transport

section Local

variable {G : Type} [Group G] [Finite G]

theorem mem_oddCoreIn_of_central {L H : Subgroup G} (hLH : L ≤ H)
    (hsub : (L.subgroupOf H).IsSubnormal) {y : L} (hy : y ∈ Subgroup.center L)
    (hodd : Odd (orderOf y)) : (y : G) ∈ oddCoreIn H := by
  set K : Subgroup H := L.subgroupOf H with hK
  have hyH : (y : G) ∈ H := hLH y.2
  have hyK : (⟨y, hyH⟩ : H) ∈ K := y.2
  set yK : K := ⟨⟨y, hyH⟩, hyK⟩ with hyKdef
  have hcen : yK ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 := Subgroup.mem_center_iff.mp hy ⟨((k : H) : G), k.2⟩
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h1))
  have hordK : orderOf yK = orderOf y := by
    rw [← Subgroup.orderOf_coe yK]
    change orderOf (⟨y, hyH⟩ : H) = _
    rw [← Subgroup.orderOf_coe (⟨y, hyH⟩ : H)]
    exact (Subgroup.orderOf_coe y)
  have hle : Subgroup.zpowers yK ≤ CFSG.oddCore K := by
    apply le_sSup
    exact ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcen),
      by rw [Nat.card_zpowers, hordK]; exact hodd⟩
  have hmem : yK ∈ CFSG.oddCore K := hle (Subgroup.mem_zpowers yK)
  have hπ := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ 2} hsub
  rw [← CFSG.oddCore_eq_piCore, ← CFSG.oddCore_eq_piCore] at hπ
  have himg : (⟨y, hyH⟩ : H) ∈ (CFSG.oddCore K).map K.subtype := ⟨yK, hmem, rfl⟩
  rw [hπ] at himg
  exact ⟨⟨y, hyH⟩, himg.2, rfl⟩

theorem lemma115_exists_invDatum {H S M : Subgroup G} {z : G} (h : Lemma115Hyp H S M z)
    {L : Subgroup G} (hL : IsComponentIn L H) :
    ∃ α : ↥L ≃* ↥L, (∀ y : L, ((α y : L) : G) = z⁻¹ * (y : G) * z) ∧ InvDatum ↥L α := by
  obtain ⟨hn, hcomm, -, hchar⟩ := h.component_action hL
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.z_sq
  refine ⟨conjAutOfNormalizer L hn, fun y => rfl, ?_⟩
  have hα : ∀ y : L, ((conjAutOfNormalizer L hn y : L) : G) = z⁻¹ * (y : G) * z := fun y => rfl
  have hqs : CFSG.IsQuasisimple L :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hL.1)).1 hL.2.1
  refine ⟨hqs, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    rw [hα, hα]
    calc z⁻¹ * (z⁻¹ * (x : G) * z) * z = (z * z)⁻¹ * (x : G) * (z * z) := by group
      _ = x := by rw [hzz]; simp
  ·
    by_contra hcon
    push Not at hcon
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hle : ⁅L, Subgroup.zpowers z⁆ ≤ (Subgroup.center L).map L.subtype := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · have : z ^ (2 * m) = 1 := by
          rw [zpow_mul, zpow_two, hzz, one_zpow]
        rw [this]
        simp [commutatorElement_def]
      · have hz1 : z ^ (2 * m + 1) = z := by
          rw [zpow_add_one, zpow_mul, zpow_two, hzz, one_zpow, one_mul]
        rw [hz1]
        set x : L := ⟨g₁, hg₁⟩ with hx
        have hc := hcon x
        refine ⟨(x⁻¹ * conjAutOfNormalizer L hn x)⁻¹, Subgroup.inv_mem _ hc, ?_⟩
        have hcen := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) x
        exact eq_commutator_of_central_aux hzz rfl (congrArg Subtype.val hcen)
    rw [hcomm] at hle
    have hall : ∀ x : L, x ∈ Subgroup.center L := by
      intro x
      obtain ⟨c, hc, hcx⟩ := hle x.2
      have : c = x := Subtype.ext hcx
      rwa [this] at hc
    obtain ⟨a, b, hab⟩ := hqs.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hall x) y).symm
  · obtain ⟨P, hP⟩ := exists_sylow_inf_of_subnormal h.sylow hL.1 hL.2.2
    refine ⟨P, fun t ht => ?_⟩
    have htS : (t : G) ∈ S := by
      have : (t : G) ∈ (P : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem _ ht
      rw [hP] at this
      exact this.1
    have h1 : (t : G) * z = z * t := Subgroup.mem_centralizer_iff.mp h.z_central (t : G) htS
    apply Subtype.ext
    rw [hα]
    calc z⁻¹ * (t : G) * z = z⁻¹ * (z * t) := by rw [mul_assoc, h1]
      _ = t := by group
  · intro y hy hodd
    have hmem := mem_oddCoreIn_of_central hL.1 hL.2.2 hy hodd
    apply Subtype.ext
    rw [hα]
    exact h.inverts_oddCoreIn _ hmem
  · have hfix : fixedSubgroup (conjAutOfNormalizer L hn) =
        (L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf L := by
      ext x
      rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        have h1 : z⁻¹ * (x : G) * z = x := by
          have := congrArg Subtype.val hx
          rwa [hα] at this
        refine ⟨x.2, ?_⟩
        calc (x : G) * z = z * (z⁻¹ * x * z) := by group
          _ = z * x := by rw [h1]
      · rintro ⟨-, hx⟩
        apply Subtype.ext
        rw [hα]
        calc z⁻¹ * (x : G) * z = z⁻¹ * (z * x) := by rw [mul_assoc, hx]
          _ = x := by group
    rw [hfix]
    exact charTwo_subgroupOf inf_le_left hchar

end Local

end CFSG.QuasithinUnique.Ch1
