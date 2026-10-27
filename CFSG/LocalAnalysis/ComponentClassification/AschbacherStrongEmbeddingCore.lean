module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingProducts
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {X : Type*} [Group X] {H : Subgroup X} {z : X}

theorem oddCore_map_normal (N : Subgroup X) [N.Normal] :
    ((CFSG.oddCore N).map N.subtype).Normal := by
  have : (CFSG.oddCore N).Characteristic :=
    Subgroup.characteristic_iff_map_eq.mpr fun ϕ =>
      CFSG.ComponentClassification.OddCore.char_invariant ϕ
  exact ConjAct.normal_of_characteristic_of_normal

theorem oddCore_eq_bot_of_normal [Finite X] (hO : CFSG.oddCore X = ⊥) (N : Subgroup X)
    [N.Normal] : CFSG.oddCore N = ⊥ := by
  have : ((CFSG.oddCore N).map N.subtype).Normal := oddCore_map_normal N
  have hodd : Odd (Nat.card ((CFSG.oddCore N).map N.subtype)) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card N
  have hle : (CFSG.oddCore N).map N.subtype ≤ CFSG.oddCore X := le_sSup ⟨inferInstance, hodd⟩
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
  exact hle

theorem normalCore_smul_eq {n : X} (hn : n ∈ H.normalCore) (ω : X ⧸ H) : n • ω = ω := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [smul_mk_eq_mk_iff]
  have h : g⁻¹ * n * g⁻¹⁻¹ ∈ H := hn g⁻¹
  simpa only [inv_inv] using h

theorem not_mem_normalCore (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H) (hH : H ≠ ⊤) :
    z ∉ H.normalCore := by
  intro hz
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ H := by
    by_contra h
    exact hH (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
  have hfix := normalCore_smul_eq hz (QuotientGroup.mk g : X ⧸ H)
  rw [smul_eq_iff_eq_base huniq, mk_eq_base_iff] at hfix
  exact hg hfix

theorem commute_of_mem_normalCore {X : Type} [Group X] [Finite X] {H : Subgroup X} {z : X}
    (hz : orderOf z = 2) (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) (hH : H ≠ ⊤) (hO : CFSG.oddCore X = ⊥)
    {n : X} (hn : n ∈ H.normalCore) : Commute z n := by
  classical
  let N := H.normalCore
  let Y : Subgroup X := N ⊔ Subgroup.zpowers z
  have hzY : z ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hnY : n ∈ Y := Subgroup.mem_sup_left hn
  have hzH := mem_of_unique huniq
  have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
  have hzN := not_mem_normalCore huniq hH
  have hzpow : ∀ b ∈ Subgroup.zpowers z, b = 1 ∨ b = z := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, ← pow_two, ← hz, pow_orderOf_eq_one, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hzz, one_zpow, one_mul]
  have hYdecomp : ∀ g ∈ Y, ∃ a ∈ N, g = a ∨ g = a * z := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := N)
      (t := Subgroup.zpowers z)).mp hg
    rcases hzpow b hb with rfl | rfl
    · exact ⟨a, ha, Or.inl (mul_one a)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  have hcommN : ∀ g ∈ Y, z * (g * z * g⁻¹) ∈ N := by
    intro g hg
    obtain ⟨a, ha, hga | hga⟩ := hYdecomp g hg
    · rw [hga]
      have h := (inferInstance : N.Normal).conj_mem a ha z
      have h' := N.mul_mem h (N.inv_mem ha)
      simpa only [mul_assoc, hzinv] using h'
    · rw [hga]
      have h := (inferInstance : N.Normal).conj_mem a ha z
      have h' := N.mul_mem h (N.inv_mem ha)
      have heq : z * (a * z * z * (a * z)⁻¹) = z * a * z⁻¹ * a⁻¹ := by
        rw [mul_assoc a z z, hzz, mul_one, mul_inv_rev, hzinv]
        group
      rw [heq]
      exact h'
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : X ⧸ H, ω₀ ≠ QuotientGroup.mk 1 := by
    obtain ⟨g, hg⟩ : ∃ g : X, g ∉ H := by
      by_contra h
      exact hH (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
    exact ⟨QuotientGroup.mk g, fun h => hg ((mk_eq_base_iff g).mp h)⟩
  have hYH : Y ≤ H := sup_le (Subgroup.normalCore_le H) (Subgroup.zpowers_le.mpr hzH)
  let zY : Y := ⟨z, hzY⟩
  have hzY1 : zY ≠ 1 := by
    intro h
    have h' : z = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hz
    exact absurd hz (by decide)
  have hzYsq : zY * zY = 1 := Subtype.ext hzz
  have hiso : ∀ g : Y, (g * zY * g⁻¹) * zY = zY * (g * zY * g⁻¹) → g * zY * g⁻¹ = zY := by
    intro g hcomm
    by_contra hne
    have hcls : (g : X) * z * (g : X)⁻¹ ∈ involutionPointClass z := by
      simpa only [inv_inv] using class_conj_mem (distinguished_mem_pointClass z) (g : X)⁻¹
    have hcommX : Commute z ((g : X) * z * (g : X)⁻¹) := (congrArg Subtype.val hcomm).symm
    have hneX : (g : X) * z * (g : X)⁻¹ ≠ z := fun h => hne (Subtype.ext h)
    have hprod := product_smul_eq_iff huniq h1 (distinguished_mem_pointClass z) hcls hcommX
      hneX ω₀
    have hfix := normalCore_smul_eq (hcommN g g.property) ω₀
    exact hω₀ ((smul_eq_iff_eq_base huniq ω₀).mp (hprod.mp hfix))
  let : Fintype Y := Fintype.ofFinite Y
  obtain ⟨K, hKnormal, hKodd, hK⟩ := CFSG.Milestones.glauberman_zStar Y zY hzY1 hzYsq hiso
  have hKN : ∀ k ∈ K, (k : X) ∈ N := by
    intro k hk
    obtain ⟨a, ha, hka | hka⟩ := hYdecomp k k.property
    · exact hka ▸ ha
    · exfalso
      have hord : Odd (orderOf k) := hKodd.of_dvd_nat (by
        rw [← Subgroup.orderOf_mk k hk]
        exact orderOf_dvd_natCard _)
      obtain ⟨r, hr⟩ := hord
      have hsq : ((k : X) * (k : X)) ∈ N := by
        rw [hka]
        have h := (inferInstance : N.Normal).conj_mem a ha z
        have h' := N.mul_mem ha h
        simpa only [mul_assoc, hzinv] using h'
      have hpow : (k : X) ^ (2 * r) ∈ N := by
        rw [pow_mul, pow_two]
        exact N.pow_mem hsq r
      have hone : (k : X) ^ (2 * r + 1) = 1 := by
        rw [← hr, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      have hk' : (k : X) ∈ N := by
        have h := N.mul_mem (N.inv_mem hpow) (show (k : X) ^ (2 * r + 1) ∈ N from
          hone ▸ N.one_mem)
        rwa [pow_succ, ← mul_assoc, inv_mul_cancel, one_mul] at h
      apply hzN
      have h := N.mul_mem (N.inv_mem ha) hk'
      rwa [hka, ← mul_assoc, inv_mul_cancel, one_mul] at h
  let KX : Subgroup X := K.map Y.subtype
  have hKXN : KX ≤ N := by
    rintro x ⟨k, hk, rfl⟩
    exact hKN k hk
  let KN : Subgroup N := KX.subgroupOf N
  have hKNnormal : KN.Normal := by
    constructor
    intro a ha b
    change ((b : X) * (a : X) * (b : X)⁻¹) ∈ KX
    obtain ⟨k, hk, hka⟩ := ha
    have hbY : (b : X) ∈ Y := Subgroup.mem_sup_left b.property
    refine ⟨⟨b, hbY⟩ * k * ⟨b, hbY⟩⁻¹, hKnormal.conj_mem k hk _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (k : X) = (a : X) from hka]
  have hKNodd : Odd (Nat.card KN) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKXN).toEquiv,
      Subgroup.card_map_of_injective Y.subtype_injective]
    exact hKodd
  have hKNbot : KN = ⊥ := by
    have hle : KN ≤ CFSG.oddCore N := le_sSup ⟨hKNnormal, hKNodd⟩
    rw [oddCore_eq_bot_of_normal hO N, le_bot_iff] at hle
    exact hle
  have hmem := hK ⟨n, hnY⟩
  have hmemN : ((⟨n, hnY⟩ * zY * ⟨n, hnY⟩⁻¹ * zY⁻¹ : Y) : X) ∈ KX := ⟨_, hmem, rfl⟩
  have hmemKN : (⟨_, hKXN hmemN⟩ : N) ∈ KN := hmemN
  rw [hKNbot, Subgroup.mem_bot] at hmemKN
  have h1' := congrArg Subtype.val hmemKN
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h1'
  change n * z * n⁻¹ * z⁻¹ = 1 at h1'
  have h2 : n * z * n⁻¹ = z := by
    have := congrArg (· * z) h1'
    simpa only [inv_mul_cancel_right, one_mul] using this
  change z * n = n * z
  calc z * n = n * z * n⁻¹ * n := by rw [h2]
    _ = n * z := by group

theorem mem_normalCore_of_smul_eq {n : X} (hn : ∀ ω : X ⧸ H, n • ω = ω) :
    n ∈ H.normalCore := by
  intro b
  have h := (smul_mk_eq_mk_iff (H := H) n b⁻¹).mp (hn _)
  simpa only [inv_inv] using h

theorem normalCore_le_center {X : Type} [Group X] [Finite X] {H : Subgroup X} {z : X}
    (hz : orderOf z = 2) (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) (hH : H ≠ ⊤) (hO : CFSG.oddCore X = ⊥)
    (hhull : involutionPointHull z = ⊤) : H.normalCore ≤ Subgroup.center X := by
  intro n hn
  have hcls : ∀ t ∈ involutionPointClass z, Commute t n := by
    rintro t ⟨g, rfl⟩
    have hn' : g * n * g⁻¹ ∈ H.normalCore :=
      (inferInstance : H.normalCore.Normal).conj_mem n hn g
    have hc := (commute_of_mem_normalCore hz huniq h1 hH hO hn').map
      (MulAut.conj g⁻¹).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hc
    change Commute (g⁻¹ * z * g) n
    convert hc using 1
    group
  have hle : involutionPointHull z ≤ Subgroup.centralizer ({n} : Set X) :=
    (Subgroup.closure_le _).mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcls t ht).eq
  rw [hhull] at hle
  exact Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))

end CFSG.ComponentClassification.AschbacherStrongEmbedding
