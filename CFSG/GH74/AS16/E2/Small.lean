module

public import CFSG.GH74.AS16.E2.Bender

public section

namespace CFSG.GH74.AS16.E2

open Subgroup
open scoped commutatorElement

structure SmallTable {G : Type*} [Group G] (L TL : Subgroup G) : Prop where
  conj_central : ∀ x ∈ TL, x ^ 2 = 1 → ∃ k ∈ L, k⁻¹ * x * k ∈ TL ∧
    ∀ y ∈ TL, y * (k⁻¹ * x * k) = (k⁻¹ * x * k) * y
  center_le_comm : ∀ a ∈ TL, (∀ y ∈ TL, y * a = a * y) → a ^ 2 = 1 → a ∈ ⁅TL, TL⁆
  center_small : ∃ s : G, ∀ a ∈ TL, (∀ y ∈ TL, y * a = a * y) → a ^ 2 = 1 → a = 1 ∨ a = s

theorem conj_fixed_of_small {G : Type*} [Group G] [Finite G] {S L : Subgroup G} {z : G}
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hzS : z ∈ S)
    (hzc : ∀ t ∈ S, t * z = z * t)
    (hLz : ∀ l ∈ L, l * z = z * l)
    (hdec : ∀ t ∈ S, ∃ s ∈ S ⊓ L, ∃ c ∈ S ⊓ centralizer (L : Set G), t = s * c)
    (hmeet : ∀ g ∈ L, g ∈ centralizer (L : Set G) → g = 1)
    (hTCcomm : ∀ c ∈ S ⊓ centralizer (L : Set G), ∀ c' ∈ S ⊓ centralizer (L : Set G),
      c * c' = c' * c)
    (hTCinv : ∀ c ∈ S ⊓ centralizer (L : Set G), c ^ 2 = 1 → c = 1 ∨ c = z)
    (hB : SmallTable L (S ⊓ L))
    (hodd : Odd ((centralizer ({z} : Set G)).subgroupOf (normalizer (S : Set G))).index) :
    ∀ n ∈ normalizer (S : Set G), n⁻¹ * z * n = z := by
  classical
  set TL : Subgroup G := S ⊓ L with hTL
  set TC : Subgroup G := S ⊓ centralizer (L : Set G) with hTC
  have hLC : ∀ l ∈ L, ∀ c ∈ TC, l * c = c * l := fun l hl c hc =>
    Subgroup.mem_centralizer_iff.1 hc.2 l hl
  have hz_TC : z ∈ TC := ⟨hzS, Subgroup.mem_centralizer_iff.2 fun l hl => hLz l hl⟩
  have claimI : ∀ u ∈ S, u ^ 2 = 1 → (∀ t ∈ S, t * u = u * t) →
      ∃ a ∈ TL, (∀ y ∈ TL, y * a = a * y) ∧ a ^ 2 = 1 ∧ ∃ c ∈ TC, u = a * c ∧ (c = 1 ∨ c = z) := by
    intro u hu hu2 huc
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec u hu
    have hcomm : Commute s c := hLC s hs.2 c hc
    have h1 : s ^ 2 * c ^ 2 = 1 := by rw [← hcomm.mul_pow]; exact hu2
    have hs2 : s ^ 2 = 1 := by
      have e1 : s ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h2L : s ^ 2 ∈ L := L.pow_mem hs.2 2
      have h2C : s ^ 2 ∈ centralizer (L : Set G) := by
        rw [e1]
        exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hc.2 2)
      exact hmeet _ h2L h2C
    have hc2 : c ^ 2 = 1 := by rw [hs2, one_mul] at h1; exact h1
    refine ⟨s, hs, fun y hy => ?_, hs2, c, hc, rfl, hTCinv c hc hc2⟩
    have h3 := huc y hy.1
    have h4 : y * c = c * y := hLC y hy.2 c hc
    calc y * s = (y * (s * c)) * c⁻¹ := by group
      _ = (s * c * y) * c⁻¹ := by rw [h3]
      _ = s * (c * y) * c⁻¹ := by group
      _ = s * (y * c) * c⁻¹ := by rw [h4]
      _ = s * y := by group
  have hcommS : ∀ t ∈ S, ∀ t' ∈ S, ⁅t, t'⁆ ∈ TL := by
    intro t ht t' ht'
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec t ht
    obtain ⟨s', hs', c', hc', rfl⟩ := hdec t' ht'
    have hcs' : c * s' = s' * c := (hLC s' hs'.2 c hc).symm
    have hc's : c' * s = s * c' := (hLC s hs.2 c' hc').symm
    have hcc' : c * c' = c' * c := hTCcomm c hc c' hc'
    have hc_comm : c * (s' * c') = (s' * c') * c := by
      rw [← mul_assoc, hcs', mul_assoc, hcc', mul_assoc]
    have hc's_inv : c' * s⁻¹ * c'⁻¹ = s⁻¹ := by
      calc c' * s⁻¹ * c'⁻¹ = (c' * s * c'⁻¹)⁻¹ := by group
        _ = s⁻¹ := by rw [show c' * s * c'⁻¹ = s by rw [hc's]; group]
    have e : ⁅s * c, s' * c'⁆ = ⁅s, s'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc s * c * (s' * c') * (s * c)⁻¹ * (s' * c')⁻¹
          = s * (c * (s' * c')) * c⁻¹ * s⁻¹ * (s' * c')⁻¹ := by group
        _ = s * ((s' * c') * c) * c⁻¹ * s⁻¹ * (s' * c')⁻¹ := by rw [hc_comm]
        _ = s * (s' * c') * s⁻¹ * (s' * c')⁻¹ := by group
        _ = s * s' * (c' * s⁻¹ * c'⁻¹) * s'⁻¹ := by group
        _ = s * s' * s⁻¹ * s'⁻¹ := by rw [hc's_inv]
    rw [e, commutatorElement_def]
    exact TL.mul_mem (TL.mul_mem (TL.mul_mem hs hs') (TL.inv_mem hs)) (TL.inv_mem hs')
  have hSS : ⁅S, S⁆ ≤ TL := Subgroup.commutator_le.2 hcommS
  have hz_nc : z ∉ ⁅S, S⁆ := by
    intro h
    exact hz1 (hmeet z (hSS h).2 hz_TC.2)
  have hnormSS : ∀ m ∈ normalizer (S : Set G), ∀ x ∈ ⁅S, S⁆, m * x * m⁻¹ ∈ ⁅S, S⁆ := by
    intro m hm x hx
    have hle : ⁅S, S⁆ ≤ (⁅S, S⁆).comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro g1 hg1 g2 hg2
      show m * ⁅g1, g2⁆ * m⁻¹ ∈ ⁅S, S⁆
      have e : m * ⁅g1, g2⁆ * m⁻¹ = ⁅m * g1 * m⁻¹, m * g2 * m⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hm g1).1 hg1)
        ((Subgroup.mem_normalizer_iff.1 hm g2).1 hg2)
    exact hle hx
  obtain ⟨s₀, hs₀⟩ := hB.center_small
  have hconj : ∀ m ∈ normalizer (S : Set G), m⁻¹ * z * m = z ∨ m⁻¹ * z * m = s₀ * z := by
    intro m hm
    have hm' : m⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hm
    have hwS : m⁻¹ * z * m ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hm' z).1 hzS
      simpa using this
    have hw2 : (m⁻¹ * z * m) ^ 2 = 1 := by
      calc (m⁻¹ * z * m) ^ 2 = m⁻¹ * z ^ 2 * m := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hz2]; group
    have hwc : ∀ t ∈ S, t * (m⁻¹ * z * m) = (m⁻¹ * z * m) * t := by
      intro t ht
      have htm : m * t * m⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hm t).1 ht
      have h1 := hzc _ htm
      calc t * (m⁻¹ * z * m) = m⁻¹ * ((m * t * m⁻¹) * z) * m := by group
        _ = m⁻¹ * (z * (m * t * m⁻¹)) * m := by rw [h1]
        _ = (m⁻¹ * z * m) * t := by group
    obtain ⟨a, haL, hac, ha2, c, hc, hwe, hc1 | hcz⟩ := claimI _ hwS hw2 hwc
    · exfalso
      rw [hc1, mul_one] at hwe
      have hw : m⁻¹ * z * m ∈ ⁅S, S⁆ := hwe ▸ Subgroup.commutator_mono (inf_le_left : TL ≤ S)
        (inf_le_left : TL ≤ S) (hB.center_le_comm a haL hac ha2)
      apply hz_nc
      have := hnormSS m hm _ hw
      simpa [mul_assoc] using this
    · rw [hwe, hcz]
      rcases hs₀ a haL hac ha2 with h | h
      · left; rw [h, one_mul]
      · right; rw [h]
  intro n hn
  by_contra hne
  have hnz : n⁻¹ * z * n = s₀ * z := (hconj n hn).resolve_left hne
  set N : Subgroup G := normalizer (S : Set G) with hN
  have hOrb : {w : G | ∃ m ∈ N, w = m⁻¹ * z * m} = {z, s₀ * z} := by
    ext w
    constructor
    · rintro ⟨m, hm, rfl⟩
      rcases hconj m hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨1, N.one_mem, by simp⟩
      · exact ⟨n, hn, hnz.symm⟩
  have hne2 : z ≠ s₀ * z := fun h => hne (by rw [hnz, ← h])
  have hcard : ({z, s₀ * z} : Set G).ncard = 2 := Set.ncard_pair hne2
  have h2 := ncard_conjOrbit_eq_index N z
  rw [hOrb, hcard] at h2
  obtain ⟨k, hk⟩ := hodd
  omega

theorem SmallTable.of_subtype {G : Type*} [Group G] (L : Subgroup G) (Q : Subgroup ↥L)
    (h : SmallTable (⊤ : Subgroup ↥L) Q) : SmallTable L (Q.map L.subtype) := by
  have hinj : Function.Injective L.subtype := L.subtype_injective
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩ hq2
    have hq2' : q ^ 2 = 1 := hinj (by simpa using hq2)
    obtain ⟨k, -, hkQ, hkc⟩ := h.conj_central q hq hq2'
    refine ⟨L.subtype k, k.2, ⟨k⁻¹ * q * k, hkQ, by simp⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hkc y hy
    simpa using congrArg L.subtype this
  · rintro _ ⟨q, hq, rfl⟩ hcen hq2
    have hq2' : q ^ 2 = 1 := hinj (by simpa using hq2)
    have hcenq : ∀ y ∈ Q, y * q = q * y := fun y hy =>
      hinj (by simpa using hcen (L.subtype y) ⟨y, hy, rfl⟩)
    have := h.center_le_comm q hq hcenq hq2'
    rw [← Subgroup.map_commutator]
    exact ⟨q, this, rfl⟩
  · obtain ⟨s, hs⟩ := h.center_small
    refine ⟨L.subtype s, ?_⟩
    rintro _ ⟨q, hq, rfl⟩ hcen hq2
    have hq2' : q ^ 2 = 1 := hinj (by simpa using hq2)
    have hcenq : ∀ y ∈ Q, y * q = q * y := fun y hy =>
      hinj (by simpa using hcen (L.subtype y) ⟨y, hy, rfl⟩)
    rcases hs q hq hcenq hq2' with h1 | h1
    · left; rw [h1]; simp
    · right; rw [h1]

theorem false_of_small {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t) (hLz : ∀ l ∈ L, l * z = z * l)
    (hdec : ∀ t ∈ (T : Subgroup G), ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c)
    (hmeet : ∀ g ∈ L, g ∈ centralizer (L : Set G) → g = 1)
    (hTCcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hB : SmallTable L ((T : Subgroup G) ⊓ L)) : False := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzTC : z ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    ⟨hzT, Subgroup.mem_centralizer_iff.2 fun l hl => hLz l hl⟩
  have hTCcomm : ∀ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G),
      ∀ c' ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), c * c' = c' * c := by
    intro c hc c' hc'
    have := cyclic_mul_comm (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G))) ⟨c, hc⟩ ⟨c', hc'⟩
    exact congrArg Subtype.val this
  have hTCinv : ∀ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), c ^ 2 = 1 → c = 1 ∨ c = z := by
    intro c hc hc2
    have := cyclic_pow_two_eq_one (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
      (z := ⟨z, hzTC⟩) (c := ⟨c, hc⟩)
      (Subtype.ext (by simpa using hz2)) (fun h => hz1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hc2))
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hodd : Odd ((centralizer ({z} : Set G)).subgroupOf
      (normalizer ((T : Subgroup G) : Set G))).index := by
    have hTle : (T : Subgroup G) ≤ normalizer ((T : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    have hSyl' := CFSG.ABGLocalTools.IsSylowOf.of_le (isSylowOf_top T) hTle le_top
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSyl'
    have hnd : ¬ 2 ∣ (T : Subgroup G).relIndex (normalizer ((T : Subgroup G) : Set G)) :=
      hSyl'.2.2
    have hle : (T : Subgroup G).subgroupOf (normalizer ((T : Subgroup G) : Set G)) ≤
        (centralizer ({z} : Set G)).subgroupOf (normalizer ((T : Subgroup G) : Set G)) := by
      intro g hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzc g hg
    have hdvd := Subgroup.index_dvd_of_le hle
    exact Nat.odd_iff.2 (by
      by_contra hcon
      have h2 : 2 ∣ ((centralizer ({z} : Set G)).subgroupOf
          (normalizer ((T : Subgroup G) : Set G))).index := by omega
      exact hnd (h2.trans hdvd))
  have hfix := conj_fixed_of_small hz1 hz2 hzT hzc hLz hdec hmeet hTCcomm hTCinv hB hodd
  refine CFSG.GH74.E2.tool_Z hs hnab hz hzT hzc ?_ ?_
  · intro u hu hu2
    have hu2' : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    obtain ⟨s, hsm, c, hc, rfl⟩ := hdec u hu
    have hcomm : Commute s c := Subgroup.mem_centralizer_iff.1 hc.2 s hsm.2
    have h1 : s ^ 2 * c ^ 2 = 1 := by rw [← hcomm.mul_pow]; exact hu2'
    have hs2 : s ^ 2 = 1 := by
      have e1 : s ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h2L : s ^ 2 ∈ L := L.pow_mem hsm.2 2
      have h2C : s ^ 2 ∈ centralizer (L : Set G) := by
        rw [e1]
        exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hc.2 2)
      exact hmeet _ h2L h2C
    obtain ⟨k, hkL, hkTL, hkc⟩ := hB.conj_central s hsm hs2
    have hkC : k * c = c * k := Subgroup.mem_centralizer_iff.1 hc.2 k hkL
    refine ⟨k, hLz k hkL, ?_, ?_⟩
    · have e : k⁻¹ * (s * c) * k = (k⁻¹ * s * k) * c := by
        calc k⁻¹ * (s * c) * k = k⁻¹ * s * (c * k) := by group
          _ = k⁻¹ * s * (k * c) := by rw [hkC]
          _ = (k⁻¹ * s * k) * c := by group
      rw [e]
      exact (T : Subgroup G).mul_mem hkTL.1 hc.1
    · intro t ht
      obtain ⟨s', hs', c', hc', rfl⟩ := hdec t ht
      have e : k⁻¹ * (s * c) * k = (k⁻¹ * s * k) * c := by
        calc k⁻¹ * (s * c) * k = k⁻¹ * s * (c * k) := by group
          _ = k⁻¹ * s * (k * c) := by rw [hkC]
          _ = (k⁻¹ * s * k) * c := by group
      rw [e]
      have e1 : Commute s' (k⁻¹ * s * k) := hkc s' hs'
      have e2 : Commute c' (k⁻¹ * s * k) :=
        (Subgroup.mem_centralizer_iff.1 hc'.2 _ hkTL.2).symm
      have e3 : Commute s' c := Subgroup.mem_centralizer_iff.1 hc.2 s' hs'.2
      have e4 : Commute c' c := congrArg Subtype.val
        (cyclic_mul_comm (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G))) ⟨c', hc'⟩ ⟨c, hc⟩)
      exact Commute.mul_left (Commute.mul_right e1 e3) (Commute.mul_right e2 e4)
  · intro n hn w _ _ hw
    rw [hw]
    exact hfix n hn

end CFSG.GH74.AS16.E2
