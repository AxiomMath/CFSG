module

public import CFSG.GroupTheory.OddInversion
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import CFSG.GroupTheory.FourGroupOddOrderIdentity
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G]

section Elements

theorem eq_one_of_conj_eq_inv_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {d f : G}
    (hd : d ∈ K) (hf : f ∈ K) (h : f⁻¹ * d * f = d⁻¹) : d = 1 := by
  have h' : f⁻¹ * d⁻¹ * f = d := by
    have : f⁻¹ * d⁻¹ * f = (f⁻¹ * d * f)⁻¹ := by group
    rw [this, h, inv_inv]
  have hf2 : Commute (f ^ 2) d := by
    have e : (f * f)⁻¹ * d * (f * f) = d := by
      calc (f * f)⁻¹ * d * (f * f) = f⁻¹ * (f⁻¹ * d * f) * f := by group
        _ = d := by rw [h]; exact h'
    show f ^ 2 * d = d * f ^ 2
    rw [pow_two]
    calc f * f * d = f * f * ((f * f)⁻¹ * d * (f * f)) := by rw [e]
      _ = d * (f * f) := by group
  have hof : Odd (orderOf f) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hf)
  obtain ⟨m, hm⟩ := hof
  have hfpow : (f ^ 2) ^ (m + 1) = f := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf f + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hfd : Commute f d := by
    rw [← hfpow]
    exact hf2.pow_left _
  have hdd : d = d⁻¹ := by
    rw [← h, mul_assoc, ← hfd.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hd2 : d ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hdd]
    exact mul_inv_cancel d
  have hod : Odd (orderOf d) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hd)
  have h1 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one hd2
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hod
    exact absurd hod (by decide)

end Elements

section Involution

theorem odd_fixed_mul_inverted {K : Subgroup G} (hK : Odd (Nat.card K)) {a : G}
    (ha : orderOf a = 2) (haK : a ∈ normalizer (K : Set G)) :
    (K : Set G) = ((K ⊓ centralizer {a} : Subgroup G) : Set G) * OddInversion.invertedSet K a ∧
      (K : Set G) =
        OddInversion.invertedSet K a * ((K ⊓ centralizer {a} : Subgroup G) : Set G) := by
  obtain ⟨h1, h2, -⟩ := OddInversion.odd_involution_product_decomposition hK ha haK
  exact ⟨by rw [← Set.image_mul_prod, h1.image_eq], by rw [← Set.image_mul_prod, h2.image_eq]⟩

theorem mem_normalizer_inf {K L : Subgroup G} {a : G} (hK : a ∈ normalizer (K : Set G))
    (hL : a ∈ normalizer (L : Set G)) : a ∈ normalizer ((K ⊓ L : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hK, hL⟩

theorem mem_normalizer_centralizer_self (a : G) :
    a ∈ normalizer ((centralizer {a} : Subgroup G) : Set G) :=
  Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

theorem mem_normalizer_normalizer {F : Subgroup G} {a : G} (ha : a ∈ normalizer (F : Set G)) :
    a ∈ normalizer ((normalizer (F : Set G) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer ha

theorem exists_inverted_centralizing_fixed {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hKp : IsPGroup p K) (hK : Odd (Nat.card K)) {a : G} (ha : orderOf a = 2)
    (haK : a ∈ normalizer (K : Set G)) (hlt : K ⊓ centralizer {a} < K) :
    ∃ y ∈ OddInversion.invertedSet K a, y ≠ 1 ∧
      y ∈ centralizer ((K ⊓ centralizer {a} : Subgroup G) : Set G) := by
  set F : Subgroup G := K ⊓ centralizer {a} with hF
  have hFK : F ≤ K := inf_le_left
  have hfin : Finite K := Nat.finite_of_card_ne_zero hK.pos.ne'
  have hnil : Group.IsNilpotent K := hKp.isNilpotent
  have hlt' : F.subgroupOf K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hlt.ne
    apply le_antisymm hFK
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ F.subgroupOf K := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := K) _ hlt'
  rw [← Subgroup.subgroupOf_normalizer_eq hFK] at hnorm
  obtain ⟨⟨n, hnK⟩, hnN, hnF⟩ := IsConcreteLE.exists_of_lt hnorm
  set N : Subgroup G := normalizer (F : Set G) ⊓ K with hN
  have hnN' : n ∈ N := ⟨hnN, hnK⟩
  have hnF' : n ∉ F := hnF
  have haF : a ∈ normalizer (F : Set G) :=
    mem_normalizer_inf haK (mem_normalizer_centralizer_self a)
  have haN : a ∈ normalizer (N : Set G) := mem_normalizer_inf (mem_normalizer_normalizer haF) haK
  have hNK : N ≤ K := inf_le_right
  have hNodd : Odd (Nat.card N) := hK.of_dvd_nat (Subgroup.card_dvd_of_le hNK)
  have hdec := (odd_fixed_mul_inverted hNodd ha haN).1
  have hn : n ∈ (N : Set G) := hnN'
  rw [hdec] at hn
  obtain ⟨c, hc, y, hy, rfl⟩ := hn
  have hcF : c ∈ F := ⟨hNK hc.1, hc.2⟩
  have hyN : y ∈ N := hy.1
  have hyF : y ∉ F := fun hyF => hnF' (F.mul_mem hcF hyF)
  refine ⟨y, ⟨hNK hyN, hy.2⟩, fun h1 => hyF (h1 ▸ F.one_mem), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxF : x ∈ F := hx
  have hz : y⁻¹ * x * y ∈ F := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN.1) x).mp hxF
    simpa using this
  have hax : a * x * a⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hxF.2
    rw [← this]; group
  have haz : a * (y⁻¹ * x * y) * a⁻¹ = y⁻¹ * x * y := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    rw [← this]; group
  have hay : a * y * a⁻¹ = y⁻¹ := hy.2
  have hyx : y * x * y⁻¹ = y⁻¹ * x * y := by
    have : a * (y⁻¹ * x * y) * a⁻¹ = (a * y * a⁻¹)⁻¹ * (a * x * a⁻¹) * (a * y * a⁻¹) := by
      group
    rw [haz, hay, hax, inv_inv] at this
    exact this.symm
  have hy2 : Commute (y ^ 2) x := by
    show y ^ 2 * x = x * y ^ 2
    rw [pow_two]
    calc y * y * x = y * (y * x * y⁻¹) * y := by group
      _ = y * (y⁻¹ * x * y) * y := by rw [hyx]
      _ = x * (y * y) := by group
  have hoy : Odd (orderOf y) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K (hNK hyN))
  obtain ⟨m, hm⟩ := hoy
  have hypow : (y ^ 2) ^ (m + 1) = y := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hyc : Commute y x := by
    rw [← hypow]
    exact hy2.pow_left _
  exact hyc.eq.symm

end Involution

section KleinFour

variable {T : Subgroup G} [IsKleinFour T]

theorem kleinFour_mul_self {a : G} (ha : a ∈ T) : a * a = 1 :=
  congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : T))

theorem kleinFour_comm {a b : G} (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (kleinFour_mul_self ha)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (kleinFour_mul_self hb)
  have h : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (kleinFour_mul_self (T.mul_mem ha hb))
  rw [← h, mul_inv_rev, hainv, hbinv]

theorem kleinFour_orderOf {a : G} (ha : a ∈ T) (h1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact kleinFour_mul_self ha) h1

theorem kleinFour_eq_mul {a b c : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b) : c = a * b := by
  have := IsKleinFour.eq_mul_of_ne_all (G := T) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) (z := ⟨c, hc⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => hca (congrArg Subtype.val h)) (fun h => hcb (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem kleinFour_mem_cases {a b t : G} (ha : a ∈ T) (hb : b ∈ T) (ht : t ∈ T) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) : t = 1 ∨ t = a ∨ t = b ∨ t = a * b := by
  by_cases h1 : t = 1
  · exact Or.inl h1
  by_cases h2 : t = a
  · exact Or.inr (Or.inl h2)
  by_cases h3 : t = b
  · exact Or.inr (Or.inr (Or.inl h3))
  exact Or.inr (Or.inr (Or.inr (kleinFour_eq_mul ha hb ht ha1 hb1 hab h1 h2 h3)))

theorem centralizer_kleinFour_eq {a b : G} (ha : a ∈ T) (hb : b ∈ T) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    centralizer (T : Set G) = centralizer {a} ⊓ centralizer {b} := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h a ha).symm, (h b hb).symm⟩
  · rintro ⟨hxa, hxb⟩ t ht
    rcases kleinFour_mem_cases ha hb ht ha1 hb1 hab with rfl | rfl | rfl | rfl
    · simp
    · exact hxa.symm
    · exact hxb.symm
    · calc a * b * x = a * (x * b) := by rw [mul_assoc, ← hxb]
        _ = x * a * b := by rw [← mul_assoc, ← hxa]
        _ = x * (a * b) := mul_assoc _ _ _

end KleinFour

section Action

@[reducible] def conjMulDistribMulAction (T K : Subgroup G)
    (hTK : T ≤ normalizer (K : Set G)) : MulDistribMulAction T K where
  smul t k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
  mul_smul s t k := Subtype.ext (by
    change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
    group)
  smul_mul t k l := Subtype.ext (by
    change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
    group)
  smul_one t := Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group)

theorem card_mul_card_centralizer_four_sq [Finite G] {T K : Subgroup G} [IsKleinFour T]
    (hK : Odd (Nat.card K)) (hTK : T ≤ normalizer (K : Set G)) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Nat.card K * Nat.card (K ⊓ centralizer (T : Set G) : Subgroup G) ^ 2 =
      Nat.card (K ⊓ centralizer {a} : Subgroup G) * Nat.card (K ⊓ centralizer {b} : Subgroup G) *
        Nat.card (K ⊓ centralizer {a * b} : Subgroup G) := by
  classical
  let : MulDistribMulAction T K := conjMulDistribMulAction T K hTK
  let : Fintype T := Fintype.ofFinite T
  have h := (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
    (A := T) (X := K) hK).1
  have hz : ∀ t : T, Nat.card (fixedPointSubgroup (Subgroup.zpowers t) K) =
      Nat.card (K ⊓ centralizer {(t : G)} : Subgroup G) := by
    intro t
    have hmap : (fixedPointSubgroup (Subgroup.zpowers t) K).map K.subtype =
        K ⊓ centralizer {(t : G)} := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        have := congrArg Subtype.val (hy ⟨t, Subgroup.mem_zpowers t⟩)
        change (t : G) * y * (t : G)⁻¹ = y at this
        have h2 : (t : G) * y = y * t := by
          calc (t : G) * y = t * y * (t : G)⁻¹ * t := by group
            _ = y * t := by rw [this]
        exact h2.symm
      · rintro ⟨hxK, hxt⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        rintro ⟨s, hs⟩
        rcases (CFSG.GroupTheory.mem_zpowers_of_isKleinFour t s).mp hs with h | h
        · apply Subtype.ext
          change (s : G) * x * (s : G)⁻¹ = x
          rw [h]
          simp
        · apply Subtype.ext
          change (s : G) * x * (s : G)⁻¹ = x
          rw [h, ← hxt]
          group
    rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]
  have htop : Nat.card (fixedPointSubgroup T K) =
      Nat.card (K ⊓ centralizer (T : Set G) : Subgroup G) := by
    have hmap : (fixedPointSubgroup T K).map K.subtype = K ⊓ centralizer (T : Set G) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        SetLike.mem_coe]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, fun t ht => ?_⟩
        have := congrArg Subtype.val (hy ⟨t, ht⟩)
        change t * y * t⁻¹ = y at this
        calc t * y = t * y * t⁻¹ * t := by group
          _ = y * t := by rw [this]
      · rintro ⟨hxK, hxt⟩
        refine ⟨⟨x, hxK⟩, fun t => ?_, rfl⟩
        apply Subtype.ext
        change (t : G) * x * (t : G)⁻¹ = x
        rw [hxt t t.2]
        group
    rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]
  set ta : T := ⟨a, ha⟩
  set tb : T := ⟨b, hb⟩
  have hta : ta ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have htb : tb ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have htab : ta ≠ tb := fun h => hab (congrArg Subtype.val h)
  have huniv := IsKleinFour.eq_finset_univ hta htb htab
  have habne1 : ta * tb ≠ 1 := fun h => hab (by
    have := congrArg Subtype.val (mul_eq_one_iff_eq_inv.mp h)
    simpa [ta, tb, inv_eq_of_mul_eq_one_right (kleinFour_mul_self hb)] using this)
  have habnea : ta * tb ≠ ta := fun h => htb (by simpa using h)
  have habneb : ta * tb ≠ tb := fun h => hta (by simpa using h)
  have herase : Finset.univ.erase (1 : T) = {ta * tb, ta, tb} := by
    rw [← huniv]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx1, hx | hx | hx | hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact absurd hx hx1
    · rintro (hx | hx | hx) <;> subst hx
      · exact ⟨habne1, Or.inl rfl⟩
      · exact ⟨hta, Or.inr (Or.inl rfl)⟩
      · exact ⟨htb, Or.inr (Or.inr (Or.inl rfl))⟩
  rw [herase, Finset.prod_insert (by simp [habnea, habneb]),
    Finset.prod_insert (by simp [htab]), Finset.prod_singleton, hz, hz, hz, htop] at h
  rw [h]
  simp only [ta, tb, Subgroup.coe_mul]
  ring

end Action

section FourGroup

theorem four_group_key {K : Subgroup G} (hK : Odd (Nat.card K)) {a₁ a₂ : G}
    (h₁₁ : a₁ * a₁ = 1) (h₂₂ : a₂ * a₂ = 1) (h₁₂ : a₁ * a₂ = a₂ * a₁)
    (hK₁ : a₁ ∈ normalizer (K : Set G)) (hK₂ : a₂ ∈ normalizer (K : Set G)) {a b₁ b₂ : G}
    (ha : a ∈ K) (hb₂ : b₂ ∈ K) (haa : a₁ * a = a * a₁) (hb₁c : a₂ * b₁ = b₁ * a₂)
    (hb₂c : a₂ * b₂ = b₂ * a₂)
    (hc : a₁ * a₂ * (b₁ * a * b₂) = b₁ * a * b₂ * (a₁ * a₂)) :
    a₂ * (b₁ * a * b₂) = b₁ * a * b₂ * a₂ := by
  set σ : MulAut G := MulAut.conj a₂ with hσ
  set τ : MulAut G := MulAut.conj a₁ with hτ
  have h₁inv : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right h₁₁
  have h₂inv : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right h₂₂
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    simp only [hσ, MulAut.conj_apply]
    calc a₂ * (a₂ * x * a₂⁻¹) * a₂⁻¹ = (a₂ * a₂) * x * (a₂ * a₂)⁻¹ := by group
      _ = x := by rw [h₂₂]; group
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    simp only [hτ, MulAut.conj_apply]
    calc a₁ * (a₁ * x * a₁⁻¹) * a₁⁻¹ = (a₁ * a₁) * x * (a₁ * a₁)⁻¹ := by group
      _ = x := by rw [h₁₁]; group
  have hστ : ∀ x, σ (τ x) = τ (σ x) := by
    intro x
    simp only [hσ, hτ, MulAut.conj_apply]
    calc a₂ * (a₁ * x * a₁⁻¹) * a₂⁻¹ = (a₂ * a₁) * x * (a₂ * a₁)⁻¹ := by group
      _ = (a₁ * a₂) * x * (a₁ * a₂)⁻¹ := by rw [h₁₂]
      _ = a₁ * (a₂ * x * a₂⁻¹) * a₁⁻¹ := by group
  have fix_of_comm : ∀ (u v : G), u * v = v * u → MulAut.conj u v = v := by
    intro u v huv
    rw [MulAut.conj_apply, huv]
    group
  set c : G := b₁ * a * b₂ with hcdef
  have hτσc : τ (σ c) = c := by
    have : MulAut.conj (a₁ * a₂) c = c := fix_of_comm _ _ hc
    have e : MulAut.conj (a₁ * a₂) = τ * σ := map_mul MulAut.conj a₁ a₂
    rw [e, MulAut.mul_apply] at this
    exact this
  have hτc : τ c = σ c := by
    have := congrArg τ hτσc
    rw [hττ] at this
    exact this.symm
  have hσb₁ : σ b₁ = b₁ := fix_of_comm _ _ hb₁c
  have hσb₂ : σ b₂ = b₂ := fix_of_comm _ _ hb₂c
  have hτa : τ a = a := fix_of_comm _ _ haa
  have hσc : σ c = b₁ * σ a * b₂ := by
    rw [hcdef, map_mul, map_mul, hσb₁, hσb₂]
  set d : G := a⁻¹ * σ a with hd
  have hτd : τ d = d := by
    rw [hd, map_mul, map_inv, hτa, ← hστ, hτa]
  set e : G := c⁻¹ * σ c with he
  have he' : e = b₂⁻¹ * d * b₂ := by
    rw [he, hσc, hcdef, hd]
    group
  have hτe : τ e = e⁻¹ := by
    rw [he, map_mul, map_inv, hτc, ← hστ, hτc, hσσ]
    group
  have hτe' : τ e = (τ b₂)⁻¹ * d * τ b₂ := by
    rw [he', map_mul, map_mul, map_inv, hτd]
  set f : G := τ b₂ * b₂⁻¹ with hf
  have hconj : f⁻¹ * d * f = d⁻¹ := by
    have h1 : (τ b₂)⁻¹ * d * τ b₂ = b₂⁻¹ * d⁻¹ * b₂ := by
      rw [← hτe', hτe, he']
      group
    calc f⁻¹ * d * f = b₂ * ((τ b₂)⁻¹ * d * τ b₂) * b₂⁻¹ := by rw [hf]; group
      _ = b₂ * (b₂⁻¹ * d⁻¹ * b₂) * b₂⁻¹ := by rw [h1]
      _ = d⁻¹ := by group
  have hσK : ∀ x ∈ K, σ x ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hK₂ x).mp hx
  have hτK : ∀ x ∈ K, τ x ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hK₁ x).mp hx
  have hdK : d ∈ K := K.mul_mem (K.inv_mem ha) (hσK a ha)
  have hfK : f ∈ K := K.mul_mem (hτK b₂ hb₂) (K.inv_mem hb₂)
  have hd1 : d = 1 := eq_one_of_conj_eq_inv_of_odd hK hdK hfK hconj
  have he1 : e = 1 := by rw [he', hd1]; group
  have hσcc : σ c = c := by
    have : c⁻¹ * σ c = 1 := he1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have := hσcc
  simp only [hσ, MulAut.conj_apply] at this
  calc a₂ * c = a₂ * c * a₂⁻¹ * a₂ := by group
    _ = c * a₂ := by rw [this]

theorem four_group_odd_eq_mul_centralizers [Finite G] {K T : Subgroup G} [IsKleinFour T]
    (hK : Odd (Nat.card K)) (hTK : T ≤ normalizer (K : Set G)) {a₁ a₂ a₃ : G}
    (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) (h₃ : a₃ ∈ T) (h₁₁ : a₁ ≠ 1) (h₂₁ : a₂ ≠ 1) (h₃₁ : a₃ ≠ 1)
    (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃) :
    (K : Set G) = ((K ⊓ centralizer {a₁} : Subgroup G) : Set G) *
      ((K ⊓ centralizer {a₂} : Subgroup G) : Set G) *
      ((K ⊓ centralizer {a₃} : Subgroup G) : Set G) := by
  classical
  have ha₃ : a₃ = a₁ * a₂ :=
    kleinFour_eq_mul h₁ h₂ h₃ h₁₁ h₂₁ h₁₂ h₃₁ (Ne.symm h₁₃) (Ne.symm h₂₃)
  set C₁ : Subgroup G := K ⊓ centralizer {a₁} with hC₁
  set C₂ : Subgroup G := K ⊓ centralizer {a₂} with hC₂
  set C₃ : Subgroup G := K ⊓ centralizer {a₃} with hC₃
  set C₀ : Subgroup G := K ⊓ centralizer (T : Set G) with hC₀
  have hC₀₁₂ : ∀ x, x ∈ C₁ → x ∈ C₂ → x ∈ C₀ := by
    intro x hx1 hx2
    refine ⟨hx1.1, ?_⟩
    rw [centralizer_kleinFour_eq h₁ h₂ h₁₁ h₂₁ h₁₂]
    exact ⟨hx1.2, hx2.2⟩
  have hC₀₂₃ : ∀ x, x ∈ C₂ → x ∈ C₃ → x ∈ C₀ := by
    intro x hx2 hx3
    refine ⟨hx2.1, ?_⟩
    rw [centralizer_kleinFour_eq h₂ h₃ h₂₁ h₃₁ h₂₃]
    exact ⟨hx2.2, hx3.2⟩
  have hC₀₁ : C₀ ≤ C₁ := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hx.2) a₁ h₁).symm⟩
  have hC₀₂ : C₀ ≤ C₂ := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hx.2) a₂ h₂).symm⟩
  have hC₃K : C₃ ≤ K := inf_le_left
  have hid := card_mul_card_centralizer_four_sq hK hTK h₁ h₂ h₁₁ h₂₁ h₁₂
  rw [← ha₃] at hid
  have hm₁ : a₁ * a₁ = 1 := kleinFour_mul_self h₁
  have hm₂ : a₂ * a₂ = 1 := kleinFour_mul_self h₂
  have hc₁₂ : a₁ * a₂ = a₂ * a₁ := kleinFour_comm h₁ h₂
  have hfib : ∀ x x' : G, x ∈ C₁ → x' ∈ C₁ → ∀ y y' : G, y ∈ C₂ → y' ∈ C₂ →
      (x' * y')⁻¹ * (x * y) ∈ C₃ → x'⁻¹ * x ∈ C₀ ∧ y'⁻¹ * (x'⁻¹ * x) * y ∈ C₀ := by
    intro x x' hx hx' y y' hy hy' hmem
    set α : G := x'⁻¹ * x with hα
    have hαC₁ : α ∈ C₁ := C₁.mul_mem (C₁.inv_mem hx') hx
    have hc : y'⁻¹ * α * y ∈ C₃ := by
      have : y'⁻¹ * α * y = (x' * y')⁻¹ * (x * y) := by rw [hα]; group
      rw [this]; exact hmem
    have hcK : y'⁻¹ * α * y ∈ K := hC₃K hc
    have hcomm : a₂ * (y'⁻¹ * α * y) = y'⁻¹ * α * y * a₂ := by
      apply four_group_key hK hm₁ hm₂ hc₁₂ (hTK h₁) (hTK h₂) hαC₁.1 hy.1
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hαC₁.2).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (C₂.inv_mem hy').2).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
      · rw [← ha₃]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
    have hcC₂ : y'⁻¹ * α * y ∈ C₂ :=
      ⟨hcK, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcC₀ : y'⁻¹ * α * y ∈ C₀ := hC₀₂₃ _ hcC₂ hc
    have hαC₂ : α ∈ C₂ := by
      have : α = y' * (y'⁻¹ * α * y) * y⁻¹ := by group
      rw [this]
      exact C₂.mul_mem (C₂.mul_mem hy' hcC₂) (C₂.inv_mem hy)
    exact ⟨hC₀₁₂ α hαC₁ hαC₂, hcC₀⟩
  let Q := K ⧸ C₃.subgroupOf K
  let φ : C₁ × C₂ → Q := fun z =>
    ((⟨(z.1 : G) * z.2, K.mul_mem z.1.2.1 z.2.2.1⟩ : K) : Q)
  have hsurj : Function.Surjective φ := by
    let : Fintype (C₁ × C₂) := Fintype.ofFinite _
    let : Fintype Q := Fintype.ofFinite _
    have hbound : ∀ q ∈ (Finset.univ : Finset (C₁ × C₂)).image φ,
        ((Finset.univ : Finset (C₁ × C₂)).filter fun z => φ z = q).card ≤
          Nat.card C₀ ^ 2 := by
      intro q hq
      obtain ⟨⟨x, y⟩, -, rfl⟩ := Finset.mem_image.mp hq
      let : Fintype (C₀ × C₀) := Fintype.ofFinite _
      let g : C₀ × C₀ → C₁ × C₂ := fun w =>
        (⟨(x : G) * w.1, C₁.mul_mem x.2 (hC₀₁ w.1.2)⟩,
          ⟨(w.1 : G)⁻¹ * y * w.2, C₂.mul_mem (C₂.mul_mem (C₂.inv_mem (hC₀₂ w.1.2)) y.2)
            (hC₀₂ w.2.2)⟩)
      calc ((Finset.univ : Finset (C₁ × C₂)).filter fun z => φ z = φ (x, y)).card
          ≤ ((Finset.univ : Finset (C₀ × C₀)).image g).card := by
            apply Finset.card_le_card
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
            obtain ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ := z
            have hmem : (x' * y')⁻¹ * ((x : G) * y) ∈ C₃ := by
              have := QuotientGroup.eq.mp hz
              rw [Subgroup.mem_subgroupOf] at this
              simpa using this
            obtain ⟨hu, hw⟩ := hfib x x' x.2 hx' y y' y.2 hy' hmem
            refine Finset.mem_image.mpr ⟨(⟨(x : G)⁻¹ * x', ?_⟩,
              ⟨((y' : G)⁻¹ * (x'⁻¹ * x) * y)⁻¹, C₀.inv_mem hw⟩), Finset.mem_univ _, ?_⟩
            · have := C₀.inv_mem hu
              rwa [mul_inv_rev, inv_inv] at this
            · simp only [g, Prod.mk.injEq, Subtype.mk.injEq]
              constructor
              · group
              · group
        _ ≤ (Finset.univ : Finset (C₀ × C₀)).card := Finset.card_image_le
        _ = Nat.card C₀ ^ 2 := by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_prod, pow_two]
    have hle := Finset.card_le_mul_card_image (Finset.univ : Finset (C₁ × C₂)) _ hbound
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_prod] at hle
    have hQ : Nat.card Q * Nat.card C₃ = Nat.card K := by
      have := Subgroup.relIndex_mul_card C₃ K
      rw [inf_eq_left.mpr hC₃K] at this
      exact this
    have hC0pos : 0 < Nat.card C₀ ^ 2 := pow_pos Nat.card_pos 2
    have hC3pos : 0 < Nat.card C₃ := Nat.card_pos
    have hcard : Nat.card Q ≤ ((Finset.univ : Finset (C₁ × C₂)).image φ).card := by
      have h1 : Nat.card Q * Nat.card C₀ ^ 2 * Nat.card C₃ =
          Nat.card C₁ * Nat.card C₂ * Nat.card C₃ := by
        rw [← hid, ← hQ]
        ring
      have h2 : Nat.card Q * Nat.card C₀ ^ 2 = Nat.card C₁ * Nat.card C₂ :=
        Nat.eq_of_mul_eq_mul_right hC3pos h1
      have h3 : Nat.card Q * Nat.card C₀ ^ 2 ≤
          ((Finset.univ : Finset (C₁ × C₂)).image φ).card * Nat.card C₀ ^ 2 := by
        rw [h2, mul_comm _ (Nat.card C₀ ^ 2)]
        exact hle
      exact Nat.le_of_mul_le_mul_right h3 hC0pos
    have himage : (Finset.univ : Finset (C₁ × C₂)).image φ = Finset.univ := by
      apply Finset.eq_univ_of_card
      apply le_antisymm (Finset.card_le_univ _)
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    intro q
    have : q ∈ (Finset.univ : Finset (C₁ × C₂)).image φ := by
      rw [himage]
      exact Finset.mem_univ q
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp this
    exact ⟨z, hz⟩
  apply Set.Subset.antisymm
  · intro k hk
    obtain ⟨⟨x, y⟩, hxy⟩ := hsurj ((⟨k, hk⟩ : K) : Q)
    have hmem : ((x : G) * y)⁻¹ * k ∈ C₃ := by
      have h' : (⟨(x : G) * y, K.mul_mem x.2.1 y.2.1⟩ : K)⁻¹ * ⟨k, hk⟩ ∈ C₃.subgroupOf K :=
        QuotientGroup.eq.mp hxy
      rw [Subgroup.mem_subgroupOf] at h'
      simpa using h'
    refine ⟨(x : G) * y, ⟨x, x.2, y, y.2, rfl⟩, ((x : G) * y)⁻¹ * k, hmem, ?_⟩
    group
  · rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩
    exact K.mul_mem (K.mul_mem hx.1 hy.1) hz.1

end FourGroup

section TDecomposition

@[expose] def fourInverted (K : Subgroup G) (ai aj : G) : Set G :=
  {k | k ∈ K ∧ ai * k * ai⁻¹ = k ∧ aj * k * aj⁻¹ = k⁻¹}

theorem coe_mul_coe_of_le {H L : Subgroup G} (h : H ≤ L) : (L : Set G) * H = L := by
  ext x
  constructor
  · rintro ⟨l, hl, k, hk, rfl⟩
    exact L.mul_mem hl (h hk)
  · intro hx
    exact ⟨x, hx, 1, H.one_mem, mul_one x⟩

theorem coe_mul_coe_of_le' {H L : Subgroup G} (h : H ≤ L) : (H : Set G) * L = L := by
  ext x
  constructor
  · rintro ⟨k, hk, l, hl, rfl⟩
    exact L.mul_mem (h hk) hl
  · intro hx
    exact ⟨1, H.one_mem, x, hx, one_mul x⟩

theorem centralizer_eq_mul_fourInverted [Finite G] {K T : Subgroup G} [IsKleinFour T]
    (hK : Odd (Nat.card K)) (hTK : T ≤ normalizer (K : Set G)) {ai aj : G} (hi : ai ∈ T)
    (hj : aj ∈ T) (hi1 : ai ≠ 1) (hj1 : aj ≠ 1) (hij : ai ≠ aj) :
    ((K ⊓ centralizer {ai} : Subgroup G) : Set G) =
        ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G) * fourInverted K ai aj ∧
      ((K ⊓ centralizer {ai} : Subgroup G) : Set G) =
        fourInverted K ai aj * ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
  set Ki : Subgroup G := K ⊓ centralizer {ai} with hKi
  have hKiodd : Odd (Nat.card Ki) := hK.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hjc : aj ∈ centralizer {ai} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (kleinFour_comm hj hi)
  have hjKi : aj ∈ normalizer (Ki : Set G) :=
    mem_normalizer_inf (hTK hj) (Subgroup.le_normalizer hjc)
  have hdec := odd_fixed_mul_inverted hKiodd (kleinFour_orderOf hj hj1) hjKi
  have hfix : Ki ⊓ centralizer {aj} = K ⊓ centralizer (T : Set G) := by
    rw [hKi, centralizer_kleinFour_eq hi hj hi1 hj1 hij, inf_assoc]
  have hinv : OddInversion.invertedSet Ki aj = fourInverted K ai aj := by
    ext k
    simp only [OddInversion.mem_invertedSet, fourInverted, Set.mem_ofPred_eq, hKi,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hkK, hk⟩, hj'⟩
      exact ⟨hkK, by rw [← hk]; group, hj'⟩
    · rintro ⟨hkK, hk, hj'⟩
      refine ⟨⟨hkK, ?_⟩, hj'⟩
      calc k * ai = ai * k * ai⁻¹ * ai := by rw [hk]
        _ = ai * k := by group
  rw [hfix, hinv] at hdec
  exact hdec

theorem four_group_T_decomposition [Finite G] {K T : Subgroup G} [IsKleinFour T]
    (hK : Odd (Nat.card K)) (hTK : T ≤ normalizer (K : Set G)) {a₁ a₂ : G}
    (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) (h₁₁ : a₁ ≠ 1) (h₂₁ : a₂ ≠ 1) (h₁₂ : a₁ ≠ a₂) :
    (∀ ai aj : G, ai ∈ T → aj ∈ T → ai ≠ 1 → aj ≠ 1 → ai ≠ aj →
      ((K ⊓ centralizer {ai} : Subgroup G) : Set G) =
          ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G) * fourInverted K ai aj ∧
        ((K ⊓ centralizer {ai} : Subgroup G) : Set G) =
          fourInverted K ai aj * ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G)) ∧
    (K : Set G) = ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G) *
      fourInverted K a₁ a₂ * fourInverted K a₂ a₁ * fourInverted K (a₁ * a₂) a₁ := by
  have hpart : ∀ ai aj : G, ai ∈ T → aj ∈ T → ai ≠ 1 → aj ≠ 1 → ai ≠ aj →
      ((K ⊓ centralizer {ai} : Subgroup G) : Set G) =
          ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G) * fourInverted K ai aj ∧
        ((K ⊓ centralizer {ai} : Subgroup G) : Set G) =
          fourInverted K ai aj * ((K ⊓ centralizer (T : Set G) : Subgroup G) : Set G) :=
    fun ai aj hi hj hi1 hj1 hij => centralizer_eq_mul_fourInverted hK hTK hi hj hi1 hj1 hij
  refine ⟨hpart, ?_⟩
  have h₃ : a₁ * a₂ ∈ T := T.mul_mem h₁ h₂
  have hinv₂ : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right (kleinFour_mul_self h₂)
  have h₃₁ : a₁ * a₂ ≠ 1 := by
    intro h
    apply h₁₂
    rw [mul_eq_one_iff_eq_inv, hinv₂] at h
    exact h
  have h₁₃ : a₁ ≠ a₁ * a₂ := fun h => h₂₁ (by simpa using h)
  have h₂₃ : a₂ ≠ a₁ * a₂ := fun h => h₁₁ (by
    have := congrArg (· * a₂⁻¹) h
    simpa using this.symm)
  have hmain := four_group_odd_eq_mul_centralizers hK hTK h₁ h₂ h₃ h₁₁ h₂₁ h₃₁ h₁₂ h₁₃ h₂₃
  set K₀ : Subgroup G := K ⊓ centralizer (T : Set G)
  have hK₀₂ : K₀ ≤ K ⊓ centralizer {a₂} := fun x hx => ⟨hx.1,
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hx.2) a₂ h₂).symm⟩
  obtain ⟨e₁, e₁'⟩ := hpart a₁ a₂ h₁ h₂ h₁₁ h₂₁ h₁₂
  obtain ⟨e₂, -⟩ := hpart a₂ a₁ h₂ h₁ h₂₁ h₁₁ (Ne.symm h₁₂)
  obtain ⟨e₃, -⟩ := hpart (a₁ * a₂) a₁ h₃ h₁ h₃₁ h₁₁ (Ne.symm h₁₃)
  have hK₀K₀ : (K₀ : Set G) * K₀ = K₀ := coe_mul_coe_of_le le_rfl
  have hK₂K₀ : ((K ⊓ centralizer {a₂} : Subgroup G) : Set G) * K₀ =
      ((K ⊓ centralizer {a₂} : Subgroup G) : Set G) := coe_mul_coe_of_le hK₀₂
  rw [hmain, e₃]
  calc ((K ⊓ centralizer {a₁} : Subgroup G) : Set G) *
        ((K ⊓ centralizer {a₂} : Subgroup G) : Set G) * (K₀ * fourInverted K (a₁ * a₂) a₁)
      = ((K ⊓ centralizer {a₁} : Subgroup G) : Set G) *
          (((K ⊓ centralizer {a₂} : Subgroup G) : Set G) * K₀) *
          fourInverted K (a₁ * a₂) a₁ := by simp only [mul_assoc]
    _ = ((K ⊓ centralizer {a₁} : Subgroup G) : Set G) *
          ((K ⊓ centralizer {a₂} : Subgroup G) : Set G) * fourInverted K (a₁ * a₂) a₁ := by
        rw [hK₂K₀]
    _ = ((K ⊓ centralizer {a₁} : Subgroup G) : Set G) * (K₀ * fourInverted K a₂ a₁) *
          fourInverted K (a₁ * a₂) a₁ := by rw [← e₂]
    _ = (K₀ * (fourInverted K a₁ a₂ * K₀)) * fourInverted K a₂ a₁ *
          fourInverted K (a₁ * a₂) a₁ := by rw [e₁]; simp only [mul_assoc]
    _ = (K₀ * K₀) * fourInverted K a₁ a₂ * fourInverted K a₂ a₁ *
          fourInverted K (a₁ * a₂) a₁ := by rw [← e₁', e₁]; simp only [mul_assoc]
    _ = K₀ * fourInverted K a₁ a₂ * fourInverted K a₂ a₁ * fourInverted K (a₁ * a₂) a₁ := by
        rw [hK₀K₀]

end TDecomposition

end CFSG.ABGLocalTools
