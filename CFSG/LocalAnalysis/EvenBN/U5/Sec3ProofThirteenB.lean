module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section S313bGeneric

variable {Q : Type*} [Group Q] [Finite Q]

theorem s313b_center_trivial {D : Subgroup Q} (hs : IsSimpleGroup D)
    (hna : ∃ x y : D, x * y ≠ y * x) {a : Q} (ha : a ∈ D)
    (hc : ∀ d ∈ D, d * a = a * d) : a = 1 := by
  have hcen : (⟨a, ha⟩ : D) ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exfalso
    obtain ⟨x, y, hxy⟩ := hna
    have : x ∈ Subgroup.center D := by rw [h]; trivial
    exact hxy (Subgroup.mem_center_iff.1 this y).symm

theorem s313b_even_card {D : Subgroup Q} (hs : IsSimpleGroup D)
    (hna : ∃ x y : D, x * y ≠ y * x) : Even (Nat.card D) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨x, y, hxy⟩ := hna
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable (G := D)).2 inferInstance x y)

theorem s313b_le_of_mem {D D' T : Subgroup Q} (hs : IsSimpleGroup D)
    (hna : ∃ x y : D, x * y ≠ y * x) (hc : ∀ x ∈ D, ∀ y ∈ D', x * y = y * x)
    (hDN : D ≤ normalizer (T : Set Q)) {t₁ t₂ : Q} (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D')
    (ht : t₁ * t₂ ∈ T) (h1 : t₁ ≠ 1) : D ≤ T := by
  have hN : ((T ⊓ D).subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, D.mul_mem (D.mul_mem g.2 n.2) (D.inv_mem g.2)⟩
    exact (mem_normalizer_iff.1 (hDN g.2) _).1 hn.1
  rcases hs.eq_bot_or_eq_top_of_normal ((T ⊓ D).subgroupOf D) with h | h
  · exfalso
    refine h1 (s313b_center_trivial hs hna h₁ fun d hd => ?_)
    have hc1 : (t₁ * t₂) * d * (t₁ * t₂)⁻¹ * d⁻¹ ∈ T := by
      have := (mem_normalizer_iff.1 (hDN hd) (t₁ * t₂)⁻¹).1 (T.inv_mem ht)
      simpa [mul_assoc] using T.mul_mem ht this
    have e : (t₁ * t₂) * d * (t₁ * t₂)⁻¹ * d⁻¹ = t₁ * d * t₁⁻¹ * d⁻¹ := by
      have h2d : t₂ * d = d * t₂ := (hc d hd t₂ h₂).symm
      calc (t₁ * t₂) * d * (t₁ * t₂)⁻¹ * d⁻¹ = t₁ * (t₂ * d) * t₂⁻¹ * t₁⁻¹ * d⁻¹ := by group
        _ = t₁ * (d * t₂) * t₂⁻¹ * t₁⁻¹ * d⁻¹ := by rw [h2d]
        _ = t₁ * d * t₁⁻¹ * d⁻¹ := by group
    have hc2 : t₁ * d * t₁⁻¹ * d⁻¹ ∈ D :=
      D.mul_mem (D.mul_mem (D.mul_mem h₁ hd) (D.inv_mem h₁)) (D.inv_mem hd)
    rw [e] at hc1
    have hmem : (⟨t₁ * d * t₁⁻¹ * d⁻¹, hc2⟩ : D) ∈ (T ⊓ D).subgroupOf D :=
      mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hc1, hc2⟩)
    rw [h, Subgroup.mem_bot] at hmem
    have h3 : t₁ * d * t₁⁻¹ * d⁻¹ = 1 := congrArg Subtype.val hmem
    have h4 : t₁ * d = d * t₁ := by
      have := congrArg (· * (d * t₁)) h3
      simp only [one_mul] at this
      calc t₁ * d = t₁ * d * t₁⁻¹ * d⁻¹ * (d * t₁) := by group
        _ = d * t₁ := by rw [h3, one_mul]
    exact h4.symm
  · intro x hx
    have := Subgroup.subgroupOf_eq_top.1 h
    exact (Subgroup.mem_inf.1 (this hx)).1

theorem s313b_normal_contains {D₁ D₂ T : Subgroup Q} (hs₁ : IsSimpleGroup D₁)
    (hna₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hna₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hT : T ≤ D₁ ⊔ D₂) (hn : D₁ ⊔ D₂ ≤ normalizer (T : Set Q)) (hT1 : T ≠ ⊥) :
    D₁ ≤ T ∨ D₂ ≤ T := by
  obtain ⟨⟨t, htT⟩, ht1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT1
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  have htT' := hT htT
  rw [← SetLike.mem_coe, (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc).2] at htT'
  obtain ⟨t₁, h₁, t₂, h₂, rfl⟩ := htT'
  by_cases h1 : t₁ = 1
  · right
    subst h1
    simp only [one_mul] at htT ht1
    refine s313b_le_of_mem hs₂ hna₂ (fun x hx y hy => (hc y hy x hx).symm)
      ((le_sup_right : D₂ ≤ D₁ ⊔ D₂).trans hn) h₂ h₁ ?_ ht1
    simpa using htT
  · left
    exact s313b_le_of_mem hs₁ hna₁ hc ((le_sup_left : D₁ ≤ D₁ ⊔ D₂).trans hn) h₁ h₂ htT h1

theorem s313b_odd_normal_trivial {D₁ D₂ T : Subgroup Q} (hs₁ : IsSimpleGroup D₁)
    (hna₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hna₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hT : T ≤ D₁ ⊔ D₂) (hn : D₁ ⊔ D₂ ≤ normalizer (T : Set Q)) (hodd : Odd (Nat.card T)) :
    T = ⊥ := by
  by_contra hT1
  rcases s313b_normal_contains hs₁ hna₁ hs₂ hna₂ hc hT hn hT1 with h | h
  · exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le h)))
      (s313b_even_card hs₁ hna₁)
  · exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le h)))
      (s313b_even_card hs₂ hna₂)

theorem s313b_not_centralizes {D₁ D₂ T : Subgroup Q} (hs₁ : IsSimpleGroup D₁)
    (hna₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hna₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hT : T ≤ D₁ ⊔ D₂) (hn : D₁ ⊔ D₂ ≤ normalizer (T : Set Q)) (hT1 : T ≠ ⊥)
    {a b : Q} (ha : a ∈ D₁) (hb : b ∈ D₂) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ¬ ∀ t ∈ T, t * (a * b) = (a * b) * t := by
  intro hall
  rcases s313b_normal_contains hs₁ hna₁ hs₂ hna₂ hc hT hn hT1 with h | h
  · refine ha1 (s313b_center_trivial hs₁ hna₁ ha fun d hd => ?_)
    have h1 := hall d (h hd)
    have h2 : d * (a * b) = (d * a) * b := by group
    have h3 : (a * b) * d = (a * d) * b := by
      calc (a * b) * d = a * (b * d) := by group
        _ = a * (d * b) := by rw [(hc d hd b hb).symm]
        _ = (a * d) * b := by group
    rw [h2, h3] at h1
    exact mul_right_cancel h1
  · refine hb1 (s313b_center_trivial hs₂ hna₂ hb fun d hd => ?_)
    have h1 := hall d (h hd)
    have h2 : d * (a * b) = a * (d * b) := by
      calc d * (a * b) = (d * a) * b := by group
        _ = (a * d) * b := by rw [(hc a ha d hd)]
        _ = a * (d * b) := by group
    have h3 : (a * b) * d = a * (b * d) := by group
    rw [h2, h3] at h1
    exact mul_left_cancel h1

theorem s313b_sylow_center {D₁ D₂ T : Subgroup Q} (hs₁ : IsSimpleGroup D₁)
    (hna₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hna₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hi : D₁ ⊓ D₂ = ⊥) (hT : IsSylowOf 2 T (D₁ ⊔ D₂)) :
    (∃ z ∈ D₁, z ≠ 1 ∧ z ∈ T ∧ ∀ t ∈ T, t * z = z * t) ∧
      (∃ z ∈ D₂, z ≠ 1 ∧ z ∈ T ∧ ∀ t ∈ T, t * z = z * t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hT₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 D₁
  obtain ⟨T₂, hT₂⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 D₂
  have hcT : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x := fun x hx y hy => hc x (hT₁.le hx) y (hT₂.le hy)
  have hbot : T₁ ⊓ T₂ = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have : z ∈ D₁ ⊓ D₂ := Subgroup.mem_inf.2 ⟨hT₁.le (Subgroup.mem_inf.1 hz).1,
      hT₂.le (Subgroup.mem_inf.1 hz).2⟩
    rwa [hi] at this
  have hcard12 : Nat.card ↥(D₁ ⊔ D₂) = Nat.card D₁ * Nat.card D₂ := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc).1
    rwa [hi, Subgroup.card_bot, mul_one] at this
  have hcardT : Nat.card ↥(T₁ ⊔ T₂) = Nat.card T₁ * Nat.card T₂ := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T₁ T₂ hcT).1
    rwa [hbot, Subgroup.card_bot, mul_one] at this
  have hsyl : IsSylowOf 2 (T₁ ⊔ T₂) (D₁ ⊔ D₂) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (sup_le_sup hT₁.le hT₂.le) ?_
    rw [hcardT, hcard12, hT₁.card_eq, hT₂.card_eq, ← pow_add,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp
  obtain ⟨g, hg, hTg⟩ := Prelim.exists_conj_of_isSylowOf hsyl hT
  have hg' := hg
  rw [← SetLike.mem_coe, (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc).2] at hg'
  obtain ⟨g₁, hg₁, g₂, hg₂, hgg⟩ := hg'
  have hgg' : g₁ * g₂ = g := hgg
  have hnt : ∀ {D' T' : Subgroup Q}, IsSimpleGroup D' → (∃ x y : D', x * y ≠ y * x) →
      IsSylowOf 2 T' D' → ∃ c ∈ T', c ≠ 1 ∧ ∀ s ∈ T', s * c = c * s := by
    intro D' T' hs hna hT'
    haveI : Nontrivial T' := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro hbot'
      have h1 := hT'.card_eq
      rw [hbot', Subgroup.card_bot] at h1
      have h2 := s313b_even_card hs hna
      have h3 : 2 ∣ Nat.card D' := even_iff_two_dvd.1 h2
      have h4 : 0 < (Nat.card D').factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h3
      have h5 : (2 : ℕ) ^ (Nat.card D').factorization 2 = 1 := h1.symm
      have := Nat.one_lt_two_pow h4.ne'
      omega
    haveI : Finite T' := inferInstance
    haveI hnc := IsPGroup.center_nontrivial (G := T') hT'.isPGroup
    obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥T'))
    refine ⟨(c.1 : Q), c.1.2, fun h => hc1 (Subtype.ext (Subtype.ext h)), fun s hs => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨s, hs⟩)
  obtain ⟨c₁, hc₁T, hc₁1, hc₁c⟩ := hnt hs₁ hna₁ hT₁
  obtain ⟨c₂, hc₂T, hc₂1, hc₂c⟩ := hnt hs₂ hna₂ hT₂
  have hcen : ∀ {c : Q}, c ∈ T₁ ⊔ T₂ → (∀ s ∈ T₁ ⊔ T₂, s * c = c * s) →
      (g * c * g⁻¹ ∈ T ∧ ∀ t ∈ T, t * (g * c * g⁻¹) = (g * c * g⁻¹) * t) := by
    intro c hc hcc
    refine ⟨?_, fun t ht => ?_⟩
    · rw [hTg]
      exact ⟨c, hc, by simp [MulAut.conj_apply]⟩
    · rw [hTg] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := hcc s hs
      calc g * s * g⁻¹ * (g * c * g⁻¹) = g * (s * c) * g⁻¹ := by group
        _ = g * (c * s) * g⁻¹ := by rw [this]
        _ = g * c * g⁻¹ * (g * s * g⁻¹) := by group
  have hsplit : ∀ s ∈ T₁ ⊔ T₂, ∃ s₁ ∈ T₁, ∃ s₂ ∈ T₂, s = s₁ * s₂ := by
    intro s hs
    have hs' := hs
    rw [← SetLike.mem_coe, (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T₁ T₂ hcT).2] at hs'
    obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := hs'
    exact ⟨s₁, hs₁, s₂, hs₂, hss.symm⟩
  refine ⟨⟨g * c₁ * g⁻¹, ?_, ?_, (hcen (mem_sup_left hc₁T) ?_).1, (hcen (mem_sup_left hc₁T) ?_).2⟩,
    ⟨g * c₂ * g⁻¹, ?_, ?_, (hcen (mem_sup_right hc₂T) ?_).1, (hcen (mem_sup_right hc₂T) ?_).2⟩⟩
  ·
    rw [← hgg', show g₁ * g₂ * c₁ * (g₁ * g₂)⁻¹ = g₁ * (g₂ * c₁ * g₂⁻¹) * g₁⁻¹ by group,
      show g₂ * c₁ * g₂⁻¹ = c₁ by rw [← hc c₁ (hT₁.le hc₁T) g₂ hg₂]; group]
    exact D₁.mul_mem (D₁.mul_mem hg₁ (hT₁.le hc₁T)) (D₁.inv_mem hg₁)
  · intro h
    exact hc₁1 (by simpa using h)
  · intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hsplit s hs
    calc s₁ * s₂ * c₁ = s₁ * (s₂ * c₁) := by group
      _ = s₁ * (c₁ * s₂) := by rw [← hcT c₁ hc₁T s₂ hs₂]
      _ = c₁ * (s₁ * s₂) := by rw [← mul_assoc, hc₁c s₁ hs₁, mul_assoc]
  · intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hsplit s hs
    calc s₁ * s₂ * c₁ = s₁ * (s₂ * c₁) := by group
      _ = s₁ * (c₁ * s₂) := by rw [← hcT c₁ hc₁T s₂ hs₂]
      _ = c₁ * (s₁ * s₂) := by rw [← mul_assoc, hc₁c s₁ hs₁, mul_assoc]
  ·
    rw [← hgg', show g₁ * g₂ * c₂ * (g₁ * g₂)⁻¹ = g₁ * (g₂ * c₂ * g₂⁻¹) * g₁⁻¹ by group]
    have h1 : g₁ * c₂ = c₂ * g₁ := hc g₁ hg₁ c₂ (hT₂.le hc₂T)
    rw [show g₁ * (g₂ * c₂ * g₂⁻¹) * g₁⁻¹ = g₂ * (g₁ * c₂ * g₁⁻¹) * g₂⁻¹ by
      rw [show g₁ * (g₂ * c₂ * g₂⁻¹) * g₁⁻¹ = g₁ * g₂ * c₂ * g₂⁻¹ * g₁⁻¹ by group,
        show g₁ * g₂ * c₂ * g₂⁻¹ * g₁⁻¹ = (g₁ * g₂) * c₂ * (g₁ * g₂)⁻¹ by group,
        show (g₁ * g₂) = g₂ * g₁ from (hc g₁ hg₁ g₂ hg₂)]
      group]
    rw [show g₁ * c₂ * g₁⁻¹ = c₂ by rw [h1]; group]
    exact D₂.mul_mem (D₂.mul_mem hg₂ (hT₂.le hc₂T)) (D₂.inv_mem hg₂)
  · intro h
    exact hc₂1 (by simpa using h)
  · intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hsplit s hs
    calc s₁ * s₂ * c₂ = s₁ * (s₂ * c₂) := by group
      _ = s₁ * (c₂ * s₂) := by rw [hc₂c s₂ hs₂]
      _ = (s₁ * c₂) * s₂ := by group
      _ = (c₂ * s₁) * s₂ := by rw [hcT s₁ hs₁ c₂ hc₂T]
      _ = c₂ * (s₁ * s₂) := by group
  · intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hsplit s hs
    calc s₁ * s₂ * c₂ = s₁ * (s₂ * c₂) := by group
      _ = s₁ * (c₂ * s₂) := by rw [hc₂c s₂ hs₂]
      _ = (s₁ * c₂) * s₂ := by group
      _ = (c₂ * s₁) * s₂ := by rw [hcT s₁ hs₁ c₂ hc₂T]
      _ = c₂ * (s₁ * s₂) := by group

theorem s313b_isSylowOf_map {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem s313b_inf_bot_of_odd {A B : Subgroup Q} (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) :
    A ⊓ B = ⊥ := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA
  have h1 : Nat.card ↥(A ⊓ B) ∣ 2 ^ n := hn ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(A ⊓ B) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.Coprime (2 ^ n) (Nat.card B) := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hB)
  exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2)

theorem s313b_ne_bot_of_nonab {D : Subgroup Q} (hn : ∃ x y : D, x * y ≠ y * x) : D ≠ ⊥ := by
  intro hbot
  obtain ⟨u, v, huv⟩ := hn
  apply huv
  apply Subtype.ext
  have hu : (u : Q) = 1 := Subgroup.mem_bot.1 (hbot ▸ u.2)
  have hv : (v : Q) = 1 := Subgroup.mem_bot.1 (hbot ▸ v.2)
  simp [hu, hv]

end S313bGeneric

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

section S313b

variable (hp : d.ProductCaseHyp) (k12 : d.Know12) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k12 hS hP

theorem s313b_L₂_eq : d.L₂ = d.E ⊔ d.M₂ := k12.s8.1

theorem s313b_M₂_le_L₂ : d.M₂ ≤ d.L₂ := (s313b_L₂_eq hp k12 hS hP) ▸ le_sup_right

theorem s313b_M₂_le_normalizer_E : d.M₂ ≤ normalizer (d.E : Set G) :=
  (s313b_M₂_le_L₂ hp k12 hS hP).trans d.L₂_le_normalizer_E

theorem s313b_E_le_S : d.E ≤ S := (k12.s9_1 S hS hP).1.symm ▸ le_sup_left

theorem s313b_E_inf_M₂ : d.E ⊓ d.M₂ = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := k12.s10_1 S hS hP
  have h2 := (k12.s10_2 S hS hP).2.1.1
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : z ∈ d.E ⊓ (S ⊓ d.M₂) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1, Subgroup.mem_inf.2
      ⟨s313b_E_le_S hp k12 hS hP (Subgroup.mem_inf.1 hz).1, (Subgroup.mem_inf.1 hz).2⟩⟩
  rw [← h2, h11.2] at hz'
  exact hz'

theorem s313b_mem_normalizer_E {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (d.E : Set G) := by
  refine mem_normalizer_fintype fun e he => ?_
  set α : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hchar := (k12.s9_1 S hS hP).2.1
  have hfix : (d.E.subgroupOf S).comap α.toMonoidHom = d.E.subgroupOf S := hchar.fixed α
  have heS : e ∈ S := s313b_E_le_S hp k12 hS hP he
  have hmem : (⟨e, heS⟩ : S) ∈ (d.E.subgroupOf S).comap α.toMonoidHom := by
    rw [hfix]; exact he
  have : (α ⟨e, heS⟩ : G) ∈ d.E := hmem
  simpa [hα] using this

end S313b

section S313bTheta

abbrev s313bH (d : Data G h) : Subgroup G := centralizer (d.I₂ : Set G)

abbrev s313bO (d : Data G h) : Subgroup ↥(s313bH d) := standardComponentOddCore ↥(s313bH d)

abbrev s313bQ (d : Data G h) : Type := ↥(s313bH d) ⧸ s313bO d

open scoped Classical in
def s313bTh (d : Data G h) (g : G) : s313bQ d :=
  if hg : g ∈ s313bH d then QuotientGroup.mk' (s313bO d) ⟨g, hg⟩ else 1

theorem s313bTh_of_mem {g : G} (hg : g ∈ s313bH d) :
    s313bTh d g = QuotientGroup.mk' (s313bO d) ⟨g, hg⟩ := by
  simp [s313bTh, hg]

theorem s313bTh_mul {g g' : G} (hg : g ∈ s313bH d) (hg' : g' ∈ s313bH d) :
    s313bTh d (g * g') = s313bTh d g * s313bTh d g' := by
  rw [s313bTh_of_mem (mul_mem hg hg'), s313bTh_of_mem hg, s313bTh_of_mem hg']
  rfl

theorem s313bTh_one : s313bTh d (1 : G) = 1 := by
  rw [s313bTh_of_mem (one_mem _)]
  rfl

theorem s313bTh_inv {g : G} (hg : g ∈ s313bH d) : s313bTh d g⁻¹ = (s313bTh d g)⁻¹ := by
  rw [s313bTh_of_mem (inv_mem hg), s313bTh_of_mem hg]
  rfl

theorem s313bTh_eq_one_iff {g : G} (hg : g ∈ s313bH d) :
    s313bTh d g = 1 ↔ (⟨g, hg⟩ : ↥(s313bH d)) ∈ s313bO d := by
  rw [s313bTh_of_mem hg]
  exact QuotientGroup.eq_one_iff _

theorem s313bTh_conj {m g : G} (hm : m ∈ s313bH d) (hg : g ∈ s313bH d) :
    s313bTh d (m * g * m⁻¹) = s313bTh d m * s313bTh d g * (s313bTh d m)⁻¹ := by
  rw [s313bTh_mul (mul_mem hm hg) (inv_mem hm), s313bTh_mul hm hg, s313bTh_inv hm]

theorem s313bTh_comm {a b : G} (ha : a ∈ s313bH d) (hb : b ∈ s313bH d) :
    s313bTh d (a * b * a⁻¹ * b⁻¹) =
      s313bTh d a * s313bTh d b * (s313bTh d a)⁻¹ * (s313bTh d b)⁻¹ := by
  rw [s313bTh_mul (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb),
    s313bTh_mul (mul_mem ha hb) (inv_mem ha), s313bTh_mul ha hb, s313bTh_inv ha, s313bTh_inv hb]

theorem s313bM₂_le_H (d : Data G h) : d.M₂ ≤ s313bH d := Subgroup.map_subtype_le _

def s313bK (d : Data G h) : Subgroup G := d.M₂ ⊓ (s313bO d).map (s313bH d).subtype

theorem s313bmem_K_iff {m : G} : m ∈ s313bK d ↔ m ∈ d.M₂ ∧ s313bTh d m = 1 := by
  constructor
  · rintro ⟨hm, o, ho, rfl⟩
    refine ⟨hm, ?_⟩
    show s313bTh d (o : G) = 1
    rw [s313bTh_eq_one_iff o.2]
    exact ho
  · rintro ⟨hm, h1⟩
    refine ⟨hm, ⟨m, s313bM₂_le_H d hm⟩, (s313bTh_eq_one_iff (s313bM₂_le_H d hm)).1 h1, rfl⟩

theorem s313bK_le_M₂ : s313bK d ≤ d.M₂ := inf_le_left

theorem s313bM₂_le_normalizer_K : d.M₂ ≤ normalizer ((s313bK d : Subgroup G) : Set G) := by
  intro m hm
  refine mem_normalizer_fintype fun k hk => ?_
  obtain ⟨hkM, hk1⟩ := s313bmem_K_iff.1 hk
  refine s313bmem_K_iff.2 ⟨mul_mem (mul_mem hm hkM) (inv_mem hm), ?_⟩
  rw [s313bTh_conj (s313bM₂_le_H d hm) (s313bM₂_le_H d hkM), hk1, mul_one, mul_inv_cancel]

theorem s313bK_odd : Odd (Nat.card (s313bK d)) := by
  have h1 : Nat.card ((s313bO d).map (s313bH d).subtype) = Nat.card (s313bO d) :=
    Subgroup.card_map_of_injective (s313bH d).subtype_injective
  have h2 : Odd (Nat.card (s313bO d)) := GMSK.odd_card_standardComponentOddCore ↥(s313bH d)
  refine Odd.of_dvd_nat (h1 ▸ h2) (Subgroup.card_dvd_of_le inf_le_right)

def s313bImg (d : Data G h) (Z : Subgroup G) : Subgroup (s313bQ d) :=
  (Z.subgroupOf (s313bH d)).map (QuotientGroup.mk' (s313bO d))

theorem s313bmem_img_iff {Z : Subgroup G} (hZ : Z ≤ s313bH d) {x : s313bQ d} :
    x ∈ s313bImg d Z ↔ ∃ z ∈ Z, s313bTh d z = x := by
  constructor
  · rintro ⟨⟨z, hzH⟩, hz, rfl⟩
    exact ⟨z, hz, s313bTh_of_mem hzH⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hZ hz⟩, hz, (s313bTh_of_mem (hZ hz)).symm⟩

def s313bPre (d : Data G h) (D' : Subgroup (s313bQ d)) : Subgroup G :=
  d.M₂ ⊓ (D'.comap (QuotientGroup.mk' (s313bO d))).map (s313bH d).subtype

theorem s313bmem_Pre_iff {D' : Subgroup (s313bQ d)} {m : G} :
    m ∈ s313bPre d D' ↔ m ∈ d.M₂ ∧ s313bTh d m ∈ D' := by
  constructor
  · rintro ⟨hm, o, ho, rfl⟩
    refine ⟨hm, ?_⟩
    rw [show ((s313bH d).subtype o : G) = (o : G) from rfl, s313bTh_of_mem o.2]
    exact ho
  · rintro ⟨hm, hD⟩
    refine ⟨hm, ⟨m, s313bM₂_le_H d hm⟩, ?_, rfl⟩
    rw [s313bTh_of_mem (s313bM₂_le_H d hm)] at hD
    exact hD

theorem s313bPre_le_M₂ (D' : Subgroup (s313bQ d)) : s313bPre d D' ≤ d.M₂ := inf_le_left

end S313bTheta

section S313bLayer

variable (hp : d.ProductCaseHyp)
include hp

theorem s313b_map_M₂ :
    (d.M₂.subgroupOf (s313bH d)).map (QuotientGroup.mk' (s313bO d)) =
      CFSG.layer (s313bQ d) :=
  (hp.hyp.sec3_3_two hp.gms).2

theorem s313b_th_mem_layer {m : G} (hm : m ∈ d.M₂) :
    s313bTh d m ∈ CFSG.layer (s313bQ d) := by
  rw [← s313b_map_M₂ hp, s313bTh_of_mem (s313bM₂_le_H d hm)]
  exact ⟨⟨m, s313bM₂_le_H d hm⟩, hm, rfl⟩

theorem s313b_exists_th_eq {x : s313bQ d} (hx : x ∈ CFSG.layer (s313bQ d)) :
    ∃ m ∈ d.M₂, s313bTh d m = x := by
  rw [← s313b_map_M₂ hp] at hx
  obtain ⟨⟨m, hmH⟩, hm, rfl⟩ := hx
  exact ⟨m, hm, s313bTh_of_mem hmH⟩

theorem s313b_layer_product :
    ∃ D₁ D₂ : Subgroup (s313bQ d), IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
      IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x) ∧
      (∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) ∧ D₁ ⊓ D₂ = ⊥ ∧
      D₁ ⊔ D₂ = CFSG.layer (s313bQ d) := by
  obtain ⟨⟨-, -, -, hncl, -, halt, -⟩, -⟩ := (hp.hyp.sec3_3_two hp.gms).1
  rcases halt with ⟨hA, -⟩ | ⟨⟨D₁, D₂, -, -, -, hs₁, hn₁, hs₂, hn₂, hsup, hinf, hcomm, -⟩, -⟩
  · exfalso
    have h1 := hA.1
    rw [hncl] at h1
    exact hp.caseB h1
  · refine ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, fun x hx y hy => ?_, hinf, hsup.trans hncl⟩
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx
    exact (mem_centralizer_iff.1 this y hy).symm

end S313bLayer

section S313bTyp

def S313bOdd (d : Data G h) (Y : Subgroup G) : Prop :=
  d.E ≤ Y ∧ Y ≤ d.L₂ ∧ d.L₂ ≤ normalizer (Y : Set G) ∧ Odd (d.E.relIndex Y)

def S313bTyp (d : Data G h) (g : G) : Prop :=
  ∃ N : Subgroup G, N ≤ d.L₂ ∧ d.L₂ ≤ normalizer (N : Set G) ∧
    (∀ Y, S313bOdd d Y → ¬ N ≤ Y) ∧ ∃ Y, S313bOdd d Y ∧ ∀ n ∈ N, n * g * n⁻¹ * g⁻¹ ∈ Y

theorem s313bOdd_map_conj {j : G} (hjE : j ∈ normalizer (d.E : Set G))
    (hjL : j ∈ normalizer (d.L₂ : Set G)) {Y : Subgroup G} (hY : S313bOdd d Y) :
    S313bOdd d (Y.map (MulAut.conj j).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    have hE' : j⁻¹ * e * j ∈ d.E := by
      have := (mem_normalizer_iff.1 (inv_mem hjE) e).1 he
      simpa using this
    refine ⟨j⁻¹ * e * j, hY.1 hE', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hjL y).1 (hY.2.1 hy)
  · intro l hl
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have hl' : j⁻¹ * l * j ∈ d.L₂ := by
      have := (mem_normalizer_iff.1 (inv_mem hjL) l).1 hl
      simpa using this
    have := (mem_normalizer_iff.1 (hY.2.2.1 hl') y).1 hy
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [← map_conj_eq_of_mem_normalizer hjE,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj j).injective]
    exact hY.2.2.2

theorem s313bTyp_conj {j : G} (hjE : j ∈ normalizer (d.E : Set G))
    (hjL : j ∈ normalizer (d.L₂ : Set G)) {g : G} (hg : S313bTyp d g) :
    S313bTyp d (j * g * j⁻¹) := by
  obtain ⟨N, hNL, hNn, hNY, Y, hY, hcomm⟩ := hg
  have hjE' : j⁻¹ ∈ normalizer (d.E : Set G) := inv_mem hjE
  have hjL' : j⁻¹ ∈ normalizer (d.L₂ : Set G) := inv_mem hjL
  refine ⟨N.map (MulAut.conj j).toMonoidHom, ?_, ?_, ?_,
    Y.map (MulAut.conj j).toMonoidHom, s313bOdd_map_conj hjE hjL hY, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff.1 hjL n).1 (hNL hn)
  · intro l hl
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨n, hn, rfl⟩ := hz
    have hl' : j⁻¹ * l * j ∈ d.L₂ := by
      have := (mem_normalizer_iff.1 hjL' l).1 hl
      simpa using this
    have := (mem_normalizer_iff.1 (hNn hl') n).1 hn
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro Y' hY' hle
    have hY'' := s313bOdd_map_conj hjE' hjL' hY'
    refine hNY _ hY'' fun n hn => ?_
    have := hle ⟨n, hn, rfl⟩
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨_, hcomm n hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem s313bTyp_mul_left {w g : G} (hw : w ∈ d.E) (hg : S313bTyp d (w * g)) : S313bTyp d g := by
  obtain ⟨N, hNL, hNn, hNY, Y, hY, hcomm⟩ := hg
  refine ⟨N, hNL, hNn, hNY, Y, hY, fun n hn => ?_⟩
  have hnE : n ∈ normalizer (d.E : Set G) := d.L₂_le_normalizer_E (hNL hn)
  have hnw : n * w⁻¹ * n⁻¹ ∈ d.E := (mem_normalizer_iff.1 hnE w⁻¹).1 (inv_mem hw)
  have e : n * g * n⁻¹ * g⁻¹ = (n * w⁻¹ * n⁻¹) * (n * (w * g) * n⁻¹ * (w * g)⁻¹) * w := by group
  rw [e]
  exact mul_mem (mul_mem (hY.1 hnw) (hcomm n hn)) (hY.1 hw)

section S313bOddLemmas

variable (hp : d.ProductCaseHyp) (k12 : d.Know12) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k12 hS hP

theorem s313b_K_le_normalizer_E : s313bK d ≤ normalizer (d.E : Set G) :=
  (s313bK_le_M₂).trans (s313b_M₂_le_normalizer_E hp k12 hS hP)

theorem s313bOdd_Ohat : S313bOdd d (d.E ⊔ s313bK d) := by
  have hEL : d.E ≤ d.L₂ := d.E_le_L₂
  have hKL : s313bK d ≤ d.L₂ := s313bK_le_M₂.trans (s313b_M₂_le_L₂ hp k12 hS hP)
  refine ⟨le_sup_left, sup_le hEL hKL, ?_, ?_⟩
  · rw [s313b_L₂_eq hp k12 hS hP]
    refine sup_le (fun e he => Subgroup.le_normalizer (mem_sup_left he)) fun m hm => ?_
    exact Common.mem_normalizer_sup (s313b_M₂_le_normalizer_E hp k12 hS hP hm)
      (s313bM₂_le_normalizer_K hm)
  · have h1 := Subgroup.relIndex_mul_card d.E (d.E ⊔ s313bK d)
    rw [inf_eq_left.2 (le_sup_left : d.E ≤ d.E ⊔ s313bK d)] at h1
    have h2 := Common.card_sup_mul_card_inf_eq (s313b_K_le_normalizer_E hp k12 hS hP)
    have hbot : d.E ⊓ s313bK d = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      have : z ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1,
        s313bK_le_M₂ (Subgroup.mem_inf.1 hz).2⟩
      rwa [s313b_E_inf_M₂ hp k12 hS hP] at this
    rw [hbot, Subgroup.card_bot, mul_one] at h2
    have hE : 0 < Nat.card d.E := Nat.card_pos
    have h3 : d.E.relIndex (d.E ⊔ s313bK d) = Nat.card (s313bK d) := by
      refine Nat.eq_of_mul_eq_mul_right hE ?_
      rw [h1, h2, mul_comm]
    rw [h3]
    exact s313bK_odd

theorem s313b_inf_le_K {Y : Subgroup G} (hY : S313bOdd d Y) : Y ⊓ d.M₂ ≤ s313bK d := by
  obtain ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, hc, hi, hsup⟩ := s313b_layer_product hp
  set Z : Subgroup G := Y ⊓ d.M₂ with hZ
  have hZM : Z ≤ d.M₂ := inf_le_right
  have hZH : Z ≤ s313bH d := hZM.trans (s313bM₂_le_H d)
  have hM₂Y : d.M₂ ≤ normalizer (Y : Set G) :=
    (s313b_M₂_le_L₂ hp k12 hS hP).trans hY.2.2.1
  have hZodd : Odd (Nat.card Z) := by
    have hZE : Z ≤ normalizer (d.E : Set G) := hZM.trans (s313b_M₂_le_normalizer_E hp k12 hS hP)
    have h2 := Common.card_sup_mul_card_inf_eq hZE
    have hbot : d.E ⊓ Z = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      have : z ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1,
        hZM (Subgroup.mem_inf.1 hz).2⟩
      rwa [s313b_E_inf_M₂ hp k12 hS hP] at this
    rw [hbot, Subgroup.card_bot, mul_one] at h2
    have hle : d.E ⊔ Z ≤ Y := sup_le hY.1 inf_le_left
    have h3 := Subgroup.card_dvd_of_le hle
    have h4 := Subgroup.relIndex_mul_card d.E Y
    rw [inf_eq_left.2 hY.1] at h4
    rw [h2, ← h4, mul_comm (d.E.relIndex Y)] at h3
    have h5 : Nat.card Z ∣ d.E.relIndex Y := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h3
    exact Odd.of_dvd_nat hY.2.2.2 h5
  set T := s313bImg d Z with hT
  have hTle : T ≤ D₁ ⊔ D₂ := by
    rw [hsup]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (s313bmem_img_iff hZH).1 hx
    exact s313b_th_mem_layer hp (hZM hz)
  have hTn : D₁ ⊔ D₂ ≤ normalizer (T : Set (s313bQ d)) := by
    rw [hsup]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := s313b_exists_th_eq hp hx
    refine mem_normalizer_fintype fun t ht => ?_
    obtain ⟨z, hz, rfl⟩ := (s313bmem_img_iff hZH).1 ht
    refine (s313bmem_img_iff hZH).2 ⟨m * z * m⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hM₂Y hm) z).1 (Subgroup.mem_inf.1 hz).1,
        mul_mem (mul_mem hm (hZM hz)) (inv_mem hm)⟩
    · exact s313bTh_conj (s313bM₂_le_H d hm) (hZH hz)
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T ∣ Nat.card (Z.subgroupOf (s313bH d)) :=
      (Z.subgroupOf (s313bH d)).card_map_dvd (QuotientGroup.mk' (s313bO d))
    have h2 : Nat.card (Z.subgroupOf (s313bH d)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hZodd h1
  have hT1 : T = ⊥ := s313b_odd_normal_trivial hs₁ hn₁ hs₂ hn₂ hc hTle hTn hTodd
  intro z hz
  have hzM : z ∈ d.M₂ := hZM hz
  refine s313bmem_K_iff.2 ⟨hzM, ?_⟩
  have : s313bTh d z ∈ T := (s313bmem_img_iff hZH).2 ⟨z, hz, rfl⟩
  rw [hT1] at this
  exact this

theorem s313bTyp_of_normal {D' : Subgroup (s313bQ d)} (hD'le : D' ≤ CFSG.layer (s313bQ d))
    (hD'n : CFSG.layer (s313bQ d) ≤ normalizer (D' : Set (s313bQ d))) (hD'1 : D' ≠ ⊥)
    {x : G} (hx : x ∈ d.M₂) (hxc : ∀ u ∈ D', u * s313bTh d x = s313bTh d x * u) :
    S313bTyp d x := by
  have hPre_le : s313bPre d D' ≤ d.M₂ := s313bPre_le_M₂ D'
  have hPreE : s313bPre d D' ≤ normalizer (d.E : Set G) :=
    hPre_le.trans (s313b_M₂_le_normalizer_E hp k12 hS hP)
  have hM₂Pre : d.M₂ ≤ normalizer ((s313bPre d D' : Subgroup G) : Set G) := by
    intro m hm
    refine mem_normalizer_fintype fun p hp' => ?_
    obtain ⟨hpM, hpD⟩ := s313bmem_Pre_iff.1 hp'
    refine s313bmem_Pre_iff.2 ⟨mul_mem (mul_mem hm hpM) (inv_mem hm), ?_⟩
    rw [s313bTh_conj (s313bM₂_le_H d hm) (s313bM₂_le_H d hpM)]
    have hm' : s313bTh d m ∈ normalizer (D' : Set (s313bQ d)) :=
      hD'n (s313b_th_mem_layer hp hm)
    exact (mem_normalizer_iff.1 hm' _).1 hpD
  refine ⟨d.E ⊔ s313bPre d D', sup_le d.E_le_L₂ (hPre_le.trans (s313b_M₂_le_L₂ hp k12 hS hP)),
    ?_, ?_, d.E ⊔ s313bK d, s313bOdd_Ohat hp k12 hS hP, ?_⟩
  · rw [s313b_L₂_eq hp k12 hS hP]
    refine sup_le (fun e he => Subgroup.le_normalizer (mem_sup_left he)) fun m hm => ?_
    exact Common.mem_normalizer_sup (s313b_M₂_le_normalizer_E hp k12 hS hP hm) (hM₂Pre hm)
  · intro Y hY hle
    obtain ⟨u₀, hu₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD'1
    obtain ⟨m₀, hm₀, hm₀u⟩ := s313b_exists_th_eq hp (hD'le u₀.2)
    have hm₀N : m₀ ∈ d.E ⊔ s313bPre d D' :=
      mem_sup_right (s313bmem_Pre_iff.2 ⟨hm₀, hm₀u ▸ u₀.2⟩)
    have hK := s313b_inf_le_K hp k12 hS hP hY (Subgroup.mem_inf.2 ⟨hle hm₀N, hm₀⟩)
    have := (s313bmem_K_iff.1 hK).2
    rw [hm₀u] at this
    exact hu₀1 (Subtype.ext this)
  · intro n hn
    obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPreE hn
    obtain ⟨hmM, hmD⟩ := s313bmem_Pre_iff.1 hm
    have hxE : x ∈ normalizer (d.E : Set G) := s313b_M₂_le_normalizer_E hp k12 hS hP hx
    have hc : m * x * m⁻¹ * x⁻¹ ∈ s313bK d := by
      refine s313bmem_K_iff.2 ⟨mul_mem (mul_mem (mul_mem hmM hx) (inv_mem hmM)) (inv_mem hx), ?_⟩
      rw [s313bTh_comm (s313bM₂_le_H d hmM) (s313bM₂_le_H d hx)]
      have := hxc _ hmD
      rw [this]
      group
    have hf : x * e⁻¹ * x⁻¹ ∈ d.E := (mem_normalizer_iff.1 hxE e⁻¹).1 (inv_mem he)
    have e1 : e * m * x * (e * m)⁻¹ * x⁻¹ = e * (m * x * m⁻¹ * x⁻¹) * (x * e⁻¹ * x⁻¹) := by
      group
    rw [show e * m * x * (e * m)⁻¹ * x⁻¹ = e * (m * x * m⁻¹ * x⁻¹) * (x * e⁻¹ * x⁻¹) from e1]
    exact mul_mem (mul_mem (mem_sup_left he) (mem_sup_right hc)) (mem_sup_left hf)

theorem s313b_not_Typ {D₁ D₂ : Subgroup (s313bQ d)} (hs₁ : IsSimpleGroup D₁)
    (hn₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hn₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hsup : D₁ ⊔ D₂ = CFSG.layer (s313bQ d)) {y : G} (hy : y ∈ d.M₂)
    {a b : s313bQ d} (ha : a ∈ D₁) (hb : b ∈ D₂) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hyab : s313bTh d y = a * b) : ¬ S313bTyp d y := by
  rintro ⟨N, hNL, hNn, hNY, Y₀, hY₀, hcomm⟩
  have hM₂E := s313b_M₂_le_normalizer_E hp k12 hS hP
  have hNÔ : ¬ N ≤ d.E ⊔ s313bK d := hNY _ (s313bOdd_Ohat hp k12 hS hP)
  obtain ⟨n₀, hn₀N, hn₀Ô⟩ := SetLike.not_le_iff_exists.1 hNÔ
  have hn₀L : n₀ ∈ d.L₂ := hNL hn₀N
  rw [s313b_L₂_eq hp k12 hS hP] at hn₀L
  obtain ⟨e, he, m₀, hm₀, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hM₂E hn₀L
  have hNE : N ≤ normalizer (d.E : Set G) := hNL.trans d.L₂_le_normalizer_E
  have hENn : d.L₂ ≤ normalizer ((d.E ⊔ N : Subgroup G) : Set G) :=
    fun g hg => Common.mem_normalizer_sup (d.L₂_le_normalizer_E hg) (hNn hg)
  set NM : Subgroup G := (d.E ⊔ N) ⊓ d.M₂ with hNM
  have hNMM : NM ≤ d.M₂ := inf_le_right
  have hNMH : NM ≤ s313bH d := hNMM.trans (s313bM₂_le_H d)
  have hm₀NM : m₀ ∈ NM := Subgroup.mem_inf.2 ⟨by
    have := mul_mem (inv_mem (mem_sup_left he : e ∈ d.E ⊔ N)) (mem_sup_right hn₀N : e * m₀ ∈ d.E ⊔ N)
    simpa using this, hm₀⟩
  have hth1 : s313bTh d m₀ ≠ 1 := by
    intro h1
    exact hn₀Ô (mul_mem (mem_sup_left he) (mem_sup_right (s313bmem_K_iff.2 ⟨hm₀, h1⟩)))
  set T := s313bImg d NM with hT
  have hthT : s313bTh d m₀ ∈ T := (s313bmem_img_iff hNMH).2 ⟨m₀, hm₀NM, rfl⟩
  have hT1 : T ≠ ⊥ := by
    intro hb'
    rw [hb', Subgroup.mem_bot] at hthT
    exact hth1 hthT
  have hTle : T ≤ D₁ ⊔ D₂ := by
    rw [hsup]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (s313bmem_img_iff hNMH).1 hx
    exact s313b_th_mem_layer hp (hNMM hz)
  have hTn : D₁ ⊔ D₂ ≤ normalizer (T : Set (s313bQ d)) := by
    rw [hsup]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := s313b_exists_th_eq hp hx
    refine mem_normalizer_fintype fun t ht => ?_
    obtain ⟨z, hz, rfl⟩ := (s313bmem_img_iff hNMH).1 ht
    refine (s313bmem_img_iff hNMH).2 ⟨m * z * m⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hENn ((s313b_M₂_le_L₂ hp k12 hS hP) hm)) z).1
          (Subgroup.mem_inf.1 hz).1, mul_mem (mul_mem hm (hNMM hz)) (inv_mem hm)⟩
    · exact s313bTh_conj (s313bM₂_le_H d hm) (hNMH hz)
  have hcen : ∀ t ∈ T, t * (a * b) = (a * b) * t := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := (s313bmem_img_iff hNMH).1 ht
    obtain ⟨hzEN, hzM⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨e', he', n, hn, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hNE hzEN
    have hyE : y ∈ normalizer (d.E : Set G) := hM₂E hy
    have hf : y * e'⁻¹ * y⁻¹ ∈ d.E := (mem_normalizer_iff.1 hyE e'⁻¹).1 (inv_mem he')
    have e1 : e' * n * y * (e' * n)⁻¹ * y⁻¹ = e' * (n * y * n⁻¹ * y⁻¹) * (y * e'⁻¹ * y⁻¹) := by
      group
    have hY : e' * n * y * (e' * n)⁻¹ * y⁻¹ ∈ Y₀ := by
      rw [e1]
      exact mul_mem (mul_mem (hY₀.1 he') (hcomm n hn)) (hY₀.1 hf)
    have hYM : e' * n * y * (e' * n)⁻¹ * y⁻¹ ∈ d.M₂ :=
      mul_mem (mul_mem (mul_mem hzM hy) (inv_mem hzM)) (inv_mem hy)
    have hK := s313b_inf_le_K hp k12 hS hP hY₀ (Subgroup.mem_inf.2 ⟨hY, hYM⟩)
    have h1 := (s313bmem_K_iff.1 hK).2
    rw [s313bTh_comm (s313bM₂_le_H d hzM) (s313bM₂_le_H d hy), hyab] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  exact s313b_not_centralizes hs₁ hn₁ hs₂ hn₂ hc hTle hTn hT1 ha hb ha1 hb1 hcen

theorem s313b_exists_xy {D₁ D₂ : Subgroup (s313bQ d)} (hs₁ : IsSimpleGroup D₁)
    (hn₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hn₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hi : D₁ ⊓ D₂ = ⊥) (hsup : D₁ ⊔ D₂ = CFSG.layer (s313bQ d)) :
    ∃ x y : G, x ∈ d.F ⊓ d.M₂ ∧ y ∈ d.F ⊓ d.M₂ ∧ ∃ a b : s313bQ d, a ∈ D₁ ∧ b ∈ D₂ ∧
      a ≠ 1 ∧ b ≠ 1 ∧ s313bTh d x = a ∧ s313bTh d y = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := S ⊓ d.M₂ with hR
  have hRsyl : IsSylowOf 2 R d.M₂ := (k12.s10_2 S hS hP).2.1.2
  have hZ₀ : d.F ⊓ d.M₂ = CFSG.centerIn R := (k12.s10_2 S hS hP).2.2.2.2.1
  have hRM : R ≤ d.M₂ := hRsyl.le
  have hRH : R ≤ s313bH d := hRM.trans (s313bM₂_le_H d)
  have hTsyl : IsSylowOf 2 (s313bImg d R) (D₁ ⊔ D₂) := by
    have h1 : IsSylowOf 2 (R.subgroupOf (s313bH d)) (d.M₂.subgroupOf (s313bH d)) := by
      refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (s313bH d)).1 ?_
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 hRH, inf_eq_left.2 (s313bM₂_le_H d)]
      exact hRsyl
    have h2 := s313b_isSylowOf_map h1 (QuotientGroup.mk' (s313bO d))
    have h3 : (d.M₂.subgroupOf (s313bH d)).map (QuotientGroup.mk' (s313bO d)) = D₁ ⊔ D₂ := by
      rw [hsup]; exact s313b_map_M₂ hp
    rw [h3] at h2
    exact h2
  obtain ⟨⟨z₁, hz₁D, hz₁1, hz₁T, hz₁c⟩, ⟨z₂, hz₂D, hz₂1, hz₂T, hz₂c⟩⟩ :=
    s313b_sylow_center hs₁ hn₁ hs₂ hn₂ hc hi hTsyl
  have hRK : R ⊓ s313bK d = ⊥ := s313b_inf_bot_of_odd hRsyl.isPGroup s313bK_odd
  have hlift : ∀ z ∈ s313bImg d R, (∀ t ∈ s313bImg d R, t * z = z * t) →
      ∃ r ∈ d.F ⊓ d.M₂, s313bTh d r = z := by
    intro z hz hzc
    obtain ⟨r, hrR, rfl⟩ := (s313bmem_img_iff hRH).1 hz
    refine ⟨r, ?_, rfl⟩
    rw [hZ₀]
    refine ⟨hrR, mem_centralizer_iff.2 fun r' hr' => ?_⟩
    have hc1 : r' * r * r'⁻¹ * r⁻¹ ∈ R ⊓ s313bK d := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hr' hrR) (inv_mem hr')) (inv_mem hrR),
        s313bmem_K_iff.2 ⟨mul_mem (mul_mem (mul_mem (hRM hr') (hRM hrR)) (inv_mem (hRM hr')))
          (inv_mem (hRM hrR)), ?_⟩⟩
      rw [s313bTh_comm (hRH hr') (hRH hrR)]
      have := hzc _ ((s313bmem_img_iff hRH).2 ⟨r', hr', rfl⟩)
      rw [this]
      group
    rw [hRK, Subgroup.mem_bot] at hc1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc1)
  obtain ⟨x, hxZ, hxz⟩ := hlift z₁ hz₁T hz₁c
  obtain ⟨x', hx'Z, hx'z⟩ := hlift z₂ hz₂T hz₂c
  refine ⟨x, x * x', hxZ, mul_mem hxZ hx'Z, z₁, z₂, hz₁D, hz₂D, hz₁1, hz₂1, hxz, ?_⟩
  rw [s313bTh_mul (s313bM₂_le_H d (Subgroup.mem_inf.1 hxZ).2)
    (s313bM₂_le_H d (Subgroup.mem_inf.1 hx'Z).2), hxz, hx'z]

end S313bOddLemmas
end S313bTyp

theorem sec313NotTrans_of_hyp (hp : d.ProductCaseHyp) (k : d.Know12) : d.Sec313NotTrans := by
  intro S hS hP J _ hJle htrans
  obtain ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, hc, hi, hsup⟩ := s313b_layer_product hp
  obtain ⟨x, y, hxZ, hyZ, a, b, ha, hb, ha1, hb1, hthx, hthy⟩ :=
    s313b_exists_xy hp k hS hP hs₁ hn₁ hs₂ hn₂ hc hi hsup
  have hJS : J ≤ normalizer (S : Set G) := (hJle.trans inf_le_left).trans inf_le_left
  have hJE : ∀ j ∈ J, j ∈ normalizer (d.E : Set G) := fun j hj =>
    s313b_mem_normalizer_E hp k hS hP (hJS hj)
  have hJL : ∀ j ∈ J, j ∈ normalizer (d.L₂ : Set G) := fun j hj =>
    d.normalizer_E_le_normalizer_L₂ (hJE j hj)
  obtain ⟨hxF, hxM⟩ := Subgroup.mem_inf.1 hxZ
  obtain ⟨hyF, hyM⟩ := Subgroup.mem_inf.1 hyZ
  have hWE : d.W ≤ d.E := d.W_le_E
  have hxW : x ∉ d.W := by
    intro hxW
    have : x ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨hWE hxW, hxM⟩
    rw [s313b_E_inf_M₂ hp k hS hP, Subgroup.mem_bot] at this
    rw [this, s313bTh_one] at hthx
    exact ha1 hthx.symm
  have hyW : y ∉ d.W := by
    intro hyW
    have : y ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨hWE hyW, hyM⟩
    rw [s313b_E_inf_M₂ hp k hS hP, Subgroup.mem_bot] at this
    rw [this, s313bTh_one] at hthy
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hthy.symm
    have : b ∈ D₁ ⊓ D₂ := Subgroup.mem_inf.2 ⟨hb' ▸ D₁.inv_mem ha, hb⟩
    rw [hi, Subgroup.mem_bot] at this
    exact hb1 this
  obtain ⟨j, hj, hjxy⟩ := htrans x hxF hxW y hyF hyW
  have hD₂le : D₂ ≤ CFSG.layer (s313bQ d) := hsup ▸ le_sup_right
  have hD₂n : CFSG.layer (s313bQ d) ≤ normalizer (D₂ : Set (s313bQ d)) := by
    rw [← hsup]
    refine sup_le (fun g hg => Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun u hu => (hc g hg u hu).symm)) Subgroup.le_normalizer
  have hTx : S313bTyp d x :=
    s313bTyp_of_normal hp k hS hP hD₂le hD₂n (s313b_ne_bot_of_nonab hn₂) hxM
      (fun u hu => by rw [hthx]; exact (hc a ha u hu).symm)
  have hTj := s313bTyp_conj (hJE j hj) (hJL j hj) hTx
  have hw : (j * x * j⁻¹) * y⁻¹ ∈ d.E := hWE hjxy
  have hTy : S313bTyp d y := by
    refine s313bTyp_mul_left hw ?_
    rwa [show (j * x * j⁻¹) * y⁻¹ * y = j * x * j⁻¹ by group]
  exact s313b_not_Typ hp k hS hP hs₁ hn₁ hs₂ hn₂ hc hsup hyM ha hb ha1 hb1 hthy hTy

end Data

namespace CaseBParts

theorem sec313NotTrans : Sec313NotTransStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec313NotTrans_of_hyp hp k

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
