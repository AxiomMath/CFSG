module

public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def omegaOnePreimage (B S : Subgroup G) [(S.subgroupOf B).Normal] (r : ℕ)
    (hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a) : Subgroup G where
  carrier := {x | x ∈ B ∧ x ^ r ∈ S}
  one_mem' := ⟨B.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxB, hxr⟩ ⟨hyB, hyr⟩
    refine ⟨B.mul_mem hxB hyB, ?_⟩
    have hxQ : ((QuotientGroup.mk' (S.subgroupOf B)) ⟨x, hxB⟩) ^ r = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxr
    have hyQ : ((QuotientGroup.mk' (S.subgroupOf B)) ⟨y, hyB⟩) ^ r = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hyr
    have hxy : (QuotientGroup.mk' (S.subgroupOf B)) ⟨x * y, B.mul_mem hxB hyB⟩ =
        (QuotientGroup.mk' (S.subgroupOf B)) ⟨x, hxB⟩ *
          (QuotientGroup.mk' (S.subgroupOf B)) ⟨y, hyB⟩ := rfl
    have hc : Commute ((QuotientGroup.mk' (S.subgroupOf B)) ⟨x, hxB⟩)
        ((QuotientGroup.mk' (S.subgroupOf B)) ⟨y, hyB⟩) := hab _ _
    have hQ : ((QuotientGroup.mk' (S.subgroupOf B)) ⟨x * y, B.mul_mem hxB hyB⟩) ^ r = 1 := by
      rw [hxy, hc.mul_pow, hxQ, hyQ, mul_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hQ
    exact hQ
  inv_mem' := by
    rintro x ⟨hxB, hxr⟩
    exact ⟨B.inv_mem hxB, by rw [inv_pow]; exact S.inv_mem hxr⟩

theorem omegaOnePreimage_le (B S : Subgroup G) [(S.subgroupOf B).Normal] (r : ℕ)
    (hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a) :
    omegaOnePreimage B S r hab ≤ B := fun _ hx => hx.1

theorem le_omegaOnePreimage {B S : Subgroup G} [(S.subgroupOf B).Normal] {r : ℕ}
    (hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a) (hSB : S ≤ B) :
    S ≤ omegaOnePreimage B S r hab := by
  intro s hs
  exact ⟨hSB hs, S.pow_mem hs r⟩

theorem omegaOnePreimage_normalizer {B S T : Subgroup G} [(S.subgroupOf B).Normal] {r : ℕ}
    (hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a) (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) :
    T ≤ Subgroup.normalizer (omegaOnePreimage B S r hab : Set G) := by
  have hconj : ∀ t : G, ∀ x : G, (t * x * t⁻¹) ^ r = t * x ^ r * t⁻¹ := by
    intro t x
    have h := map_pow (MulAut.conj t) x r
    rw [MulAut.conj_apply, MulAut.conj_apply] at h
    exact h.symm
  intro t ht
  have hmem : ∀ x : G, x ∈ omegaOnePreimage B S r hab ↔
      t * x * t⁻¹ ∈ omegaOnePreimage B S r hab := by
    intro x
    constructor
    · rintro ⟨hxB, hxr⟩
      refine ⟨Subgroup.mem_normalizer_iff.1 (hTB ht) x |>.1 hxB, ?_⟩
      rw [hconj]
      exact Subgroup.mem_normalizer_iff.1 (hTS ht) _ |>.1 hxr
    · rintro ⟨hxB, hxr⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hTB ht) x).2 hxB, by
        have h1 : (t * x * t⁻¹) ^ r ∈ S := hxr
        rw [hconj] at h1
        exact (Subgroup.mem_normalizer_iff.1 (hTS ht) (x ^ r)).2 h1⟩
  rw [Subgroup.mem_normalizer_iff]
  exact hmem

theorem set_mul_assoc' (A B C : Set G) : (A * B) * C = A * (B * C) := by
  ext x
  simp only [Set.mem_mul]
  constructor
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b * c, ⟨b, hb, c, hc, rfl⟩, (mul_assoc a b c).symm⟩
  · rintro ⟨a, ha, y, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, c, hc, mul_assoc a b c⟩

theorem set_mul_comm_of_le_normalizer {H T : Subgroup G}
    (h : T ≤ Subgroup.normalizer (H : Set G)) :
    (H : Set G) * (T : Set G) = (T : Set G) * (H : Set G) := by
  ext x
  simp only [Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, b⁻¹ * a * b,
      by simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (h hb)) a).1 ha,
      by group⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨b * a * b⁻¹, Subgroup.mem_normalizer_iff.1 (h hb) a |>.1 ha, b, hb, by group⟩

theorem exists_elemAbelian_permutes_of_abelian_quotient {B S T : Subgroup G}
    [(S.subgroupOf B).Normal] {r : ℕ}
    (hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a) (hSB : S ≤ B) (hST : S ≤ T)
    (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hTS : T ≤ Subgroup.normalizer (S : Set G))
    (hr : r.Prime) (hr2 : r ≠ 2) (hS2 : IsPGroup 2 S) :
    ∃ E : Subgroup G, E ≤ B ∧ CFSG.Open.IsElemAbelian r E ∧
      Nat.card E = r ^ CFSG.Open.pRank r B ∧
      (E : Set G) * (T : Set G) = (T : Set G) * (E : Set G) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hTN : T ≤ Subgroup.normalizer (omegaOnePreimage B S r hab : Set G) :=
    omegaOnePreimage_normalizer hab hTB hTS
  set N : Subgroup G := omegaOnePreimage B S r hab with hNdef
  have hNB : N ≤ B := omegaOnePreimage_le B S r hab
  have hSN : S ≤ N := le_omegaOnePreimage hab hSB
  set φ : ↥N →* (B ⧸ S.subgroupOf B) :=
    (QuotientGroup.mk' (S.subgroupOf B)).comp (Subgroup.inclusion hNB) with hφdef
  have hφker : φ.ker = S.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' (S.subgroupOf B)) (Subgroup.inclusion hNB x) = 1 ↔ (x : G) ∈ S
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion]
  have hφrange : IsPGroup r ↥φ.range := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := hq
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    have hxker : x ^ r ∈ φ.ker := by
      rw [hφker, Subgroup.mem_subgroupOf]
      exact x.2.2
    rwa [MonoidHom.mem_ker] at hxker
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥S := by
    rw [hφker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hcardN : Nat.card ↥N = Nat.card ↥S * Nat.card ↥φ.range := by
    rw [← hcardker, ← Subgroup.card_ker_mul_card_range φ]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hφrange
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hS2
  have hfac : (Nat.card ↥N).factorization r = k := by
    have hN : Nat.card ↥N = 2 ^ m * r ^ k := by rw [hcardN, hk, hm]
    rw [hN]
    have hfac1 : (2 ^ m * r ^ k).factorization = (2 ^ m).factorization + (r ^ k).factorization :=
      Nat.factorization_mul (pow_ne_zero m (by norm_num)) (pow_ne_zero k hr.ne_zero)
    have hzero : (2 ^ m).factorization r = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd ?_
      intro hdvd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
    have hrk : (r ^ k).factorization r = k := by
      rw [Nat.factorization_pow, Nat.Prime.factorization hr, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rw [hfac1, Finsupp.add_apply, hzero, hrk, zero_add]
  obtain ⟨E₀⟩ : Nonempty (Sylow r ↥N) := Sylow.nonempty
  set E : Subgroup G := (E₀ : Subgroup ↥N).map N.subtype with hEdef
  have hEN : E ≤ N := Subgroup.map_subtype_le _
  have hEB : E ≤ B := hEN.trans hNB
  have hEcard : Nat.card ↥E = r ^ k := by
    rw [hEdef, Subgroup.card_map_of_injective N.subtype_injective,
      Sylow.card_eq_multiplicity E₀, hfac]
  have hEr : IsPGroup r ↥E := E₀.isPGroup'.map N.subtype
  have hEodd : Odd (Nat.card ↥E) := by
    obtain ⟨n, hn⟩ := hEr.exists_card_eq
    rw [hn]
    exact Odd.pow (hr.odd_of_ne_two hr2)
  have hES : E ⊓ S = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_two_of_odd hS2 hEodd
  have hEel : CFSG.Open.IsElemAbelian r E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have hcommE : ⁅(a : G), (b : G)⁆ ∈ E := by
        rw [commutatorElement_def]
        have h1 : (a : G) * (b : G) ∈ E := E.mul_mem a.2 b.2
        have h2 : (a : G) * (b : G) * (a : G)⁻¹ ∈ E := E.mul_mem h1 (E.inv_mem a.2)
        exact E.mul_mem h2 (E.inv_mem b.2)
      have haN : (a : G) ∈ N := hEN a.2
      have hbN : (b : G) ∈ N := hEN b.2
      have hq : ((QuotientGroup.mk' (S.subgroupOf B)) ⟨(a : G), hNB haN⟩) *
          ((QuotientGroup.mk' (S.subgroupOf B)) ⟨(b : G), hNB hbN⟩) =
          ((QuotientGroup.mk' (S.subgroupOf B)) ⟨(b : G), hNB hbN⟩) *
          ((QuotientGroup.mk' (S.subgroupOf B)) ⟨(a : G), hNB haN⟩) := hab _ _
      have hcommN : ⁅(a : G), (b : G)⁆ ∈ N := by
        rw [commutatorElement_def]
        have h1 : (a : G) * (b : G) ∈ N := N.mul_mem haN hbN
        have h2 : (a : G) * (b : G) * (a : G)⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem haN)
        exact N.mul_mem h2 (N.inv_mem hbN)
      have hcommS : ⁅(a : G), (b : G)⁆ ∈ S := by
        have h1 : (⟨⁅(a : G), (b : G)⁆, hcommN⟩ : ↥N) ∈ φ.ker := by
          rw [MonoidHom.mem_ker]
          have h3 : (⟨⁅(a : G), (b : G)⁆, hcommN⟩ : ↥N) =
              ⁅(⟨(a : G), haN⟩ : ↥N), (⟨(b : G), hbN⟩ : ↥N)⁆ := Subtype.ext rfl
          rw [h3, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact hab _ _
        rw [hφker, Subgroup.mem_subgroupOf] at h1
        exact h1
      have hmem : ⁅(a : G), (b : G)⁆ ∈ E ⊓ S := ⟨hcommE, hcommS⟩
      rw [hES, Subgroup.mem_bot] at hmem
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 hmem)
    · have hxN : x ∈ N := hEN hx
      have hxrS : x ^ r ∈ S := hxN.2
      have hxrE : x ^ r ∈ E := E.pow_mem hx r
      have hmem : x ^ r ∈ E ⊓ S := ⟨hxrE, hxrS⟩
      rw [hES, Subgroup.mem_bot] at hmem
      exact hmem
  have hkB : k ≤ CFSG.Open.pRank r B := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEB, hEel, hEcard⟩
    rintro j ⟨F, -, -, hj⟩
    have h1 : Nat.card ↥F ≤ Nat.card G := Subgroup.card_le_card_group F
    rw [hj] at h1
    have h2 : j ≤ r ^ j := Nat.le_of_lt (Nat.lt_pow_self hr.one_lt)
    omega
  have hBk : CFSG.Open.pRank r B ≤ k := by
    refine csSup_le' ?_
    rintro j ⟨A, hAB, hAel, hAcard⟩
    have hAn : ∀ a : ↥A, ((a : G) ^ r ∈ S) := by
      intro a
      rw [hAel.2 (a : G) a.2]
      exact S.one_mem
    have hAelr : IsPGroup r ↥A := hAel.isPGroup
    have hAodd : Odd (Nat.card ↥A) := by
      obtain ⟨n, hn⟩ := hAelr.exists_card_eq
      rw [hn]
      exact Odd.pow (hr.odd_of_ne_two hr2)
    have hAS : A ⊓ S = ⊥ := by
      rw [inf_comm]
      exact inf_eq_bot_of_isPGroup_two_of_odd hS2 hAodd
    let f : ↥A → ↥φ.range := fun a =>
      ⟨φ ⟨(a : G), ⟨hAB a.2, hAn a⟩⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 : φ ⟨(a : G), ⟨hAB a.2, hAn a⟩⟩ = φ ⟨(b : G), ⟨hAB b.2, hAn b⟩⟩ :=
        congrArg Subtype.val hab
      have h2 : ((QuotientGroup.mk' (S.subgroupOf B)) ⟨(a : G), hAB a.2⟩) =
          (QuotientGroup.mk' (S.subgroupOf B)) ⟨(b : G), hAB b.2⟩ := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at h2
      have h4 : ((a : G)⁻¹ * (b : G)) ∈ A := A.mul_mem (A.inv_mem a.2) b.2
      have h5 : ((a : G)⁻¹ * (b : G)) ∈ A ⊓ S := ⟨h4, h2⟩
      rw [hAS, Subgroup.mem_bot] at h5
      exact Subtype.ext (by
        calc (a : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by rw [h5, mul_one]
          _ = (b : G) := by group)
    have hle := Nat.card_le_card_of_injective f hfinj
    rw [hAcard, hk] at hle
    exact (pow_le_pow_iff_right₀ hr.one_lt).1 hle
  have hpRank : CFSG.Open.pRank r B = k := le_antisymm hBk hkB
  refine ⟨E, hEB, hEel, by rw [hEcard, hpRank], ?_⟩
  have hSE : (N : Set G) = (S : Set G) * (E : Set G) := by
    have hsub : (S : Set G) * (E : Set G) ⊆ (N : Set G) := by
      rintro _ ⟨s, hs, e, he, rfl⟩
      exact N.mul_mem (hSN hs) (hEN he)
    have hcard : Nat.card ↥N = Nat.card ↥S * Nat.card ↥E := by
      rw [hcardN, hk, hEcard]
    have hinj : Function.Injective (fun z : ↥S × ↥E =>
        (⟨(z.1 : G) * (z.2 : G), N.mul_mem (hSN z.1.2) (hEN z.2.2)⟩ : ↥N)) := by
      rintro ⟨s₁, e₁⟩ ⟨s₂, e₂⟩ h
      have h' : (s₁ : G) * (e₁ : G) = (s₂ : G) * (e₂ : G) := congrArg Subtype.val h
      have h2 : (s₂ : G)⁻¹ * (s₁ : G) = (e₂ : G) * (e₁ : G)⁻¹ := by
        have h'' : (s₁ : G) = (s₂ : G) * (e₂ : G) * (e₁ : G)⁻¹ := by
          rw [← h']
          group
        rw [h'']
        group
      have hmem : (s₂ : G)⁻¹ * (s₁ : G) ∈ S ⊓ E := by
        refine ⟨S.mul_mem (S.inv_mem s₂.2) s₁.2, ?_⟩
        rw [h2]
        exact E.mul_mem e₂.2 (E.inv_mem e₁.2)
      rw [inf_comm, hES, Subgroup.mem_bot] at hmem
      have hs : s₁ = s₂ := Subtype.ext (by
        calc (s₁ : G) = (s₂ : G) * ((s₂ : G)⁻¹ * (s₁ : G)) := by group
          _ = (s₂ : G) := by rw [hmem, mul_one])
      have he : e₁ = e₂ := by
        rw [hs] at h'
        exact Subtype.ext (mul_left_cancel h')
      rw [hs, he]
    haveI : Fintype ↥N := Fintype.ofFinite _
    haveI : Fintype ↥S := Fintype.ofFinite _
    haveI : Fintype ↥E := Fintype.ofFinite _
    have hcardEq : Fintype.card (↥S × ↥E) = Fintype.card ↥N := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, hcard]
    have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcardEq⟩
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := hbij.2 ⟨x, hx⟩
      exact ⟨z.1, z.1.2, z.2, z.2.2, congrArg Subtype.val hz⟩
    · exact fun hx => hsub hx
  have hES' : (N : Set G) = (E : Set G) * (S : Set G) := by
    have hsub : (E : Set G) * (S : Set G) ⊆ (N : Set G) := by
      rintro _ ⟨e, he, s, hs, rfl⟩
      exact N.mul_mem (hEN he) (hSN hs)
    have hcard2 : Nat.card ↥N = Nat.card ↥E * Nat.card ↥S := by
      rw [hcardN, hk, hEcard, Nat.mul_comm]
    have hinj : Function.Injective (fun z : ↥E × ↥S =>
        (⟨(z.1 : G) * (z.2 : G), N.mul_mem (hEN z.1.2) (hSN z.2.2)⟩ : ↥N)) := by
      rintro ⟨e₁, s₁⟩ ⟨e₂, s₂⟩ h
      have h' : (e₁ : G) * (s₁ : G) = (e₂ : G) * (s₂ : G) := congrArg Subtype.val h
      have h3 : (e₂ : G)⁻¹ * (e₁ : G) = (s₂ : G) * (s₁ : G)⁻¹ := by
        have h'' : (e₁ : G) = (e₂ : G) * (s₂ : G) * (s₁ : G)⁻¹ := by
          rw [← h']
          group
        rw [h'']
        group
      have hmem : (e₂ : G)⁻¹ * (e₁ : G) ∈ E ⊓ S := by
        refine ⟨E.mul_mem (E.inv_mem e₂.2) e₁.2, ?_⟩
        rw [h3]
        exact S.mul_mem s₂.2 (S.inv_mem s₁.2)
      rw [hES, Subgroup.mem_bot] at hmem
      have he : e₁ = e₂ := Subtype.ext (by
        calc (e₁ : G) = (e₂ : G) * ((e₂ : G)⁻¹ * (e₁ : G)) := by group
          _ = (e₂ : G) := by rw [hmem, mul_one])
      have hs : s₁ = s₂ := by
        rw [he] at h'
        exact Subtype.ext (mul_left_cancel h')
      rw [he, hs]
    haveI : Fintype ↥N := Fintype.ofFinite _
    haveI : Fintype ↥S := Fintype.ofFinite _
    haveI : Fintype ↥E := Fintype.ofFinite _
    have hcardEq : Fintype.card (↥E × ↥S) = Fintype.card ↥N := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, hcard2]
    have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcardEq⟩
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := hbij.2 ⟨x, hx⟩
      exact ⟨z.1, z.1.2, z.2, z.2.2, congrArg Subtype.val hz⟩
    · exact fun hx => hsub hx
  have hTE : (T : Set G) * (S : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨t, ht, s, hs, rfl⟩
      exact T.mul_mem ht (hST hs)
    · intro hx
      exact ⟨x, hx, 1, S.one_mem, mul_one x⟩
  have hST' : (S : Set G) * (T : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact T.mul_mem (hST hs) ht
    · intro hx
      exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  have hTNsets : (T : Set G) * (N : Set G) = (N : Set G) * (T : Set G) :=
    (set_mul_comm_of_le_normalizer (H := N) (T := T) hTN).symm
  have h1 : (T : Set G) * (N : Set G) = (T : Set G) * (E : Set G) := by
    rw [hSE, ← set_mul_assoc', hTE]
  have h2 : (N : Set G) * (T : Set G) = (E : Set G) * (T : Set G) := by
    rw [hES', set_mul_assoc', hST']
  rw [← h2, ← h1, hTNsets]

end CFSG.GroupTheory
