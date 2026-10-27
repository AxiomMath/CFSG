module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Radical
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.PreStep

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (mem_barM barM_normalizer_inf)

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

omit [Finite G] in
theorem barM_isPGroup {M S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup 2 S) :
    IsPGroup 2 (barM M S) :=
  (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm).map (QuotientGroup.mk' _)

omit [Finite G] in
theorem exists_pow_two_eq_one {M : Subgroup G} (m : ↥M)
    (h : ∃ e : ℕ, (QuotientGroup.mk m : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 2 ^ e = 1) :
    ∃ k : ℕ, m ^ 2 ^ k = 1 := by
  obtain ⟨e, he⟩ := h
  have h1 : m ^ 2 ^ e ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact he
  obtain ⟨f, hf⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨m ^ 2 ^ e, h1⟩
  refine ⟨e + f, ?_⟩
  have := congrArg Subtype.val hf
  simpa [pow_add, pow_mul] using this

omit [Finite G] in
theorem exists_mul_of_mem_sup {S L : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ L ⊔ S) : ∃ s ∈ S, ∃ l ∈ L, x = s * l := by
  have : x ∈ ((S ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S L hSL] at this
  obtain ⟨s, hs, l, hl, rfl⟩ := this
  exact ⟨s, hs, l, hl, rfl⟩

theorem isTwoRadicalIn_barM (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hSQ : S ≤ L ⊔ pCoreOf 2 (L ⊔ S)) (hne : ¬ L ≤ Subgroup.normalizer (S : Set G)) :
    IsTwoRadicalIn (barM (L ⊔ S) L) (barM (L ⊔ S) S) := by
  classical
  set M : Subgroup G := L ⊔ S with hM
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hSM : S ≤ M := le_sup_right
  have hLM : L ≤ M := le_sup_left
  have hQS : Q ≤ S := hA.twoCore_le
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hO2 : ∀ x : ↥M, x ∈ CFSG.pCore 2 ↥M → (x : G) ∈ S := fun x hx => hQS (coe_mem_pCoreOf hx)
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hPL : barM M S ≤ barM M L := by
    intro x hx
    obtain ⟨⟨s, hsM⟩, hs, rfl⟩ := (mem_barM x).1 hx
    obtain ⟨l, hl, q, hq, hlq⟩ : ∃ l ∈ L, ∃ q ∈ Q, s = l * q := by
      have : s ∈ ((L ⊔ Q : Subgroup G) : Set G) := hSQ hs
      rw [Subgroup.coe_mul_of_left_le_normalizer_right L Q (le_sup_left.trans hMQ)] at this
      obtain ⟨l, hl, q, hq, rfl⟩ := this
      exact ⟨l, hl, q, hq, rfl⟩
    refine (mem_barM _).2 ⟨⟨l, hLM hl⟩, hl, ?_⟩
    have hqM : q ∈ M := hQS hq |> hSM
    have e : (⟨s, hsM⟩ : ↥M) = ⟨l, hLM hl⟩ * ⟨q, hqM⟩ := Subtype.ext hlq
    rw [e, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨q, hqM⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_pCore_of_coe_mem hq)
    rw [this, mul_one]
  have hP0 : barM M S ≠ ⊥ := by
    intro h
    have hSQ' : S ≤ Q := by
      intro x hx
      have h1 : (QuotientGroup.mk (⟨x, hSM hx⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M S :=
        (mem_barM _).2 ⟨⟨x, hSM hx⟩, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
      exact coe_mem_pCoreOf h1
    have hSeq : S = Q := le_antisymm hSQ' hQS
    apply hne
    intro l hl
    have := hMQ (hLM hl)
    rwa [← hSeq] at this
  refine isTwoRadicalIn_iff.mpr ⟨hPL, hP0, barM_isPGroup hSM hS2, fun T hT hT2 hTn => ?_⟩
  have hN : barM M (Subgroup.normalizer (S : Set G) ⊓ L) =
      Subgroup.normalizer ((barM M S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) ⊓ barM M L :=
    barM_normalizer_inf hSM hO2
  have hT'' : T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    rw [hN, inf_comm]; exact hT
  set That : Subgroup G :=
    ((T.comap π) ⊓ ((Subgroup.normalizer (S : Set G)).subgroupOf M)).map M.subtype with hThat
  have hmem : ∀ x : G, x ∈ That ↔ ∃ m : ↥M, (m : G) = x ∧ π m ∈ T ∧ (m : G) ∈ Subgroup.normalizer (S : Set G) := by
    intro x
    simp only [hThat, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.mem_subgroupOf, Subgroup.subtype_apply]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, rfl, h1, h2⟩
    · rintro ⟨m, rfl, h1, h2⟩; exact ⟨m, ⟨h1, h2⟩, rfl⟩
  have hThatle : That ≤ M ⊓ Subgroup.normalizer (S : Set G) := by
    intro x hx
    obtain ⟨m, rfl, -, h2⟩ := (hmem x).1 hx
    exact ⟨m.2, h2⟩
  have hThat2 : IsPGroup 2 That := by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl, h1, -⟩ := (hmem x).1 hx
    obtain ⟨e, he⟩ := hT2 ⟨π m, h1⟩
    obtain ⟨k, hk⟩ := exists_pow_two_eq_one m ⟨e, congrArg Subtype.val he⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hnorm_bar : ∀ n : ↥M, (n : G) ∈ Subgroup.normalizer (S : Set G) →
      π n ∈ barM M L ⊓ Subgroup.normalizer ((barM M S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
    intro n hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · obtain ⟨s, hs, l, hl, hsl⟩ := exists_mul_of_mem_sup hSL n.2
      have hsM : s ∈ M := hSM hs
      have hlM : l ∈ M := hLM hl
      have e : n = ⟨s, hsM⟩ * ⟨l, hlM⟩ := Subtype.ext hsl
      have h1 : π ⟨s, hsM⟩ ∈ barM M S := (mem_barM _).2 ⟨⟨s, hsM⟩, hs, rfl⟩
      have h2 : π ⟨l, hlM⟩ ∈ barM M L := (mem_barM _).2 ⟨⟨l, hlM⟩, hl, rfl⟩
      rw [e, map_mul]
      exact (barM M L).mul_mem (hPL h1) h2
    · rw [Subgroup.mem_normalizer_iff]
      have key : ∀ n' : ↥M, (n' : G) ∈ Subgroup.normalizer (S : Set G) → ∀ c ∈ barM M S,
          π n' * c * (π n')⁻¹ ∈ barM M S := by
        intro n' hn' c hc
        obtain ⟨⟨s', hs'M⟩, hs', rfl⟩ := (mem_barM c).1 hc
        refine (mem_barM _).2 ⟨n' * ⟨s', hs'M⟩ * n'⁻¹, ?_, by simp [hπ]⟩
        exact (Subgroup.mem_normalizer_iff.mp hn' s').mp hs'
      intro c
      refine ⟨fun hc => key n hn c hc, fun hc => ?_⟩
      have hn' : ((n⁻¹ : ↥M) : G) ∈ Subgroup.normalizer (S : Set G) := by
        rw [Subgroup.coe_inv]; exact Subgroup.inv_mem _ hn
      have := key n⁻¹ hn' _ hc
      simpa [mul_assoc] using this
  have hconj : ∀ n : G, n ∈ M ⊓ Subgroup.normalizer (S : Set G) → ∀ x ∈ That, n * x * n⁻¹ ∈ That := by
    intro n hn x hx
    obtain ⟨m, rfl, h1, h2⟩ := (hmem x).1 hx
    obtain ⟨hnM, hnN⟩ := hn
    refine (hmem _).2 ⟨⟨n, hnM⟩ * m * ⟨n, hnM⟩⁻¹, by simp, ?_, ?_⟩
    · have hg := hnorm_bar ⟨n, hnM⟩ hnN
      have h3 := hTn.conj_mem (⟨π m, hT h1⟩ : ↥(barM M L ⊓ Subgroup.normalizer
        ((barM M S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)))
        (Subgroup.mem_subgroupOf.mpr h1) ⟨π ⟨n, hnM⟩, hg⟩
      have h4 := Subgroup.mem_subgroupOf.mp h3
      simpa [map_mul, map_inv] using h4
    · have := (Subgroup.normalizer (S : Set G)).mul_mem
        ((Subgroup.normalizer (S : Set G)).mul_mem hnN h2) (Subgroup.inv_mem _ hnN)
      simpa using this
  have hThatnorm : M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (That : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj n hn x hx, fun hx => ?_⟩
    have hn' : n⁻¹ ∈ M ⊓ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hn
    have := hconj n⁻¹ hn' _ hx
    simpa [mul_assoc] using this
  have hThatnormal : (That.subgroupOf (M ⊓ Subgroup.normalizer (S : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hThatle).mpr hThatnorm
  have hmaxG := (isTwoRadicalIn_iff.mp hA.twoRadical).2.2.2 That hThatle hThat2 hThatnormal
  intro t ht
  obtain ⟨m, hm, rfl⟩ := (mem_barM t).1 (hT'' ht)
  have hmN : (m : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.1 hm).1
  have : (m : G) ∈ That := (hmem _).2 ⟨m, rfl, ht, hmN⟩
  exact (mem_barM _).2 ⟨m, hmaxG this, rfl⟩

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
