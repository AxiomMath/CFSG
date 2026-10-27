module

public import CFSG.GH74.AS16.TIBase
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalTightCommuting
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

section I77

variable {G : Type*} [Group G] [Finite G]

noncomputable def rightConjugateEquiv (P : Subgroup G) (g : G) : P ≃* rightConjugate P g :=
  P.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem exists_isSylowOf_ge {N X : Subgroup G} (hXN : X ≤ N) (hX : IsPGroup 2 X) :
    ∃ P : Subgroup G, IsSylowOf 2 P N ∧ X ≤ P := by
  have hX' : IsPGroup 2 (X.subgroupOf N) := hX.comap_subtype
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  refine ⟨(P : Subgroup N).map N.subtype, ⟨P, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hXN hx⟩, hP hx, rfl⟩

theorem card_le_of_isSylowOf {N P X : Subgroup G} (hP : IsSylowOf 2 P N) (hXN : X ≤ N)
    (hX : IsPGroup 2 X) : Nat.card X ≤ Nat.card P := by
  obtain ⟨P', hP', hXP'⟩ := exists_isSylowOf_ge hXN hX
  rw [hP.card_eq, ← hP'.card_eq]
  exact Subgroup.card_le_of_le hXP'

theorem ne_bot_of_isSylowOf_even {P N : Subgroup G} (hP : IsSylowOf 2 P N)
    (hN : Even (Nat.card N)) : P ≠ ⊥ := by
  intro hbot
  have hcard := hP.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have h2 : 2 ∣ Nat.card N := even_iff_two_dvd.mp hN
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hf : 0 < (Nat.card N).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' h2
  have h3 : 2 ∣ (2 : ℕ) ^ (Nat.card N).factorization 2 := dvd_pow_self 2 hf.ne'
  rw [← hcard] at h3
  omega

theorem le_normalizer_of_commute {K R X : Subgroup G} (hK : TightlyEmbedded K) (hRK : R ≤ K)
    (hR2 : IsPGroup 2 R) (hRne : R ≠ ⊥) (hc : ∀ x ∈ X, ∀ r ∈ R, x * r = r * x) :
    X ≤ normalizer (K : Set G) :=
  fun x hx => centralizer_two_subgroup_le K R hK hR2 hRK hRne
    (mem_centralizer_iff.mpr fun r hr => (hc x hx r hr).symm)

structure Data77 (K K' R S : Subgroup G) : Prop where
  tight : TightlyEmbedded K
  conj : ∃ g : G, K' = rightConjugate K g
  ne : K' ≠ K
  R_ne : R ≠ ⊥
  R_syl : IsSylowOf 2 R (K ⊓ normalizer (K' : Set G))
  S_syl : IsSylowOf 2 S (K' ⊔ R)
  R_le_S : R ≤ S

namespace Data77

variable {K K' R S : Subgroup G} (h : Data77 K K' R S)
include h

omit [Finite G] in
theorem R_le_K : R ≤ K := h.R_syl.le.trans inf_le_left

omit [Finite G] in
theorem R_le_N : R ≤ normalizer (K' : Set G) := h.R_syl.le.trans inf_le_right

omit [Finite G] in
theorem R_pGroup : IsPGroup 2 R := h.R_syl.isPGroup

omit [Finite G] in
theorem le_N : K' ⊔ R ≤ normalizer (K' : Set G) := sup_le le_normalizer h.R_le_N

omit [Finite G] in
theorem tight' : TightlyEmbedded K' := by
  obtain ⟨g, rfl⟩ := h.conj
  exact tightlyEmbedded_rightConjugate h.tight g

omit [Finite G] in
theorem card_K' : Nat.card K' = Nat.card K := by
  obtain ⟨g, rfl⟩ := h.conj
  exact rightConjugate_card K g

omit [Finite G] in
theorem inf_odd : Odd (Nat.card ↥(K ⊓ K')) := by
  obtain ⟨g, rfl⟩ := h.conj
  have hg : g ∉ normalizer (K : Set G) := fun hg => h.ne ((rightConjugate_eq_self_iff K g).mpr hg)
  exact h.tight.2 g hg

theorem two_inf_K' {X : Subgroup G} (hX : IsPGroup 2 X) (hXK : X ≤ K) : X ⊓ K' = ⊥ :=
  two_subgroup_of_odd_eq_bot _ _ (hX.to_le inf_le_left) h.inf_odd
    (inf_le_inf_right K' hXK)

theorem R_inf_K' : R ⊓ K' = ⊥ := h.two_inf_K' h.R_pGroup h.R_le_K

theorem setup : Setup K (K' ⊔ R) R S where
  tight := h.tight
  le_inf := le_inf le_sup_right h.R_le_K
  sylow := by
    intro R₂ hR₂ hR₂2 hRR₂
    have hle : R₂ ≤ K ⊓ normalizer (K' : Set G) :=
      le_inf (hR₂.trans inf_le_right) ((hR₂.trans inf_le_left).trans h.le_N)
    exact h.R_syl.eq_of_le hRR₂ hle hR₂2
  pGroup := h.R_pGroup
  ne_bot := h.R_ne
  S_le := h.S_syl.le
  S_pGroup := h.S_syl.isPGroup
  le_S := h.R_le_S

omit [Finite G] in
theorem S_decomp {s : G} (hs : s ∈ S) : ∃ x ∈ S ⊓ K', ∃ r ∈ R, s = x * r := by
  have hsK : s ∈ (K' ⊔ R : Subgroup G) := h.S_syl.le hs
  have hmul : (↑(K' ⊔ R) : Set G) = (K' : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K' R h.R_le_N
  have hsK' : s ∈ (K' : Set G) * (R : Set G) := by
    rw [← hmul]
    exact hsK
  obtain ⟨k, hk, r, hr, hkr⟩ := hsK'
  have hkr' : k * r = s := hkr
  refine ⟨k, ⟨?_, hk⟩, r, hr, hkr'.symm⟩
  have : k = s * r⁻¹ := by rw [← hkr']; group
  rw [this]
  exact S.mul_mem hs (S.inv_mem (h.R_le_S hr))

theorem commute_S₁ {s r : G} (hs : s ∈ (S ⊓ K') ⊓ normalizer (R : Set G)) (hr : r ∈ R) :
    s * r = r * s := by
  obtain ⟨⟨_, hsK'⟩, hsN⟩ := hs
  have h1 : s * r * s⁻¹ ∈ R := (mem_normalizer_iff.mp hsN r).mp hr
  have h2 : r * s⁻¹ * r⁻¹ ∈ K' :=
    (mem_normalizer_iff.mp (h.R_le_N hr) s⁻¹).mp (K'.inv_mem hsK')
  have hc : s * r * s⁻¹ * r⁻¹ ∈ R ⊓ K' := by
    refine ⟨R.mul_mem h1 (R.inv_mem hr), ?_⟩
    have : s * r * s⁻¹ * r⁻¹ = s * (r * s⁻¹ * r⁻¹) := by group
    rw [this]
    exact K'.mul_mem hsK' h2
  rw [h.R_inf_K', mem_bot] at hc
  calc s * r = (s * r * s⁻¹ * r⁻¹) * (r * s) := by group
    _ = r * s := by rw [hc, one_mul]

omit [Finite G] in
theorem normS_decomp {s : G} (hs : s ∈ S ⊓ normalizer (R : Set G)) :
    ∃ x ∈ (S ⊓ K') ⊓ normalizer (R : Set G), ∃ r ∈ R, s = x * r := by
  obtain ⟨x, hx, r, hr, rfl⟩ := h.S_decomp hs.1
  refine ⟨x, ⟨hx, ?_⟩, r, hr, rfl⟩
  have : x = (x * r) * r⁻¹ := by group
  rw [this]
  exact (normalizer (R : Set G)).mul_mem hs.2
    ((normalizer (R : Set G)).inv_mem (le_normalizer hr))

theorem S₁_inf_R : ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ R ⊓ K' := ⟨hx.2, hx.1.1.2⟩
  rw [h.R_inf_K', mem_bot] at this
  exact mem_bot.mpr this

theorem S₁_le : (S ⊓ K') ⊓ normalizer (R : Set G) ≤ K' ⊓ normalizer (K : Set G) :=
  le_inf (inf_le_left.trans inf_le_right)
    (le_normalizer_of_commute h.tight h.R_le_K h.R_pGroup h.R_ne
      (fun _ hs _ hr => h.commute_S₁ hs hr))

omit [Finite G] in
theorem S₁_pGroup : IsPGroup 2 ↥((S ⊓ K') ⊓ normalizer (R : Set G)) :=
  h.S_syl.isPGroup.to_le (inf_le_left.trans inf_le_left)

theorem S₀_syl : IsSylowOf 2 (S ⊓ K') K' := h.S_syl.inf_of_le_normalizer le_sup_left h.le_N

theorem S₀_ne : S ⊓ K' ≠ ⊥ :=
  ne_bot_of_isSylowOf_even h.S₀_syl (by rw [h.card_K']; exact h.tight.1)

theorem caseA (hA : S ⊓ K' ≤ normalizer (R : Set G)) :
    IsSylowOf 2 R K ∧ Nat.card (S ⊓ K' : Subgroup G) = Nat.card R := by
  have hcomm : ∀ s ∈ S ⊓ K', ∀ r ∈ R, s * r = r * s := fun s hs r hr =>
    h.commute_S₁ ⟨hs, hA hs⟩ hr
  have hNK : S ⊓ K' ≤ normalizer (K : Set G) :=
    le_normalizer_of_commute h.tight h.R_le_K h.R_pGroup h.R_ne hcomm
  have hS₀syl : IsSylowOf 2 (S ⊓ K') K' := h.S₀_syl
  have hS₀ne : S ⊓ K' ≠ ⊥ := h.S₀_ne
  have hS₀2 : IsPGroup 2 (S ⊓ K' : Subgroup G) := hS₀syl.isPGroup
  have hSR : (S ⊓ K') ⊔ R ≤ S := sup_le inf_le_left h.R_le_S
  have hSR2 : IsPGroup 2 ↥((S ⊓ K') ⊔ R) := h.S_syl.isPGroup.to_le hSR
  have hKS₀ : K ⊔ (S ⊓ K') ≤ normalizer (K : Set G) := sup_le le_normalizer hNK
  obtain ⟨P, hP, hPge⟩ := exists_isSylowOf_ge (N := K ⊔ (S ⊓ K')) (X := (S ⊓ K') ⊔ R)
    (sup_le le_sup_right (h.R_le_K.trans le_sup_left)) hSR2
  have hR₁ : IsSylowOf 2 (P ⊓ K) K := hP.inf_of_le_normalizer le_sup_left hKS₀
  have hRR₁ : R ≤ P ⊓ K := le_inf (le_sup_right.trans hPge) h.R_le_K
  have hS₀P : S ⊓ K' ≤ P := le_sup_left.trans hPge
  have hS₀N : S ⊓ K' ≤ normalizer ((P ⊓ K : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    have h1 : s ∈ normalizer (P : Set G) := le_normalizer (hS₀P hs)
    have h2 := hNK hs
    constructor
    · rintro ⟨hyP, hyK⟩
      exact ⟨(mem_normalizer_iff.mp h1 y).mp hyP, (mem_normalizer_iff.mp h2 y).mp hyK⟩
    · rintro ⟨hyP, hyK⟩
      exact ⟨(mem_normalizer_iff.mp h1 y).mpr hyP, (mem_normalizer_iff.mp h2 y).mpr hyK⟩
  have hR₁K' : (P ⊓ K) ⊓ K' = ⊥ := h.two_inf_K' hR₁.isPGroup inf_le_right
  have hsetup : Setup K' ((S ⊓ K') ⊔ (P ⊓ K)) (S ⊓ K') ((S ⊓ K') ⊔ (P ⊓ K)) :=
    { tight := h.tight'
      le_inf := le_inf le_sup_left inf_le_right
      sylow := by
        intro R₂ hR₂ _ hS₀R₂
        have hsub : ((S ⊓ K') ⊔ (P ⊓ K)) ⊓ K' ≤ S ⊓ K' := by
          intro y hy
          have hmul : (↑((S ⊓ K') ⊔ (P ⊓ K)) : Set G) =
              ((S ⊓ K' : Subgroup G) : Set G) * ((P ⊓ K : Subgroup G) : Set G) :=
            Subgroup.coe_mul_of_left_le_normalizer_right (S ⊓ K') (P ⊓ K) hS₀N
          have hy1 : y ∈ ((S ⊓ K' : Subgroup G) : Set G) * ((P ⊓ K : Subgroup G) : Set G) := by
            rw [← hmul]
            exact hy.1
          obtain ⟨s, hs, r, hr, hyr⟩ := hy1
          have hyr' : s * r = y := hyr
          have hr' : r ∈ (P ⊓ K) ⊓ K' := by
            refine ⟨hr, ?_⟩
            have : r = s⁻¹ * y := by rw [← hyr']; group
            rw [this]
            exact K'.mul_mem (K'.inv_mem hs.2) hy.2
          rw [hR₁K', mem_bot] at hr'
          rw [← hyr', hr', mul_one]
          exact hs
        exact le_antisymm (hR₂.trans hsub) hS₀R₂
      pGroup := hS₀2
      ne_bot := hS₀ne
      S_le := le_rfl
      S_pGroup := hP.isPGroup.to_le (sup_le hS₀P inf_le_left)
      le_S := le_sup_left }
  have hcardR₁ : Nat.card (P ⊓ K : Subgroup G) = Nat.card (S ⊓ K' : Subgroup G) := by
    rw [hR₁.card_eq, hS₀syl.card_eq, h.card_K']
  have hcard : Nat.card ↥((S ⊓ K') ⊔ (P ⊓ K)) ≤ Nat.card (S ⊓ K' : Subgroup G) ^ 2 := by
    have h1 := card_sup_le_of_le_normalizer hS₀N
    rw [sup_comm (P ⊓ K) (S ⊓ K'), hcardR₁, ← pow_two] at h1
    exact h1
  have hN₁ := hsetup.le_normalizer_of_card hcard
  have hR₁N : P ⊓ K ≤ normalizer (K' : Set G) :=
    (le_sup_right.trans hN₁).trans
      (normalizer_two_subgroup_le K' (S ⊓ K') h.tight' hS₀2 inf_le_right hS₀ne)
  have hR₁eq : P ⊓ K = R :=
    h.R_syl.eq_of_le hRR₁ (le_inf inf_le_right hR₁N) hR₁.isPGroup
  refine ⟨hR₁eq ▸ hR₁, ?_⟩
  rw [← hcardR₁, hR₁eq]

theorem caseB (hB : ¬ S ⊓ K' ≤ normalizer (R : Set G)) :
    ∃ x ∈ S, rightConjugate R x ≠ R ∧ rightConjugate R x ≤ S ⊓ normalizer (R : Set G) ∧
      Commutes R (rightConjugate R x) ∧ R ⊓ rightConjugate R x = ⊥ ∧
      Nat.card R ≤ Nat.card ↥((S ⊓ K') ⊓ normalizer (R : Set G)) := by
  have hlt : S ⊓ normalizer (R : Set G) < S := by
    refine lt_of_le_of_ne inf_le_left fun heq => hB fun s hs => ?_
    have : s ∈ S ⊓ normalizer (R : Set G) := by
      rw [heq]
      exact hs.1
    exact this.2
  obtain ⟨x, hxS, hxN, hxNN⟩ := exists_mem_normalizer_not_mem h.S_syl.isPGroup hlt
  have hRN : R ≤ S ⊓ normalizer (R : Set G) := le_inf h.R_le_S le_normalizer
  have hconj : rightConjugate (S ⊓ normalizer (R : Set G)) x = S ⊓ normalizer (R : Set G) :=
    (rightConjugate_eq_self_iff _ x).mpr hxNN
  have hRx : rightConjugate R x ≤ S ⊓ normalizer (R : Set G) := by
    have := rightConjugate_mono x hRN
    rwa [hconj] at this
  have hne : rightConjugate R x ≠ R := by
    intro heq
    exact hxN ⟨hxS, (rightConjugate_eq_self_iff R x).mp heq⟩
  have hxH : x ∈ K' ⊔ R := h.S_syl.le hxS
  obtain ⟨hcomm, hinf⟩ := h.setup.commutes_of_le_normalizer hxH hne (hRx.trans inf_le_left)
    (hRx.trans inf_le_right)
  refine ⟨x, hxS, hne, hRx, hcomm, hinf, ?_⟩
  have h1 := card_mul_le_card_sup hinf hRN hRx
  rw [rightConjugate_card] at h1
  have h2 : Nat.card ↥(S ⊓ normalizer (R : Set G)) ≤
      Nat.card ↥((S ⊓ K') ⊓ normalizer (R : Set G)) * Nat.card R := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_surjective
      (fun p : ↥((S ⊓ K') ⊓ normalizer (R : Set G)) × ↥R =>
        (⟨(p.1 : G) * p.2, S.mul_mem p.1.2.1.1 (h.R_le_S p.2.2),
          (normalizer (R : Set G)).mul_mem p.1.2.2 (le_normalizer p.2.2)⟩ :
          ↥(S ⊓ normalizer (R : Set G)))) ?_
    rintro ⟨s, hs⟩
    obtain ⟨x₁, hx₁, r, hr, rfl⟩ := h.normS_decomp hs
    exact ⟨(⟨x₁, hx₁⟩, ⟨r, hr⟩), rfl⟩
  have hpos : 0 < Nat.card R := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right (h1.trans h2) hpos

theorem star : Nat.card R ≤ Nat.card ↥((S ⊓ K') ⊓ normalizer (R : Set G)) := by
  by_cases hA : S ⊓ K' ≤ normalizer (R : Set G)
  · obtain ⟨-, hcard⟩ := h.caseA hA
    have : (S ⊓ K') ⊓ normalizer (R : Set G) = S ⊓ K' := inf_eq_left.mpr hA
    rw [this, hcard]
  · obtain ⟨-, -, -, -, -, -, hcard⟩ := h.caseB hA
    exact hcard

theorem sylow_S₁ :
    IsSylowOf 2 ((S ⊓ K') ⊓ normalizer (R : Set G)) (K' ⊓ normalizer (K : Set G)) ∧
      Nat.card ↥((S ⊓ K') ⊓ normalizer (R : Set G)) = Nat.card R := by
  obtain ⟨S₂, hS₂, hS₁S₂⟩ := exists_isSylowOf_ge h.S₁_le h.S₁_pGroup
  have hstar := h.star
  have hRpos : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).mpr h.R_ne
  have hc12 : Nat.card ↥((S ⊓ K') ⊓ normalizer (R : Set G)) ≤ Nat.card S₂ :=
    Subgroup.card_le_of_le hS₁S₂
  have hS₂ne : S₂ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hc12
    omega
  obtain ⟨S'', hS'', hS₂S''⟩ :=
    exists_isSylowOf_ge (N := K ⊔ S₂) (X := S₂) le_sup_right hS₂.isPGroup
  have hdata : Data77 K' K S₂ S'' :=
    { tight := h.tight'
      conj := by
        obtain ⟨g, hg⟩ := h.conj
        exact ⟨g⁻¹, by rw [hg, rightConjugate_rightConjugate_inv]⟩
      ne := h.ne.symm
      R_ne := hS₂ne
      R_syl := hS₂
      S_syl := hS''
      R_le_S := hS₂S'' }
  have hstar' := hdata.star
  have hle' : Nat.card ↥((S'' ⊓ K) ⊓ normalizer (S₂ : Set G)) ≤ Nat.card R :=
    card_le_of_isSylowOf h.R_syl hdata.S₁_le hdata.S₁_pGroup
  have heq : (S ⊓ K') ⊓ normalizer (R : Set G) = S₂ :=
    Subgroup.eq_of_le_of_card_ge hS₁S₂ (by omega)
  rw [heq]
  exact ⟨hS₂, by omega⟩

omit [Finite G] in
theorem normS_eq : S ⊓ normalizer (R : Set G) = ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊔ R := by
  apply le_antisymm
  · intro s hs
    obtain ⟨x, hx, r, hr, rfl⟩ := h.normS_decomp hs
    exact mul_mem_sup hx hr
  · exact sup_le (fun x hx => ⟨hx.1.1, hx.2⟩) (le_inf h.R_le_S le_normalizer)

theorem S₁_eq_centralizer :
    (S ⊓ K') ⊓ normalizer (R : Set G) = (S ⊓ K') ⊓ centralizer (R : Set G) := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, mem_centralizer_iff.mpr (fun r hr => (h.commute_S₁ hx hr).symm)⟩
  · intro hx
    have hc : ∀ r ∈ R, x * r = r * x := fun r hr => ((mem_centralizer_iff.mp hx.2) r hr).symm
    refine ⟨hx.1, mem_normalizer_iff.mpr (fun y => ?_)⟩
    constructor
    · intro hy
      have e : x * y * x⁻¹ = y := by rw [hc y hy]; group
      rw [e]
      exact hy
    · intro hy
      have h1 := hc _ hy
      have h2 : x * (x * y * x⁻¹) = x * y := by rw [h1]; group
      have e : x * y * x⁻¹ = y := mul_left_cancel h2
      rw [e] at hy
      exact hy

omit [Finite G] in
theorem exists_decomp_fun {T : Subgroup G} (hT : T ≤ S ⊓ normalizer (R : Set G)) :
    ∃ q : ↥T → G × G, ∀ y, (q y).1 ∈ (S ⊓ K') ⊓ normalizer (R : Set G) ∧ (q y).2 ∈ R ∧
      (y : G) = (q y).1 * (q y).2 := by
  have hdec : ∀ y : ↥T, ∃ q : G × G, q.1 ∈ (S ⊓ K') ⊓ normalizer (R : Set G) ∧ q.2 ∈ R ∧
      (y : G) = q.1 * q.2 := by
    intro y
    obtain ⟨x₁, hx₁, r, hr, hyr⟩ := h.normS_decomp (hT y.2)
    exact ⟨(x₁, r), hx₁, hr, hyr⟩
  choose q hq using hdec
  exact ⟨q, hq⟩

theorem decomp_unique {x x' r r' : G} (hx : x ∈ (S ⊓ K') ⊓ normalizer (R : Set G))
    (hx' : x' ∈ (S ⊓ K') ⊓ normalizer (R : Set G)) (hr : r ∈ R) (hr' : r' ∈ R)
    (hxr : x * r = x' * r') : x = x' ∧ r = r' := by
  have hmem : x'⁻¹ * x ∈ ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊓ R := by
    refine ⟨((S ⊓ K') ⊓ normalizer (R : Set G)).mul_mem
      (((S ⊓ K') ⊓ normalizer (R : Set G)).inv_mem hx') hx, ?_⟩
    have : x'⁻¹ * x = r' * r⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * r) * r⁻¹ := by group
        _ = x'⁻¹ * (x' * r') * r⁻¹ := by rw [hxr]
        _ = r' * r⁻¹ := by group
    rw [this]
    exact R.mul_mem hr' (R.inv_mem hr)
  rw [h.S₁_inf_R, mem_bot] at hmem
  have hx1 : x = x' := by
    calc x = x' * (x'⁻¹ * x) := by group
      _ = x' := by rw [hmem, mul_one]
  refine ⟨hx1, ?_⟩
  rw [hx1] at hxr
  exact mul_left_cancel hxr

theorem conj_inf_K' {x : G} (hx : x ∈ S) : rightConjugate R x ⊓ K' = ⊥ := by
  have hxN : x ∈ normalizer (K' : Set G) := h.le_N (h.S_syl.le hx)
  have hK'x : rightConjugate K' x = K' := (rightConjugate_eq_self_iff K' x).mpr hxN
  have := rightConjugate_inf R K' x
  rw [h.R_inf_K', hK'x] at this
  rw [← this]
  simp [rightConjugate]

theorem S₁_inf_conj {x : G} (hx : x ∈ S) :
    ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊓ rightConjugate R x = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : z ∈ rightConjugate R x ⊓ K' := ⟨hz.2, hz.1.1.2⟩
  rw [h.conj_inf_K' hx, mem_bot] at this
  exact mem_bot.mpr this

theorem isMulCommutative_R (hlt : (S ⊓ K') ⊓ normalizer (R : Set G) < S ⊓ K') :
    IsMulCommutative ↥R := by
  have hA : ¬ S ⊓ K' ≤ normalizer (R : Set G) := by
    intro hA
    have : (S ⊓ K') ⊓ normalizer (R : Set G) = S ⊓ K' := inf_eq_left.mpr hA
    rw [this] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨x, hxS, hne, hRx, hcomm, hinf, hcard⟩ := h.caseB hA
  rw [isMulCommutative_iff]
  by_contra hnc
  push Not at hnc
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hnc
  have hab' : a * b ≠ b * a := fun h' => hab (Subtype.ext h')
  have hbC : b ∉ R ⊓ centralizer ({a} : Set G) := fun hb' =>
    hab' (mem_centralizer_singleton_iff.mp hb'.2).symm
  have hClt : Nat.card ↥(R ⊓ centralizer ({a} : Set G)) < Nat.card R :=
    card_lt_of_le_of_not_mem inf_le_left hb hbC
  obtain ⟨q, hq⟩ := h.exists_decomp_fun hRx
  have hqC : ∀ y, (q y).2 ∈ R ⊓ centralizer ({a} : Set G) := by
    intro y
    obtain ⟨hq1, hq2, hq3⟩ := hq y
    refine ⟨hq2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : a * (y : G) = (y : G) * a := hcomm a ha y y.2
    have h2 : (q y).1 * a = a * (q y).1 := h.commute_S₁ hq1 ha
    rw [hq3] at h1
    have : (q y).1 * ((q y).2 * a) = (q y).1 * (a * (q y).2) := by
      calc (q y).1 * ((q y).2 * a) = ((q y).1 * (q y).2) * a := by group
        _ = a * ((q y).1 * (q y).2) := h1.symm
        _ = (a * (q y).1) * (q y).2 := by group
        _ = ((q y).1 * a) * (q y).2 := by rw [h2]
        _ = (q y).1 * (a * (q y).2) := by group
    exact mul_left_cancel this
  let f : ↥(rightConjugate R x) → ↥(R ⊓ centralizer ({a} : Set G)) := fun y => ⟨(q y).2, hqC y⟩
  have hf : Function.Injective f := by
    intro y y' hyy'
    have hr : (q y).2 = (q y').2 := congrArg Subtype.val hyy'
    obtain ⟨hq1, -, hq3⟩ := hq y
    obtain ⟨hq1', -, hq3'⟩ := hq y'
    have hyy : (y : G) * (y' : G)⁻¹ = (q y).1 * (q y').1⁻¹ := by
      rw [hq3, hq3', hr]
      group
    have hmem : (y : G) * (y' : G)⁻¹ ∈ ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊓ rightConjugate R x := by
      refine ⟨?_, (rightConjugate R x).mul_mem y.2 ((rightConjugate R x).inv_mem y'.2)⟩
      rw [hyy]
      exact ((S ⊓ K') ⊓ normalizer (R : Set G)).mul_mem hq1
        (((S ⊓ K') ⊓ normalizer (R : Set G)).inv_mem hq1')
    rw [h.S₁_inf_conj hxS, mem_bot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp hmem)
  have := Nat.card_le_card_of_injective f hf
  rw [rightConjugate_card] at this
  omega

theorem nonempty_equiv_S₁ :
    Nonempty (↥((S ⊓ K') ⊓ normalizer (R : Set G)) ≃* ↥R) := by
  by_cases hA : S ⊓ K' ≤ normalizer (R : Set G)
  · obtain ⟨hRK, -⟩ := h.caseA hA
    have hS₁ : (S ⊓ K') ⊓ normalizer (R : Set G) = S ⊓ K' := inf_eq_left.mpr hA
    obtain ⟨g, hg⟩ := h.conj
    have hRg : IsSylowOf 2 (rightConjugate R g) K' := by
      refine isSylowOf_of_card ?_ ?_
      · rw [hg]
        exact rightConjugate_mono g h.R_le_K
      · rw [rightConjugate_card, hRK.card_eq, h.card_K']
    obtain ⟨k, -, hk⟩ := h.S₀_syl.exists_mem_conj hRg
    have hRgeq : rightConjugate R g = rightConjugate (S ⊓ K') k⁻¹ := by
      ext y
      rw [hk y, mem_rightConjugate_iff (S ⊓ K') k⁻¹ y]
      simp
    rw [hS₁]
    exact ⟨((rightConjugateEquiv (S ⊓ K') k⁻¹).trans
      (MulEquiv.subgroupCongr hRgeq.symm)).trans (rightConjugateEquiv R g).symm⟩
  · obtain ⟨x, hxS, hne, hRx, hcomm, hinf, hcard⟩ := h.caseB hA
    obtain ⟨hsyl, hcardeq⟩ := h.sylow_S₁
    obtain ⟨q, hq⟩ := h.exists_decomp_fun hRx
    let φ : ↥(rightConjugate R x) →* ↥((S ⊓ K') ⊓ normalizer (R : Set G)) :=
      MonoidHom.mk' (fun y => ⟨(q y).1, (hq y).1⟩) (by
        intro y y'
        apply Subtype.ext
        obtain ⟨hq1, hq2, hq3⟩ := hq y
        obtain ⟨hq1', hq2', hq3'⟩ := hq y'
        obtain ⟨hq1'', hq2'', hq3''⟩ := hq (y * y')
        have hc : (q y).2 * (q y').1 = (q y').1 * (q y).2 := (h.commute_S₁ hq1' hq2).symm
        have hprod : (q (y * y')).1 * (q (y * y')).2 =
            ((q y).1 * (q y').1) * ((q y).2 * (q y').2) := by
          have hyy : ((y * y' : ↥(rightConjugate R x)) : G) = (y : G) * y' := rfl
          rw [← hq3'', hyy, hq3, hq3']
          calc (q y).1 * (q y).2 * ((q y').1 * (q y').2)
              = (q y).1 * ((q y).2 * (q y').1) * (q y').2 := by group
            _ = (q y).1 * ((q y').1 * (q y).2) * (q y').2 := by rw [hc]
            _ = ((q y).1 * (q y').1) * ((q y).2 * (q y').2) := by group
        exact (h.decomp_unique hq1''
          (((S ⊓ K') ⊓ normalizer (R : Set G)).mul_mem hq1 hq1') hq2'' (R.mul_mem hq2 hq2')
          hprod).1)
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have h1 : (q y).1 = 1 := congrArg Subtype.val hy
      obtain ⟨hq1, hq2, hq3⟩ := hq y
      have : (y : G) ∈ R ⊓ rightConjugate R x := by
        refine ⟨?_, y.2⟩
        rw [hq3, h1, one_mul]
        exact hq2
      rw [hinf, mem_bot] at this
      exact Subtype.ext this
    have hbij : Function.Bijective φ := by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨hφinj, ?_⟩
      rw [rightConjugate_card, hcardeq]
    exact ⟨(MulEquiv.ofBijective φ hbij).symm.trans (rightConjugateEquiv R x).symm⟩

end Data77

structure Conclusion77 (K K' R S : Subgroup G) : Prop where
  normalizer_eq_centralizer :
    (S ⊓ K') ⊓ normalizer (R : Set G) = (S ⊓ K') ⊓ centralizer (R : Set G)
  normalizer_eq : S ⊓ normalizer (R : Set G) = ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊔ R
  inf_eq_bot : ((S ⊓ K') ⊓ normalizer (R : Set G)) ⊓ R = ⊥
  commutes : Commutes ((S ⊓ K') ⊓ normalizer (R : Set G)) R
  equiv : Nonempty (↥((S ⊓ K') ⊓ normalizer (R : Set G)) ≃* ↥R)
  sylow : IsSylowOf 2 ((S ⊓ K') ⊓ normalizer (R : Set G)) (K' ⊓ normalizer (K : Set G))
  abelian : (S ⊓ K') ⊓ normalizer (R : Set G) < S ⊓ K' → IsMulCommutative ↥R

theorem Data77.conclusion {K K' R S : Subgroup G} (h : Data77 K K' R S) :
    Conclusion77 K K' R S where
  normalizer_eq_centralizer := h.S₁_eq_centralizer
  normalizer_eq := h.normS_eq
  inf_eq_bot := h.S₁_inf_R
  commutes := fun _ hx _ hr => h.commute_S₁ hx hr
  equiv := h.nonempty_equiv_S₁
  sylow := h.sylow_S₁.1
  abelian := h.isMulCommutative_R

end I77

end CFSG.GH74.AS16
