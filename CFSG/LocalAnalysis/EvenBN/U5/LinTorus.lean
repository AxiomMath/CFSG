module

public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.LinLift
public import CFSG.LocalAnalysis.EvenBN.U5.LinModelTorus

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace LinCase

theorem linto_isSylowOf_map {M Λ : Type} [Group M] [Group Λ] [Finite M] [Finite Λ]
    (π : M →* Λ) (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {R : Subgroup M}
    (hR : IsSylowOf 2 R ⊤) : IsSylowOf 2 (R.map π) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRcard : Nat.card R = 2 ^ (Nat.card M).factorization 2 := by
    have h := hR.card_eq
    rwa [Subgroup.card_top] at h
  have hK : π.ker ⊓ R = ⊥ := by
    have hKdvd : Nat.card (π.ker ⊓ R : Subgroup M) ∣ 2 ^ (Nat.card M).factorization 2 := by
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ Nat.card (π.ker ⊓ R : Subgroup M) := by
        rw [hk]
        exact dvd_pow_self 2 hk0
      exact hker.not_two_dvd_nat (h2.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact Subgroup.card_eq_one.1 (by rw [hk, hk0, pow_zero])
  have hinj : Function.Injective (π.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : (g : M) ∈ π.ker ⊓ R := Subgroup.mem_inf.2 ⟨(MonoidHom.mem_ker).2 hg, g.2⟩
    rw [hK, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hRtop : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hRmap : R.map π = (⊤ : Subgroup R).map (π.comp R.subtype) := by
    rw [← Subgroup.map_map, hRtop]
  have hcardRmap : Nat.card (R.map π) = Nat.card R := by
    rw [hRmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hMfac : Nat.card M = Nat.card π.ker * Nat.card Λ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, mul_comm]
  have hne₁ : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hne₂ : Nat.card Λ ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card M).factorization 2 = (Nat.card Λ).factorization 2 := by
    rw [hMfac, Nat.factorization_mul hne₁ hne₂, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker.not_two_dvd_nat, zero_add]
  have hcardΛ : Nat.card (R.map π) = 2 ^ (Nat.card Λ).factorization 2 := by
    rw [hcardRmap, hRcard, hfac]
  exact CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [Subgroup.card_top]; exact hcardΛ)

theorem exists_odd_torus_of_odd_ker {M Λ : Type} [Group M] [Group Λ] [Finite M] [Finite Λ]
    {f : ℕ} (hf : 1 ≤ f) (hΛ : LieModel Λ .PSL 3 2 (2 * f)) (π : M →* Λ)
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {R : Subgroup M}
    (hR : IsSylowOf 2 R ⊤) :
    ∃ J : Subgroup M, J ≤ normalizer (R : Set M) ∧ Odd (Nat.card J) ∧
      ∀ x ∈ R ⊓ centralizer (R : Set M), x ≠ 1 → ∀ y ∈ R ⊓ centralizer (R : Set M), y ≠ 1 →
        ∃ j ∈ J, j * x * j⁻¹ = y := by
  have hA : LieModel (↥(⊤ : Subgroup Λ)) .PSL 3 2 (2 * f) :=
    LieModel.of_mulEquiv Subgroup.topEquiv.symm hΛ
  have hV := linto_isSylowOf_map π hπ hker hR
  obtain ⟨J', -, hJ'N, hJ'odd, htrans⟩ := l3Torus f hf Λ ⊤ hA (R.map π) hV
  exact exists_odd_normalizer_transitive π hπ hker hR hJ'N hJ'odd htrans

end LinCase

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_exists_odd_torus (hl : d.LinCtx) {R : Subgroup G} (hR : IsSylowOf 2 R d.M₂) :
    ∃ J : Subgroup G, J ≤ d.M₂ ∧ J ≤ normalizer (R : Set G) ∧ Odd (Nat.card J) ∧
      ∀ x ∈ R ⊓ centralizer (R : Set G), x ≠ 1 → ∀ y ∈ R ⊓ centralizer (R : Set G), y ≠ 1 →
        ∃ j ∈ J, j * x * j⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by have := hl.hyp.two_le; omega
  have hRle : R ≤ d.M₂ := hR.le
  have hR' : IsSylowOf 2 (R.subgroupOf d.M₂) (⊤ : Subgroup ↥d.M₂) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hR.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hR).2.2
  obtain ⟨J₀, hJ₀N, hJ₀odd, hJ₀t⟩ := LinCase.exists_odd_torus_of_odd_ker hf
    (lin_layer_facts hl).2.1 (linπ hl) (lin_π_surjective hl) (lin_π_ker_odd hl) hR'
  refine ⟨J₀.map d.M₂.subtype, fun x ⟨j, _, hj⟩ => hj ▸ j.2, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxM : x ∈ d.M₂ := hRle hx
      have := (mem_normalizer_iff.1 (hJ₀N hj) ⟨x, hxM⟩).1 (mem_subgroupOf.2 hx)
      exact mem_subgroupOf.1 this
    · intro hx
      have hxM : (j : G) * x * (j : G)⁻¹ ∈ d.M₂ := hRle hx
      have hxM' : x ∈ d.M₂ := by
        have := mul_mem (mul_mem (inv_mem j.2) hxM) j.2
        simpa [mul_assoc] using this
      have := (mem_normalizer_iff.1 (hJ₀N hj) ⟨x, hxM'⟩).2
        (mem_subgroupOf.2 (by simpa using hx))
      exact mem_subgroupOf.1 this
  · rw [Subgroup.card_map_of_injective d.M₂.subtype_injective]
    exact hJ₀odd
  · intro x hx hx1 y hy hy1
    have hxM : x ∈ d.M₂ := hRle hx.1
    have hyM : y ∈ d.M₂ := hRle hy.1
    have hcen : ∀ (z : G) (hzM : z ∈ d.M₂), z ∈ R ⊓ centralizer (R : Set G) →
        (⟨z, hzM⟩ : ↥d.M₂) ∈
          R.subgroupOf d.M₂ ⊓ centralizer ((R.subgroupOf d.M₂ : Subgroup ↥d.M₂) : Set ↥d.M₂) := by
      intro z hzM hz
      refine Subgroup.mem_inf.2 ⟨mem_subgroupOf.2 hz.1, mem_centralizer_iff.2 fun w hw => ?_⟩
      exact Subtype.ext (mem_centralizer_iff.1 hz.2 (w : G) (mem_subgroupOf.1 hw))
    obtain ⟨j, hj, hjxy⟩ := hJ₀t ⟨x, hxM⟩ (hcen x hxM hx) (fun e => hx1 (congrArg Subtype.val e))
      ⟨y, hyM⟩ (hcen y hyM hy) (fun e => hy1 (congrArg Subtype.val e))
    exact ⟨(j : G), ⟨j, hj, rfl⟩, congrArg Subtype.val hjxy⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
