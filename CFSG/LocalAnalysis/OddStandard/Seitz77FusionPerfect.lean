module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Act
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionGen
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

private theorem not_surjective_units_of_isPerfect {H : Type*} [Group H]
    (hH : Group.IsPerfect H) (ε : H →* ℤˣ) : ¬ Function.Surjective ε := by
  intro hsurj
  obtain ⟨h, hh⟩ := hsurj (-1)
  have hmem : h ∈ commutator H := by
    rw [hH.commutator_eq_top]
    exact Subgroup.mem_top h
  have hker : ε h = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker ε hmem)
  rw [hker] at hh
  exact absurd hh (by decide)

theorem odd_card_of_isPerfect_of_cyclic_sylow {H : Type*} [Group H] [Finite H]
    (hH : Group.IsPerfect H) (hcyc : ∀ S : Sylow 2 H, IsCyclic ↥S) : Odd (Nat.card H) := by
  classical
  by_contra hodd
  have heven : Even (Nat.card H) := Nat.not_odd_iff_even.mp hodd
  have := Fintype.ofFinite H
  have heven' : Even (Fintype.card H) := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨-, hsurj, -, -⟩ :=
    CFSG.LinearGroups.cyclic_sylow_index_two heven' default (hcyc default)
  exact not_surjective_units_of_isPerfect hH _ hsurj

theorem cyclic_sylow_of_surjective {K Q : Type*} [Group K] [Finite K] [Group Q]
    (φ : K →* Q) (hφ : Function.Surjective φ) (hK : ∀ S : Sylow 2 K, IsCyclic ↥S) :
    ∀ T : Sylow 2 Q, IsCyclic ↥T := by
  intro T
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hφ 2 T
  have := hK S
  exact isCyclic_of_surjective _ (φ.subgroupMap_surjective S)

theorem cyclic_sylow_of_le {Q : Type*} [Group Q] [Finite Q]
    (hQ : ∀ S : Sylow 2 Q, IsCyclic ↥S) (H : Subgroup Q) : ∀ T : Sylow 2 ↥H, IsCyclic ↥T := by
  intro T
  obtain ⟨S, hS⟩ := (T.2.map H.subtype).exists_le_sylow
  have := hQ S
  have : IsCyclic (T.toSubgroup.map H.subtype) := Subgroup.isCyclic_of_le hS
  exact isCyclic_of_surjective _
    (Subgroup.equivMapOfInjective T.toSubgroup H.subtype H.subtype_injective).symm.surjective

private theorem card_primeFactors_twelve_le : (Nat.primeFactors 12).card ≤ 2 := by
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h12, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

theorem eq_bot_of_perfect_of_card_twelve {Q : Type*} [Group Q] (hQ : Nat.card Q = 12)
    (H : Subgroup Q) (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Group.IsSolvable Q :=
    CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      (by rw [hQ]; exact card_primeFactors_twelve_le)
  by_contra hne
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  exact Group.IsPerfect.not_isSolvable H inferInstance

theorem mem_of_mul_self_of_perfect {G : Type*} [Group G]
    [Finite G] {A : Subgroup G} (hA : commutator ↥A = ⊤)
    (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S)
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    {D : Subgroup G} (hDN : D ≤ normalizer (A : Set G)) (hD : ⁅D, D⁆ = D) {c : G} (hc : c ∈ D)
    (hc2 : c * c = 1) : c ∈ A := by
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hA e
  have hDperf : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hD
  let Nₛ : Subgroup ↥PSL3Four.R := PSL3Four.S.subgroupOf PSL3Four.R
  have : Nₛ.Normal := PSL3Four.S_normal
  have hN : Nat.card Nₛ = 20160 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe PSL3Four.S_le_R).toEquiv, PSL3Four.card_S]
  have hQ : Nat.card (PSL3Four.R ⧸ Nₛ) = 12 := by
    have h := card_eq_card_quotient_mul_card_subgroup Nₛ
    rw [PSL3Four.card_R, hN] at h
    omega
  let f : ↥D →* ↥PSL3Four.R ⧸ Nₛ :=
    (QuotientGroup.mk' Nₛ).comp (ψ.comp (Subgroup.inclusion hDN))
  have hfperf : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hfbot : f.range = ⊥ :=
    eq_bot_of_perfect_of_card_twelve hQ f.range (Subgroup.isPerfect_iff.mp hfperf)
  have hDAK : ∀ d ∈ D, d ∈ A ⊔ centralizer (A : Set G) := by
    intro d hd
    have h1 : f ⟨d, hd⟩ = 1 := by
      have : f ⟨d, hd⟩ ∈ f.range := ⟨_, rfl⟩
      rw [hfbot, Subgroup.mem_bot] at this
      exact this
    have h2 : ψ ⟨d, hDN hd⟩ ∈ Nₛ := (QuotientGroup.eq_one_iff _).1 h1
    exact (L34.mem_sup_centralizer_iff hψ (hDN hd)).2 h2
  let N₀ : Subgroup G := normalizer (A : Set G)
  let A' : Subgroup ↥N₀ := A.subgroupOf N₀
  have hA'n : A'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl
  let q : ↥N₀ →* ↥N₀ ⧸ A' := QuotientGroup.mk' A'
  have hKN : centralizer (A : Set G) ≤ N₀ := Subgroup.centralizer_le_normalizer _
  let φ : ↥(centralizer (A : Set G)) →* ↥N₀ ⧸ A' := q.comp (Subgroup.inclusion hKN)
  have hQcyc : ∀ T : Sylow 2 ↥φ.range, IsCyclic ↥T :=
    cyclic_sylow_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective hcyc
  let f₂ : ↥D →* ↥N₀ ⧸ A' := q.comp (Subgroup.inclusion hDN)
  have hf₂ : ∀ x : ↥D, f₂ x ∈ φ.range := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, hdak⟩ := mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.mp hk a ha) (hDAK d hd)
    refine ⟨⟨k, hk⟩, ?_⟩
    have h1 : (⟨d, hDN hd⟩ : ↥N₀) = ⟨a, le_normalizer ha⟩ * ⟨k, hKN hk⟩ :=
      Subtype.ext hdak
    show q (Subgroup.inclusion hKN ⟨k, hk⟩) = q (Subgroup.inclusion hDN ⟨d, hd⟩)
    have h2 : q ⟨a, le_normalizer ha⟩ = 1 := (QuotientGroup.eq_one_iff _).2 ha
    show q ⟨k, hKN hk⟩ = q ⟨d, hDN hd⟩
    rw [h1, map_mul, h2, one_mul]
  let g : ↥D →* ↥φ.range := f₂.codRestrict φ.range hf₂
  have hgperf : Group.IsPerfect ↥g.range := Group.IsPerfect.range g
  have hodd : Odd (Nat.card ↥g.range) :=
    odd_card_of_isPerfect_of_cyclic_sylow hgperf (cyclic_sylow_of_le hQcyc g.range)
  let y : ↥g.range := ⟨g ⟨c, hc⟩, ⟨_, rfl⟩⟩
  have hy2 : y * y = 1 := by
    apply Subtype.ext
    show g ⟨c, hc⟩ * g ⟨c, hc⟩ = 1
    rw [← map_mul]
    have : (⟨c, hc⟩ : ↥D) * ⟨c, hc⟩ = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hy1 : y = 1 := by
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy2)
    have h2 : orderOf y ∣ Nat.card ↥g.range := orderOf_dvd_natCard y
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd hodd (Nat.not_odd_iff_even.2 (even_iff_two_dvd.2 h2))
  have hg1 : g ⟨c, hc⟩ = 1 := congrArg Subtype.val hy1
  have hq1 : q ⟨c, hDN hc⟩ = 1 := congrArg Subtype.val hg1
  have hmem : (⟨c, hDN hc⟩ : ↥N₀) ∈ A' := (QuotientGroup.eq_one_iff (N := A') _).1 hq1
  exact hmem

end CFSG.OddStandard.Seitz77
