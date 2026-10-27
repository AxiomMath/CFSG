module

public import CFSG.ClassicalInvolution.Balance.PassTwoLocal
public import CFSG.ClassicalInvolution.Balance.PassTwoGeneral
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Components

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaFreeAt_or_rankOneAt_or_isOddLieComponent (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {a : G}
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) :
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ IsOddLieComponent L := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH ha
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · rcases D.rankOne_or_lie i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hlie
    · right
      left
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    · exact Or.inr (Or.inr hlie)
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Ω a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    exact (hcomm y hy x hxY).symm

end Components

section BProperty

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isQuasisimple_of_isTwoComponent_of_isQuasisimple {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {M : Subgroup Q} (hM : TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M := by
  have : Group.IsPerfect ↥M := ⟨TwoComponents.perfect hM⟩
  exact Quasisimple.perfect_subnormal_quasisimple hQ M hM.1
    ((Subgroup.nontrivial_iff_ne_bot M).mp (TwoComponents.nontrivial hM))

theorem hB_of_localLieSystems (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {L₀ : Subgroup G} (hL₀ : L₀ ∈ Ω) {z₀ : G}
    (hz₀ : IsCentralInvolution L₀ z₀) {f₀ : G} (hf₀ : ¬ ({f₀} : Set G) ⊆ Subgroup.center G)
    (hL₀f : L₀ ≤ Subgroup.centralizer ({f₀} : Set G)) (hzf : z₀ * f₀ = f₀ * z₀)
    (M : Subgroup ↥(imageModOddCore f₀ (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer {f₀})))
    (hM : TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M ∨
      ⁅M.map (imageModOddCore f₀
        (Subgroup.centralizer {z₀} ⊓ Subgroup.centralizer {f₀})).subtype,
        imageModOddCore f₀ L₀⁆ = ⊥ := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hf₀
  have := memberJoin_normal (a := f₀) hΩ.conjInvariant
  have hLbmem : modOdd f₀ L₀ ∈ memberImages Ω f₀ := ⟨L₀, ⟨hL₀, hL₀f⟩, rfl⟩
  obtain ⟨i, hi⟩ := D.exists_le _ hLbmem
  have hz₀C : z₀ ∈ Subgroup.centralizer ({f₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzf
  set t : OddQuot f₀ := oddQuotMk f₀ ⟨z₀, hz₀C⟩ with ht
  have htL : t ∈ modOdd f₀ L₀ := oddQuotMk_mem_modOdd hz₀.mem hz₀C
  have htQ : t ∈ D.Q i := hi htL
  have hsq : (⟨z₀, hz₀C⟩ : ↥(Subgroup.centralizer ({f₀} : Set G))) * ⟨z₀, hz₀C⟩ = 1 :=
    Subtype.ext hz₀.sq
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul, hsq, map_one]
  have ht1 : t ≠ 1 := fun h =>
    hz₀.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have hQB : ∀ M₁ : Subgroup ↥(D.Q i ⊓ Subgroup.centralizer ({t} : Set (OddQuot f₀))),
      TwoComponents.IsTwoComponent M₁ → CFSG.Open.IsQuasisimple M₁ := by
    intro M₁ hM₁
    rcases D.rankOne_or_lie i with ⟨-, hmin⟩ | hlie
    ·
      have hQeq : modOdd f₀ L₀ = D.Q i := hmin _ hLbmem hi
      have hcent : D.Q i ≤ Subgroup.centralizer ({t} : Set (OddQuot f₀)) := by
        rw [← hQeq]
        rintro _ ⟨l, hl, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ht, ← map_mul, ← map_mul]
        exact congrArg (oddQuotMk f₀) (Subtype.ext (hz₀.central l hl).symm)
      have hRQ : CFSG.Open.IsQuasisimple ↥(D.Q i ⊓ Subgroup.centralizer ({t} : Set (OddQuot f₀))) :=
        Components.quasisimple_of_equiv
          (MulEquiv.subgroupCongr (inf_eq_left.mpr hcent)) (D.quasisimple i)
      exact isQuasisimple_of_isTwoComponent_of_isQuasisimple hRQ hM₁
    · exact involutionCentralizerB_of_isOddLieComponent (D.quasisimple i) hlie t ht1 ht2
        (Subgroup.le_normalizer htQ) M₁ hM₁
  have hW := imageModOddCore_centralizer hz₀C (isPGroup_zpowers_of_mul_self_eq_one hz₀.sq)
  exact isQuasisimple_or_commutator_eq_bot_of_mem_component l2PrimeBalance
    (OddCore.quotient_corefree _) (D.isComponentOf i) htQ ht2 hQB hi hW M hM

theorem modOdd_perfect_ne_bot {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    {a : G} (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) :
    ⁅modOdd a K, modOdd a K⁆ = modOdd a K ∧ modOdd a K ≠ ⊥ := by
  have hzC : z ∈ Subgroup.centralizer ({a} : Set G) := hKa hz.mem
  constructor
  · have := hz.perfect
    have : Group.IsPerfect ↥(K.subgroupOf (Subgroup.centralizer ({a} : Set G))) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hKa).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKa).symm.surjective
    have hKK := (Subgroup.commutator_eq_self (H := K.subgroupOf (Subgroup.centralizer
      ({a} : Set G))))
    unfold modOdd
    rw [← Subgroup.map_commutator, hKK]
  · intro hbot
    have hzsq : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z, hzC⟩ = 1 :=
      Subtype.ext (by
        rw [← pow_two]
        exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hz.orderOf_eq_two]))
    have hmem : oddQuotMk a ⟨z, hzC⟩ ∈ modOdd a K := oddQuotMk_mem_modOdd hz.mem hzC
    rw [hbot, Subgroup.mem_bot] at hmem
    have hz1 : z = 1 := congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hzsq hmem)
    refine absurd hz.orderOf_eq_two ?_
    rw [hz1, orderOf_one]
    omega

theorem hB_of_localLieSystems_of_centralizes (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ Ω) {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htL : ∀ l ∈ L₀, t * l = l * t) {f₀ : G} (hf₀ : ¬ ({f₀} : Set G) ⊆ Subgroup.center G)
    (hL₀f : L₀ ≤ Subgroup.centralizer ({f₀} : Set G)) (htf : t * f₀ = f₀ * t)
    (M : Subgroup ↥(imageModOddCore f₀ (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f₀})))
    (hM : TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M ∨
      ⁅M.map (imageModOddCore f₀
        (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f₀})).subtype,
        imageModOddCore f₀ L₀⁆ = ⊥ := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hf₀
  have := memberJoin_normal (a := f₀) hΩ.conjInvariant
  obtain ⟨z, hz⟩ := hΩ.classical L₀ hL₀
  have hLbmem : modOdd f₀ L₀ ∈ memberImages Ω f₀ := ⟨L₀, ⟨hL₀, hL₀f⟩, rfl⟩
  obtain ⟨i, hi⟩ := D.exists_le _ hLbmem
  have htC : t ∈ Subgroup.centralizer ({f₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htf
  set t' : OddQuot f₀ := oddQuotMk f₀ ⟨t, htC⟩ with ht'
  have hsq : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({f₀} : Set G))) * ⟨t, htC⟩ = 1 :=
    Subtype.ext ht2
  have ht'2 : t' * t' = 1 := by
    rw [ht', ← map_mul, hsq, map_one]
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have ht'L : ∀ l ∈ modOdd f₀ L₀, t' * l = l * t' := by
    rintro _ ⟨l, hl, rfl⟩
    rw [ht', ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk f₀) (Subtype.ext (htL l hl))
  obtain ⟨hperf, hne⟩ := modOdd_perfect_ne_bot hz hL₀f
  have hQ : IsComponentOf (D.Q i) ⊤ := D.isComponentOf i
  have hQB : ∀ M₁ : Subgroup ↥(D.Q i ⊓ Subgroup.centralizer ({t'} : Set (OddQuot f₀))),
      TwoComponents.IsTwoComponent M₁ → CFSG.Open.IsQuasisimple M₁ := by
    intro M₁ hM₁
    rcases D.rankOne_or_lie i with ⟨-, hmin⟩ | hlie
    · have hQeq : modOdd f₀ L₀ = D.Q i := hmin _ hLbmem hi
      have hcent : D.Q i ≤ Subgroup.centralizer ({t'} : Set (OddQuot f₀)) := by
        intro q hq
        rw [← hQeq] at hq
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (ht'L q hq).symm
      have hRQ : CFSG.Open.IsQuasisimple
          ↥(D.Q i ⊓ Subgroup.centralizer ({t'} : Set (OddQuot f₀))) :=
        Components.quasisimple_of_equiv
          (MulEquiv.subgroupCongr (inf_eq_left.mpr hcent)) (D.quasisimple i)
      exact isQuasisimple_of_isTwoComponent_of_isQuasisimple hRQ hM₁
    · have hnorm : t' ∈ Subgroup.normalizer ((D.Q i : Subgroup (OddQuot f₀)) : Set (OddQuot f₀)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          (map_conj_eq_of_centralizes hQ hi hperf hne ht'L)
      exact involutionCentralizerB_of_isOddLieComponent (D.quasisimple i) hlie t' ht'1 ht'2
        hnorm M₁ hM₁
  have hW := imageModOddCore_centralizer htC (isPGroup_zpowers_of_mul_self_eq_one ht2)
  exact isQuasisimple_or_commutator_eq_bot_of_centralizes l2PrimeBalance
    (OddCore.quotient_corefree _) hQ hi hperf hne ht'2 ht'L hQB hW M hM

end BProperty

end CFSG.ClassicalInvolution.Balance
