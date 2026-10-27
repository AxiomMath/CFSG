module

public import Mathlib
public import CFSG.ClassicalInvolution.Omega
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsKG2Dichotomy
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

section UniqueInvolution

variable {Y : Type} [Group Y] [Finite Y]

theorem isUniqueInvolution_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) : IsUniqueInvolution L z := by
  have hodd := odd_natCard_galoisField hp2 hq
  obtain ⟨e⟩ := h.nonempty_equiv
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hzc : ∀ l ∈ L, z * l = l * z := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (isSubnormal_le h.subnormal hl) z (Set.mem_singleton z)
  have hz2 : orderOf z = 2 := h.orderOf_eq_two
  refine ⟨h.mem, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  · intro y hy hy2
    set y' : L := ⟨y, hy⟩ with hy'
    set z' : L := ⟨z, h.mem⟩ with hz'
    have hz'c : ∀ l : L, l * z' = z' * l := fun l => Subtype.ext (hzc l.1 l.2).symm
    have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz2
    by_cases hy1 : y' = 1
    · exact Or.inl (congrArg Subtype.val hy1)
    · refine Or.inr ?_
      have hyy : y' * y' = 1 := Subtype.ext hy2
      have hord : orderOf y' = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
      have hρy := (orderOf_eq_two_iff_of_equiv_sl2 hodd e
        (QuotientGroup.mk' (classicalInvolutionOddCore L) y')).mp
        (orderOf_mk_oddCore_eq_two hord)
      have hρz := (orderOf_eq_two_iff_of_equiv_sl2 hodd e
        (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp
        (orderOf_mk_oddCore_eq_two hz'2)
      have hmem : z'⁻¹ * y' ∈ classicalInvolutionOddCore L :=
        QuotientGroup.eq.mp (hρz.trans hρy.symm)
      have hzz : z' * z' = 1 := by
        have := pow_orderOf_eq_one z'
        rwa [hz'2, pow_two] at this
      have hyo : y' = z' * (z'⁻¹ * y') := by group
      set o : L := z'⁻¹ * y' with ho
      have hoo : o * o = 1 := by
        have h1 : (z' * o) * (z' * o) = (z' * z') * (o * o) := by
          calc (z' * o) * (z' * o) = z' * (o * z') * o := by group
            _ = z' * (z' * o) * o := by rw [hz'c o]
            _ = (z' * z') * (o * o) := by group
        rw [← hyo, hyy, hzz, one_mul] at h1
        exact h1.symm
      have ho1 : o = 1 := by
        by_contra ho1
        exact ho1 (eq_one_of_mem_odd_of_orderOf_eq_two_pow hOodd hmem (k := 1)
          (by rw [pow_one]; exact orderOf_eq_prime (by rwa [pow_two]) ho1))
      rw [ho1, mul_one] at hyo
      exact congrArg Subtype.val hyo

end UniqueInvolution

section Twins

variable {G : Type} [Group G]

theorem orderOf_eq_two_of_isUniqueInvolution {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one

theorem eq_of_orderOf_eq_two_of_isUniqueInvolution {K : Subgroup G} {z t : G}
    (hz : IsUniqueInvolution K z) (ht : t ∈ K) (h2 : orderOf t = 2) : t = z := by
  have hsq : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h2, pow_two] at this
  rcases hz.unique t ht hsq with h1 | h1
  · rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact h1

theorem conjSub_mem_omegaAt_self {K : Subgroup G} {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c K ∈ omegaAt K z z := by
  rw [omegaAt_self_eq_map_conj]
  exact ⟨c, hc, rfl⟩

theorem conjSub_eq_or_twin {K : Subgroup G} {z c : G} (hz : IsUniqueInvolution K z)
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c K = K ∨ (conjSub c K ≠ K ∧ IsUniqueInvolution (conjSub c K) z ∧
      conjSub c K ∈ omegaAt K z z) := by
  by_cases h : conjSub c K = K
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_, conjSub_mem_omegaAt_self hc⟩
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hc z (Set.mem_singleton z)
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have := hz.conj c
    rwa [hcz] at this

theorem not_commutes_conjSub_of_mem {K₁ K₂ : Subgroup G} {c : G} (hc : c ∈ K₂)
    (hnc : ¬ Commutes K₁ K₂) : ¬ Commutes (conjSub c K₁) K₂ := by
  intro h
  apply hnc
  intro x hx y hy
  have hcy : c * y * c⁻¹ ∈ K₂ := K₂.mul_mem (K₂.mul_mem hc hy) (K₂.inv_mem hc)
  have h1 := h (c * x * c⁻¹) (conj_mem_conjSub hx) (c * y * c⁻¹) hcy
  have h2 : c * (x * y) * c⁻¹ = c * (y * x) * c⁻¹ := by
    calc c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      _ = (c * y * c⁻¹) * (c * x * c⁻¹) := h1
      _ = c * (y * x) * c⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

@[expose] def NormalizesOrSwaps (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop :=
  conjSub z₂ K₁ = K₁ ∨ (conjSub z₂ K₁ ≠ K₁ ∧ IsUniqueInvolution (conjSub z₂ K₁) z₁ ∧
    ¬ Commutes (conjSub z₂ K₁) K₂)

theorem normalizesOrSwaps_of_commuting {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (h₁ : IsUniqueInvolution K₁ z₁) (h₂ : IsUniqueInvolution K₂ z₂) (hcomm : z₁ * z₂ = z₂ * z₁)
    (hnc : ¬ Commutes K₁ K₂) : NormalizesOrSwaps K₁ K₂ z₁ z₂ := by
  have hc : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hcomm
  rcases conjSub_eq_or_twin h₁ hc with h | ⟨h, h', -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, h', not_commutes_conjSub_of_mem h₂.mem hnc⟩

theorem exists_a2Pair [Finite G] {K : Subgroup G} {z : G} (hb : Branch p f K z) :
    ∃ K₁ K₂ : Subgroup G, ∃ z₁ z₂ : G, K₁ ∈ omegaAt K z z₁ ∧ K₂ ∈ omegaAt K z z₂ ∧
      IsUniqueInvolution K₁ z₁ ∧ IsUniqueInvolution K₂ z₂ ∧ K₁ ≠ K₂ ∧ z₁ ≠ z₂ ∧
      z₁ * z₂ = z₂ * z₁ ∧ ¬ Commutes K₁ K₂ := by
  have hU := isUniqueInvolution_of_isClassicalMember hb.odd hb.five hb.member
  obtain ⟨g, h, hne, hzne, hcomm, hnc⟩ := hb.a2
  have hU₁ : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have := hU.conj g⁻¹
    rwa [inv_inv] at this
  have hU₂ : IsUniqueInvolution (conjSub h⁻¹ K) (h⁻¹ * z * h) := by
    have := hU.conj h⁻¹
    rwa [inv_inv] at this
  exact ⟨conjSub g⁻¹ K, conjSub h⁻¹ K, g⁻¹ * z * g, h⁻¹ * z * h, ⟨g, rfl, rfl⟩, ⟨h, rfl, rfl⟩,
    hU₁, hU₂, hne, hzne, hcomm, hnc⟩

theorem a2Configuration_good_or_swap [Finite G] {K : Subgroup G} {z : G}
    (hb : Branch p f K z) :
    ∃ K₁ ∈ conjClass K, ∃ K₂ ∈ conjClass K, ∃ z₁ z₂ : G, IsUniqueInvolution K₁ z₁ ∧
      IsUniqueInvolution K₂ z₂ ∧ K₁ ≠ K₂ ∧ z₁ ≠ z₂ ∧ z₁ * z₂ = z₂ * z₁ ∧ ¬ Commutes K₁ K₂ ∧
      NormalizesOrSwaps K₁ K₂ z₁ z₂ ∧ NormalizesOrSwaps K₂ K₁ z₂ z₁ := by
  obtain ⟨K₁, K₂, z₁, z₂, hK₁, hK₂, h₁, h₂, hne, hzne, hcomm, hnc⟩ := exists_a2Pair hb
  refine ⟨K₁, ?_, K₂, ?_, z₁, z₂, h₁, h₂, hne, hzne, hcomm, hnc,
    normalizesOrSwaps_of_commuting h₁ h₂ hcomm hnc,
    normalizesOrSwaps_of_commuting h₂ h₁ hcomm.symm (fun hc => hnc hc.symm)⟩
  · rw [← conjugateSet_eq_range]
    exact omegaAt_subset_conjugateSet K z z₁ hK₁
  · rw [← conjugateSet_eq_range]
    exact omegaAt_subset_conjugateSet K z z₂ hK₂

end Twins

section Tight

variable {G : Type} [Group G] [Finite G]

theorem conjSub_eq_of_tightlyEmbedded {K A : Subgroup G} {z a c : G}
    (hz : IsUniqueInvolution K z) (hT : classicalInvolutionTightlyEmbedded K)
    (hA : A ∈ omegaAt K z a) (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    conjSub c A = A := by
  have hord := orderOf_eq_two_of_isUniqueInvolution hz
  have hU : ∀ t ∈ K, orderOf t = 2 → t = z := fun t ht h2 =>
    eq_of_orderOf_eq_two_of_isUniqueInvolution hz ht h2
  have hsub := (tightlyEmbedded_iff_subsingleton_omegaAt hz.mem hord hU).mp hT a
  have hA' : conjSub c A ∈ omegaAt K z a := by
    rw [omegaAt_eq_orbit hA]
    exact ⟨c, hc, rfl⟩
  exact hsub hA' hA

theorem eq_of_tightlyEmbedded {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hT : classicalInvolutionTightlyEmbedded K) {A B : Subgroup G} {w : G}
    (hA : A ∈ conjClass K) (hB : B ∈ conjClass K) (hwA : IsUniqueInvolution A w)
    (hwB : IsUniqueInvolution B w) : A = B := by
  have hord := orderOf_eq_two_of_isUniqueInvolution hz
  have hU : ∀ t ∈ K, orderOf t = 2 → t = z := fun t ht h2 =>
    eq_of_orderOf_eq_two_of_isUniqueInvolution hz ht h2
  have hsub := (tightlyEmbedded_iff_subsingleton_omegaAt hz.mem hord hU).mp hT w
  have hw2 := orderOf_eq_two_of_isUniqueInvolution hwA
  rw [← conjugateSet_eq_range] at hA hB
  exact hsub ((mem_omegaAt_iff_of_unique_involution hz.mem hord hU).mpr ⟨hA, hwA.mem, hw2⟩)
    ((mem_omegaAt_iff_of_unique_involution hz.mem hord hU).mpr ⟨hB, hwB.mem, hw2⟩)

theorem a2Configuration_good_of_tightlyEmbedded {K : Subgroup G} {z : G}
    (hb : Branch p f K z) (hT : classicalInvolutionTightlyEmbedded K) :
    ∃ K₁ ∈ conjClass K, ∃ K₂ ∈ conjClass K, ∃ z₁ z₂ : G, IsUniqueInvolution K₁ z₁ ∧
      IsUniqueInvolution K₂ z₂ ∧ K₁ ≠ K₂ ∧ z₁ ≠ z₂ ∧ z₁ * z₂ = z₂ * z₁ ∧ ¬ Commutes K₁ K₂ ∧
      conjSub z₂ K₁ = K₁ ∧ conjSub z₁ K₂ = K₂ := by
  have hU := isUniqueInvolution_of_isClassicalMember hb.odd hb.five hb.member
  obtain ⟨K₁, K₂, z₁, z₂, hK₁, hK₂, h₁, h₂, hne, hzne, hcomm, hnc⟩ := exists_a2Pair hb
  have hc₂ : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hcomm
  have hc₁ : z₁ ∈ Subgroup.centralizer ({z₂} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hcomm.symm
  refine ⟨K₁, ?_, K₂, ?_, z₁, z₂, h₁, h₂, hne, hzne, hcomm, hnc,
    conjSub_eq_of_tightlyEmbedded hU hT hK₁ hc₂, conjSub_eq_of_tightlyEmbedded hU hT hK₂ hc₁⟩
  · rw [← conjugateSet_eq_range]
    exact omegaAt_subset_conjugateSet K z z₁ hK₁
  · rw [← conjugateSet_eq_range]
    exact omegaAt_subset_conjugateSet K z z₂ hK₂

end Tight

section Inputs

variable (p f)

@[expose] def A2DatumTight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → classicalInvolutionTightlyEmbedded K → HasDatum p f K

@[expose] def A2DatumTwins : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → ¬ classicalInvolutionTightlyEmbedded K → HasDatum p f K

theorem a2Datum_of_cases (h₁ : A2DatumTight p f) (h₂ : A2DatumTwins p f) : A2Datum p f := by
  intro G _ _ _ K z hb
  by_cases hT : classicalInvolutionTightlyEmbedded K
  · exact h₁ G K z hb hT
  · exact h₂ G K z hb hT

end Inputs

section Exact

variable {G : Type} [Group G]

theorem oddCore_range_eq_bot {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {φ : SL(2, F) →* G} (hφ : Function.Injective φ) :
    classicalInvolutionOddCore ↥φ.range = ⊥ := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  let e : SL(2, F) ≃* φ.range := MonoidHom.ofInjective hφ
  have h := CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hO : componentClassificationOddCore SL(2, F) = ⊥ :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.oddCore_sl2_eq_bot h2 h4
  rw [hO, Subgroup.map_bot] at h
  exact h.symm

theorem exactMembers_of_mem_frame {K : Subgroup G} {F : Type} [Field F] {A : Subgroup G}
    {S : Set (Subgroup G)} (Fr : RankFrame F (conjClass K) A S) {K₁ : Subgroup G} (h₁ : K₁ ∈ S) :
    ExactMembers (conjClass K) := by
  have : Finite F := Fr.finite
  obtain ⟨φ, hφ, hD⟩ := Fr.inSigma h₁
  have h5 := Fr.five
  have hO : classicalInvolutionOddCore ↥K₁ = ⊥ := by
    rw [← hφ]
    exact oddCore_range_eq_bot Fr.odd (by omega) hD.inj
  exact Balance.exactMembers_of_oddCore_eq_bot ⟨K, mem_conjClass_self K, single_class K⟩
    (Fr.subset h₁) hO

end Exact

section Connected

variable {G : Type} [Group G]

theorem exists_neighbor_of_connected {K : Subgroup G} (hconn : DeltaConnected K)
    {K₁ K₂ B : Subgroup G} (h₁ : K₁ ∈ conjClass K) (hB : B ∈ conjClass K) (hB₁ : B ≠ K₁)
    (hB₂ : B ≠ K₂) :
    ∃ J, J ∈ conjClass K ∧ J ≠ K₁ ∧ J ≠ K₂ ∧ (Commutes K₁ J ∨ Commutes K₂ J) := by
  rw [← conjugateSet_eq_range] at h₁ hB
  have hpath := hconn K₁ h₁ B hB
  have key : ∀ Y, Relation.ReflTransGen (commutingAdj K) K₁ Y →
      Y = K₁ ∨ Y = K₂ ∨ ∃ J, J ∈ conjugateSet K ∧ J ≠ K₁ ∧ J ≠ K₂ ∧
        (Commutes K₁ J ∨ Commutes K₂ J) := by
    intro Y hY
    induction hY with
    | refl => exact Or.inl rfl
    | @tail b c _ hadj ih =>
      rcases ih with hb | hb | hex
      · subst hb
        obtain ⟨-, hc, -, hcomm⟩ := hadj
        by_cases hcK₁ : c = b
        · exact Or.inl hcK₁
        by_cases hcK₂ : c = K₂
        · exact Or.inr (Or.inl hcK₂)
        exact Or.inr (Or.inr ⟨c, hc, hcK₁, hcK₂, Or.inl hcomm⟩)
      · subst hb
        obtain ⟨-, hc, -, hcomm⟩ := hadj
        by_cases hcK₁ : c = K₁
        · exact Or.inl hcK₁
        by_cases hcK₂ : c = b
        · exact Or.inr (Or.inl hcK₂)
        exact Or.inr (Or.inr ⟨c, hc, hcK₁, hcK₂, Or.inr hcomm⟩)
      · exact Or.inr (Or.inr hex)
  rcases key B hpath with h | h | ⟨J, hJ, hJ₁, hJ₂, hJc⟩
  · exact absurd h hB₁
  · exact absurd h hB₂
  · exact ⟨J, by rw [← conjugateSet_eq_range]; exact hJ, hJ₁, hJ₂, hJc⟩

end Connected

section NoTwins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_chart_of_exact (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {L : Subgroup G} {t : G}
    (hL : IsClassicalMember p f L t) (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ φ : SL(2, GaloisField p f) →* G, Function.Injective φ ∧ φ.range = L ∧ φ (-1) = t := by
  obtain ⟨e⟩ := hL.nonempty_equiv_sl2 hO
  have hodd := odd_natCard_galoisField hp2 hq
  let φ : SL(2, GaloisField p f) →* G := L.subtype.comp e.symm.toMonoidHom
  have hinj : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hrange : φ.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [φ]⟩
  refine ⟨φ, hinj, hrange, ?_⟩
  have hU := isUniqueInvolution_of_isClassicalMember hp2 hq hL
  have hmem : φ (-1) ∈ L := hrange ▸ ⟨-1, rfl⟩
  have h2 : orderOf (φ (-1)) = 2 := by
    rw [orderOf_injective φ hinj, sl2_orderOf_neg_one hodd]
  exact eq_of_orderOf_eq_two_of_isUniqueInvolution hU hmem h2

theorem bootData_of_twin_charts {K : Subgroup G} {z : G} (hb : Branch p f K z) {F : Type}
    [Field F] [Finite F] (hodd : Odd (Nat.card F)) {φ₁ φ₂ : SL(2, F) →* G}
    (h₁ : Function.Injective φ₁) (hcom : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x)
    (hw : φ₁ (-1) = φ₂ (-1)) {M : Subgroup G} (hM : M ∈ conjClass K)
    (hc₁ : ∀ m ∈ M, ∀ x, m * φ₁ x = φ₁ x * m) (hc₂ : ∀ m ∈ M, ∀ y, m * φ₂ y = φ₂ y * m) :
    BootData p f (conjClass K) := by
  obtain ⟨g, rfl⟩ := hM
  have hU := isUniqueInvolution_of_isClassicalMember hb.odd hb.five hb.member
  have hm := hU.conj g
  obtain ⟨E, hEel, hEcard, hmE, hME⟩ := exists_elemAbelian_eight_of_twin_charts hodd h₁ hcom hw
    (M := conjSub g K) hc₁ hc₂ hm.mem hm.sq hm.ne_one
    (fun m' hm' => mul_comm_of_isUniqueInvolution hm hm')
  exact ⟨conjSub g K, g * z * g⁻¹, E, ⟨g, rfl⟩, hb.member.conj g, hEel, hEcard, hmE, hME⟩

omit [Finite G] in
theorem exists_third_member {M₁ M₂ K₁ K₂ : Subgroup G} (hM12 : M₁ ≠ M₂)
    (hnc : ¬ Commutes M₁ M₂) (hcom : Commutes K₁ K₂) :
    (M₁ ≠ K₁ ∧ M₁ ≠ K₂) ∨ (M₂ ≠ K₁ ∧ M₂ ≠ K₂) := by
  by_contra hcon
  rw [not_or, not_and_or, not_and_or, not_not, not_not, not_not, not_not] at hcon
  obtain ⟨e1, e2⟩ := hcon
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
  · exact hM12 rfl
  · exact hnc hcom
  · exact hnc hcom.symm
  · exact hM12 rfl

variable [IsSimpleGroup G]

theorem false_of_twins {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ conjClass K)
    (h₂ : K₂ ∈ conjClass K) {w : G} (hw₁ : IsUniqueInvolution K₁ w)
    (hw₂ : IsUniqueInvolution K₂ w) (hP1 : LocalOddCentral (conjClass K) {w}) (hne : K₁ ≠ K₂) :
    False := by
  have hcl₁ := isClassicalMember_of_isUniqueInvolution hb.member h₁ hw₁
  have hcl₂ := isClassicalMember_of_isUniqueInvolution hb.member h₂ hw₂
  have hN₁ : K₁ ∈ centralizingMembers (conjClass K) {w} := ⟨h₁, DeltaClosure.le_centralizer hcl₁⟩
  have hN₂ : K₂ ∈ centralizingMembers (conjClass K) {w} := ⟨h₂, DeltaClosure.le_centralizer hcl₂⟩
  have hcom : Commutes K₁ K₂ := by
    rcases commutes_or_eq_of_branch hb hex hw₁.ne_one hP1 hN₁ hN₂ hcl₁ with h | h
    · exact h
    · exact absurd h.symm hne
  obtain ⟨φ₁, hφ₁i, hφ₁, hφ₁w⟩ := exists_chart_of_exact hb.odd hb.five hcl₁ (hex K₁ h₁)
  obtain ⟨φ₂, -, hφ₂, hφ₂w⟩ := exists_chart_of_exact hb.odd hb.five hcl₂ (hex K₂ h₂)
  have hodd := odd_natCard_galoisField hb.odd hb.five
  have hmem₁ : ∀ x, φ₁ x ∈ K₁ := fun x => by rw [← hφ₁]; exact ⟨x, rfl⟩
  have hmem₂ : ∀ y, φ₂ y ∈ K₂ := fun y => by rw [← hφ₂]; exact ⟨y, rfl⟩
  obtain ⟨M₁, M₂, z₁, z₂, hM₁, hM₂, -, -, hM12, -, -, hnc⟩ := exists_a2Pair hb
  have hM₁Ω : M₁ ∈ conjClass K := by
    rw [← conjugateSet_eq_range]
    exact omegaAt_subset_conjugateSet K z z₁ hM₁
  have hM₂Ω : M₂ ∈ conjClass K := by
    rw [← conjugateSet_eq_range]
    exact omegaAt_subset_conjugateSet K z z₂ hM₂
  obtain ⟨B, hBΩ, hB₁, hB₂⟩ : ∃ B ∈ conjClass K, B ≠ K₁ ∧ B ≠ K₂ := by
    rcases exists_third_member hM12 hnc hcom with h | h
    · exact ⟨M₁, hM₁Ω, h.1, h.2⟩
    · exact ⟨M₂, hM₂Ω, h.1, h.2⟩
  obtain ⟨J, hJ, hJ₁, hJ₂, hJc⟩ := exists_neighbor_of_connected hb.connected h₁ hBΩ hB₁ hB₂
  have hJw : ∀ N : Subgroup G, Commutes N J → w ∈ N →
      J ∈ centralizingMembers (conjClass K) {w} := fun N hN hwN =>
    ⟨hJ, fun j hj => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hN w hwN j hj⟩
  have hcharts := fun {M : Subgroup G} (hM : M ∈ conjClass K) (hc₁ : Commutes M K₁)
      (hc₂ : Commutes M K₂) =>
    bootData_of_twin_charts hb hodd hφ₁i
      (fun x y => hcom _ (hmem₁ x) _ (hmem₂ y)) (hφ₁w.trans hφ₂w.symm) hM
      (fun m' hm' x => hc₁ m' hm' _ (hmem₁ x)) (fun m' hm' y => hc₂ m' hm' _ (hmem₂ y))
  rcases hJc with hc | hc
  · rcases commutes_or_eq_of_branch hb hex hw₁.ne_one hP1 hN₂ (hJw K₁ hc hw₁.mem) hcl₂ with
      h | h
    · exact hb.noBoot (hcharts hJ hc.symm h.symm)
    · exact hJ₂ h
  · rcases commutes_or_eq_of_branch hb hex hw₁.ne_one hP1 hN₁ (hJw K₂ hc hw₂.mem) hcl₁ with
      h | h
    · exact hb.noBoot (hcharts hJ h.symm hc.symm)
    · exact hJ₁ h

theorem eq_of_same_involution_of_branch {K : Subgroup G} {z : G} (hb : Branch p f K z)
    {F : Type} [Field F] {A : Subgroup G} {S : Set (Subgroup G)}
    (Fr : RankFrame F (conjClass K) A S) (hP1 : FrameP1 (conjClass K) A) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ S) (h₂ : K₂ ∈ S) {w : G} (hw₁ : IsUniqueInvolution K₁ w)
    (hw₂ : IsUniqueInvolution K₂ w) : K₁ = K₂ := by
  by_contra hne
  exact false_of_twins hb (exactMembers_of_mem_frame Fr h₁) (Fr.subset h₁) (Fr.subset h₂) hw₁ hw₂
    (hP1 w (Fr.mem_of_isUniqueInvolution h₁ hw₁) hw₁.ne_one) hne

theorem tightlyEmbedded_of_branch {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (hP1 : LocalOddCentral (conjClass K) {z}) :
    classicalInvolutionTightlyEmbedded K := by
  have hU := isUniqueInvolution_of_isClassicalMember hb.odd hb.five hb.member
  have hord := orderOf_eq_two_of_isUniqueInvolution hU
  have hUk : ∀ t ∈ K, orderOf t = 2 → t = z := fun t ht h2 =>
    eq_of_orderOf_eq_two_of_isUniqueInvolution hU ht h2
  rw [tightlyEmbedded_iff_omegaAt_self_eq hU.mem hord hUk, Set.eq_singleton_iff_unique_mem]
  refine ⟨self_mem_omegaAt K z, fun K₂ hK₂ => ?_⟩
  by_contra hne
  obtain ⟨g, rfl, hgz⟩ := hK₂
  have hU₂ : IsUniqueInvolution (conjSub g⁻¹ K) z := by
    have := hU.conj g⁻¹
    rwa [inv_inv, hgz] at this
  exact false_of_twins hb hex (mem_conjClass_self K) ⟨g⁻¹, rfl⟩ hU hU₂ hP1 (Ne.symm hne)

end NoTwins

section Injective

variable (p f)

theorem a2InjectiveCentral : A2InjectiveCentral p f := by
  intro G _ _ _ K z hb hD F _ hF A S Fr hcard hnc hP1A ht K' hK' L' hL' hw hax
  obtain ⟨w, hwK, hwL⟩ := hw
  exact eq_of_same_involution_of_branch hb Fr hP1A hK' hL' hwK hwL

variable {p f}

theorem smallConnectedA2_of_model_facts_noInjective (hD : A2Datum p f) (hP1 : A2P1 p f)
    (hN : A2NoG2D4 p f) (hFE : ModelFacts.StandardPairDichotomyFE p) (hO : A2OrthEndpoint p f) :
    CoreAssembly.SmallConnectedA2 p f :=
  smallConnectedA2_of_model_facts hD hP1 hN hFE (a2InjectiveCentral p f) hO

end Injective

end CFSG.ClassicalInvolution.ConnectedA2
