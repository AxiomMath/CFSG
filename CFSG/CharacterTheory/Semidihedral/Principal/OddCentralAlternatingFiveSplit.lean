module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Semidihedral.Principal

universe u v

namespace OddCentralSplit

variable {K : Type u} [Group K]

theorem sylow_isMulCommutative [Finite K] (Z : Subgroup K) [Z.Normal]
    (hZ : Z ≤ Subgroup.center K) (hcard : Nat.card (K ⧸ Z) = 60) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (P : Sylow p K) : IsMulCommutative (P : Subgroup K) := by
  have hp : p.Prime := Fact.out
  let f : (P : Subgroup K) →* K ⧸ Z := (QuotientGroup.mk' Z).comp (P : Subgroup K).subtype
  have hrange : Nat.card f.range ∣ p := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp
      (P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    have hdvd : Nat.card f.range ∣ 60 := hcard ▸ Subgroup.card_subgroup_dvd_card f.range
    rw [hj] at hdvd ⊢
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · exact one_dvd p
      · rw [pow_one]
    · exfalso
      have hsq : p ^ 2 ∣ 60 := (pow_dvd_pow p hj2).trans hdvd
      have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hsq
      have hp8 : p ≤ 7 := by nlinarith
      have hp1 := hp.two_le
      interval_cases p
      · exact hp2 rfl
      · norm_num at hsq
      · norm_num at hp
      · norm_num at hsq
      · norm_num at hp
      · norm_num at hsq
  have : IsCyclic f.range := isCyclic_of_card_dvd_prime hrange
  refine f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center ?_
  intro x hx
  rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
  have hxZ : (x : K) ∈ Z := (QuotientGroup.eq_one_iff (x : K)).mp hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZ hxZ)) y)

theorem not_mem_commutator [Finite K] (Z : Subgroup K) [Z.Normal]
    (hZ : Z ≤ Subgroup.center K) (hcard : Nat.card (K ⧸ Z) = 60) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : K) (hzZ : z ∈ Z) (hz : orderOf z = p) : z ∉ commutator K := by
  intro hzc
  obtain ⟨P⟩ : Nonempty (Sylow p K) := inferInstance
  have hcomm := sylow_isMulCommutative Z hZ hcard hp2 P
  let V := MonoidHom.transfer
    (Abelianization.of : (P : Subgroup K) →* Abelianization (P : Subgroup K))
  have hcentral : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.mp (hZ hzZ) g
  have hV := MonoidHom.transfer_eq_pow (Abelianization.of : (P : Subgroup K) →* _) z
    (fun k g₀ _ => by
      have h1 : g₀ * z ^ k = z ^ k * g₀ :=
        (Commute.pow_right (hcentral g₀ : Commute g₀ z) k).eq
      rw [mul_assoc, ← h1, inv_mul_cancel_left])
  have hV1 : V z = 1 := Abelianization.commutator_subset_ker V hzc
  change V z = _ at hV
  rw [hV1] at hV
  have hmem := (Abelianization.ker_of (G := (P : Subgroup K))).le (MonoidHom.mem_ker.mpr hV.symm)
  have hbot : commutator (P : Subgroup K) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact hcomm.is_comm.comm b a
  rw [hbot, Subgroup.mem_bot] at hmem
  have hpow : z ^ (P : Subgroup K).index = 1 := congrArg Subtype.val hmem
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [hz] at hdvd
  exact P.not_dvd_index hdvd

end OddCentralSplit

theorem odd_central_alternating_five_extension_splits_over_derived_subgroup
    {K : Type u} [Group K] [Finite K] {α : Type v} [Fintype α] [DecidableEq α]
    (hα : Nat.card α = 5) (Z : Subgroup K) [Z.Normal] (hZ : Z ≤ Subgroup.center K)
    (hodd : Odd (Nat.card Z)) (hquot : Nonempty (K ⧸ Z ≃* alternatingGroup α)) :
    Z ⊓ commutator K = ⊥ ∧ Z ⊔ commutator K = ⊤ ∧
      (∀ z ∈ Z, ∀ c ∈ commutator K, z * c = c * z) ∧ Z.IsComplement' (commutator K) ∧
      Function.Bijective ((QuotientGroup.mk' Z).comp (commutator K).subtype) ∧
      Nonempty (commutator K ≃* alternatingGroup α) ∧ (commutator K).Characteristic := by
  obtain ⟨ψ⟩ := hquot
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by rw [hα]; norm_num)
  have hcard : Nat.card (K ⧸ Z) = 60 := by
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, hα]
    rfl
  have hinf : Z ⊓ commutator K = ⊥ := by
    by_contra hne
    have hc : Nat.card (Z ⊓ commutator K : Subgroup K) ≠ 1 := fun h =>
      hne (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (Z ⊓ commutator K : Subgroup K)) p hpd
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ Nat.card Z := hpd.trans (Subgroup.card_dvd_of_le inf_le_left)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
    exact OddCentralSplit.not_mem_commutator Z hZ hcard hp2 x x.2.1
      (by rw [Subgroup.orderOf_coe, hx]) x.2.2
  have hmap : (commutator K).map (QuotientGroup.mk' Z) = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup (alternatingGroup α)) ⊤ ψ.symm.toMonoidHom
    rw [Subgroup.map_top_of_surjective _ ψ.symm.surjective, ← commutator_def, ← commutator_def,
      commutator_alternatingGroup_eq_top (by rw [hα]),
      Subgroup.map_top_of_surjective _ ψ.symm.surjective] at h1
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z), ← commutator_def, ← h1]
  have hsurj : Function.Surjective ((QuotientGroup.mk' Z).comp (commutator K).subtype) := by
    intro q
    have hq : q ∈ (commutator K).map (QuotientGroup.mk' Z) := by
      rw [hmap]
      trivial
    obtain ⟨c, hc, hcq⟩ := hq
    exact ⟨⟨c, hc⟩, hcq⟩
  have hinj : Function.Injective ((QuotientGroup.mk' Z).comp (commutator K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    have h1 : (c : K) ∈ Z ⊓ commutator K := ⟨hc, c.2⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsup : Z ⊔ commutator K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨c, hc⟩ := hsurj (QuotientGroup.mk' Z k)
    have h1 : (c : K)⁻¹ * k ∈ Z := QuotientGroup.eq.mp (by simpa using hc)
    have h2 : k = (c : K) * ((c : K)⁻¹ * k) := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right c.2) (Subgroup.mem_sup_left h1)
  have hcomm : ∀ z ∈ Z, ∀ c ∈ commutator K, z * c = c * z := fun z hz c _ =>
    (Subgroup.mem_center_iff.mp (hZ hz) c).symm
  have hcompl : Z.IsComplement' (commutator K) := by
    apply Subgroup.isComplement'_of_card_mul_and_disjoint
    · rw [Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    · exact disjoint_iff.mpr hinf
  exact ⟨hinf, hsup, hcomm, hcompl, ⟨hinj, hsurj⟩,
    ⟨(MulEquiv.ofBijective _ ⟨hinj, hsurj⟩).trans ψ⟩, inferInstance⟩

end CFSG.Semidihedral.Principal
