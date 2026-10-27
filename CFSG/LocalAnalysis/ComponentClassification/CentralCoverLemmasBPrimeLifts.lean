module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

universe u v

private theorem commutator_lift_mem_ker_pow_eq_one {p : ℕ} {Q : Type v} [Group Q] {x y : Q}
    (hx : orderOf x = p) (hxy : x * y = y * x) {L : Type u} [Group L] (π : L →* Q)
    (hcen : π.ker ≤ center L) {U V : L} (hU : π U = x) (hV : π V = y) :
    U⁻¹ * V⁻¹ * U * V ∈ π.ker ∧ (U⁻¹ * V⁻¹ * U * V) ^ p = 1 := by
  have hcA : U⁻¹ * V⁻¹ * U * V ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hU, hV, mul_assoc,
      hxy, ← mul_assoc, inv_mul_cancel_right, inv_mul_cancel]
  refine ⟨hcA, ?_⟩
  set c := U⁻¹ * V⁻¹ * U * V with hc
  have hcU : U * c = c * U := mem_center_iff.mp (hcen hcA) U
  have hUp : U ^ p ∈ center L := hcen (by
    rw [MonoidHom.mem_ker, map_pow, hU, ← hx, pow_orderOf_eq_one])
  have h1 : V⁻¹ * U * V = U * c := by rw [hc]; group
  have h2 : V⁻¹ * U ^ p * V = U ^ p * c ^ p := by
    rw [← (Commute.mul_pow hcU p), ← h1]
    simpa only [inv_inv] using (conj_pow (a := V⁻¹) (b := U) (i := p)).symm
  have h3 : V⁻¹ * U ^ p * V = U ^ p := by
    rw [mem_center_iff.mp hUp V⁻¹, inv_mul_cancel_right]
  rw [h3] at h2
  exact (mul_eq_left.mp h2.symm)

theorem universal_noncommuting_prime_lifts_bound_central_p_kernels {p : ℕ} (hp : p.Prime)
    {Q : Type v} [Group Q] {x y : Q} (hx : orderOf x = p) (hxy : x * y = y * x)
    (huniv : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (ρ : E →* Q),
      Function.Surjective ρ → ρ.ker ≤ center E → Nat.card ρ.ker = p →
        ∀ X Y : E, ρ X = x → ρ Y = y → X⁻¹ * Y⁻¹ * X * Y ≠ 1)
    {L : Type u} [Group L] [Finite L] [Group.IsPerfect L] (π : L →* Q)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center L) (hA : IsPGroup p π.ker)
    {U V : L} (hU : π U = x) (hV : π V = y) :
    π.ker = zpowers (U⁻¹ * V⁻¹ * U * V) ∧ Nat.card π.ker ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcA, hcp⟩ := commutator_lift_mem_ker_pow_eq_one hx hxy π hcen hU hV
  set c := U⁻¹ * V⁻¹ * U * V
  set A := π.ker
  have hcard_c : Nat.card (zpowers c) ∣ p := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hcp
  have hle : zpowers c ≤ A := (zpowers_le (G := L)).mpr hcA
  have heq : A = zpowers c := by
    by_contra hne
    set C' : Subgroup A := (zpowers c).subgroupOf A
    have hC'card : Nat.card C' = Nat.card (zpowers c) :=
      Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    obtain ⟨i, hi1, hi⟩ := (Nat.dvd_prime_pow hp (m := 1) (i := Nat.card (zpowers c))).mp
      (by rwa [pow_one])
    have hC'ne : C' ≠ ⊤ := by
      intro htop
      apply hne
      apply le_antisymm _ hle
      intro a ha
      have : (⟨a, ha⟩ : A) ∈ C' := htop ▸ mem_top _
      exact this
    have hik : i < k := by
      have hdvd : Nat.card C' ∣ Nat.card A := card_subgroup_dvd_card C'
      rw [hC'card, hi, hk] at hdvd
      rcases (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd |>.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hC'ne
        apply Subgroup.eq_top_of_card_eq
        rw [hC'card, hi, hk, h]
    obtain ⟨K, hKcard, hCK⟩ := Sylow.exists_subgroup_card_pow_prime_le p
      (n := i) (m := k - 1) (by rw [hk]; exact pow_dvd_pow p (Nat.sub_le k 1)) C'
      (by rw [hC'card, hi]) (by omega)
    set N : Subgroup L := K.map A.subtype with hN
    have hNA : N ≤ A := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hNn : N.Normal := normal_of_le_center (hNA.trans hcen)
    have hcN : c ∈ N := ⟨⟨c, hcA⟩, hCK (mem_subgroupOf.mpr (mem_zpowers c)), rfl⟩
    let ρ : L ⧸ N →* Q := QuotientGroup.lift N π hNA
    have hρsurj : Function.Surjective ρ := QuotientGroup.lift_surjective_of_surjective N π hπ hNA
    have hρker : ρ.ker = A.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N π hNA
    have hρcen : ρ.ker ≤ center (L ⧸ N) := by
      rw [hρker]
      rintro _ ⟨a, ha, rfl⟩
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
      rw [← map_mul, ← map_mul, mem_center_iff.mp (hcen ha) g]
    have hρcard : Nat.card ρ.ker = p := by
      have hrange : ((QuotientGroup.mk' N).domRestrict A).range = A.map (QuotientGroup.mk' N) :=
        MonoidHom.domRestrict_range A _
      have hkerR : ((QuotientGroup.mk' N).domRestrict A).ker = K := by
        rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', hN]
        exact comap_map_eq_self_of_injective A.subtype_injective K
      have hindex := Subgroup.index_ker ((QuotientGroup.mk' N).domRestrict A)
      rw [hkerR, hrange] at hindex
      have hmul := K.card_mul_index
      rw [hKcard, hk, hindex] at hmul
      rw [hρker]
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1, pow_succ] at hmul
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) hmul
    refine huniv (L ⧸ N) ρ hρsurj hρcen hρcard (U : L ⧸ N) (V : L ⧸ N) hU hV ?_
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hcN
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Nat.le_of_dvd hp.pos hcard_c

end CFSG.ComponentClassification.CentralCover
