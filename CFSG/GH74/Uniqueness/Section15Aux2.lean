module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.Uniqueness

open Subgroup MulAction

variable {X : Type} [Group X] [Finite X]

theorem comm_mem_of_cyclic_quotient {D A N : Subgroup X} (hAD : A ≤ D) (hNA : N ≤ A)
    (hAn : ∀ d ∈ D, ∀ x ∈ A, d * x * d⁻¹ ∈ A) (hNn : ∀ d ∈ D, ∀ x ∈ N, d * x * d⁻¹ ∈ N)
    (h2 : Nat.card A = 2 * Nat.card N)
    (hcyc : ∃ g₀ ∈ D, ∀ d ∈ D, ∃ i : ℕ, d * (g₀ ^ i)⁻¹ ∈ A) :
    ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ N := by
  classical
  have hND : N ≤ D := hNA.trans hAD
  have hidx : (N.subgroupOf A).index = 2 := by
    have h1 := Subgroup.card_mul_index (N.subgroupOf A)
    have h3 : Nat.card (N.subgroupOf A) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
    rw [h3, h2] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  have hcentral : ∀ d ∈ D, ∀ a ∈ A, d * a * d⁻¹ * a⁻¹ ∈ N := by
    intro d hd a ha
    by_cases haN : a ∈ N
    · exact N.mul_mem (hNn d hd a haN) (N.inv_mem haN)
    · have hbA : d * a * d⁻¹ ∈ A := hAn d hd a ha
      have hbN : d * a * d⁻¹ ∉ N := by
        intro hb
        apply haN
        have := hNn d⁻¹ (D.inv_mem hd) _ hb
        simpa [mul_assoc] using this
      have hab : a⁻¹ * (d * a * d⁻¹) ∈ N := by
        have h := (Subgroup.mul_mem_iff_of_index_two hidx
          (a := (⟨a⁻¹, A.inv_mem ha⟩ : ↥A)) (b := ⟨d * a * d⁻¹, hbA⟩)).mpr
          (iff_of_false (fun h => haN (by simpa using N.inv_mem (Subgroup.mem_subgroupOf.mp h)))
            (fun h => hbN (Subgroup.mem_subgroupOf.mp h)))
        exact Subgroup.mem_subgroupOf.mp h
      have e : d * a * d⁻¹ * a⁻¹ = a * (a⁻¹ * (d * a * d⁻¹)) * a⁻¹ := by group
      rw [e]
      exact hNn a (hAD ha) _ hab
  set N' : Subgroup ↥D := N.subgroupOf D with hN'
  have hN'n : N'.Normal := by
    rw [hN', Subgroup.normal_subgroupOf_iff_le_normalizer hND]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hNn g hg x hx, fun hx => ?_⟩
    have := hNn g⁻¹ (D.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  let φ : ↥D →* ↥D ⧸ N' := QuotientGroup.mk' N'
  have hker : ∀ u : ↥D, φ u = 1 ↔ (u : X) ∈ N := fun u =>
    (QuotientGroup.eq_one_iff u).trans Iff.rfl
  have hcomm_iff : ∀ u v : ↥D, Commute (φ u) (φ v) ↔
      (u : X) * v * (u : X)⁻¹ * (v : X)⁻¹ ∈ N := by
    intro u v
    have hcoe : (((u * v * u⁻¹ * v⁻¹ : ↥D)) : X) = (u : X) * v * (u : X)⁻¹ * (v : X)⁻¹ := by
      simp
    rw [← hcoe, ← hker, map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro h
      calc φ u * φ v * (φ u)⁻¹ * (φ v)⁻¹ = (φ v * φ u) * (φ u)⁻¹ * (φ v)⁻¹ := by rw [h.eq]
        _ = 1 := by group
    · intro h
      show φ u * φ v = φ v * φ u
      calc φ u * φ v = (φ u * φ v * (φ u)⁻¹ * (φ v)⁻¹) * (φ v * φ u) := by group
        _ = φ v * φ u := by rw [h, one_mul]
  obtain ⟨g₀, hg₀, hg₀rep⟩ := hcyc
  set g : ↥D := ⟨g₀, hg₀⟩ with hg
  have hrep : ∀ u : ↥D, ∃ i : ℕ, ∃ α : ↥D, (α : X) ∈ A ∧ u = α * g ^ i := by
    intro u
    obtain ⟨i, hi⟩ := hg₀rep u u.2
    refine ⟨i, ⟨(u : X) * (g₀ ^ i)⁻¹, D.mul_mem u.2 (D.inv_mem (D.pow_mem hg₀ i))⟩, hi, ?_⟩
    apply Subtype.ext
    simp [hg]
  have hcA : ∀ α : ↥D, (α : X) ∈ A → ∀ δ : ↥D, Commute (φ α) (φ δ) := by
    intro α hα δ
    exact ((hcomm_iff δ α).mpr (hcentral δ δ.2 α hα)).symm
  intro a ha b hb
  obtain ⟨i, α, hαA, hai⟩ := hrep ⟨a, ha⟩
  obtain ⟨j, β, hβA, hbj⟩ := hrep ⟨b, hb⟩
  have hcomm : Commute (φ ⟨a, ha⟩) (φ ⟨b, hb⟩) := by
    rw [hai, hbj, map_mul, map_mul, map_pow, map_pow]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact hcA α hαA β
    · exact (hcA α hαA g).pow_right j
    · exact (hcA β hβA g).symm.pow_left i
    · exact (Commute.refl (φ g)).pow_pow i j
  exact (hcomm_iff _ _).mp hcomm

@[instance_reducible] private noncomputable def conjCosetAction (A P N : Subgroup X)
    (hAP : ∀ a ∈ A, ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hAN : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N) :
    MulAction ↥A (↥P ⧸ N.subgroupOf P) where
  smul a := Quotient.map' (fun x : ↥P => (⟨(a : X) * x * (a : X)⁻¹, hAP a a.2 x x.2⟩ : ↥P))
    (fun x y h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have := hAN a a.2 _ h
      simpa [mul_assoc] using this)
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H x => exact congrArg (QuotientGroup.mk) (Subtype.ext (by simp))
  mul_smul a b q := by
    induction q using QuotientGroup.induction_on with
    | H x => exact congrArg (QuotientGroup.mk) (Subtype.ext (by simp [mul_assoc]))

theorem card_dvd_index_sub_one {A P N : Subgroup X} (_hNP : N ≤ P)
    (hAP : ∀ a ∈ A, ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hAN : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ P, x⁻¹ * (a * x * a⁻¹) ∈ N → x ∈ N) :
    Nat.card A ∣ (N.subgroupOf P).index - 1 := by
  classical
  let _ : MulAction ↥A (↥P ⧸ N.subgroupOf P) := conjCosetAction A P N hAP hAN
  have hsmul : ∀ (a : ↥A) (x : ↥P), a • (QuotientGroup.mk x : ↥P ⧸ N.subgroupOf P) =
      QuotientGroup.mk (⟨(a : X) * x * (a : X)⁻¹, hAP a a.2 x x.2⟩ : ↥P) := fun a x => rfl
  have _ : Fintype ↥A := Fintype.ofFinite _
  have _ : Fintype (↥P ⧸ N.subgroupOf P) := Fintype.ofFinite _
  have _ : ∀ a : ↥A, Fintype (fixedBy (↥P ⧸ N.subgroupOf P) a) := fun a => Fintype.ofFinite _
  have _ : Fintype (Quotient (orbitRel ↥A (↥P ⧸ N.subgroupOf P))) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥A (↥P ⧸ N.subgroupOf P)
  have hfix1 : Fintype.card (fixedBy (↥P ⧸ N.subgroupOf P) (1 : ↥A)) =
      Fintype.card (↥P ⧸ N.subgroupOf P) :=
    Fintype.card_congr
      { toFun := Subtype.val
        invFun := fun q => ⟨q, by simp⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hfixne : ∀ a : ↥A, a ≠ 1 → Fintype.card (fixedBy (↥P ⧸ N.subgroupOf P) a) = 1 := by
    intro a ha
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨QuotientGroup.mk 1, ?_⟩, ?_⟩
    · show a • (QuotientGroup.mk 1 : ↥P ⧸ N.subgroupOf P) = QuotientGroup.mk 1
      rw [hsmul]
      exact congrArg QuotientGroup.mk (Subtype.ext (by simp))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      apply Subtype.ext
      show (QuotientGroup.mk x : ↥P ⧸ N.subgroupOf P) = QuotientGroup.mk 1
      have hy' : a • (QuotientGroup.mk x : ↥P ⧸ N.subgroupOf P) = QuotientGroup.mk x := hy
      rw [hsmul] at hy'
      have h1 := QuotientGroup.eq.mp hy'.symm
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : (x : X)⁻¹ * ((a : X) * x * (a : X)⁻¹) ∈ N := by simpa using h1
      have ha' : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
      have hxN := hfree (a : X) a.2 ha' (x : X) x.2 h2
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using hxN
  have hsum : ∑ g : ↥A, Fintype.card (fixedBy (↥P ⧸ N.subgroupOf P) g) =
      Fintype.card (↥P ⧸ N.subgroupOf P) + (Fintype.card ↥A - 1) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : ↥A)), hfix1]
    congr 1
    rw [Finset.sum_congr rfl (fun a ha => hfixne a (Finset.ne_of_mem_erase ha))]
    simp [Finset.card_erase_of_mem]
  rw [hsum] at hburn
  have hidx : (N.subgroupOf P).index = Fintype.card (↥P ⧸ N.subgroupOf P) := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  rw [hidx, Nat.card_eq_fintype_card]
  have hpos : 0 < Fintype.card (↥P ⧸ N.subgroupOf P) := Fintype.card_pos
  have hgpos : 0 < Fintype.card ↥A := Fintype.card_pos
  set k := Fintype.card (Quotient (orbitRel ↥A (↥P ⧸ N.subgroupOf P)))
  set g := Fintype.card ↥A
  set i := Fintype.card (↥P ⧸ N.subgroupOf P)
  refine ⟨k - 1, ?_⟩
  rw [Nat.mul_sub_one]
  have : i + (g - 1) = g * k := by rw [hburn, Nat.mul_comm]
  omega

omit [Finite X] in
theorem sq_mem_of_transitive {A P N : Subgroup X} (hP : IsPGroup 2 P) (_hNP : N ≤ P)
    (hPN : ∀ g ∈ P, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (_hAP : ∀ a ∈ A, ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hAN : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N)
    (htrans : ∀ x ∈ P, x ∉ N → ∀ y ∈ P, y ∉ N → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ N) :
    ∀ x ∈ P, x * x ∈ N := by
  classical
  intro x hxP
  by_cases hxN : x ∈ N
  · exact N.mul_mem hxN hxN
  obtain ⟨z, hzP, hzN, hzz⟩ : ∃ z ∈ P, z ∉ N ∧ z * z ∈ N := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
    have hk' : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hxP]; exact hk
    have hex : ∃ j : ℕ, x ^ (2 ^ j) ∈ N := by
      refine ⟨k, ?_⟩
      have h1 : x ^ (2 ^ k) = 1 := by rw [← hk']; exact pow_orderOf_eq_one x
      rw [h1]; exact N.one_mem
    obtain ⟨j, hj, hjmin⟩ : ∃ j : ℕ, x ^ (2 ^ j) ∈ N ∧ ∀ m < j, x ^ (2 ^ m) ∉ N :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hj0 : j ≠ 0 := by
      intro h0
      apply hxN
      rw [h0, pow_zero, pow_one] at hj
      exact hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    refine ⟨x ^ (2 ^ i), P.pow_mem hxP _, hjmin i (Nat.lt_succ_self i), ?_⟩
    have : x ^ (2 ^ i) * x ^ (2 ^ i) = x ^ (2 ^ (i + 1)) := by
      rw [← pow_add, pow_succ, mul_two]
    rw [this]; exact hj
  obtain ⟨a, haA, ha⟩ := htrans z hzP hzN x hxP hxN
  have hww : (a * z * a⁻¹) * (a * z * a⁻¹) ∈ N := by
    have := hAN a haA _ hzz
    have e : (a * z * a⁻¹) * (a * z * a⁻¹) = a * (z * z) * a⁻¹ := by group
    rw [e]; exact this
  have hn1 : x⁻¹ * (a * z * a⁻¹) ∈ N := ha
  have hn2 : x⁻¹ * (x⁻¹ * (a * z * a⁻¹)) * x⁻¹⁻¹ ∈ N := hPN x⁻¹ (P.inv_mem hxP) _ hn1
  have e : x ^ 2 = ((a * z * a⁻¹) * (a * z * a⁻¹)) * (x⁻¹ * (a * z * a⁻¹))⁻¹ *
      (x⁻¹ * (x⁻¹ * (a * z * a⁻¹)) * x⁻¹⁻¹)⁻¹ := by group
  rw [pow_two] at e
  rw [e]
  exact N.mul_mem (N.mul_mem hww (N.inv_mem hn1)) (N.inv_mem hn2)

theorem dvd_of_two_pow_sub_one_dvd {n m : ℕ} (_hn : 0 < n) (h : 2 ^ n - 1 ∣ 2 ^ m - 1) :
    n ∣ m := by
  have h1 : Nat.gcd (2 ^ n - 1) (2 ^ m - 1) = 2 ^ n - 1 := Nat.gcd_eq_left h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h1
  have h2 : 2 ^ Nat.gcd n m = 2 ^ n := by
    have a1 : 1 ≤ 2 ^ Nat.gcd n m := Nat.one_le_two_pow
    have a2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have h3 : Nat.gcd n m = n := Nat.pow_right_injective (le_refl 2) h2
  exact h3 ▸ Nat.gcd_dvd_right n m

theorem exists_central_mod {S P N : Subgroup X} (hS : IsPGroup 2 S) (hNP : N ≤ P) (hPS : P ≤ S)
    (hNn : ∀ s ∈ S, ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hPn : ∀ s ∈ S, ∀ x ∈ P, s * x * s⁻¹ ∈ P)
    (hne : N ≠ P) :
    ∃ x ∈ P, x ∉ N ∧ x * x ∈ N ∧ ∀ s ∈ S, x⁻¹ * (s * x * s⁻¹) ∈ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N'' : Subgroup ↥S := N.subgroupOf S with hN''
  have hN''n : N''.Normal := by
    rw [hN'', Subgroup.normal_subgroupOf_iff_le_normalizer (hNP.trans hPS)]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hNn g hg x hx, fun hx => ?_⟩
    have := hNn g⁻¹ (S.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hP''n : (P.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPS]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hPn g hg x hx, fun hx => ?_⟩
    have := hPn g⁻¹ (S.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  let φ : ↥S →* ↥S ⧸ N'' := QuotientGroup.mk' N''
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective N''
  let Pb : Subgroup (↥S ⧸ N'') := (P.subgroupOf S).map φ
  have hPb : Pb.Normal := hP''n.map φ hφ
  have hQp : IsPGroup 2 (↥S ⧸ N'') := hS.of_surjective φ hφ
  have hQn : Group.IsNilpotent (↥S ⧸ N'') := hQp.isNilpotent
  have hker : ∀ u : ↥S, φ u = 1 ↔ (u : X) ∈ N := fun u => by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff u).trans Iff.rfl
  have hPbne : Pb ≠ ⊥ := by
    obtain ⟨p0, hp0P, hp0N⟩ : ∃ p0 ∈ P, p0 ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hNP hcon)
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨φ ⟨p0, hPS hp0P⟩, ⟨⟨p0, hPS hp0P⟩, hp0P, rfl⟩⟩, ?_⟩
    intro h1
    have h2 : φ ⟨p0, hPS hp0P⟩ = 1 := congrArg Subtype.val h1
    exact hp0N ((hker _).mp h2)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := Pb) hPbne
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hinf
  obtain ⟨⟨q, hqPb, hqc⟩, hq1⟩ := hinf
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQp) q
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hq1' (orderOf_eq_one_iff.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  set w : ↥S ⧸ N'' := q ^ (2 ^ i) with hw
  have hwPb : w ∈ Pb := Pb.pow_mem hqPb _
  have hwc : w ∈ Subgroup.center (↥S ⧸ N'') := Subgroup.pow_mem _ hqc _
  have hww : w * w = 1 := by
    rw [hw, ← pow_add, ← two_mul, ← pow_succ']
    rw [← hj]
    exact pow_orderOf_eq_one q
  have hw1 : w ≠ 1 := by
    intro h
    have h2 : orderOf q ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one h
    rw [hj] at h2
    have := Nat.le_of_dvd (by positivity) h2
    have h3 : 2 ^ i < 2 ^ i.succ := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self i)
    omega
  obtain ⟨p, hpP, hpw⟩ := hwPb
  refine ⟨(p : X), hpP, ?_, ?_, ?_⟩
  · intro hpN
    exact hw1 (hpw ▸ (hker p).mpr hpN)
  · have : φ (p * p) = 1 := by rw [map_mul, hpw, hww]
    exact (hker (p * p)).mp this
  · intro s hs
    have hc := (Subgroup.mem_center_iff.mp hwc) (φ ⟨s, hs⟩)
    have : φ (p⁻¹ * (⟨s, hs⟩ * p * ⟨s, hs⟩⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hpw]
      calc w⁻¹ * (φ ⟨s, hs⟩ * w * (φ ⟨s, hs⟩)⁻¹) = w⁻¹ * (w * φ ⟨s, hs⟩ * (φ ⟨s, hs⟩)⁻¹) := by
            rw [hc]
        _ = 1 := by group
    have := (hker _).mp this
    simpa using this

omit [Finite X] in
theorem le_of_isSylowOf_of_normal {S M N : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S M)
    (hNM : N ≤ M) (hNn : ∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hN : IsPGroup 2 N) : N ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hS
  have hnorm : (N.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNM]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hNn g hg x hx, fun hx => ?_⟩
    have := hNn g⁻¹ (M.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hN' : IsPGroup 2 (N.subgroupOf M) := hN.comap_subtype
  have hle := hN'.le_sylow_of_normal Q
  intro x hx
  exact ⟨⟨x, hNM hx⟩, hle hx, rfl⟩

theorem eq_bot_of_forall_sq {P : Subgroup X} (hP : IsPGroup 2 P)
    (h : ∀ x ∈ P, x * x = 1 → x = 1) : P = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  have h2 : 2 ∣ Nat.card P := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  have hxx : (x : X) * x = 1 := by
    have : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h' : ((x ^ 2 : ↥P) : X) = 1 := by rw [this]; rfl
    simpa [pow_two] using h'
  have h1 := h x x.2 hxx
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  omega

end CFSG.GH74.Uniqueness
