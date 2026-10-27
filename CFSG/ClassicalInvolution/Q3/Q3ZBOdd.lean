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

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

theorem exists_fixed_mem_coset {G : Type*} [Group G] [Finite G] (σ : G ≃* G)
    (hσ : ∀ x, σ (σ x) = x) {A : Subgroup G} (hA : ∀ a ∈ A, σ a ∈ A) (hodd : Odd (Nat.card A))
    {r : G} (hr : r⁻¹ * σ r ∈ A) : ∃ r', r⁻¹ * r' ∈ A ∧ σ r' = r' := by
  classical
  let X : Type _ := {x : G // r⁻¹ * x ∈ A}
  have : Fintype X := Fintype.ofFinite _
  have hmem : ∀ x : G, r⁻¹ * x ∈ A → r⁻¹ * σ x ∈ A := by
    intro x hx
    have h2 : (r⁻¹ * σ r) * σ (r⁻¹ * x) ∈ A := A.mul_mem hr (hA _ hx)
    have e : (r⁻¹ * σ r) * σ (r⁻¹ * x) = r⁻¹ * σ x := by
      rw [map_mul, map_inv]
      group
    rwa [e] at h2
  let τ : Equiv.Perm X :=
    { toFun := fun x => ⟨σ x.1, hmem _ x.2⟩
      invFun := fun x => ⟨σ x.1, hmem _ x.2⟩
      left_inv := fun x => Subtype.ext (hσ x.1)
      right_inv := fun x => Subtype.ext (hσ x.1) }
  have hτ : τ ^ 2 ^ 1 = 1 := by
    ext x
    exact hσ x.1
  have hcard : ¬ 2 ∣ Fintype.card X := by
    have : Fintype.card X = Nat.card A := by
      rw [← Nat.card_eq_fintype_card]
      refine Nat.card_congr ⟨fun x => ⟨r⁻¹ * x.1, x.2⟩, fun a => ⟨r * a.1, ?_⟩, ?_, ?_⟩
      · simp
      · intro x; apply Subtype.ext; simp
      · intro a; apply Subtype.ext; simp
    rw [this]
    intro h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hτ
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

theorem fpf_inverts {V : Type*} [Group V] [Finite V] (φ : V ≃* V) (hφ : ∀ v, φ (φ v) = v)
    (hfix : ∀ v, φ v = v → v = 1) : ∀ v, φ v = v⁻¹ := by
  have hinj : Function.Injective (fun x : V => x⁻¹ * φ x) := by
    intro x y hxy
    have h1 : x⁻¹ * φ x = y⁻¹ * φ y := hxy
    have h : φ (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv]
      calc φ y * (φ x)⁻¹ = y * (y⁻¹ * φ y) * (x⁻¹ * φ x)⁻¹ * x⁻¹ := by group
        _ = y * (x⁻¹ * φ x) * (x⁻¹ * φ x)⁻¹ * x⁻¹ := by rw [← h1]
        _ = y * x⁻¹ := by group
    exact (mul_inv_eq_one.1 (hfix _ h)).symm
  intro v
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hinj v
  rw [← hx, map_mul, map_inv, hφ]
  group

theorem fpf_comm {V : Type*} [Group V] [Finite V] (φ : V ≃* V) (hφ : ∀ v, φ (φ v) = v)
    (hfix : ∀ v, φ v = v → v = 1) (u v : V) : u * v = v * u := by
  have h := fpf_inverts φ hφ hfix
  have h1 : (u * v)⁻¹ = u⁻¹ * v⁻¹ := by rw [← h, map_mul, h, h]
  have h2 : v⁻¹ * u⁻¹ = u⁻¹ * v⁻¹ := by rw [← mul_inv_rev]; exact h1
  have h3 := congrArg (fun x : V => x⁻¹) h2
  simpa using h3

theorem exists_decomp_of_odd {V : Type*} [CommGroup V] [Finite V] (hodd : Odd (Nat.card V))
    (φ : V ≃* V) (hφ : ∀ v, φ (φ v) = v) (v : V) :
    ∃ v₀ v₂, φ v₀ = v₀ ∧ φ v₂ = v₂⁻¹ ∧ v = v₀ * v₂ := by
  have hcop : (Nat.card V).Coprime 2 := Nat.coprime_two_right.2 hodd
  obtain ⟨w, hw⟩ := (powCoprime hcop).surjective v
  have hw' : w ^ 2 = v := hw
  refine ⟨w * φ w, w * (φ w)⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, hφ, mul_comm]
  · rw [map_mul, map_inv, hφ, mul_inv_rev, inv_inv, mul_comm]
  · rw [← hw', pow_two, mul_mul_mul_comm, mul_inv_cancel, mul_one]

theorem mem_of_sq_mem_of_odd {G : Type*} [Group G] {c : G} (hc : Odd (orderOf c))
    {S : Subgroup G} (h : c * c ∈ S) : c ∈ S := by
  obtain ⟨k, hk⟩ := hc
  have h2 : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  have h1 : (c * c) ^ (k + 1) = c := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h2, one_mul]
  rw [← h1]
  exact S.pow_mem h _

theorem exists_decomp_of_inverting {H : Type*} [Group H] [Finite H] (hodd : Odd (Nat.card H))
    {Z : Subgroup H} (hZ : Z ≤ Subgroup.center H) (σ τ : H ≃* H)
    (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hZσ : ∀ z ∈ Z, σ z ∈ Z) (hZτ : ∀ z ∈ Z, τ z ∈ Z)
    (hinv : ∀ x, ∃ z ∈ Z, σ (τ x) = x⁻¹ * z) (x : H) :
    ∃ x₁ x₂ : H, ∃ z ∈ Z, σ x₁ = x₁ ∧ τ x₂ = x₂ ∧ x = x₁ * x₂ * z := by
  classical
  have hcen : ∀ z ∈ Z, ∀ g : H, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 (hZ hz) g
  have hN : Z.Normal := ⟨fun n hn g => by rw [hcen n hn g, mul_inv_cancel_right]; exact hn⟩
  have hmapσ : Z.map σ.toMonoidHom = Z := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hZσ w hw
    · intro hy
      exact ⟨σ y, hZσ y hy, hσ y⟩
  have hmapτ : Z.map τ.toMonoidHom = Z := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hZτ w hw
    · intro hy
      exact ⟨τ y, hZτ y hy, hτ y⟩
  let σ' : H ⧸ Z ≃* H ⧸ Z := QuotientGroup.congr Z Z σ hmapσ
  let τ' : H ⧸ Z ≃* H ⧸ Z := QuotientGroup.congr Z Z τ hmapτ
  have hσ'mk : ∀ y : H, σ' (QuotientGroup.mk y) = QuotientGroup.mk (σ y) := fun y => rfl
  have hτ'mk : ∀ y : H, τ' (QuotientGroup.mk y) = QuotientGroup.mk (τ y) := fun y => rfl
  have hσ'σ' : ∀ v : H ⧸ Z, σ' (σ' v) = v := by
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [hσ'mk, hσ'mk, hσ]
  have hinvV : ∀ v : H ⧸ Z, σ' (τ' v) = v⁻¹ := by
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨z, hz, h⟩ := hinv y
    rw [hτ'mk, hσ'mk, h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one,
      QuotientGroup.mk_inv]
  have hcommV : ∀ u v : H ⧸ Z, u * v = v * u := by
    intro u v
    have h1 : (u * v)⁻¹ = u⁻¹ * v⁻¹ := by
      rw [← hinvV (u * v), map_mul, map_mul, hinvV, hinvV]
    have h2 : v⁻¹ * u⁻¹ = u⁻¹ * v⁻¹ := by rw [← mul_inv_rev]; exact h1
    have h3 := congrArg (fun t : H ⧸ Z => t⁻¹) h2
    simpa using h3
  let _ : CommGroup (H ⧸ Z) := { (inferInstance : Group (H ⧸ Z)) with mul_comm := hcommV }
  have hoddV : Odd (Nat.card (H ⧸ Z)) := hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card Z)
  have hoddZ : Odd (Nat.card Z) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Z)
  obtain ⟨v₀, v₂, h₀, h₂, hv⟩ := exists_decomp_of_odd hoddV σ' hσ'σ' (QuotientGroup.mk x)
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective v₀
  obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective v₂
  have hy₀ : y₀⁻¹ * σ y₀ ∈ Z := by
    rw [hσ'mk] at h₀
    exact (QuotientGroup.eq).1 h₀.symm
  have hτy₂ : τ' (QuotientGroup.mk y₂) = QuotientGroup.mk y₂ := by
    have h4 : τ' (QuotientGroup.mk y₂) = σ' (σ' (τ' (QuotientGroup.mk y₂))) := (hσ'σ' _).symm
    rw [h4, hinvV, map_inv, h₂, inv_inv]
  have hy₂ : y₂⁻¹ * τ y₂ ∈ Z := (QuotientGroup.eq).1 hτy₂.symm
  obtain ⟨x₁, hx₁Z, hx₁⟩ := exists_fixed_mem_coset σ hσ hZσ hoddZ hy₀
  obtain ⟨x₂, hx₂Z, hx₂⟩ := exists_fixed_mem_coset τ hτ hZτ hoddZ hy₂
  have hm₁ : (QuotientGroup.mk x₁ : H ⧸ Z) = QuotientGroup.mk y₀ :=
    ((QuotientGroup.eq).2 hx₁Z).symm
  have hm₂ : (QuotientGroup.mk x₂ : H ⧸ Z) = QuotientGroup.mk y₂ :=
    ((QuotientGroup.eq).2 hx₂Z).symm
  have hx : (QuotientGroup.mk x : H ⧸ Z) = QuotientGroup.mk (x₁ * x₂) := by
    rw [QuotientGroup.mk_mul, hm₁, hm₂]
    exact hv
  refine ⟨x₁, x₂, (x₁ * x₂)⁻¹ * x, (QuotientGroup.eq).1 hx.symm, hx₁, hx₂, ?_⟩
  group

section Subgroups

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G}

@[expose] def conjAut (σ : G) (hσ : σ * σ = 1) (hR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R) : R ≃* R where
  toFun r := ⟨σ * r * σ⁻¹, hR r r.2⟩
  invFun r := ⟨σ * r * σ⁻¹, hR r r.2⟩
  left_inv r := Subtype.ext (by
    have h : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
    show σ * (σ * r * σ⁻¹) * σ⁻¹ = r
    rw [h]
    calc σ * (σ * (r : G) * σ) * σ = (σ * σ) * r * (σ * σ) := by group
      _ = r := by rw [hσ]; group)
  right_inv r := Subtype.ext (by
    have h : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
    show σ * (σ * r * σ⁻¹) * σ⁻¹ = r
    rw [h]
    calc σ * (σ * (r : G) * σ) * σ = (σ * σ) * r * (σ * σ) := by group
      _ = r := by rw [hσ]; group)
  map_mul' x y := Subtype.ext (by
    show σ * (x * y : G) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹)
    group)

theorem inverts_mod_of_fixed (hodd : Odd (Nat.card R)) {a : G} (ha : a ∈ R)
    (hac : ∀ r ∈ R, r * a = a * r) {σ : G} (hσ : σ * σ = 1)
    (hσR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R) (hσa : σ * a * σ⁻¹ = a)
    (hfix : ∀ c ∈ R, σ * c * σ⁻¹ = c → ∃ j : ℤ, c = a ^ j) :
    (∀ r ∈ R, ∃ j : ℤ, σ * r * σ⁻¹ = r⁻¹ * a ^ j) ∧
      ∀ r ∈ R, ∀ s ∈ R, ∃ j : ℤ, r * s = s * r * a ^ j := by
  classical
  let a' : R := ⟨a, ha⟩
  set σ' : R ≃* R := conjAut σ hσ hσR with hσ'
  let Z : Subgroup R := Subgroup.zpowers a'
  have hZc : Z ≤ Subgroup.center R := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (hac g g.2)
  have hN : Z.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.1 (hZc hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hσ'a : σ' a' = a' := Subtype.ext hσa
  have hσ'Z : ∀ z ∈ Z, σ' z = z := by
    rintro _ ⟨k, rfl⟩
    rw [map_zpow, hσ'a]
  have hσσ : ∀ x, σ' (σ' x) = x := by
    intro x
    apply Subtype.ext
    have h : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
    show σ * (σ * (x : G) * σ⁻¹) * σ⁻¹ = x
    rw [h]
    calc σ * (σ * (x : G) * σ) * σ = (σ * σ) * x * (σ * σ) := by group
      _ = x := by rw [hσ]; group
  have hmap : Z.map σ'.toMonoidHom = Z := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hσ'Z w hw]
      exact hw
    · intro hy
      exact ⟨y, hy, hσ'Z y hy⟩
  have hoddZ : Odd (Nat.card Z) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Z)
  let σV : R ⧸ Z ≃* R ⧸ Z := QuotientGroup.congr Z Z σ' hmap
  have hσV : ∀ y : R, σV (QuotientGroup.mk y) = QuotientGroup.mk (σ' y) := fun y => rfl
  have hσVσV : ∀ v : R ⧸ Z, σV (σV v) = v := by
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [hσV, hσV, hσσ]
  have hfixV : ∀ v : R ⧸ Z, σV v = v → v = 1 := by
    intro v hv
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [hσV] at hv
    have hy : y⁻¹ * σ' y ∈ Z := (QuotientGroup.eq).1 hv.symm
    obtain ⟨r', hr'Z, hr'⟩ :=
      exists_fixed_mem_coset σ' hσσ (fun z hz => by rw [hσ'Z z hz]; exact hz) hoddZ hy
    have hrR : (r' : G) ∈ R := r'.2
    obtain ⟨j, hj⟩ := hfix r' hrR (congrArg Subtype.val hr')
    have hr'Z' : r' ∈ Z := ⟨j, Subtype.ext hj.symm⟩
    have hy' : y ∈ Z := by
      have := Z.mul_mem hr'Z' (Z.inv_mem hr'Z)
      simpa using this
    exact (QuotientGroup.eq_one_iff y).2 hy'
  have hinvV := fpf_inverts σV hσVσV hfixV
  let _ : CommGroup (R ⧸ Z) := { (inferInstance : Group (R ⧸ Z)) with
    mul_comm := fun u v => fpf_comm σV hσVσV hfixV u v }
  have hzp : ∀ (x : R) (k : ℤ), a' ^ k = x → (x : G) = a ^ k := by
    intro x k hx
    rw [← hx]
    simp [a']
  refine ⟨fun r hr => ?_, fun r hr s hs => ?_⟩
  · have h1 := hinvV (QuotientGroup.mk (⟨r, hr⟩ : R))
    rw [hσV] at h1
    have h2 : (⟨r, hr⟩ : R)⁻¹⁻¹ * σ' ⟨r, hr⟩ ∈ Z := (QuotientGroup.eq).1 (by
      rw [h1, QuotientGroup.mk_inv])
    obtain ⟨k, hk⟩ := h2
    have h3 := hzp _ k hk
    refine ⟨k, ?_⟩
    have h4 : r * (σ * r * σ⁻¹) = a ^ k := by
      simpa [hσ', conjAut] using h3
    calc σ * r * σ⁻¹ = r⁻¹ * (r * (σ * r * σ⁻¹)) := by group
      _ = r⁻¹ * a ^ k := by rw [h4]
  · have h1 : (QuotientGroup.mk (⟨r, hr⟩ : R) : R ⧸ Z) * QuotientGroup.mk ⟨s, hs⟩ =
        QuotientGroup.mk ⟨s, hs⟩ * QuotientGroup.mk ⟨r, hr⟩ := mul_comm _ _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    obtain ⟨k, hk⟩ := (QuotientGroup.eq).1 h1.symm
    have h3 := hzp _ k hk
    refine ⟨k, ?_⟩
    have h4 : (s * r)⁻¹ * (r * s) = a ^ k := by simpa using h3
    calc r * s = (s * r) * ((s * r)⁻¹ * (r * s)) := by group
      _ = s * r * a ^ k := by rw [h4]

theorem exists_decomp_in_subgroup (hodd : Odd (Nat.card R)) {a : G} (ha : a ∈ R)
    (hac : ∀ r ∈ R, r * a = a * r) {σ τ : G} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hσR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R) (hτR : ∀ r ∈ R, τ * r * τ⁻¹ ∈ R)
    (hσa : σ * a * σ⁻¹ = a) (hτa : τ * a * τ⁻¹ = a)
    (hinv : ∀ r ∈ R, ∃ j : ℤ, (σ * τ) * r * (σ * τ)⁻¹ = r⁻¹ * a ^ j) {r : G} (hr : r ∈ R) :
    ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ j : ℤ, σ * r₁ * σ⁻¹ = r₁ ∧ τ * r₂ * τ⁻¹ = r₂ ∧
      r = r₁ * r₂ * a ^ j := by
  classical
  let a' : R := ⟨a, ha⟩
  let σ' : R ≃* R := conjAut σ hσ hσR
  let τ' : R ≃* R := conjAut τ hτ hτR
  let Z : Subgroup R := Subgroup.zpowers a'
  have hZc : Z ≤ Subgroup.center R := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (hac g g.2)
  have hσ'Z : ∀ z ∈ Z, σ' z = z := by
    rintro _ ⟨k, rfl⟩
    rw [map_zpow, show σ' a' = a' from Subtype.ext hσa]
  have hτ'Z : ∀ z ∈ Z, τ' z = z := by
    rintro _ ⟨k, rfl⟩
    rw [map_zpow, show τ' a' = a' from Subtype.ext hτa]
  have hsq : ∀ (u : G) (hu : u * u = 1) (hR : ∀ r ∈ R, u * r * u⁻¹ ∈ R) (x : R),
      conjAut u hu hR (conjAut u hu hR x) = x := by
    intro u hu hR x
    apply Subtype.ext
    have h : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    show u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    rw [h]
    calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu]; group
  have hinv' : ∀ x : R, ∃ z ∈ Z, σ' (τ' x) = x⁻¹ * z := by
    intro x
    obtain ⟨j, hj⟩ := hinv x x.2
    refine ⟨a' ^ j, ⟨j, rfl⟩, Subtype.ext ?_⟩
    show σ * (τ * (x : G) * τ⁻¹) * σ⁻¹ = (x : G)⁻¹ * a ^ j
    rw [← hj]
    group
  obtain ⟨x₁, x₂, z, hz, h1, h2, h3⟩ := exists_decomp_of_inverting hodd hZc σ' τ'
    (hsq σ hσ hσR) (hsq τ hτ hτR) (fun z hz => by rw [hσ'Z z hz]; exact hz)
    (fun z hz => by rw [hτ'Z z hz]; exact hz) hinv' ⟨r, hr⟩
  obtain ⟨j, hj⟩ := hz
  refine ⟨x₁, x₁.2, x₂, x₂.2, j, congrArg Subtype.val h1, congrArg Subtype.val h2, ?_⟩
  have h4 := congrArg Subtype.val h3
  rw [← hj] at h4
  simpa [a'] using h4

end Subgroups

end CFSG.ClassicalInvolution.Q3.Q3ZB
