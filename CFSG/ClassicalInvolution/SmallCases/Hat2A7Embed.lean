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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.ClassicalInvolution

open scoped commutatorElement

theorem exists_involution_pow {R : Type*} [Group R] (hR : IsPGroup 2 R) {x : R} (hx : x ≠ 1) :
    ∃ k : ℕ, orderOf (x ^ k) = 2 := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hR) x
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0] at hm
    simp only [pow_zero, orderOf_eq_one_iff] at hm
    exact hx hm
  refine ⟨2 ^ (m - 1), ?_⟩
  have hdvd : 2 ^ (m - 1) ∣ orderOf x := by
    rw [hm]
    exact pow_dvd_pow 2 (by omega)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hm]
  have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2]
  exact Nat.mul_div_cancel_left 2 (by positivity)

theorem mem_of_ne_bot_of_unique_involution {R : Type*} [Group R] (hR : IsPGroup 2 R) {z : R}
    (huniq : ∀ x : R, orderOf x = 2 → x = z) {H : Subgroup R} (hH : H ≠ ⊥) : z ∈ H := by
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH
  obtain ⟨k, hk⟩ := exists_involution_pow hR (x := (x : R)) (by simpa using hx1)
  have hz : (x : R) ^ k = z := huniq _ hk
  rw [← hz]
  exact H.pow_mem x.2 k

theorem card_le_four_of_perm_fin_seven {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    {z : R} (huniq : ∀ x : R, orderOf x = 2 → x = z)
    (f : R →* Equiv.Perm (Fin 7)) (hfz : f z ≠ 1) : Nat.card R ≤ 4 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 7, f z a ≠ a := by
    by_contra h
    apply hfz
    refine Equiv.ext fun b => ?_
    by_contra hne
    exact h ⟨b, by simpa using hne⟩
  have hinj : Function.Injective fun r : R => f r a := by
    intro r s hrs
    simp only at hrs
    by_contra hne
    set x : R := s⁻¹ * r with hx
    have hx1 : x ≠ 1 := by
      intro h
      have : s⁻¹ * r = 1 := h
      exact hne (inv_mul_eq_one.mp this).symm
    have hxa : f x a = a := by
      rw [hx, map_mul, Equiv.Perm.mul_apply, hrs, ← Equiv.Perm.mul_apply, ← map_mul]
      simp
    obtain ⟨k, hk⟩ := exists_involution_pow hR hx1
    have hyz : x ^ k = z := huniq _ hk
    have hya : f (x ^ k) a = a := by
      rw [map_pow]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxa _
    exact ha (hyz ▸ hya)
  have hle : Nat.card R ≤ 7 := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn] at hle ⊢
  have hn2 : n ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ n := by omega
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    omega
  calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

theorem card_le_four_or_involution_acts_trivially {R L : Type*} [Group R] [Finite R] [Group L]
    (hR : IsPGroup 2 R) {z : R} (huniq : ∀ x : R, orderOf x = 2 → x = z) (ρ : R →* MulAut L)
    (ι : MulAut L →* Equiv.Perm (Fin 7)) (hι : Function.Injective ι) :
    Nat.card R ≤ 4 ∨ ρ z = 1 := by
  by_cases h : ρ z = 1
  · exact Or.inr h
  · refine Or.inl (card_le_four_of_perm_fin_seven hR huniq (ι.comp ρ) ?_)
    intro h1
    apply h
    apply hι
    simpa using h1

theorem involution_acts_trivially_of_four_lt_card {R L : Type*} [Group R] [Finite R] [Group L]
    (hR : IsPGroup 2 R) {z : R} (huniq : ∀ x : R, orderOf x = 2 → x = z) (ρ : R →* MulAut L)
    (ι : MulAut L →* Equiv.Perm (Fin 7)) (hι : Function.Injective ι) (hcard : 4 < Nat.card R) :
    ρ z = 1 :=
  (card_le_four_or_involution_acts_trivially hR huniq ρ ι hι).resolve_left (by omega)

theorem hom_trivial_of_perfect_of_commute {K B : Type*} [Group K] [Group B]
    (hK : Group.IsPerfect K) (f : K →* B) (hcomm : ∀ x y : K, f x * f y = f y * f x) :
    ∀ k : K, f k = 1 := by
  have htop : commutator K = ⊤ := hK.commutator_eq_top
  have hle : commutator K ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcomm g₁ g₂]
    group
  intro k
  have : k ∈ f.ker := hle (by rw [htop]; trivial)
  simpa using this

theorem commute_of_perfect_of_commutator_central {G : Type*} [Group G] {K : Subgroup G}
    (hK : Group.IsPerfect K) {z : G} (hz : z ∈ Subgroup.normalizer (K : Set G))
    (hc : ∀ k ∈ K, ∀ l ∈ K, (k * z * k⁻¹ * z⁻¹) * l = l * (k * z * k⁻¹ * z⁻¹)) :
    ∀ k ∈ K, k * z = z * k := by
  have hconj : ∀ k ∈ K, z * k * z⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.mp hz k).mp hk
  have hmem : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ K := by
    intro k hk
    have h := hconj k⁻¹ (K.inv_mem hk)
    have : k * z * k⁻¹ * z⁻¹ = k * (z * k⁻¹ * z⁻¹) := by group
    rw [this]
    exact K.mul_mem hk h
  let φ : K →* K :=
    MonoidHom.mk' (fun k => ⟨k.1 * z * k.1⁻¹ * z⁻¹, hmem k.1 k.2⟩) (by
      intro a b
      apply Subtype.ext
      have hb := hc b.1 b.2 a.1 a.2
      have h1 : (a.1 * b.1) * z * (a.1 * b.1)⁻¹ * z⁻¹
          = a.1 * (b.1 * z * b.1⁻¹ * z⁻¹) * a.1⁻¹ * (a.1 * z * a.1⁻¹ * z⁻¹) := by group
      have h2 : a.1 * (b.1 * z * b.1⁻¹ * z⁻¹) * a.1⁻¹ = b.1 * z * b.1⁻¹ * z⁻¹ := by
        rw [← hb]
        group
      have hab := hc a.1 a.2 (b.1 * z * b.1⁻¹ * z⁻¹) (hmem b.1 b.2)
      show (a.1 * b.1) * z * (a.1 * b.1)⁻¹ * z⁻¹ =
        (a.1 * z * a.1⁻¹ * z⁻¹) * (b.1 * z * b.1⁻¹ * z⁻¹)
      rw [h1, h2]
      exact hab.symm)
  have hcomm : ∀ x y : K, φ x * φ y = φ y * φ x := by
    intro x y
    apply Subtype.ext
    exact hc x.1 x.2 (y.1 * z * y.1⁻¹ * z⁻¹) (hmem y.1 y.2)
  have hφ := hom_trivial_of_perfect_of_commute hK φ hcomm
  intro k hk
  have h3 : k * z * k⁻¹ * z⁻¹ = 1 := congrArg Subtype.val (hφ ⟨k, hk⟩)
  calc k * z = (k * z * k⁻¹ * z⁻¹) * z * k := by group
    _ = z * k := by rw [h3]; simp

theorem centralizes_of_perfect_of_commutator_mem {G : Type*} [Group G] {K : Subgroup G}
    (hK : Group.IsPerfect K) {z : G} (hz : z ∈ Subgroup.normalizer (K : Set G)) {N : Subgroup G}
    (hN : ∀ n ∈ N, ∀ l ∈ K, n * l = l * n) (hNz : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ N) :
    ∀ k ∈ K, k * z = z * k :=
  commute_of_perfect_of_commutator_central hK hz fun k hk l hl => hN _ (hNz k hk) l hl

theorem eq_of_commute_of_inv_mul_mem_odd {G : Type*} [Group G] {z w : G} (hz : z * z = 1)
    (hw : w * w = 1) (hzw : z * w = w * z) (N : Subgroup G) (hN : Odd (Nat.card N))
    (h : z⁻¹ * w ∈ N) : z = w := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hx2 : (z⁻¹ * w) ^ 2 = 1 := by
    rw [hzi, pow_two]
    calc z * w * (z * w) = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [hzw]
      _ = (z * z) * (w * w) := by group
      _ = 1 := by rw [hz, hw, one_mul]
  have hdvd2 : orderOf (⟨z⁻¹ * w, h⟩ : N) ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Subtype.ext
    simpa using hx2
  have hdvdN : orderOf (⟨z⁻¹ * w, h⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have hodd : Odd (orderOf (⟨z⁻¹ * w, h⟩ : N)) := hN.of_dvd_nat hdvdN
  have hone : orderOf (⟨z⁻¹ * w, h⟩ : N) = 1 := by
    have h2 : orderOf (⟨z⁻¹ * w, h⟩ : N) ∣ 2 := hdvd2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · exact h1
    · rw [h2'] at hodd
      exact absurd hodd (by decide)
  have hx : (⟨z⁻¹ * w, h⟩ : N) = 1 := orderOf_eq_one_iff.mp hone
  have hx' : z⁻¹ * w = 1 := congrArg Subtype.val hx
  rw [hzi] at hx'
  exact (mul_eq_one_iff_eq_inv.mp hx' |>.trans (inv_eq_of_mul_eq_one_right hw))

theorem unique_involution_of_central_of_quotient {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hN : Odd (Nat.card N)) {z : K} (hz : z * z = 1) (hzc : ∀ k : K, k * z = z * k)
    (hq : ∀ y : K ⧸ N, y ≠ 1 → y * y = 1 → y = (z : K ⧸ N)) :
    ∀ w : K, orderOf w = 2 → w = z := by
  intro w hw
  have hw2 : w * w = 1 := by
    have : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    simpa [pow_two] using this
  by_cases hwN : (w : K ⧸ N) = 1
  · exfalso
    have hwmem : w ∈ N := (QuotientGroup.eq_one_iff w).mp hwN
    have hdvd : orderOf (⟨w, hwmem⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have hord : orderOf (⟨w, hwmem⟩ : N) = 2 := by
      rw [← hw]
      exact (Subgroup.orderOf_mk w hwmem)
    rw [hord] at hdvd
    exact absurd (hN.of_dvd_nat hdvd) (by decide)
  · have hwz : (w : K ⧸ N) = (z : K ⧸ N) := by
      refine hq _ hwN ?_
      rw [← QuotientGroup.mk_mul, hw2]
      rfl
    have hmem : z⁻¹ * w ∈ N := by
      have := (QuotientGroup.eq).mp hwz.symm
      simpa using this
    exact (eq_of_commute_of_inv_mul_mem_odd hz hw2 (hzc w).symm N hN hmem).symm

@[expose] def CommOrEq {F : Type*} [Group F] (L M : Subgroup F) : Prop :=
  L = M ∨ ∀ a ∈ L, ∀ b ∈ M, a * b = b * a

theorem CommOrEq.refl {F : Type*} [Group F] (L : Subgroup F) : CommOrEq L L := Or.inl rfl

theorem CommOrEq.symm {F : Type*} [Group F] {L M : Subgroup F} (h : CommOrEq L M) :
    CommOrEq M L := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr fun b hb a ha => (h a ha b hb).symm

theorem commOrEq_trans {F : Type*} [Group F] {Ω : Set (Subgroup F)} (z : Subgroup F → F)
    (hz : ∀ L ∈ Ω, z L ∈ L ∧ z L ≠ 1 ∧ ∀ l ∈ L, l * z L = z L * l)
    (IH : ∀ x : F, x ≠ 1 → ∀ L ∈ Ω, ∀ M ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set F) →
      M ≤ Subgroup.centralizer ({x} : Set F) → CommOrEq L M)
    {K₀ K₁ K₂ : Subgroup F} (h₀ : K₀ ∈ Ω) (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω)
    (h01 : CommOrEq K₀ K₁) (h12 : CommOrEq K₁ K₂) : CommOrEq K₀ K₂ := by
  obtain ⟨hz1, hz1ne, hzc⟩ := hz K₁ h₁
  have hcent : ∀ K : Subgroup F, CommOrEq K K₁ → ∀ k ∈ K, k * z K₁ = z K₁ * k := by
    intro K hK k hk
    rcases hK with rfl | hK
    · exact hzc k hk
    · exact hK k hk _ hz1
  have hcent' : ∀ K : Subgroup F, CommOrEq K₁ K → ∀ k ∈ K, k * z K₁ = z K₁ * k := fun K hK =>
    hcent K hK.symm
  refine IH (z K₁) hz1ne K₀ h₀ K₂ h₂ ?_ ?_
  · intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (hcent K₀ h01 k hk)
  · intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (hcent' K₂ h12 k hk)

end CFSG.ClassicalInvolution
