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

namespace CFSG.GH74.AS16.E2

open Subgroup

section Transv

variable {A : Type*} [Group A]

@[expose] def IsTransv (z : A) (φ : MulAut A) : Prop := ∀ a : A, φ a = a ∨ φ a = a * z

theorem IsTransv.apply_centre (hsq : ∀ a : A, a * a = 1) {z : A} {φ : MulAut A}
    (h : IsTransv z φ) (hz : z ≠ 1) : φ z = z := by
  rcases h z with h1 | h1
  · exact h1
  · exfalso
    have : φ z = φ 1 := by rw [map_one, h1, hsq]
    exact hz (φ.injective this)

theorem IsTransv.mul_self (hsq : ∀ a : A, a * a = 1) {z : A} {φ : MulAut A}
    (h : IsTransv z φ) (hz : z ≠ 1) : φ * φ = 1 := by
  ext a
  rcases h a with h1 | h1
  · show φ (φ a) = a
    rw [h1, h1]
  · show φ (φ a) = a
    rw [h1, map_mul, h.apply_centre hsq hz, h1, mul_assoc, hsq, mul_one]

theorem IsTransv.conj {z : A} {φ : MulAut A}
    (h : IsTransv z φ) (g : MulAut A) : IsTransv (g z) (g * φ * g⁻¹) := by
  intro a
  have e : (g * φ * g⁻¹) a = g (φ (g⁻¹ a)) := rfl
  rcases h (g⁻¹ a) with h1 | h1
  · left
    rw [e, h1]
    exact g.apply_symm_apply a
  · right
    rw [e, h1, map_mul]
    congr 1
    exact g.apply_symm_apply a

theorem IsTransv.centre_unique {z c : A} {φ : MulAut A} (h1 : IsTransv z φ) (h2 : IsTransv c φ)
    (hφ : φ ≠ 1) : z = c := by
  by_contra hne
  apply hφ
  ext a
  show φ a = a
  rcases h1 a with e1 | e1
  · exact e1
  · rcases h2 a with e2 | e2
    · exact e2
    · exact absurd (mul_left_cancel (e1.symm.trans e2)) hne

theorem transv_comm (hcomm : ∀ a b : A, a * b = b * a) {z u : A} {φ ψ : MulAut A}
    (hφ : IsTransv z φ) (hψ : IsTransv u ψ) (hφu : φ u = u) (hψz : ψ z = z) :
    φ * ψ = ψ * φ := by
  ext a
  show φ (ψ a) = ψ (φ a)
  rcases hφ a with h1 | h1 <;> rcases hψ a with h2 | h2
  · rw [h1, h2, h1]
  · rw [h2, map_mul, hφu, h1, h2]
  · rw [h2, h1, map_mul, h2, hψz]
  · rw [h2, map_mul, hφu, h1, map_mul, h2, hψz, mul_assoc, mul_assoc, hcomm z u]

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {p : G} (hp : p * p = 1) :
    IsPGroup 2 (Subgroup.zpowers p) := by
  have h2 : p ^ 2 = 1 := by rw [pow_two, hp]
  have hd : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

theorem isPGroup_sup_of_commute' {G : Type*} [Group G] [Finite G] (Q T : Subgroup G)
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T) (hcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) :
    IsPGroup 2 ↥(Q ⊔ T) := by
  have hconj : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ = q := fun t ht q hq => by
    rw [← hcomm q hq t ht, mul_assoc, mul_inv_cancel, mul_one]
  refine IsPGroup.to_sup_of_normal_left' hQ hT fun t ht => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨fun hq => (hconj t ht q hq).symm ▸ hq, fun h => ?_⟩
  have h2 : q = t * q * t⁻¹ := by
    calc q = t⁻¹ * (t * q * t⁻¹) * t⁻¹⁻¹ := by group
      _ = t * q * t⁻¹ := hconj t⁻¹ (T.inv_mem ht) _ h
  rw [h2]
  exact h

theorem IsTransv.card_le_two_mul_fixed [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    {z : A} {φ : MulAut A} (h : IsTransv z φ) :
    Nat.card A ≤ 2 * Nat.card {a : A // φ a = a} := by
  let χ : A →* A := MonoidHom.mk' (fun a => φ a * a⁻¹) (fun a b => by
    have hc : (φ b * b⁻¹) * a⁻¹ = a⁻¹ * (φ b * b⁻¹) := hcomm _ _
    calc φ (a * b) * (a * b)⁻¹ = φ a * ((φ b * b⁻¹) * a⁻¹) := by simp [mul_assoc]
      _ = φ a * (a⁻¹ * (φ b * b⁻¹)) := by rw [hc]
      _ = (φ a * a⁻¹) * (φ b * b⁻¹) := by simp [mul_assoc])
  have hχ : ∀ a, χ a = φ a * a⁻¹ := fun a => rfl
  have hker : ∀ a, a ∈ χ.ker ↔ φ a = a := by
    intro a
    rw [MonoidHom.mem_ker, hχ, mul_inv_eq_one]
  have hrange : Nat.card χ.range ≤ 2 := by
    have hsub : (χ.range : Set A) ⊆ {1, z} := by
      rintro _ ⟨a, rfl⟩
      rcases h a with h1 | h1
      · left; rw [hχ, h1, mul_inv_cancel]
      · right
        rw [Set.mem_singleton_iff, hχ, h1, hcomm a z]
        group
    calc Nat.card χ.range = Set.ncard (χ.range : Set A) := (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, z} : Set A) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
  have hkerc : Nat.card χ.ker = Nat.card {a : A // φ a = a} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have := χ.ker.card_mul_index
  rw [Subgroup.index_ker, hkerc] at this
  rw [← this, mul_comm 2]
  exact Nat.mul_le_mul_left _ hrange

theorem exists_fix_of_transv [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a * a = 1) (hcard : 4 < Nat.card A) {z : A} (hz : z ≠ 1)
    (V : Subgroup (MulAut A)) (hV : ∀ φ ∈ V, IsTransv z φ)
    (hC : ∀ b : A, b ≠ 1 → b ≠ z → ∃ φ ∈ V, φ b ≠ b)
    {u : A} (hu1 : u ≠ 1) (huz : u ≠ z) : ∃ φ ∈ V, φ ≠ 1 ∧ φ u = u := by
  by_contra hne
  push Not at hne
  obtain ⟨φ₀, hφ₀V, hφ₀u⟩ := hC u hu1 huz
  have hφ₀inv : φ₀⁻¹ = φ₀ := inv_eq_of_mul_eq_one_right ((hV φ₀ hφ₀V).mul_self hsq hz)
  have hφ₀u' : φ₀ u = u * z := (hV φ₀ hφ₀V u).resolve_left hφ₀u
  have hall : ∀ φ ∈ V, φ = 1 ∨ φ = φ₀ := by
    intro φ hφ
    by_cases h1 : φ = 1
    · exact Or.inl h1
    · right
      have hφu : φ u = u * z := (hV φ hφ u).resolve_left (hne φ hφ h1)
      have hmem : φ₀⁻¹ * φ ∈ V := V.mul_mem (V.inv_mem hφ₀V) hφ
      have hfix : (φ₀⁻¹ * φ) u = u := by
        rw [hφ₀inv]
        show φ₀ (φ u) = u
        rw [hφu, map_mul, hφ₀u', (hV φ₀ hφ₀V).apply_centre hsq hz, mul_assoc, hsq, mul_one]
      have h2 : φ₀⁻¹ * φ = 1 := by
        by_contra h3
        exact hne _ hmem h3 hfix
      exact (inv_mul_eq_one.1 h2).symm
  have hsub : {a : A | φ₀ a = a} ⊆ {1, z} := by
    intro b hb
    by_contra hb'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb'
    obtain ⟨φ, hφV, hφb⟩ := hC b hb'.1 hb'.2
    rcases hall φ hφV with h1 | h1
    · exact hφb (by rw [h1]; rfl)
    · exact hφb (by rw [h1]; exact hb)
  have hle : Nat.card {a : A // φ₀ a = a} ≤ 2 := by
    calc Nat.card {a : A // φ₀ a = a} = Set.ncard {a : A | φ₀ a = a} :=
          (Nat.card_coe_set_eq {a : A | φ₀ a = a}).symm
      _ ≤ Set.ncard ({1, z} : Set A) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
  have := (hV φ₀ hφ₀V).card_le_two_mul_fixed hcomm
  omega

theorem false_of_transv_sylow [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a * a = 1) (hcard : 4 < Nat.card A) {z : A} (hz : z ≠ 1)
    (H : Subgroup (MulAut A)) (P : Sylow 2 H)
    (hP : ∀ p : H, p ∈ (P : Subgroup H) → IsTransv z (p : MulAut A))
    (hC : ∀ b : A, b ≠ 1 → b ≠ z → ∃ p : H, p ∈ (P : Subgroup H) ∧ (p : MulAut A) b ≠ b)
    (h : H) (hhz : (h : MulAut A) z ≠ z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : Subgroup (MulAut A) := (P : Subgroup H).map H.subtype
  have hV : ∀ φ ∈ V, IsTransv z φ := by
    intro φ hφ
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hφ
    exact hP p hp
  have hC' : ∀ b : A, b ≠ 1 → b ≠ z → ∃ φ ∈ V, φ b ≠ b := by
    intro b hb1 hbz
    obtain ⟨p, hp, hpb⟩ := hC b hb1 hbz
    exact ⟨p, Subgroup.mem_map.2 ⟨p, hp, rfl⟩, hpb⟩
  set hm : MulAut A := (h : MulAut A) with hhm
  have hw1 : hm z ≠ 1 := by
    intro h1
    apply hz
    apply hm.injective
    rw [h1, map_one]
  have hz'1 : hm⁻¹ z ≠ 1 := by
    intro h1
    apply hz
    apply hm⁻¹.injective
    rw [h1, map_one]
  have hz'z : hm⁻¹ z ≠ z := by
    intro h1
    apply hhz
    have : hm (hm⁻¹ z) = hm z := by rw [h1]
    rw [← this]
    exact (hm.apply_symm_apply z)
  obtain ⟨φ, hφV, hφ1, hφw⟩ := exists_fix_of_transv hcomm hsq hcard hz V hV hC' hw1 hhz
  obtain ⟨φ', hφ'V, hφ'1, hφ'z⟩ := exists_fix_of_transv hcomm hsq hcard hz V hV hC' hz'1 hz'z
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hφV
  obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.1 hφ'V
  let q : H := h * p' * h⁻¹
  have hq : (q : MulAut A) = hm * (p' : MulAut A) * hm⁻¹ := rfl
  have hqtr : IsTransv (hm z) (q : MulAut A) := by
    rw [hq]
    exact (hP p' hp').conj hm
  have hqz : (q : MulAut A) z = z := by
    rw [hq]
    show hm ((p' : MulAut A) (hm⁻¹ z)) = z
    have hφ'z' : (p' : MulAut A) (hm⁻¹ z) = hm⁻¹ z := hφ'z
    rw [hφ'z']
    exact hm.apply_symm_apply z
  have hq1 : (q : MulAut A) ≠ 1 := by
    intro h1
    apply hφ'1
    have : hm * (p' : MulAut A) * hm⁻¹ = 1 := by rw [← hq]; exact h1
    calc (p' : MulAut A) = hm⁻¹ * (hm * (p' : MulAut A) * hm⁻¹) * hm := by group
      _ = 1 := by rw [this]; group
  have hpq : p * q = q * p := Subtype.ext (transv_comm hcomm (hP p hp) hqtr hφw hqz)
  have hp2 : p * p = 1 := Subtype.ext ((hP p hp).mul_self hsq hz)
  have hq2 : q * q = 1 := Subtype.ext (hqtr.mul_self hsq hw1)
  have hE : IsPGroup 2 ↥(Subgroup.zpowers p ⊔ Subgroup.zpowers q) := by
    refine isPGroup_sup_of_commute' _ _ (isPGroup_zpowers_of_sq hp2)
      (isPGroup_zpowers_of_sq hq2) ?_
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow (show Commute p q from hpq) m n).eq
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H P Q
  have key : ∀ x : H, x ∈ (Q : Subgroup H) → IsTransv ((k : MulAut A) z) (x : MulAut A) := by
    intro x hx
    rw [← hk] at hx
    have hx' : k⁻¹ * x * k ∈ (P : Subgroup H) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simpa [MulAut.conj_apply] using hx
    have h1 := (hP _ hx').conj (k : MulAut A)
    have e : (k : MulAut A) * ((k⁻¹ * x * k : H) : MulAut A) * (k : MulAut A)⁻¹ =
        (x : MulAut A) := by
      simp [mul_assoc]
    rwa [e] at h1
  have hpQ : p ∈ (Q : Subgroup H) := hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers p))
  have hqQ : q ∈ (Q : Subgroup H) := hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers q))
  have e1 : z = (k : MulAut A) z := (hP p hp).centre_unique (key p hpQ) hφ1
  have e2 : hm z = (k : MulAut A) z := hqtr.centre_unique (key q hqQ) hq1
  exact hhz (e2.trans e1.symm)

theorem fixed_of_transv_normalizer {G : Type} [Group G] [Finite G] {T : Sylow 2 G}
    {A : Subgroup G} {z : G} (hz1 : z ≠ 1) (hzA : z ∈ A)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcard : 4 < Nat.card A) (hTN : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hTA : ∀ t ∈ (T : Subgroup G), ∀ a ∈ A, t * a * t⁻¹ = a ∨ t * a * t⁻¹ = a * z)
    (hmove : ∀ b ∈ A, b ≠ 1 → b ≠ z → ∃ t ∈ (T : Subgroup G), t * b * t⁻¹ ≠ b) :
    ∀ n ∈ normalizer (A : Set G), n⁻¹ * z * n = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn, hne⟩ := hcon
  set N : Subgroup G := normalizer (A : Set G) with hN
  let ρ : ↥N →* MulAut ↥A := A.normalizerMonoidHom
  let H : Subgroup (MulAut ↥A) := ρ.range
  have hρ' : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  let TN : Sylow 2 ↥N := T.subtype hTN
  let P : Sylow 2 ↥H := TN.mapSurjective hρ'
  have hPmem : ∀ x : ↥H, x ∈ (P : Subgroup ↥H) ↔
      ∃ t : ↥N, (t : G) ∈ (T : Subgroup G) ∧ ρ.rangeRestrict t = x := by
    intro x
    simp only [P, TN, Sylow.coe_mapSurjective, Sylow.coe_subtype, Subgroup.mem_map,
      Subgroup.mem_subgroupOf]
  have hact : ∀ (t : ↥N) (a : ↥A), ((ρ t a : ↥A) : G) = (t : G) * a * (t : G)⁻¹ := fun t a => rfl
  let z' : ↥A := ⟨z, hzA⟩
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  refine false_of_transv_sylow (A := ↥A) (z := z') (fun a b => Subtype.ext (hAcomm a a.2 b b.2))
    (fun a => Subtype.ext (hA2 a a.2)) hcard hz'1 H P ?_ ?_ (ρ.rangeRestrict ⟨n⁻¹, N.inv_mem hn⟩)
    ?_
  · intro p hp a
    obtain ⟨t, htT, rfl⟩ := (hPmem p).1 hp
    have h1 : ((ρ.rangeRestrict t : ↥H) : MulAut ↥A) a = ρ t a := rfl
    rw [h1]
    rcases hTA t htT a a.2 with h | h
    · left; exact Subtype.ext ((hact t a).trans h)
    · right; exact Subtype.ext ((hact t a).trans h)
  · intro b hb1 hbz
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbz' : (b : G) ≠ z := fun h => hbz (Subtype.ext h)
    obtain ⟨t, htT, htb⟩ := hmove b b.2 hb1' hbz'
    refine ⟨ρ.rangeRestrict ⟨t, hTN htT⟩, (hPmem _).2 ⟨⟨t, hTN htT⟩, htT, rfl⟩, ?_⟩
    intro h
    apply htb
    have h1 : ((ρ.rangeRestrict ⟨t, hTN htT⟩ : ↥H) : MulAut ↥A) b = ρ ⟨t, hTN htT⟩ b := rfl
    rw [h1] at h
    exact (hact ⟨t, hTN htT⟩ b).symm.trans (congrArg Subtype.val h)
  · intro h
    apply hne
    have h1 : ((ρ.rangeRestrict ⟨n⁻¹, N.inv_mem hn⟩ : ↥H) : MulAut ↥A) z' =
        ρ ⟨n⁻¹, N.inv_mem hn⟩ z' := rfl
    rw [h1] at h
    have h2 := congrArg Subtype.val h
    rw [hact] at h2
    simpa using h2

end Transv

end CFSG.GH74.AS16.E2
