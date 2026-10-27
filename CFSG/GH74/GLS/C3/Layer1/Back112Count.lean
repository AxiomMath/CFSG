module

public import CFSG.GH74.GLS.C3.Layer1.Back93

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG

variable {G : Type} [Group G]

theorem mem_centralizer_singleton_iff' {y a : G} :
    a ∈ centralizer ({y} : Set G) ↔ y * a = a * y := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h y (Set.mem_singleton y)
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h

theorem card_cent_sq_gt [Finite G] {R : Subgroup G}
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hR2 : ∀ a ∈ R, a * a = 1)
    {y : G} (hy : ∀ r ∈ R, y * r * y⁻¹ ∈ R) (hy2 : y * y ∈ R)
    (hno : ∀ r ∈ R, (y * r) * (y * r) ≠ 1) :
    Nat.card ↥R < Nat.card ↥(R ⊓ centralizer ({y} : Set G)) ^ 2 := by
  set C : Subgroup G := R ⊓ centralizer ({y} : Set G) with hCdef
  have hCR : C ≤ R := inf_le_left
  let φ : ↥R →* ↥R :=
    { toFun := fun r => ⟨(y * r * y⁻¹) * r, R.mul_mem (hy r r.2) r.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun r s => Subtype.ext (by
        have h1 : (y * (s : G) * y⁻¹) * r = r * (y * s * y⁻¹) := hRab _ (hy s s.2) r r.2
        show (y * ((r : G) * s) * y⁻¹) * ((r : G) * s) =
          ((y * r * y⁻¹) * r) * ((y * s * y⁻¹) * s)
        calc (y * ((r : G) * s) * y⁻¹) * ((r : G) * s)
            = (y * r * y⁻¹) * ((y * s * y⁻¹) * r) * s := by group
          _ = (y * r * y⁻¹) * (r * (y * s * y⁻¹)) * s := by rw [h1]
          _ = ((y * r * y⁻¹) * r) * ((y * s * y⁻¹) * s) := by group) }
  have hker : φ.ker = C.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hCdef, Subgroup.mem_inf,
      mem_centralizer_singleton_iff']
    constructor
    · intro h
      have h' : (y * (r : G) * y⁻¹) * r = 1 := congrArg Subtype.val h
      have hr : (r : G) * r = 1 := hR2 r r.2
      refine ⟨r.2, ?_⟩
      have hinv : (r : G)⁻¹ = r := inv_eq_of_mul_eq_one_right hr
      have h1 : y * (r : G) * y⁻¹ = r := by
        have : y * (r : G) * y⁻¹ = (r : G)⁻¹ := eq_inv_of_mul_eq_one_left h'
        rw [this, hinv]
      calc y * (r : G) = (y * r * y⁻¹) * y := by group
        _ = r * y := by rw [h1]
    · rintro ⟨-, h1⟩
      have h2 : y * (r : G) * y⁻¹ = r := by
        calc y * (r : G) * y⁻¹ = (r * y) * y⁻¹ := by rw [h1]
          _ = r := by group
      apply Subtype.ext
      show (y * (r : G) * y⁻¹) * r = 1
      rw [h2]
      exact hR2 r r.2
  have hconj : ∀ x : G, y * x * y⁻¹ = x → y * x = x * y := fun x h => by
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [h]
  have hrange : φ.range ≤ C.subgroupOf R := by
    rintro _ ⟨r, rfl⟩
    rw [Subgroup.mem_subgroupOf, hCdef, Subgroup.mem_inf, mem_centralizer_singleton_iff']
    refine ⟨(φ r).2, hconj _ ?_⟩
    show y * ((y * (r : G) * y⁻¹) * r) * y⁻¹ = (y * r * y⁻¹) * r
    have h1 : (y * y) * (r : G) = r * (y * y) := hRab _ hy2 r r.2
    have h2 : (y * (r : G) * y⁻¹) * r = r * (y * r * y⁻¹) := hRab _ (hy r r.2) r r.2
    have h3 : y * (y * (r : G) * y⁻¹) * y⁻¹ = r := by
      calc y * (y * (r : G) * y⁻¹) * y⁻¹ = (y * y) * r * (y * y)⁻¹ := by group
        _ = (r * (y * y)) * (y * y)⁻¹ := by rw [h1]
        _ = r := by group
    calc y * ((y * (r : G) * y⁻¹) * r) * y⁻¹
        = (y * (y * (r : G) * y⁻¹) * y⁻¹) * (y * r * y⁻¹) := by group
      _ = r * (y * r * y⁻¹) := by rw [h3]
      _ = (y * r * y⁻¹) * r := h2.symm
  have hy2C : (⟨y * y, hy2⟩ : ↥R) ∈ C.subgroupOf R := by
    rw [Subgroup.mem_subgroupOf, hCdef, Subgroup.mem_inf, mem_centralizer_singleton_iff']
    exact ⟨hy2, by group⟩
  have hy2not : (⟨y * y, hy2⟩ : ↥R) ∉ φ.range := by
    rintro ⟨ρ, hρ⟩
    have hφρ : (y * (ρ : G) * y⁻¹) * ρ = y * y := congrArg Subtype.val hρ
    apply hno ρ ρ.2
    have hac : (y * (ρ : G) * y⁻¹) * (y * y) = (y * y) * (y * (ρ : G) * y⁻¹) :=
      hRab _ (hy ρ ρ.2) _ hy2
    calc (y * (ρ : G)) * (y * ρ) = (y * ρ * y⁻¹) * (y * y) * ρ := by group
      _ = (y * y) * (y * ρ * y⁻¹) * ρ := by rw [hac]
      _ = (y * y) * ((y * ρ * y⁻¹) * ρ) := by group
      _ = (y * y) * (y * y) := by rw [hφρ]
      _ = 1 := hR2 _ hy2
  have hlt : φ.range < C.subgroupOf R :=
    lt_of_le_of_ne hrange (fun h => hy2not (by rw [h]; exact hy2C))
  have hc1 : Nat.card ↥φ.range < Nat.card ↥(C.subgroupOf R) := Subgroup.card_lt_of_lt hlt
  have hc2 : Nat.card ↥(C.subgroupOf R) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv
  have hc3 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hc2] at hc3
  rw [hc2] at hc1
  have hpos : 0 < Nat.card ↥C := Nat.card_pos
  rw [← hc3, sq]
  exact (Nat.mul_lt_mul_left hpos).2 hc1

theorem card_inf_centralizer_le [Finite G] {P Q : Subgroup G} (hPQ : P ⊓ Q = ⊥)
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) {y : G}
    (hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P) (hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) :
    Nat.card ↥((P ⊔ Q) ⊓ centralizer ({y} : Set G)) ≤
      Nat.card ↥(P ⊓ centralizer ({y} : Set G)) * Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) := by
  let f : ↥(P ⊓ centralizer ({y} : Set G)) × ↥(Q ⊓ centralizer ({y} : Set G)) →
      ↥((P ⊔ Q) ⊓ centralizer ({y} : Set G)) := fun ab =>
    ⟨(ab.1 : G) * (ab.2 : G),
      ⟨Subgroup.mul_mem_sup ab.1.2.1 ab.2.2.1, (centralizer ({y} : Set G)).mul_mem ab.1.2.2 ab.2.2.2⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨r, hrPQ, hrC⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hrPQ
    have h1 : y * (p * q) = (p * q) * y := mem_centralizer_singleton_iff'.1 hrC
    have h2 : (y * p * y⁻¹) * (y * q * y⁻¹) = p * q := by
      calc (y * p * y⁻¹) * (y * q * y⁻¹) = y * (p * q) * y⁻¹ := by group
        _ = (p * q) * y * y⁻¹ := by rw [h1]
        _ = p * q := by group
    obtain ⟨hp', hq'⟩ := eq_of_mul_eq_of_inf_bot hPQ (hyP p hp) hp (hyQ q hq) hq h2
    have hpC : p ∈ centralizer ({y} : Set G) := by
      rw [mem_centralizer_singleton_iff']
      calc y * p = (y * p * y⁻¹) * y := by group
        _ = p * y := by rw [hp']
    have hqC : q ∈ centralizer ({y} : Set G) := by
      rw [mem_centralizer_singleton_iff']
      calc y * q = (y * q * y⁻¹) * y := by group
        _ = q * y := by rw [hq']
    exact ⟨(⟨p, hp, hpC⟩, ⟨q, hq, hqC⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem sq_mem_of_card_le_two [Finite G] {R T : Subgroup G} (hRT : R ≤ T)
    (hcard : Nat.card ↥T ≤ 2 * Nat.card ↥R) : ∀ t ∈ T, t * t ∈ R := by
  intro t ht
  by_contra hsq
  have htR : t ∉ R := fun h => hsq (R.mul_mem h h)
  classical
  let t' : ↥T := ⟨t, ht⟩
  have hne1 : (QuotientGroup.mk 1 : ↥T ⧸ R.subgroupOf T) ≠ QuotientGroup.mk t' := by
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact htR (by simpa using h)
  have hne2 : (QuotientGroup.mk 1 : ↥T ⧸ R.subgroupOf T) ≠ QuotientGroup.mk (t' * t') := by
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact hsq (by simpa using h)
  have hne3 : (QuotientGroup.mk t' : ↥T ⧸ R.subgroupOf T) ≠ QuotientGroup.mk (t' * t') := by
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    apply htR
    have : ((t'⁻¹ * (t' * t') : ↥T) : G) = t := by
      show (t⁻¹ * (t * t)) = t
      group
    rwa [this] at h
  have h3 : 2 < Nat.card (↥T ⧸ R.subgroupOf T) := by
    have := Fintype.ofFinite (↥T ⧸ R.subgroupOf T)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.two_lt_card_iff.2 ⟨_, _, _, hne1, hne2, hne3⟩
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf T)
  have h5 : Nat.card ↥(R.subgroupOf T) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv
  rw [h5] at h4
  have hpos : 0 < Nat.card ↥R := Nat.card_pos
  have h6 : 3 * Nat.card ↥R ≤ Nat.card (↥T ⧸ R.subgroupOf T) * Nat.card ↥R :=
    Nat.mul_le_mul_right _ h3
  omega

end CFSG.GH74.GLS.C3.Layer1.Back
