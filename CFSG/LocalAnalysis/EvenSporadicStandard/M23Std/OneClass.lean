module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.M23Std

variable {G : Type*} [Group G]

theorem even_card_sq_eq_one {H : Type*} [Group H] [Finite H] (h2 : Even (Nat.card H)) :
    Even (Nat.card {x : H // x * x = 1}) := by
  classical
  have := Fintype.ofFinite H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End H := fun x => x⁻¹
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    show f (f x) = x
    simp [f]
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  have hfix : Fintype.card (Function.fixedPoints f) = Nat.card {x : H // x * x = 1} := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, f]
    exact inv_eq_iff_mul_eq_one
  have hH : Fintype.card H = Nat.card H := Nat.card_eq_fintype_card.symm
  rw [hfix, hH] at hmod
  unfold Nat.ModEq at hmod
  obtain ⟨k, hk⟩ := h2
  exact Nat.even_iff.2 (by omega)

theorem odd_card_involutions {H : Type*} [Group H] [Finite H] (h2 : Even (Nat.card H)) :
    Odd (Nat.card {x : H // x * x = 1 ∧ x ≠ 1}) := by
  have hA := even_card_sq_eq_one h2
  have h1 : Nat.card {x : H // x * x = 1} = ({x : H | x * x = 1}).ncard :=
    Nat.card_coe_set_eq _
  have h2' : Nat.card {x : H // x * x = 1 ∧ x ≠ 1} = ({x : H | x * x = 1} \ {1}).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)
  have hmem : (1 : H) ∈ {x : H | x * x = 1} := by simp
  have hfin : ({x : H | x * x = 1}).Finite := Set.toFinite _
  have h3 := Set.ncard_sdiff_singleton_of_mem hmem
  have hpos : 0 < ({x : H | x * x = 1}).ncard := (Set.ncard_pos hfin).2 ⟨1, hmem⟩
  rw [h2', h3]
  rw [h1] at hA
  obtain ⟨k, hk⟩ := hA
  exact ⟨k - 1, by omega⟩

structure OneClassData (L : Subgroup G) (z t : G) : Prop where
  z_mul_self : z * z = 1
  z_ne_one : z ≠ 1
  t_mul_self : t * t = 1
  t_ne_one : t ≠ 1
  t_mem : t ∈ L
  z_comm : ∀ l ∈ L, z * l = l * z
  z_not_mem : z ∉ L
  centralizer_z : ∀ g : G, z * g = g * z → ∃ l ∈ L, g = l ∨ g = l * z
  oneClass : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∃ c ∈ L, u = c * t * c⁻¹
  t_sq : ∃ c ∈ L, c * c = t

namespace OneClassData

variable {L : Subgroup G} {z t : G} (h : OneClassData L z t)
include h

theorem z_ne_sq (g : G) : g * g ≠ z := by
  intro hg
  have hc : z * g = g * z := by
    rw [← hg]; group
  obtain ⟨l, hl, hcases⟩ := h.centralizer_z g hc
  have hsq : g * g ∈ L := by
    rcases hcases with rfl | rfl
    · exact L.mul_mem hl hl
    · have : l * z * (l * z) = l * l * (z * z) := by
        calc l * z * (l * z) = l * (z * l) * z := by simp only [mul_assoc]
          _ = l * (l * z) * z := by rw [h.z_comm l hl]
          _ = l * l * (z * z) := by simp only [mul_assoc]
      rw [this, h.z_mul_self, mul_one]
      exact L.mul_mem hl hl
  exact h.z_not_mem (hg ▸ hsq)

theorem not_isConj_of_sq {u : G} (hu : ∃ c, c * c = u) : ¬ IsConj z u := by
  rintro hcj
  obtain ⟨c, hc⟩ := hu
  obtain ⟨g, hg⟩ := isConj_iff.1 hcj
  refine h.z_ne_sq (g⁻¹ * c * g) ?_
  calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
    _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hc, hg]
    _ = z := by group

theorem t_isSq : ∃ c, c * c = t := by
  obtain ⟨c, -, hc⟩ := h.t_sq
  exact ⟨c, hc⟩

theorem not_isConj_z_t : ¬ IsConj z t := h.not_isConj_of_sq h.t_isSq

theorem not_isConj_z_of_mem {u : G} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ¬ IsConj z u := by
  obtain ⟨c, hc, rfl⟩ := h.oneClass u hu hu2 hu1
  obtain ⟨s, -, hs⟩ := h.t_sq
  exact h.not_isConj_of_sq ⟨c * s * c⁻¹, by
    calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [hs]⟩

theorem mul_z_sq {l : G} (hl : l ∈ L) : l * z * (l * z) = l * l := by
  calc l * z * (l * z) = l * (z * l) * z := by simp only [mul_assoc]
    _ = l * (l * z) * z := by rw [h.z_comm l hl]
    _ = l * l * (z * z) := by simp only [mul_assoc]
    _ = l * l := by rw [h.z_mul_self, mul_one]

theorem isConj_mul_z {l : G} (hl : l ∈ L) (hl2 : l * l = 1) (hl1 : l ≠ 1)
    (hconj : IsConj z (l * z)) {u : G} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    IsConj z (u * z) := by
  obtain ⟨c₁, hc₁, hl'⟩ := h.oneClass l hl hl2 hl1
  obtain ⟨c₂, hc₂, hu'⟩ := h.oneClass u hu hu2 hu1
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  set c : G := c₂ * c₁⁻¹ with hcdef
  have hcL : c ∈ L := L.mul_mem hc₂ (L.inv_mem hc₁)
  have hcz : c * z * c⁻¹ = z := by
    rw [← h.z_comm c hcL]; group
  refine isConj_iff.2 ⟨c * g, ?_⟩
  have hu_eq : u = c * l * c⁻¹ := by
    rw [hu', hl', hcdef]; group
  calc c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by group
    _ = c * (l * z) * c⁻¹ := by rw [hg]
    _ = (c * l * c⁻¹) * (c * z * c⁻¹) := by group
    _ = u * z := by rw [← hu_eq, hcz]

theorem mem_of_isConj_commute
    (hZ : ∃ l ∈ L, l * l = 1 ∧ l ≠ 1 ∧ IsConj z (l * z)) {w : G} (hw : IsConj t w)
    (hcomm : z * w = w * z) : w ∈ L ∧ w * w = 1 ∧ w ≠ 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hw
  have hw2 : w * w = 1 := by
    rw [← hg]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h.t_mul_self]; group
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact h.t_ne_one (by simpa using hg)
  obtain ⟨l, hl, hcases⟩ := h.centralizer_z w hcomm
  rcases hcases with rfl | rfl
  · exact ⟨hl, hw2, hw1⟩
  · exfalso
    have hl2 : l * l = 1 := by rw [← h.mul_z_sq hl]; exact hw2
    by_cases hl1 : l = 1
    · subst hl1
      have htz : IsConj t z := by simpa using hw
      exact h.not_isConj_z_t htz.symm
    · obtain ⟨l₀, hl₀, hl₀2, hl₀1, hl₀c⟩ := hZ
      have := h.isConj_mul_z hl₀ hl₀2 hl₀1 hl₀c hl hl2 hl1
      exact h.not_isConj_z_t (this.trans hw.symm)

theorem exists_conj_of_commute
    (hZ : ∃ l ∈ L, l * l = 1 ∧ l ≠ 1 ∧ IsConj z (l * z)) {x : G} (hx : IsConj z x)
    (hcomm : t * x = x * t) : ∃ m : G, m * t = t * m ∧ m * z * m⁻¹ = x := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  set w : G := c⁻¹ * t * c with hw
  have hwconj : IsConj t w := isConj_iff.2 ⟨c⁻¹, by rw [hw]; group⟩
  have hzw : z * w = w * z := by
    have h1 : t * (c * z * c⁻¹) = c * z * c⁻¹ * t := by rw [hc]; exact hcomm
    calc z * w = c⁻¹ * (c * z * c⁻¹ * t) * c := by rw [hw]; group
      _ = c⁻¹ * (t * (c * z * c⁻¹)) * c := by rw [h1]
      _ = w * z := by rw [hw]; group
  obtain ⟨hwL, hw2, hw1⟩ := h.mem_of_isConj_commute hZ hwconj hzw
  obtain ⟨a, haL, ha⟩ := h.oneClass w hwL hw2 hw1
  have haz : a * z * a⁻¹ = z := by rw [← h.z_comm a haL]; group
  refine ⟨c * a, ?_, ?_⟩
  · have : c * a * t * (c * a)⁻¹ = t := by
      calc c * a * t * (c * a)⁻¹ = c * (a * t * a⁻¹) * c⁻¹ := by group
        _ = c * w * c⁻¹ := by rw [← ha]
        _ = t := by rw [hw]; group
    calc c * a * t = c * a * t * (c * a)⁻¹ * (c * a) := by group
      _ = t * (c * a) := by rw [this]
  · calc c * a * z * (c * a)⁻¹ = c * (a * z * a⁻¹) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [haz]
      _ = x := hc

theorem odd_index_centralizer [Finite G]
    (hZ : ∃ l ∈ L, l * l = 1 ∧ l ≠ 1 ∧ IsConj z (l * z)) :
    Odd (Subgroup.centralizer ({t} : Set G)).index := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := Subgroup.centralizer ({t} : Set G) with hM
  have hzM : z ∈ M := Subgroup.mem_centralizer_singleton_iff.2 (h.z_comm t h.t_mem)
  let f : Function.End (G ⧸ M) := fun q => z • q
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext q
    show z • (z • q) = q
    rw [← mul_smul, h.z_mul_self, one_smul]
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  have hfix : ∀ g : G, f (g : G ⧸ M) = (g : G ⧸ M) ↔ g⁻¹ * z * g ∈ M := by
    intro g
    show z • (g : G ⧸ M) = (g : G ⧸ M) ↔ _
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, mul_inv_rev]
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_mul_self
    rw [hzi]
  have hconj : ∀ m : G, m * t = t * m → m * t * m⁻¹ = t := fun m hm => by rw [hm]; group
  have hmem : ∀ m : G, m ∈ M ↔ m * t = t * m := fun m => Subgroup.mem_centralizer_singleton_iff
  let D := {x : L // x * x = 1 ∧ x ≠ 1}
  have hDsq : ∀ x : D, ((x.1 : L) : G) * ((x.1 : L) : G) = 1 := fun x => by
    simpa using congrArg Subtype.val x.2.1
  have hD1 : ∀ x : D, ((x.1 : L) : G) ≠ 1 := fun x h1 => x.2.2 (Subtype.ext h1)
  have hc : ∀ x : D, ∃ c ∈ L, ((x.1 : L) : G) = c * t * c⁻¹ := fun x =>
    h.oneClass _ x.1.2 (hDsq x) (hD1 x)
  choose c hcL hcx using hc
  have hczc : ∀ x : D, (c x)⁻¹ * z * c x = z := fun x => by
    rw [mul_assoc, h.z_comm _ (hcL x), ← mul_assoc, inv_mul_cancel, one_mul]
  have hfp : ∀ x : D, f ((c x : G) : G ⧸ M) = ((c x : G) : G ⧸ M) := fun x => by
    rw [hfix, hczc]; exact hzM
  let Φ : D → Function.fixedPoints f := fun x => ⟨((c x : G) : G ⧸ M), hfp x⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      have hq : ((c x : G) : G ⧸ M) = ((c y : G) : G ⧸ M) := congrArg Subtype.val hxy
      rw [QuotientGroup.eq, hmem] at hq
      have hm := hconj _ hq
      apply Subtype.ext
      apply Subtype.ext
      rw [hcx x, hcx y]
      calc c x * t * (c x)⁻¹
          = c x * ((c x)⁻¹ * c y * t * ((c x)⁻¹ * c y)⁻¹) * (c x)⁻¹ := by rw [hm]
        _ = c y * t * (c y)⁻¹ := by group
    · rintro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hgM : g⁻¹ * z * g ∈ M := (hfix g).1 hq
      rw [hmem] at hgM
      set w : G := g * t * g⁻¹ with hw
      have hwconj : IsConj t w := isConj_iff.2 ⟨g, rfl⟩
      have hzw : z * w = w * z := by
        calc z * w = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by rw [hw]; group
          _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [hgM]
          _ = w * z := by rw [hw]; group
      obtain ⟨hwL, hw2, hw1⟩ := h.mem_of_isConj_commute hZ hwconj hzw
      let x : D := ⟨⟨w, hwL⟩, Subtype.ext (by simpa using hw2),
        fun h1 => hw1 (by simpa using congrArg Subtype.val h1)⟩
      refine ⟨x, Subtype.ext ?_⟩
      show ((c x : G) : G ⧸ M) = (g : G ⧸ M)
      rw [QuotientGroup.eq, hmem]
      have e1 : g * t * g⁻¹ = c x * t * (c x)⁻¹ := hcx x
      calc (c x)⁻¹ * g * t = (c x)⁻¹ * (g * t * g⁻¹) * g := by group
        _ = (c x)⁻¹ * (c x * t * (c x)⁻¹) * g := by rw [e1]
        _ = t * ((c x)⁻¹ * g) := by group
  have hcard : Fintype.card D = Fintype.card (Function.fixedPoints f) :=
    Fintype.card_of_bijective hΦ
  have hLeven : Even (Nat.card L) := by
    have ht2 : orderOf (⟨t, h.t_mem⟩ : L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact h.t_mul_self) h.t_ne_one
    exact even_iff_two_dvd.2 (ht2 ▸ orderOf_dvd_natCard _)
  have hodd : Odd (Fintype.card D) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_card_involutions hLeven
  have hidx : M.index = Fintype.card (G ⧸ M) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  rw [hidx]
  unfold Nat.ModEq at hmod
  rw [← hcard] at hmod
  obtain ⟨k, hk⟩ := hodd
  exact Nat.odd_iff.2 (by omega)

end OneClassData

end CFSG.EvenSporadicStandard.M23Std
