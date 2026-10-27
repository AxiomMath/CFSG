module

public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.SL2MinimalFaithful

variable {G : Type*} [Group G]

@[expose] def conjAut {Y : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    MulAut Y where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp y.2
    rwa [inv_inv] at h⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjAut_apply {Y : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (y : Y) : (conjAut hg y : G) = g * y * g⁻¹ :=
  rfl

@[expose] def conjAction {J Y : Subgroup G} (hJY : J ≤ Subgroup.normalizer (Y : Set G)) :
    J →* MulAut Y where
  toFun j := conjAut (hJY j.2)
  map_one' := by
    ext y
    simp [conjAut_apply]
  map_mul' j k := by
    ext y
    simp [conjAut_apply, MulAut.mul_apply, mul_assoc]

theorem conjAction_apply {J Y : Subgroup G} (hJY : J ≤ Subgroup.normalizer (Y : Set G))
    (j : J) (y : Y) : (conjAction hJY j y : G) = j * y * j⁻¹ :=
  rfl

theorem inv_mul_mem_iff {Y Z : Subgroup G} (hYZ : Y ≤ Subgroup.normalizer (Z : Set G))
    {y a : G} (hy : y ∈ Y) : a⁻¹ * y ∈ Z ↔ a * y⁻¹ ∈ Z := by
  have hn := Subgroup.mem_normalizer_iff.mp (hYZ hy)
  constructor
  · intro h
    have h1 := (hn _).mp h
    have h2 : y * (a⁻¹ * y) * y⁻¹ = (a * y⁻¹)⁻¹ := by group
    rw [h2] at h1
    simpa using Z.inv_mem h1
  · intro h
    have h1 := (hn (a⁻¹ * y)).mpr (by
      have h2 : y * (a⁻¹ * y) * y⁻¹ = (a * y⁻¹)⁻¹ := by group
      rw [h2]
      exact Z.inv_mem h)
    exact h1

theorem card_section_fixed_le [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {J Y Z Q Qs : Subgroup G} (hJ : Nat.card J = p ^ f * ((p ^ f) ^ 2 - 1))
    (hQJ : Q ≤ J) (hQsJ : Qs ≤ J) (hQ : Nat.card Q = p ^ f) (hQs : Nat.card Qs = p ^ f)
    (hinf : Q ⊓ Qs = ⊥) (hsup : Q ⊔ Qs = J)
    (hZY : Z ≤ Y) (hYZ : Y ≤ Subgroup.normalizer (Z : Set G))
    (hJY : J ≤ Subgroup.normalizer (Y : Set G)) (hJZ : J ≤ Subgroup.normalizer (Z : Set G))
    (hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' * y⁻¹ * y'⁻¹ ∈ Z)
    (hexp : ∀ y ∈ Y, y ^ p ∈ Z) (hcard : Nat.card Y = (p ^ f) ^ 2 * Nat.card Z)
    (hfaith : ∀ j ∈ J, (∀ y ∈ Y, j * y * j⁻¹ * y⁻¹ ∈ Z) → j = 1) :
    Nat.card {y : G | y ∈ Y ∧ ∀ u ∈ Q, u * y * u⁻¹ * y⁻¹ ∈ Z} ≤ p ^ f * Nat.card Z := by
  set Z' : Subgroup Y := Z.subgroupOf Y with hZ'
  have hZ'n : Z'.Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hYZ g.2) n).mp (Subgroup.mem_subgroupOf.mp hn))⟩
  have hZ'card : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  set ρY := conjAction hJY
  have hmap : ∀ j, Z'.map (ρY j : Y →* Y) = Z' := by
    intro j
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change (j : G) * z * (j : G)⁻¹ ∈ Z
      exact (Subgroup.mem_normalizer_iff.mp (hJZ j.2) z).mp hz
    · intro z hz
      refine ⟨ρY j⁻¹ z, ?_, ?_⟩
      · change ((j⁻¹ : J) : G) * z * ((j⁻¹ : J) : G)⁻¹ ∈ Z
        exact (Subgroup.mem_normalizer_iff.mp (hJZ (J.inv_mem j.2)) z).mp hz
      · change ρY j (ρY j⁻¹ z) = z
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  set ρ := quotientAction ρY Z' hmap
  have hfix : ∀ (j : J) (y : Y), ρ j (y : Y ⧸ Z') = y ↔ (j : G) * y * j⁻¹ * y⁻¹ ∈ Z := by
    intro j y
    rw [quotientAction_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (ρY j y : G)⁻¹ * y ∈ Z ↔ _
    rw [conjAction_apply]
    exact inv_mul_mem_iff hYZ y.2
  have hVcomm : ∀ v w : Y ⧸ Z', v * w = w * v := by
    intro v w
    induction v using QuotientGroup.induction_on with | H a =>
    induction w using QuotientGroup.induction_on with | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h := hcomm _ (Y.inv_mem b.2) _ (Y.inv_mem a.2)
    simpa [mul_assoc] using h
  have hVexp : ∀ v : Y ⧸ Z', v ^ p = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hexp a a.2
  have hVcard : Nat.card (Y ⧸ Z') = (p ^ f) ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [hZ'card, hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Z)) h).symm
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h := hfaith j j.2 (fun y hy => (hfix j ⟨y, hy⟩).mp (by rw [hj, MulAut.one_apply]))
    exact Subtype.ext h
  have hQ' : Nat.card (Q.subgroupOf J) = p ^ f := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, hQ]
  have hQs' : Nat.card (Qs.subgroupOf J) = p ^ f := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQsJ).toEquiv, hQs]
  have hinf' : Q.subgroupOf J ⊓ Qs.subgroupOf J = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h : (u : G) ∈ Q ⊓ Qs :=
      ⟨Subgroup.mem_subgroupOf.mp hu.1, Subgroup.mem_subgroupOf.mp hu.2⟩
    rw [hinf, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext h)
  have hsup' : Q.subgroupOf J ⊔ Qs.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQJ hQsJ, hsup, Subgroup.subgroupOf_self]
  have hmain := card_fixedPoints_le hp hp2 hf hJ hVcomm hVexp hVcard ρ hρ hQ' hQs' hinf' hsup'
  set A := fixedPoints ρ (Q.subgroupOf J)
  set B : Subgroup Y := A.comap (QuotientGroup.mk' Z')
  have hBcard : Nat.card B = Nat.card A * Nat.card Z := by
    have h1 := B.card_mul_index
    have h2 := A.card_mul_index
    have h3 : B.index = A.index :=
      Subgroup.index_comap_of_surjective A (QuotientGroup.mk'_surjective Z')
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [hZ'card] at h4
    rw [h3, h4, ← h2] at h1
    have hpos : 0 < A.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    nlinarith [h1]
  have hset : {y : G | y ∈ Y ∧ ∀ u ∈ Q, u * y * u⁻¹ * y⁻¹ ∈ Z} = (B.map Y.subtype : Set G) := by
    ext y
    constructor
    · rintro ⟨hy, hyQ⟩
      refine ⟨⟨y, hy⟩, fun u hu => ?_, rfl⟩
      exact (hfix u ⟨y, hy⟩).mpr (hyQ u (Subgroup.mem_subgroupOf.mp hu))
    · rintro ⟨y', hy', rfl⟩
      refine ⟨y'.2, fun u hu => ?_⟩
      exact (hfix ⟨u, hQJ hu⟩ y').mp (hy' ⟨u, hQJ hu⟩ (Subgroup.mem_subgroupOf.mpr hu))
  rw [hset]
  change Nat.card (B.map Y.subtype) ≤ _
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hBcard]
  exact Nat.mul_le_mul_right _ hmain

end CFSG.SL2MinimalFaithful
