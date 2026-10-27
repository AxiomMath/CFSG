module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Abstract

variable {R : Type*} [Group R]

@[expose] def twistNorm15 (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) : R →* R :=
  MonoidHom.mk' (fun r => r * sg r) (fun a b => by
    have : Std.Commutative (α := R) (· * ·) := ⟨hc⟩
    simp only [map_mul]
    ac_rfl)

theorem twistNorm15_apply (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) (r : R) :
    twistNorm15 hc sg r = r * sg r := rfl

theorem twistNorm15_twistNorm15 (hc : ∀ a b : R, a * b = b * a) (sg : R →* R)
    (h2 : ∀ r : R, r * r = 1) (hs : ∀ r : R, sg (sg r) = r) (r : R) :
    twistNorm15 hc sg (twistNorm15 hc sg r) = 1 := by
  have : Std.Commutative (α := R) (· * ·) := ⟨hc⟩
  rw [twistNorm15_apply, twistNorm15_apply, map_mul, hs]
  calc r * sg r * (sg r * r) = (r * r) * (sg r * sg r) := by ac_rfl
    _ = 1 := by rw [h2, h2, one_mul]

theorem twistNorm15_range_le_ker (hc : ∀ a b : R, a * b = b * a) (sg : R →* R)
    (h2 : ∀ r : R, r * r = 1) (hs : ∀ r : R, sg (sg r) = r) :
    (twistNorm15 hc sg).range ≤ (twistNorm15 hc sg).ker := by
  rintro _ ⟨r, rfl⟩
  exact MonoidHom.mem_ker.2 (twistNorm15_twistNorm15 hc sg h2 hs r)

theorem card_ker_mul_card_range15 {S : Type*} [Group S] [Finite R] (f : R →* S) :
    Nat.card f.ker * Nat.card f.range = Nat.card R := by
  have h := Subgroup.card_mul_index f.ker
  rwa [Subgroup.index_ker] at h

theorem four_le_card_ker15 [Finite R] (hc : ∀ a b : R, a * b = b * a) (sg : R →* R)
    (h2 : ∀ r : R, r * r = 1) (hs : ∀ r : R, sg (sg r) = r) (h16 : Nat.card R = 16) :
    4 ≤ Nat.card (twistNorm15 hc sg).ker := by
  have hle : Nat.card (twistNorm15 hc sg).range ≤ Nat.card (twistNorm15 hc sg).ker :=
    Subgroup.card_le_of_le (twistNorm15_range_le_ker hc sg h2 hs)
  have hmul := card_ker_mul_card_range15 (twistNorm15 hc sg)
  rw [h16] at hmul
  by_contra hlt
  push Not at hlt
  have : Nat.card (twistNorm15 hc sg).ker * Nat.card (twistNorm15 hc sg).range ≤ 3 * 3 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem range_eq_ker15 [Finite R] (hc : ∀ a b : R, a * b = b * a) (sg : R →* R)
    (h2 : ∀ r : R, r * r = 1) (hs : ∀ r : R, sg (sg r) = r) (h16 : Nat.card R = 16)
    (hle : Nat.card (twistNorm15 hc sg).ker ≤ 4) :
    (twistNorm15 hc sg).range = (twistNorm15 hc sg).ker := by
  have h4 := four_le_card_ker15 hc sg h2 hs h16
  have hmul := card_ker_mul_card_range15 (twistNorm15 hc sg)
  have hk : Nat.card (twistNorm15 hc sg).ker = 4 := le_antisymm hle h4
  rw [h16, hk] at hmul
  refine Subgroup.eq_of_le_of_card_ge (twistNorm15_range_le_ker hc sg h2 hs) ?_
  omega

theorem card_le_two_mul15 [Finite R] {K L : Subgroup R}
    (h : ∀ a ∈ K, a ∉ L → ∀ b ∈ K, b ∉ L → b * a ∈ L) :
    Nat.card K ≤ 2 * Nat.card L := by
  by_cases hKL : ∀ a ∈ K, a ∈ L
  · have h1 : K ≤ L := hKL
    have h2 := Subgroup.card_le_of_le h1
    omega
  · push Not at hKL
    obtain ⟨a, haK, haL⟩ := hKL
    have hsub : (K : Set R) ⊆ (L : Set R) ∪ (fun x => x * a⁻¹) '' (L : Set R) := by
      intro b hb
      by_cases hbL : b ∈ L
      · exact Or.inl hbL
      · exact Or.inr ⟨b * a, h a haK haL b hb hbL, by simp⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (L : Set R) ((fun x => x * a⁻¹) '' (L : Set R))
    have h3 : ((fun x => x * a⁻¹) '' (L : Set R)).ncard = (L : Set R).ncard :=
      Set.ncard_image_of_injective _ (mul_left_injective a⁻¹)
    have hK : Nat.card K = (K : Set R).ncard := Nat.card_coe_set_eq (K : Set R)
    have hL : Nat.card L = (L : Set R).ncard := Nat.card_coe_set_eq (L : Set R)
    omega

theorem four_le_card_of_obstruction15 [Finite R] (hc : ∀ a b : R, a * b = b * a) (sg : R →* R)
    (h16 : Nat.card R = 16) (L : Subgroup R)
    (hLN : ∀ r, twistNorm15 hc sg r ∈ L)
    (hprod : ∀ a ∈ (twistNorm15 hc sg).ker, a ∉ L → ∀ b ∈ (twistNorm15 hc sg).ker, b ∉ L →
      b * a ∈ L) :
    4 ≤ Nat.card L := by
  have hrk : (twistNorm15 hc sg).range ≤ L := by
    rintro _ ⟨r, rfl⟩
    exact hLN r
  have h1 : Nat.card (twistNorm15 hc sg).range ≤ Nat.card L := Subgroup.card_le_of_le hrk
  have h3 : Nat.card (twistNorm15 hc sg).ker ≤ 2 * Nat.card L := card_le_two_mul15 hprod
  have hmul := card_ker_mul_card_range15 (twistNorm15 hc sg)
  rw [h16] at hmul
  have hdvd : Nat.card L ∣ 16 := h16 ▸ Subgroup.card_subgroup_dvd_card L
  have hpos : 0 < Nat.card L := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have hL2 : Nat.card L ≤ 2 := by
    obtain ⟨k, hk⟩ := hdvd
    interval_cases hL : Nat.card L <;> omega
  have : Nat.card (twistNorm15 hc sg).ker * Nat.card (twistNorm15 hc sg).range ≤ 4 * 2 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end Abstract

section Transport

variable {G : Type*} [Group G]

theorem normal15 (W A : Subgroup G) (hAn : ∀ w ∈ W, ∀ a ∈ A, w * a * w⁻¹ ∈ A) :
    (A.subgroupOf W).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hAn g g.2 n hn⟩

theorem exists_conjQ15 (W A : Subgroup G) [(A.subgroupOf W).Normal] (c d : G) (hcd : c * d = 1)
    (hW : ∀ w ∈ W, c * w * d ∈ W) (hA : ∀ a ∈ A, c * a * d ∈ A) :
    ∃ f : (↥W ⧸ A.subgroupOf W) →* (↥W ⧸ A.subgroupOf W),
      ∀ w w' : ↥W, (w' : G) = c * w * d →
        f (QuotientGroup.mk w) = QuotientGroup.mk w' := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥W →* ↥W, ∀ w : ↥W, ((σ w : ↥W) : G) = c * w * d := by
    have hd : d = c⁻¹ := eq_inv_of_mul_eq_one_right hcd
    refine ⟨{ toFun := fun w => ⟨c * w * d, hW w w.2⟩
              map_one' := Subtype.ext (by simpa using hcd)
              map_mul' := fun a b => Subtype.ext (by
                subst hd
                simp only [Subgroup.coe_mul]
                group) }, fun w => rfl⟩
  refine ⟨QuotientGroup.map _ _ σ (fun a ha => ?_), fun w w' hw' => ?_⟩
  · show ((σ a : ↥W) : G) ∈ A
    rw [hσ]
    exact hA a ha
  · have : w' = σ w := Subtype.ext (by rw [hσ]; exact hw')
    rw [this]
    rfl

theorem card_quot15 [Finite G] (W A : Subgroup G) [(A.subgroupOf W).Normal] (hAW : A ≤ W) :
    Nat.card (↥W ⧸ A.subgroupOf W) * Nat.card A = Nat.card W := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf W)
  have h5 : Nat.card ↥(A.subgroupOf W) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv
  rw [h5] at h1
  exact h1.symm

theorem exists_setup15 {Y U : Subgroup G} {d : G} [(U.subgroupOf Y).Normal]
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U) (hsq : ∀ a ∈ Y, a * a ∈ U)
    (hdN : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (hd2 : d * d = 1) (hdU : ∀ c ∈ U, d * c * d⁻¹ ∈ U) :
    ∃ sg : (↥Y ⧸ U.subgroupOf Y) →* (↥Y ⧸ U.subgroupOf Y),
      (∀ a b : ↥Y ⧸ U.subgroupOf Y, a * b = b * a) ∧ (∀ r : ↥Y ⧸ U.subgroupOf Y, r * r = 1) ∧
      (∀ r : ↥Y ⧸ U.subgroupOf Y, sg (sg r) = r) ∧
      ∀ (y : G) (hy : y ∈ Y), sg (QuotientGroup.mk ⟨y, hy⟩) =
        (QuotientGroup.mk ⟨d * y * d⁻¹, hdN y hy⟩ : ↥Y ⧸ U.subgroupOf Y) := by
  obtain ⟨sg, hsg⟩ := exists_conjQ15 Y U d d⁻¹ (mul_inv_cancel d) hdN hdU
  have hsgW : ∀ (y : G) (hy : y ∈ Y), sg (QuotientGroup.mk ⟨y, hy⟩) =
      (QuotientGroup.mk ⟨d * y * d⁻¹, hdN y hy⟩ : ↥Y ⧸ U.subgroupOf Y) :=
    fun y hy => hsg ⟨y, hy⟩ _ rfl
  refine ⟨sg, ?_, ?_, ?_, hsgW⟩
  · intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := hcomm (y : G)⁻¹ (inv_mem y.2) (x : G)⁻¹ (inv_mem x.2)
    simpa [mul_assoc] using this
  · intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq x x.2
  · intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
    rw [hsgW x x.2, hsgW _ (hdN x x.2)]
    congr 1
    apply Subtype.ext
    show d * (d * (x : G) * d⁻¹) * d⁻¹ = x
    have e : d * (d * (x : G) * d⁻¹) * d⁻¹ = (d * d) * (x : G) * (d * d)⁻¹ := by group
    rw [e, hd2]
    group

end Transport

section Lifting

variable {G : Type*} [Group G] {Y U : Subgroup G} {d : G}

structure Setup15 (Y U : Subgroup G) (d : G) : Prop where
  le : U ≤ Y
  central : ∀ c ∈ U, ∀ y ∈ Y, c * y = y * c
  comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U
  sq : ∀ a ∈ Y, a * a ∈ U
  norm : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y
  inv2 : d * d = 1
  normU : ∀ c ∈ U, d * c * d⁻¹ ∈ U

theorem e_cocycle15 (hd2 : d * d = 1) (y : G) :
    (y⁻¹ * (d * y * d⁻¹)) * (d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹) = 1 := by
  have e : (y⁻¹ * (d * y * d⁻¹)) * (d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹) =
      y⁻¹ * (d * d) * y * (d * d)⁻¹ := by group
  rw [e, hd2]
  group

theorem comm_iff_e15 (d y : G) : d * y = y * d ↔ y⁻¹ * (d * y * d⁻¹) = 1 := by
  constructor
  · intro h
    have : d * y * d⁻¹ = y := by rw [h]; group
    rw [this]
    group
  · intro h
    have h1 : d * y * d⁻¹ = y := by
      calc d * y * d⁻¹ = y * (y⁻¹ * (d * y * d⁻¹)) := by group
        _ = y := by rw [h, mul_one]
    calc d * y = d * y * d⁻¹ * d := by group
      _ = y * d := by rw [h1]

theorem e_mem15 (S : Setup15 Y U d) {y : G} (hy : y ∈ Y) (h : y * (d * y * d⁻¹) ∈ U) :
    y⁻¹ * (d * y * d⁻¹) ∈ U := by
  have h1 : y⁻¹ * (d * y * d⁻¹) = (y * y)⁻¹ * (y * (d * y * d⁻¹)) := by group
  rw [h1]
  exact mul_mem (inv_mem (S.sq y hy)) h

theorem e_mul15 (S : Setup15 Y U d) {a b : G} (hb : b ∈ Y) (ha : a⁻¹ * (d * a * d⁻¹) ∈ U) :
    (a * b)⁻¹ * (d * (a * b) * d⁻¹) =
      (a⁻¹ * (d * a * d⁻¹)) * (b⁻¹ * (d * b * d⁻¹)) := by
  have hc := S.central _ ha b⁻¹ (inv_mem hb)
  calc (a * b)⁻¹ * (d * (a * b) * d⁻¹)
      = b⁻¹ * (a⁻¹ * (d * a * d⁻¹)) * (d * b * d⁻¹) := by group
    _ = (a⁻¹ * (d * a * d⁻¹)) * b⁻¹ * (d * b * d⁻¹) := by rw [← hc]
    _ = (a⁻¹ * (d * a * d⁻¹)) * (b⁻¹ * (d * b * d⁻¹)) := by group

theorem comm_sq15 (S : Setup15 Y U d) {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) :
    a⁻¹ * b⁻¹ * a * b ∈ U ∧ (a⁻¹ * b⁻¹ * a * b) * (a⁻¹ * b⁻¹ * a * b) = 1 := by
  have hmem : a⁻¹ * b⁻¹ * a * b ∈ U := by
    have := S.comm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
    simpa using this
  refine ⟨hmem, ?_⟩
  set e := a⁻¹ * b⁻¹ * a * b with he
  have hea : e * a = a * e := S.central e hmem a ha
  have h1 : b⁻¹ * (a * a) * b = a * a := by
    have := S.central (a * a) (S.sq a ha) b hb
    rw [mul_assoc, this, inv_mul_cancel_left]
  have h2 : b⁻¹ * (a * a) * b = (a * e) * (a * e) := by
    have : a * e = b⁻¹ * a * b := by rw [he]; group
    rw [this]
    group
  have h3 : (a * e) * (a * e) = (a * a) * (e * e) := by
    calc (a * e) * (a * e) = a * (e * a) * e := by group
      _ = a * (a * e) * e := by rw [hea]
      _ = (a * a) * (e * e) := by group
  have h4 : (a * a) * (e * e) = (a * a) * 1 := by
    rw [mul_one, ← h3, ← h2, h1]
  exact mul_left_cancel h4

end Lifting

section Quot

variable {G : Type*} [Group G] {Y U : Subgroup G} {d : G} [(U.subgroupOf Y).Normal]

omit [(U.subgroupOf Y).Normal] in
theorem mk_eq_mk_iff15 {y y' : G} (hy : y ∈ Y) (hy' : y' ∈ Y) :
    (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ U.subgroupOf Y) = QuotientGroup.mk ⟨y', hy'⟩ ↔
      y⁻¹ * y' ∈ U := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem mk_eq_one_iff15 {y : G} (hy : y ∈ Y) :
    (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ U.subgroupOf Y) = 1 ↔ y ∈ U := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem twistNorm15_mk {hc : ∀ a b : ↥Y ⧸ U.subgroupOf Y, a * b = b * a}
    {sg : (↥Y ⧸ U.subgroupOf Y) →* (↥Y ⧸ U.subgroupOf Y)} (hdN : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y)
    (hsgW : ∀ (y : G) (hy : y ∈ Y), sg (QuotientGroup.mk ⟨y, hy⟩) =
      (QuotientGroup.mk ⟨d * y * d⁻¹, hdN y hy⟩ : ↥Y ⧸ U.subgroupOf Y))
    (y : G) (hy : y ∈ Y) :
    twistNorm15 hc sg (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk ⟨y * (d * y * d⁻¹), mul_mem hy (hdN y hy)⟩ := by
  rw [twistNorm15_apply, hsgW y hy, ← QuotientGroup.mk_mul]
  rfl

theorem twistNorm15_mk_eq_one_iff {hc : ∀ a b : ↥Y ⧸ U.subgroupOf Y, a * b = b * a}
    {sg : (↥Y ⧸ U.subgroupOf Y) →* (↥Y ⧸ U.subgroupOf Y)} (hdN : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y)
    (hsgW : ∀ (y : G) (hy : y ∈ Y), sg (QuotientGroup.mk ⟨y, hy⟩) =
      (QuotientGroup.mk ⟨d * y * d⁻¹, hdN y hy⟩ : ↥Y ⧸ U.subgroupOf Y))
    (y : G) (hy : y ∈ Y) :
    twistNorm15 hc sg (QuotientGroup.mk ⟨y, hy⟩) = 1 ↔ y * (d * y * d⁻¹) ∈ U := by
  rw [twistNorm15_mk hdN hsgW y hy, mk_eq_one_iff15]

end Quot

section Pair

variable {G : Type*} [Group G] {Y U : Subgroup G} {d z u : G}

theorem sq_z15 (hUe : ∀ x ∈ U, x = 1 ∨ x = z ∨ x = u ∨ x = u * z) (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hzd : d * z * d⁻¹ = z) (hud : d * u * d⁻¹ = u * z) : z * z = 1 := by
  have hτ : d * (z * z) * d⁻¹ = z * z := by
    calc d * (z * z) * d⁻¹ = (d * z * d⁻¹) * (d * z * d⁻¹) := by group
      _ = z * z := by rw [hzd]
  rcases hUe (z * z) (mul_mem hzU hzU) with h | h | h | h
  · exact h
  · exact absurd (by simpa using h) hz1
  · exfalso
    rw [h, hud] at hτ
    exact hz1 (by simpa using hτ)
  · exfalso
    have huz : z = u := mul_right_cancel h
    rw [← huz, hzd] at hud
    exact hz1 (by simpa using hud.symm)

theorem sq_u15 (hUe : ∀ x ∈ U, x = 1 ∨ x = z ∨ x = u ∨ x = u * z) (huU : u ∈ U) (hz1 : z ≠ 1)
    (hzd : d * z * d⁻¹ = z) (hud : d * u * d⁻¹ = u * z) : u * u = 1 ∨ u * u = z := by
  rcases hUe (u * u) (mul_mem huU huU) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hu1 : u = 1 := by simpa using h
    rw [hu1] at hud
    exact hz1 (by simpa using hud.symm)
  · exfalso
    have huz : u = z := mul_left_cancel h
    rw [huz, hzd] at hud
    exact hz1 (by simpa using hud.symm)

theorem uzu15 (hz2 : z * z = 1) (hzu : u * z = z * u) :
    (u * z) * u = u * u * z ∧ (u * z) * (u * z) = u * u := by
  have hA : (u * z) * u = u * u * z := by
    calc (u * z) * u = u * (z * u) := by rw [mul_assoc]
      _ = u * (u * z) := by rw [← hzu]
      _ = u * u * z := by rw [mul_assoc]
  refine ⟨hA, ?_⟩
  calc (u * z) * (u * z) = (u * z * u) * z := by group
    _ = (u * u * z) * z := by rw [hA]
    _ = u * u * (z * z) := by rw [mul_assoc]
    _ = u * u := by rw [hz2, mul_one]

theorem prod_pair15 (hz2 : z * z = 1) (hzu : u * z = z * u) (hu2 : u * u = 1 ∨ u * u = z)
    {e e' : G} (he : e = u ∨ e = u * z) (he' : e' = u ∨ e' = u * z) :
    e * e' = 1 ∨ e * e' = z := by
  obtain ⟨hA, hC⟩ := uzu15 hz2 hzu
  have hB : u * (u * z) = u * u * z := by rw [mul_assoc]
  have hD : u * u * z = 1 ∨ u * u * z = z := by
    rcases hu2 with h | h
    · right
      rw [h, one_mul]
    · left
      rw [h, hz2]
  rcases he with h | h <;> rcases he' with h' | h' <;> rw [h, h']
  · exact hu2
  · rw [hB]
    exact hD
  · rw [hA]
    exact hD
  · rw [hC]
    exact hu2

theorem e_pair15 (hUe : ∀ x ∈ U, x = 1 ∨ x = z ∨ x = u ∨ x = u * z) (hzU : z ∈ U) (huU : u ∈ U)
    (hz1 : z ≠ 1) (hzd : d * z * d⁻¹ = z) (hud : d * u * d⁻¹ = u * z) (hz2 : z * z = 1)
    (hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {e : G} (heU : e ∈ U) (he2 : e * e = 1)
    (hco : e * (d * e * d⁻¹) = 1) : e = 1 ∨ e = z := by
  have hzu : u * z = z * u := hUcomm u huU z hzU
  rcases hUe e heU with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h, hud] at hco
    have : u * u * z = 1 := by rw [mul_assoc]; exact hco
    rw [h] at he2
    rw [he2, one_mul] at this
    exact hz1 this
  · exfalso
    rw [h] at he2 hco
    have hτ : d * (u * z) * d⁻¹ = u := by
      calc d * (u * z) * d⁻¹ = (d * u * d⁻¹) * (d * z * d⁻¹) := by group
        _ = (u * z) * z := by rw [hud, hzd]
        _ = u := by rw [mul_assoc, hz2, mul_one]
    rw [hτ] at hco
    obtain ⟨hA, hC⟩ := uzu15 hz2 hzu
    rw [hC] at he2
    rw [hA, he2, one_mul] at hco
    exact hz1 hco

theorem lift15 (S : Setup15 Y U d) (hzU : z ∈ U) (huU : u ∈ U) (hz2 : z * z = 1)
    (hud : d * u * d⁻¹ = u * z) {y : G} (hy : y ∈ Y)
    (h : y⁻¹ * (d * y * d⁻¹) = 1 ∨ y⁻¹ * (d * y * d⁻¹) = z) :
    ∃ y' ∈ Y, d * y' = y' * d ∧ y⁻¹ * y' ∈ U := by
  rcases h with h | h
  · exact ⟨y, hy, (comm_iff_e15 d y).2 h, by simp⟩
  · have huY : u ∈ Y := S.le huU
    have hmul := e_mul15 S huY (a := y) (by rw [h]; exact hzU)
    have hu : u⁻¹ * (d * u * d⁻¹) = z := by
      rw [hud]
      group
    refine ⟨y * u, mul_mem hy huY, (comm_iff_e15 d _).2 ?_, ?_⟩
    · rw [hmul, h, hu, hz2]
    · have : y⁻¹ * (y * u) = u := by group
      rw [this]
      exact huU

theorem e_norm15 (hd2 : d * d = 1) (m : G) :
    (m * (d * m * d⁻¹))⁻¹ * (d * (m * (d * m * d⁻¹)) * d⁻¹) =
      (d * m * d⁻¹)⁻¹ * m⁻¹ * (d * m * d⁻¹) * m := by
  have e : d * (m * (d * m * d⁻¹)) * d⁻¹ = (d * m * d⁻¹) * ((d * d) * m * (d * d)⁻¹) := by group
  rw [e, hd2]
  group

end Pair

section Main

open scoped Pointwise

theorem exists_conj_into_U {G : Type*} [Group G] [Finite G] {Y U : Subgroup G} {d : G}
    (hUY : U ≤ Y) (hUc : ∀ c ∈ U, ∀ y ∈ Y, c * y = y * c)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U) (hsq : ∀ a ∈ Y, a * a ∈ U)
    (hY : Nat.card ↥Y = 64) (hU : Nat.card ↥U = 4)
    (hdN : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (hd2 : d * d = 1)
    (hdU : ∀ c ∈ U, d * c * d⁻¹ = c)
    (hfix : ∀ y ∈ Y, d * y = y * d → y ∈ U) :
    ∀ y ∈ Y, (y * d) * (y * d) = 1 → ∃ m ∈ Y, m * (y * d) * m⁻¹ ∈ (U : Set G) * {d} := by
  classical
  have hUn : ∀ w ∈ Y, ∀ a ∈ U, w * a * w⁻¹ ∈ U := by
    intro w hw a ha
    have h := hUc a ha w hw
    have : w * a * w⁻¹ = a := by rw [← h]; group
    rw [this]
    exact ha
  have hN : (U.subgroupOf Y).Normal := normal15 Y U hUn
  have hdU' : ∀ c ∈ U, d * c * d⁻¹ ∈ U := fun c hc => by rw [hdU c hc]; exact hc
  have S : Setup15 Y U d := ⟨hUY, hUc, hcomm, hsq, hdN, hd2, hdU'⟩
  obtain ⟨sg, hc, h2, hs, hsgW⟩ := exists_setup15 hcomm hsq hdN hd2 hdU'
  have h16 : Nat.card (↥Y ⧸ U.subgroupOf Y) = 16 := by
    have := card_quot15 Y U hUY
    rw [hY, hU] at this
    omega
  have hker : Nat.card (twistNorm15 hc sg).ker ≤ 4 := by
    choose g hg using fun k : ↥Y ⧸ U.subgroupOf Y => QuotientGroup.mk_surjective k
    have hmem : ∀ k : (twistNorm15 hc sg).ker,
        ((g k : ↥Y) : G)⁻¹ * (d * (g k : G) * d⁻¹) ∈ U := by
      intro k
      apply e_mem15 S (g k).2
      have h1 : twistNorm15 hc sg (QuotientGroup.mk (g k)) = 1 := by
        rw [hg k]
        exact MonoidHom.mem_ker.1 k.2
      exact (twistNorm15_mk_eq_one_iff hdN hsgW (g k) (g k).2).1 h1
    let f : (twistNorm15 hc sg).ker → U := fun k => ⟨_, hmem k⟩
    have hf : Function.Injective f := by
      intro k₁ k₂ h
      have hcc : ((g k₁ : ↥Y) : G)⁻¹ * (d * (g k₁ : G) * d⁻¹) =
          ((g k₂ : ↥Y) : G)⁻¹ * (d * (g k₂ : G) * d⁻¹) := congrArg Subtype.val h
      set y₁ : G := (g k₁ : G) with hy₁def
      set y₂ : G := (g k₂ : G) with hy₂def
      have hy₁ : y₁ ∈ Y := (g k₁).2
      have hy₂ : y₂ ∈ Y := (g k₂).2
      have key : d * (y₁ * y₂⁻¹) * d⁻¹ =
          (y₁ * (y₁⁻¹ * (d * y₁ * d⁻¹))) * (y₂ * (y₂⁻¹ * (d * y₂ * d⁻¹)))⁻¹ := by group
      have hw1 : d * (y₁ * y₂⁻¹) * d⁻¹ = y₁ * y₂⁻¹ := by
        rw [key, hcc]
        group
      have hwY : y₁ * y₂⁻¹ ∈ Y := mul_mem hy₁ (inv_mem hy₂)
      have hwd : d * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * d := by
        calc d * (y₁ * y₂⁻¹) = d * (y₁ * y₂⁻¹) * d⁻¹ * d := by group
          _ = (y₁ * y₂⁻¹) * d := by rw [hw1]
      have hwU : y₁ * y₂⁻¹ ∈ U := hfix _ hwY hwd
      have hcen := S.central _ (inv_mem hwU) y₁ hy₁
      have hy12 : y₁⁻¹ * y₂ ∈ U := by
        have : y₁⁻¹ * y₂ = (y₁ * y₂⁻¹)⁻¹ := by
          calc y₁⁻¹ * y₂ = y₁⁻¹ * ((y₂ * y₁⁻¹) * y₁) := by group
            _ = y₁⁻¹ * ((y₁ * y₂⁻¹)⁻¹ * y₁) := by rw [mul_inv_rev, inv_inv]
            _ = y₁⁻¹ * (y₁ * (y₁ * y₂⁻¹)⁻¹) := by rw [hcen]
            _ = (y₁ * y₂⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem hwU
      have hk : (QuotientGroup.mk (g k₁) : ↥Y ⧸ U.subgroupOf Y) = QuotientGroup.mk (g k₂) :=
        (mk_eq_mk_iff15 hy₁ hy₂).2 hy12
      rw [hg k₁, hg k₂] at hk
      exact Subtype.ext hk
    calc Nat.card (twistNorm15 hc sg).ker ≤ Nat.card U := Nat.card_le_card_of_injective f hf
      _ = 4 := hU
  have hrange := range_eq_ker15 hc sg h2 hs h16 hker
  intro y hy hyd
  have hyτ : y * (d * y * d⁻¹) = 1 := by
    have e : (y * d) * (y * d) = y * (d * y * d⁻¹) * (d * d) := by group
    rw [e, hd2, mul_one] at hyd
    exact hyd
  have hkmem : (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ U.subgroupOf Y) ∈ (twistNorm15 hc sg).ker := by
    rw [MonoidHom.mem_ker, twistNorm15_mk_eq_one_iff hdN hsgW y hy, hyτ]
    exact one_mem U
  rw [← hrange] at hkmem
  obtain ⟨r, hr⟩ := hkmem
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective r
  have hm : (m : G) ∈ Y := m.2
  rw [show (QuotientGroup.mk m : ↥Y ⧸ U.subgroupOf Y) = QuotientGroup.mk ⟨(m : G), hm⟩ from rfl,
    twistNorm15_mk hdN hsgW m hm, mk_eq_mk_iff15] at hr
  refine ⟨m, hm, ?_⟩
  set w : G := ((m : G) * (d * m * d⁻¹))⁻¹ * y with hw
  have hwU : w ∈ U := hr
  have hτm : d * (m : G) * d⁻¹ ∈ Y := hdN m hm
  have hcen : w * (d * m * d⁻¹) = (d * m * d⁻¹) * w := S.central w hwU _ hτm
  have hyw : y = ((m : G) * (d * m * d⁻¹)) * w := by rw [hw]; group
  have hcU : ((m : G) * m) * w ∈ U := mul_mem (hsq m hm) hwU
  refine Set.mem_mul.2 ⟨((m : G) * m) * w, hcU, d, Set.mem_singleton d, ?_⟩
  calc ((m : G) * m) * w * d = ((m : G) * (((m : G) * (d * m * d⁻¹)) * w) * (d * m * d⁻¹)⁻¹) * d := by
        calc ((m : G) * m) * w * d = (m : G) * m * ((d * m * d⁻¹) * w * (d * m * d⁻¹)⁻¹) * d := by
              rw [← hcen]; group
          _ = _ := by group
    _ = m * (y * d) * (m : G)⁻¹ := by rw [← hyw]; group

theorem card_cent_ge_eight {G : Type*} [Group G] [Finite G] {Y U : Subgroup G} {d z u : G}
    (hUY : U ≤ Y) (hUc : ∀ c ∈ U, ∀ y ∈ Y, c * y = y * c)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U) (hsq : ∀ a ∈ Y, a * a ∈ U)
    (hY : Nat.card ↥Y = 64) (hU : Nat.card ↥U = 4)
    (hdN : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (hd2 : d * d = 1)
    (hUe : ∀ x ∈ U, x = 1 ∨ x = z ∨ x = u ∨ x = u * z) (hzU : z ∈ U) (huU : u ∈ U) (hz1 : z ≠ 1)
    (hzd : d * z * d⁻¹ = z) (hud : d * u * d⁻¹ = u * z) :
    8 ≤ Nat.card ↥(Y ⊓ centralizer ({d} : Set G)) := by
  classical
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hUc a ha b (hUY hb)
  have hz2 : z * z = 1 := sq_z15 hUe hzU hz1 hzd hud
  have hu2 : u * u = 1 ∨ u * u = z := sq_u15 hUe huU hz1 hzd hud
  have hzu : u * z = z * u := hUcomm u huU z hzU
  have hdU' : ∀ c ∈ U, d * c * d⁻¹ ∈ U := by
    intro c hc
    rcases hUe c hc with h | h | h | h
    · rw [h]
      simp
    · rw [h, hzd]
      exact hzU
    · rw [h, hud]
      exact mul_mem huU hzU
    · have : d * (u * z) * d⁻¹ = u := by
        calc d * (u * z) * d⁻¹ = (d * u * d⁻¹) * (d * z * d⁻¹) := by group
          _ = (u * z) * z := by rw [hud, hzd]
          _ = u := by rw [mul_assoc, hz2, mul_one]
      rw [h, this]
      exact huU
  have hUn : ∀ w ∈ Y, ∀ a ∈ U, w * a * w⁻¹ ∈ U := by
    intro w hw a ha
    have h := hUc a ha w hw
    have : w * a * w⁻¹ = a := by rw [← h]; group
    rw [this]
    exact ha
  have hN : (U.subgroupOf Y).Normal := normal15 Y U hUn
  have S : Setup15 Y U d := ⟨hUY, hUc, hcomm, hsq, hdN, hd2, hdU'⟩
  obtain ⟨sg, hc, h2, hs, hsgW⟩ := exists_setup15 hcomm hsq hdN hd2 hdU'
  have h16 : Nat.card (↥Y ⧸ U.subgroupOf Y) = 16 := by
    have := card_quot15 Y U hUY
    rw [hY, hU] at this
    omega
  set C : Subgroup G := Y ⊓ centralizer ({d} : Set G) with hC
  have hmemC : ∀ y : G, y ∈ C ↔ y ∈ Y ∧ d * y = y * d := by
    intro y
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp
  let ψ : ↥C →* ↥Y ⧸ U.subgroupOf Y :=
    (QuotientGroup.mk' (U.subgroupOf Y)).comp (Subgroup.inclusion (inf_le_left : C ≤ Y))
  have hψ : ∀ c : ↥C, ψ c = QuotientGroup.mk ⟨(c : G), ((hmemC c).1 c.2).1⟩ := fun c => rfl
  set L : Subgroup (↥Y ⧸ U.subgroupOf Y) := ψ.range with hL
  have hLmem : ∀ (y : G) (hy : y ∈ Y), (∃ y' ∈ Y, d * y' = y' * d ∧ y⁻¹ * y' ∈ U) →
      (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ U.subgroupOf Y) ∈ L := by
    rintro y hy ⟨y', hy', hdy', hyy'⟩
    refine ⟨⟨y', (hmemC y').2 ⟨hy', hdy'⟩⟩, ?_⟩
    rw [hψ]
    exact (mk_eq_mk_iff15 hy' hy).2 (by simpa using inv_mem hyy')
  have hLN : ∀ r, twistNorm15 hc sg r ∈ L := by
    intro r
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective r
    have hm : (m : G) ∈ Y := m.2
    rw [show (QuotientGroup.mk m : ↥Y ⧸ U.subgroupOf Y) = QuotientGroup.mk ⟨(m : G), hm⟩ from rfl,
      twistNorm15_mk hdN hsgW m hm]
    apply hLmem
    apply lift15 S hzU huU hz2 hud (mul_mem hm (hdN m hm))
    have hcs := comm_sq15 S (hdN m hm) hm
    have heq := e_norm15 (d := d) hd2 (m : G)
    refine e_pair15 hUe hzU huU hz1 hzd hud hz2 hUcomm ?_ ?_ (e_cocycle15 hd2 _)
    · rw [heq]
      exact hcs.1
    · rw [heq]
      exact hcs.2
  have hprod : ∀ a ∈ (twistNorm15 hc sg).ker, a ∉ L → ∀ b ∈ (twistNorm15 hc sg).ker, b ∉ L →
      b * a ∈ L := by
    have key : ∀ x : ↥Y, (QuotientGroup.mk x : ↥Y ⧸ U.subgroupOf Y) ∈ (twistNorm15 hc sg).ker →
        (QuotientGroup.mk x : ↥Y ⧸ U.subgroupOf Y) ∉ L →
        (x : G)⁻¹ * (d * x * d⁻¹) ∈ U ∧
          ((x : G)⁻¹ * (d * x * d⁻¹) = u ∨ (x : G)⁻¹ * (d * x * d⁻¹) = u * z) := by
      intro x hx hxL
      have hxU : (x : G)⁻¹ * (d * x * d⁻¹) ∈ U := by
        apply e_mem15 S x.2
        exact (twistNorm15_mk_eq_one_iff hdN hsgW x x.2).1 (MonoidHom.mem_ker.1 hx)
      refine ⟨hxU, ?_⟩
      rcases hUe _ hxU with h | h | h | h
      · exact absurd (hLmem x x.2 (lift15 S hzU huU hz2 hud x.2 (Or.inl h))) hxL
      · exact absurd (hLmem x x.2 (lift15 S hzU huU hz2 hud x.2 (Or.inr h))) hxL
      · exact Or.inl h
      · exact Or.inr h
    intro a ha haL b hb hbL
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨hxU, hx⟩ := key x ha haL
    obtain ⟨hxU', hx'⟩ := key x' hb hbL
    rw [← QuotientGroup.mk_mul]
    have hmul := e_mul15 S x.2 hxU'
    exact hLmem ((x' : G) * x) (mul_mem x'.2 x.2)
      (lift15 S hzU huU hz2 hud (mul_mem x'.2 x.2)
        (by rw [hmul]; exact prod_pair15 hz2 hzu hu2 hx' hx))
  have h4 := four_le_card_of_obstruction15 hc sg h16 L hLN hprod
  have hcard := card_ker_mul_card_range15 ψ
  have hzC : z ∈ C := (hmemC z).2 ⟨hUY hzU, by
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hzd]⟩
  have hker2 : 2 ≤ Nat.card ψ.ker := by
    have hne : ψ.ker ≠ ⊥ := by
      intro hbot
      have hmem : (⟨z, hzC⟩ : ↥C) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hψ]
        exact (mk_eq_one_iff15 _).2 hzU
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hz1 (congrArg Subtype.val hmem)
    have := (Subgroup.one_lt_card_iff_ne_bot ψ.ker).2 hne
    omega
  have hmulle : 2 * 4 ≤ Nat.card ψ.ker * Nat.card ψ.range := Nat.mul_le_mul hker2 h4
  omega

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
