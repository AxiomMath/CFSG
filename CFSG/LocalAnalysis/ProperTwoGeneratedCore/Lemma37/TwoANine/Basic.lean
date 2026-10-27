module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

structure IsTwoANine (J : Type*) [Group J] : Prop where
  perfect : Group.IsPerfect J
  card_center : Nat.card (center J) = 2
  nonempty_mulEquiv : Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 9))

variable {J : Type*} [Group J]

section Proj

variable (e : J ⧸ center J ≃* alternatingGroup (Fin 9))

@[expose] def proj : J →* alternatingGroup (Fin 9) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center J))

@[simp] theorem proj_apply (x : J) : proj e x = e (x : J ⧸ center J) :=
  rfl

theorem proj_surjective : Function.Surjective (proj e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem proj_eq_one_iff {x : J} : proj e x = 1 ↔ x ∈ center J := by
  rw [proj_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem ker_proj : (proj e).ker = center J := by
  ext x
  rw [MonoidHom.mem_ker, proj_eq_one_iff]

theorem proj_eq_proj_iff {x y : J} : proj e x = proj e y ↔ x⁻¹ * y ∈ center J := by
  rw [← proj_eq_one_iff e, map_mul, map_inv, inv_mul_eq_one, eq_comm]

theorem proj_mul_of_mem_center {x c : J} (hc : c ∈ center J) : proj e (x * c) = proj e x := by
  rw [map_mul, (proj_eq_one_iff e).mpr hc, mul_one]

theorem exists_conj_eq_mul_of_isConj {u v : J} (h : IsConj (proj e u) (proj e v)) :
    ∃ g : J, ∃ c ∈ center J, g * u * g⁻¹ = v * c := by
  obtain ⟨h, hh⟩ := isConj_iff.mp h
  obtain ⟨g, rfl⟩ := proj_surjective e h
  refine ⟨g, v⁻¹ * (g * u * g⁻¹), (proj_eq_proj_iff e).mp ?_, (mul_inv_cancel_left v _).symm⟩
  rw [map_mul, map_mul, map_inv, hh]

end Proj

@[expose] noncomputable def zbar (J : Type*) [Group J] : J :=
  Classical.epsilon fun z => z ∈ center J ∧ z ≠ 1

namespace IsTwoANine

variable (hJ : IsTwoANine J)
include hJ

theorem exists_mem_center_ne_one : ∃ z ∈ center J, z ≠ 1 := by
  rcases (center J).bot_or_exists_ne_one with h | h
  · have h2 := hJ.card_center
    rw [h, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  · exact h

private theorem zbar_spec : zbar J ∈ center J ∧ zbar J ≠ 1 := by
  obtain ⟨z, hz, hz1⟩ := hJ.exists_mem_center_ne_one
  exact Classical.epsilon_spec (p := fun z => z ∈ center J ∧ z ≠ 1) ⟨z, hz, hz1⟩

theorem zbar_mem_center : zbar J ∈ center J :=
  hJ.zbar_spec.1

theorem zbar_ne_one : zbar J ≠ 1 :=
  hJ.zbar_spec.2

theorem eq_zbar_of_mem_center {z : J} (hz : z ∈ center J) (hz1 : z ≠ 1) : z = zbar J := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center J)).mp hJ.card_center
  have h1 : (⟨z, hz⟩ : center J) = y := hy _ fun h => hz1 (congrArg Subtype.val h)
  have h2 : (⟨zbar J, hJ.zbar_mem_center⟩ : center J) = y :=
    hy _ fun h => hJ.zbar_ne_one (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem mem_center_iff {x : J} : x ∈ center J ↔ x = 1 ∨ x = zbar J := by
  refine ⟨fun hx => (eq_or_ne x 1).imp_right (hJ.eq_zbar_of_mem_center hx), ?_⟩
  rintro (rfl | rfl)
  · exact (center J).one_mem
  · exact hJ.zbar_mem_center

theorem commute_zbar (g : J) : Commute g (zbar J) :=
  (Subgroup.mem_center_iff.mp hJ.zbar_mem_center g)

theorem zbar_mul_zbar : zbar J * zbar J = 1 := by
  have h := hJ.mem_center_iff.mp ((center J).mul_mem hJ.zbar_mem_center hJ.zbar_mem_center)
  rcases h with h | h
  · exact h
  · exact absurd (mul_eq_left.mp h) hJ.zbar_ne_one

theorem zbar_sq : zbar J ^ 2 = 1 := by
  rw [sq, hJ.zbar_mul_zbar]

theorem orderOf_zbar : orderOf (zbar J) = 2 :=
  orderOf_eq_prime hJ.zbar_sq hJ.zbar_ne_one

theorem sq_eq_one_of_mem_center {c : J} (hc : c ∈ center J) : c ^ 2 = 1 := by
  rcases hJ.mem_center_iff.mp hc with rfl | rfl
  · exact one_pow 2
  · exact hJ.zbar_sq

theorem isPGroup_center : IsPGroup 2 (center J) :=
  IsPGroup.of_card (n := 1) (by rw [hJ.card_center, pow_one])

theorem proj_zbar (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) : proj e (zbar J) = 1 :=
  (proj_eq_one_iff e).mpr hJ.zbar_mem_center

theorem proj_eq_proj_iff' (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {x y : J} :
    proj e x = proj e y ↔ y = x ∨ y = x * zbar J := by
  rw [proj_eq_proj_iff, hJ.mem_center_iff, inv_mul_eq_one, inv_mul_eq_iff_eq_mul, eq_comm]

theorem sq_eq_of_isConj (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {u v : J}
    (h : IsConj (proj e u) (proj e v)) (hv : v ^ 2 ∈ center J) : u ^ 2 = v ^ 2 := by
  obtain ⟨g, c, hc, hg⟩ := exists_conj_eq_mul_of_isConj e h
  have hcv : Commute v c := Subgroup.mem_center_iff.mp hc v
  have h2 : g * u ^ 2 * g⁻¹ = v ^ 2 := by
    rw [← conj_pow, hg, hcv.mul_pow, hJ.sq_eq_one_of_mem_center hc, mul_one]
  calc u ^ 2 = g⁻¹ * (g * u ^ 2 * g⁻¹) * g := by group
    _ = g⁻¹ * v ^ 2 * g := by rw [h2]
    _ = v ^ 2 := by rw [mul_assoc, ← Subgroup.mem_center_iff.mp hv g, inv_mul_cancel_left]

theorem card_eq : Nat.card J = 362880 := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center J), Nat.card_congr e.toEquiv,
    hJ.card_center, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem finite : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [hJ.card_eq]; norm_num)

theorem of_mulEquiv {K : Type*} [Group K] (f : J ≃* K) : IsTwoANine K := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  have : Group.IsPerfect J := hJ.perfect
  exact ⟨Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective,
    (Nat.card_congr (Subgroup.centerCongr f).toEquiv).symm.trans hJ.card_center,
    ⟨(QuotientGroup.congr (center J) (center K) f (Subgroup.map_center_eq f)).symm.trans e⟩⟩

end IsTwoANine

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
