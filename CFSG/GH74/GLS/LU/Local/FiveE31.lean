module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

open Subgroup

namespace CFSG.GH74.GLS.LU.Local.Five

section E31Aux

variable {G : Type} [Group G]

private theorem finite_subgroup_subtype [Finite G] (p : Subgroup G → Prop) :
    Finite {A : Subgroup G // p A} :=
  Finite.of_injective (fun A : {A : Subgroup G // p A} => ((A.1 : Subgroup G) : Set G))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

private theorem orderOf_eq_five_of_mem {E : Subgroup G} (hexp : ∀ e ∈ E, e ^ 5 = 1) {y : G}
    (hy : y ∈ E) (hy1 : y ≠ 1) : orderOf y = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (hexp y hy) hy1

private theorem eq_zpowers_of_card_five [Finite G] {E A : Subgroup G}
    (hexp : ∀ e ∈ E, e ^ 5 = 1) (hAE : A ≤ E) (hA : Nat.card ↥A = 5) {y : G} (hy : y ∈ A)
    (hy1 : y ≠ 1) : A = zpowers y := by
  have hord : orderOf y = 5 := orderOf_eq_five_of_mem hexp (hAE hy) hy1
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr hy)
  rw [Nat.card_zpowers, hord, hA]

private theorem mem_map_conj_iff {g x : G} {X : Subgroup G} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  rw [Subgroup.mem_map_equiv]
  rfl

end E31Aux

theorem card_subgroups_five_le {G : Type} [Group G] [Finite G] (E : Subgroup G)
    (hcard : Nat.card ↥E = 125) (hexp : ∀ e ∈ E, e ^ 5 = 1) :
    Nat.card {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} ≤ 31 := by
  have hex : ∀ A : {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5}, ∃ a : G, a ∈ A.1 ∧ a ≠ 1 := by
    intro A
    have hnt : Nontrivial ↥A.1 := Finite.one_lt_card_iff_nontrivial.mp (by rw [A.2.2]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥A.1)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  choose gen hgenmem hgenne using hex
  have hgenord : ∀ A, orderOf (gen A) = 5 := fun A =>
    orderOf_eq_five_of_mem hexp (A.2.1 (hgenmem A)) (hgenne A)
  have hpow_ne : ∀ (A : {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5}) (i : Fin 4),
      gen A ^ (i.val + 1) ≠ 1 := by
    intro A i h
    have h5 : 5 ∣ i.val + 1 := by
      rw [← hgenord A]
      exact orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by omega) h5
    omega
  let F : {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} × Fin 4 → {g : ↥E // g ≠ 1} := fun p =>
    ⟨⟨gen p.1 ^ (p.2.val + 1), pow_mem (p.1.2.1 (hgenmem p.1)) _⟩, fun h =>
      hpow_ne p.1 p.2 (congrArg Subtype.val h)⟩
  have hF : Function.Injective F := by
    rintro ⟨A, i⟩ ⟨B, j⟩ h
    have h' : gen A ^ (i.val + 1) = gen B ^ (j.val + 1) :=
      congrArg (fun z : {g : ↥E // g ≠ 1} => (z.1 : G)) h
    have hy1 : gen A ^ (i.val + 1) ≠ 1 := hpow_ne A i
    have hAy : gen A ^ (i.val + 1) ∈ A.1 := pow_mem (hgenmem A) _
    have hBy : gen A ^ (i.val + 1) ∈ B.1 := h' ▸ pow_mem (hgenmem B) _
    have hAB : A.1 = B.1 :=
      (eq_zpowers_of_card_five hexp A.2.1 A.2.2 hAy hy1).trans
        (eq_zpowers_of_card_five hexp B.2.1 B.2.2 hBy hy1).symm
    have hAB' : A = B := Subtype.ext hAB
    subst hAB'
    have hij : i.val + 1 = j.val + 1 :=
      pow_injOn_Iio_orderOf (x := gen A) (by simp [hgenord A]; omega)
        (by simp [hgenord A]; omega) h'
    exact Prod.ext rfl (Fin.ext (Nat.add_right_cancel hij))
  have hcT : Nat.card {g : ↥E // g ≠ 1} + 1 = 125 := by
    classical
    have h1 := Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥E))
    have : Fintype {g : ↥E // g ≠ 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, hcard] at h1
    exact h1
  have : Finite {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} :=
    finite_subgroup_subtype _
  have hle := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_fin] at hle
  omega

theorem card_le_mul_normalizer_of_five {G : Type} [Group G] [Finite G] (N E X : Subgroup G)
    (hNE : N ≤ Subgroup.normalizer (E : Set G)) (hcard : Nat.card ↥E = 125)
    (hexp : ∀ e ∈ E, e ^ 5 = 1) (hXE : X ≤ E) (hX : Nat.card ↥X = 5) :
    Nat.card ↥N ≤ 31 * Nat.card ↥(N ⊓ Subgroup.normalizer (X : Set G)) := by
  have hS := card_subgroups_five_le E hcard hexp
  have : Finite {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} := finite_subgroup_subtype _
  have hconj_le : ∀ n : ↥N, X.map (MulAut.conj (n : G)).toMonoidHom ≤ E := by
    intro n x hx
    rw [mem_map_conj_iff] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNE n.2) ((n : G)⁻¹ * x * (n : G))).mp (hXE hx)
    have e : (n : G) * ((n : G)⁻¹ * x * (n : G)) * (n : G)⁻¹ = x := by group
    rwa [e] at h1
  have hconj_card : ∀ n : ↥N, Nat.card ↥(X.map (MulAut.conj (n : G)).toMonoidHom) = 5 := by
    intro n
    rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective, hX]
  let f : ↥N → {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} := fun n =>
    ⟨X.map (MulAut.conj (n : G)).toMonoidHom, hconj_le n, hconj_card n⟩
  let M : Subgroup ↥N := (N ⊓ Subgroup.normalizer (X : Set G)).subgroupOf N
  have hM : ∀ a b : ↥N, a⁻¹ * b ∈ M ↔ f a = f b := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨-, hm⟩
      apply Subtype.ext
      ext x
      show x ∈ X.map (MulAut.conj (a : G)).toMonoidHom ↔ x ∈ X.map (MulAut.conj (b : G)).toMonoidHom
      rw [mem_map_conj_iff, mem_map_conj_iff]
      have h1 := Subgroup.mem_normalizer_iff.mp (inv_mem hm) ((a : G)⁻¹ * x * (a : G))
      have e : ((a : G)⁻¹ * (b : G))⁻¹ * ((a : G)⁻¹ * x * (a : G)) * (((a : G)⁻¹ * (b : G))⁻¹)⁻¹
          = (b : G)⁻¹ * x * (b : G) := by group
      rw [e] at h1
      exact h1
    · intro h
      refine ⟨(a⁻¹ * b).2, ?_⟩
      have hmap : ∀ x : G, (a : G)⁻¹ * x * (a : G) ∈ X ↔ (b : G)⁻¹ * x * (b : G) ∈ X := by
        intro x
        have := SetLike.ext_iff.mp (congrArg Subtype.val h) x
        rwa [mem_map_conj_iff, mem_map_conj_iff] at this
      refine Subgroup.mem_normalizer_iff.mpr (fun h' => ?_)
      have h1 := hmap ((b : G) * h' * (b : G)⁻¹)
      have e1 : (a : G)⁻¹ * ((b : G) * h' * (b : G)⁻¹) * (a : G)
          = ((a : G)⁻¹ * (b : G)) * h' * ((a : G)⁻¹ * (b : G))⁻¹ := by group
      have e2 : (b : G)⁻¹ * ((b : G) * h' * (b : G)⁻¹) * (b : G) = h' := by group
      rw [e1, e2] at h1
      exact h1.symm
  let g : ↥N ⧸ M → {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} :=
    Quotient.lift f (fun a b hab => (hM a b).mp (QuotientGroup.leftRel_apply.mp hab))
  have hg : Function.Injective g := by
    intro q₁ q₂ h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.mpr ((hM a b).mpr h)
  have hidx : M.index ≤ Nat.card {A : Subgroup G // A ≤ E ∧ Nat.card ↥A = 5} :=
    Nat.card_le_card_of_injective g hg
  have hMcard : Nat.card ↥M = Nat.card ↥(N ⊓ Subgroup.normalizer (X : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card ↥N = M.index * Nat.card ↥M := (Subgroup.index_mul_card M).symm
    _ ≤ 31 * Nat.card ↥(N ⊓ Subgroup.normalizer (X : Set G)) := by
        rw [hMcard]
        exact Nat.mul_le_mul (hidx.trans hS) le_rfl

end CFSG.GH74.GLS.LU.Local.Five
