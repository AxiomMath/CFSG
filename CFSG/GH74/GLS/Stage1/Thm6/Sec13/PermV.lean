module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

abbrev Vs (V : Subgroup G) : Type _ := {v : G // v ∈ V ∧ v ≠ 1}

theorem card_Vs [Finite G] (V : Subgroup G) (hV : Nat.card V = 4) : Nat.card (Vs V) = 3 := by
  have e : Vs V ≃ ↥((V : Set G) \ {1}) :=
    Equiv.subtypeEquivRight (fun v => by simp)
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem V.one_mem,
    ← Nat.card_coe_set_eq]
  have : Nat.card ((V : Set G)) = 4 := hV
  omega

@[expose] def permOf (V : Subgroup G) (n : G) (hn : n ∈ normalizer (V : Set G)) :
    Equiv.Perm (Vs V) where
  toFun v := ⟨n * v * n⁻¹, (mem_normalizer_iff.1 hn v.1).1 v.2.1, fun h => v.2.2 (by
    have : (v : G) = n⁻¹ * (n * v * n⁻¹) * n := by group
    rw [this, h]; group)⟩
  invFun v := ⟨n⁻¹ * v * n, (mem_normalizer_iff''.1 hn v.1).1 v.2.1, fun h => v.2.2 (by
    have : (v : G) = n * (n⁻¹ * v * n) * n⁻¹ := by group
    rw [this, h]; group)⟩
  left_inv v := by
    apply Subtype.ext
    show n⁻¹ * (n * (v : G) * n⁻¹) * n = v
    group
  right_inv v := by
    apply Subtype.ext
    show n * (n⁻¹ * (v : G) * n) * n⁻¹ = v
    group

@[expose] def permHom (V : Subgroup G) : ↥(normalizer (V : Set G)) →* Equiv.Perm (Vs V) where
  toFun n := permOf V n n.2
  map_one' := by
    ext v
    show (1 : G) * (v : G) * (1 : G)⁻¹ = v
    group
  map_mul' n m := by
    ext v
    show ((n : G) * (m : G)) * (v : G) * ((n : G) * (m : G))⁻¹ =
      (n : G) * ((m : G) * (v : G) * (m : G)⁻¹) * (n : G)⁻¹
    group

theorem permHom_eq_one_iff (V : Subgroup G) (n : ↥(normalizer (V : Set G))) :
    permHom V n = 1 ↔ (n : G) ∈ centralizer (V : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; simp
    · have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨v, hv, hv1⟩)
      have h2 : (n : G) * v * (n : G)⁻¹ = v := h1
      calc v * (n : G) = ((n : G) * v * (n : G)⁻¹) * (n : G) := by rw [h2]
        _ = (n : G) * v := by group
  · intro h
    ext v
    show (n : G) * (v : G) * (n : G)⁻¹ = v
    have := mem_centralizer_iff.1 h v v.2.1
    calc (n : G) * v * (n : G)⁻¹ = (v * (n : G)) * (n : G)⁻¹ := by rw [this]
      _ = v := by group

@[expose] def permQ (V : Subgroup G) {Q : Subgroup G} (hQ : Q ≤ normalizer (V : Set G)) :
    ↥Q →* Equiv.Perm (Vs V) :=
  (permHom V).comp (Subgroup.inclusion hQ)

theorem ker_permQ (V : Subgroup G) {Q : Subgroup G} (hQ : Q ≤ normalizer (V : Set G)) :
    (permQ V hQ).ker = (centralizer (V : Set G) ⊓ Q).subgroupOf Q := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show permHom V (Subgroup.inclusion hQ q) = 1 ↔ _
  rw [permHom_eq_one_iff]
  constructor
  · intro h; exact ⟨h, q.2⟩
  · intro h; exact h.1

theorem relIndex_eq_card_range [Finite G] (V : Subgroup G) {Q : Subgroup G}
    (hQ : Q ≤ normalizer (V : Set G)) :
    (centralizer (V : Set G) ⊓ Q).relIndex Q = Nat.card (permQ V hQ).range := by
  rw [Subgroup.relIndex, ← ker_permQ V hQ, Subgroup.index_ker]

theorem relIndex_dvd_six [Finite G] {V Q : Subgroup G} (hV : Nat.card V = 4)
    (hQ : Q ≤ normalizer (V : Set G)) : (centralizer (V : Set G) ⊓ Q).relIndex Q ∣ 6 := by
  rw [relIndex_eq_card_range V hQ]
  have h1 := Subgroup.card_subgroup_dvd_card (permQ V hQ).range
  have h2 : Nat.card (Equiv.Perm (Vs V)) = 6 := by
    rw [Nat.card_perm, card_Vs V hV]; rfl
  rw [h2] at h1
  exact h1

theorem relIndex_dvd_of_le [Finite G] (V : Subgroup G) {Q Q' : Subgroup G} (hQ' : Q' ≤ Q)
    (hQ : Q ≤ normalizer (V : Set G)) :
    (centralizer (V : Set G) ⊓ Q').relIndex Q' ∣ (centralizer (V : Set G) ⊓ Q).relIndex Q := by
  rw [relIndex_eq_card_range V (hQ'.trans hQ), relIndex_eq_card_range V hQ]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨q, rfl⟩
  exact ⟨Subgroup.inclusion hQ' q, rfl⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
