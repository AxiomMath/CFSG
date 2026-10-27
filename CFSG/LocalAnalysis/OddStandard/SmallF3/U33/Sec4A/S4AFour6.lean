module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type*} [Group G]

theorem card_le_six_mul_card_inf_centralizer {K E : Subgroup G} (hE : Nat.card E = 4)
    (hKE : ∀ k ∈ K, ∀ e ∈ E, k * e * k⁻¹ ∈ E) [Finite G] :
    Nat.card K ≤ 6 * Nat.card ↥(K ⊓ centralizer (E : Set G)) := by
  classical
  let X : Type _ := {e : ↥E // e ≠ 1}
  have hne : ∀ k e : G, e ≠ 1 → k * e * k⁻¹ ≠ 1 := by
    intro k e he h1
    apply he
    have h2 : e = k⁻¹ * (k * e * k⁻¹) * k := by group
    rw [h2, h1]
    group
  let c : ↥K → X → X := fun k x =>
    ⟨⟨(k : G) * (x.1 : G) * (k : G)⁻¹, hKE k k.2 x.1 x.1.2⟩, fun h =>
      hne k x.1 (fun h1 => x.2 (Subtype.ext h1)) (congrArg Subtype.val h)⟩
  have hcc : ∀ k l x, c k (c l x) = c (k * l) x := by
    intro k l x
    apply Subtype.ext
    apply Subtype.ext
    simp only [c, Subgroup.coe_mul, mul_inv_rev]
    group
  have hc1 : ∀ x, c 1 x = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simp [c]
  let φ : ↥K →* Equiv.Perm X :=
    { toFun := fun k =>
        ⟨c k, c k⁻¹, fun x => by rw [hcc, inv_mul_cancel, hc1],
          fun x => by rw [hcc, mul_inv_cancel, hc1]⟩
      map_one' := by
        ext x
        exact congrArg (fun y : X => ((y : ↥E) : G)) (hc1 x)
      map_mul' := fun k l => by
        ext x
        exact congrArg (fun y : X => ((y : ↥E) : G)) (hcc k l x).symm }
  have hker : φ.ker ≤ (K ⊓ centralizer (E : Set G)).subgroupOf K := by
    intro k hk
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      simp
    · have hx : φ k ⟨⟨e, he⟩, fun h => he1 (congrArg Subtype.val h)⟩ =
          ⟨⟨e, he⟩, fun h => he1 (congrArg Subtype.val h)⟩ := by
        rw [MonoidHom.mem_ker.mp hk]
        rfl
      have hx' : (k : G) * e * (k : G)⁻¹ = e :=
        congrArg (fun y : X => ((y : ↥E) : G)) hx
      calc e * (k : G) = ((k : G) * e * (k : G)⁻¹) * (k : G) := by rw [hx']
        _ = (k : G) * e := by group
  have hXcard : Nat.card X ≤ 3 := by
    haveI : Fintype ↥E := Fintype.ofFinite _
    have h1 : Fintype.card X = Fintype.card ↥E - 1 := by
      have := Fintype.card_subtype_compl (fun e : ↥E => e = 1)
      rw [Fintype.card_subtype_eq] at this
      exact this
    rw [Nat.card_eq_fintype_card, h1, ← Nat.card_eq_fintype_card, hE]
  have hperm : Nat.card (Equiv.Perm X) ≤ 6 := by
    haveI : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have h3 : Fintype.card X ≤ 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact hXcard
    exact (Nat.factorial_le h3).trans (by decide)
  have hrange : Nat.card φ.range ≤ 6 := (Subgroup.card_le_card_group _).trans hperm
  have hkerc : Nat.card φ.ker ≤ Nat.card ↥(K ⊓ centralizer (E : Set G)) := by
    have h1 := Subgroup.card_le_of_le hker
    have h2 : Nat.card ((K ⊓ centralizer (E : Set G)).subgroupOf K) =
        Nat.card ↥(K ⊓ centralizer (E : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    omega
  calc Nat.card K = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index φ.ker).symm
    _ = Nat.card φ.ker * Nat.card φ.range := by rw [Subgroup.index_ker]
    _ ≤ Nat.card ↥(K ⊓ centralizer (E : Set G)) * 6 := Nat.mul_le_mul hkerc hrange
    _ = 6 * Nat.card ↥(K ⊓ centralizer (E : Set G)) := mul_comm _ _

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
