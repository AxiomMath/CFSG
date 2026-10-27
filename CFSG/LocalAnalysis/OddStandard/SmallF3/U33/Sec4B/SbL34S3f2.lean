module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3f1
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem exists_subgroup_centralized_mod (O V : Subgroup G) (a b : G) (hVO : V ≤ O)
    (hVn : ∀ o ∈ O, ∀ v ∈ V, o * v * o⁻¹ ∈ V)
    (hcomm : ∀ x ∈ O, ∀ y ∈ O, x * y * x⁻¹ * y⁻¹ ∈ V) (hsq : ∀ x ∈ O, x * x ∈ V)
    (hcard : Nat.card O = 2 ^ 6 * Nat.card V)
    (haO : ∀ x ∈ O, a * x * a⁻¹ ∈ O) (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (hbO : ∀ x ∈ O, b * x * b⁻¹ ∈ O) (hbV : ∀ v ∈ V, b * v * b⁻¹ ∈ V)
    (ha2 : a * a ∈ O) (hb2 : b * b ∈ O) (hab : a * b * a⁻¹ * b⁻¹ ∈ O) :
    ∃ A : Subgroup G, V ≤ A ∧ A ≤ O ∧ 4 * Nat.card V ≤ Nat.card A ∧
      (∀ x ∈ A, a * x * a⁻¹ * x⁻¹ ∈ V) ∧ (∀ x ∈ A, b * x * b⁻¹ * x⁻¹ ∈ V) := by
  let N : Subgroup ↥O := V.subgroupOf O
  have hNnormal : N.Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hVn (g : G) g.2 (n : G) hn⟩
  letI : N.Normal := hNnormal
  let π : ↥O →* (↥O ⧸ N) := QuotientGroup.mk' N
  let cA : ↥O →* ↥O :=
    { toFun := fun x => ⟨a * (x : G) * a⁻¹, haO (x : G) x.2⟩
      map_one' := by
        apply Subtype.ext
        show a * (1 : G) * a⁻¹ = 1
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show a * ((x : G) * (y : G)) * a⁻¹ =
          (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹)
        group }
  have hcA : ∀ x : ↥O, (cA x : G) = a * (x : G) * a⁻¹ := fun _ => rfl
  let cB : ↥O →* ↥O :=
    { toFun := fun x => ⟨b * (x : G) * b⁻¹, hbO (x : G) x.2⟩
      map_one' := by
        apply Subtype.ext
        show b * (1 : G) * b⁻¹ = 1
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show b * ((x : G) * (y : G)) * b⁻¹ =
          (b * (x : G) * b⁻¹) * (b * (y : G) * b⁻¹)
        group }
  have hcB : ∀ x : ↥O, (cB x : G) = b * (x : G) * b⁻¹ := fun _ => rfl
  have hcaN : N ≤ N.comap cA := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hcA x]
    exact haV (x : G) hx
  have hcbN : N ≤ N.comap cB := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hcB x]
    exact hbV (x : G) hx
  let α : (↥O ⧸ N) →* (↥O ⧸ N) := QuotientGroup.map N N cA hcaN
  let β : (↥O ⧸ N) →* (↥O ⧸ N) := QuotientGroup.map N N cB hcbN
  have hmkA : ∀ x : ↥O, α (QuotientGroup.mk x) = QuotientGroup.mk (cA x) :=
    fun x => QuotientGroup.map_mk N N cA hcaN x
  have hmkB : ∀ x : ↥O, β (QuotientGroup.mk x) = QuotientGroup.mk (cB x) :=
    fun x => QuotientGroup.map_mk N N cB hcbN x
  have hEsq : ∀ x : ↥O ⧸ N, x * x = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    rw [← QuotientGroup.mk_mul N y y, QuotientGroup.eq_one_iff (y * y)]
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul] using hsq (y : G) y.2
  have hNcard : Nat.card N = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVO).toEquiv
  have hEcard : Nat.card (↥O ⧸ N) = 2 ^ 6 := by
    have hO : Nat.card ↥O = Nat.card (↥O ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, hcard] at hO
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥V)) hO.symm
  haveI hEcomm : IsMulCommutative (↥O ⧸ N) :=
    IsMulCommutative.of_comm fun x y => by
      refine QuotientGroup.induction_on x ?_
      intro p
      refine QuotientGroup.induction_on y ?_
      intro q
      rw [← QuotientGroup.mk_mul N p q, ← QuotientGroup.mk_mul N q p, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have h2 := hcomm ((q : G)⁻¹) (O.inv_mem q.2) ((p : G)⁻¹) (O.inv_mem p.2)
      convert h2 using 1 <;> simp only [Subgroup.coe_mul, Subgroup.coe_inv] <;> group
  have hα : ∀ x, α (α x) = x := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    rw [hmkA y, hmkA (cA y)]
    have hw : (cA (cA y) * y⁻¹ : ↥O) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      have h := hcomm (a * a) ha2 (y : G) y.2
      convert h using 1 <;>
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcA] <;> group
    have h1 : (QuotientGroup.mk (cA (cA y) * y⁻¹) : ↥O ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hw
    calc (QuotientGroup.mk (cA (cA y)) : ↥O ⧸ N)
        = QuotientGroup.mk (cA (cA y) * y⁻¹ * y) := by congr 1; group
      _ = QuotientGroup.mk (cA (cA y) * y⁻¹) * QuotientGroup.mk y := by
            rw [QuotientGroup.mk_mul N (cA (cA y) * y⁻¹) y]
      _ = 1 * QuotientGroup.mk y := by rw [h1]
      _ = QuotientGroup.mk y := one_mul _
  have hβ : ∀ x, β (β x) = x := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    rw [hmkB y, hmkB (cB y)]
    have hw : (cB (cB y) * y⁻¹ : ↥O) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      have h := hcomm (b * b) hb2 (y : G) y.2
      convert h using 1 <;>
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcB] <;> group
    have h1 : (QuotientGroup.mk (cB (cB y) * y⁻¹) : ↥O ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hw
    calc (QuotientGroup.mk (cB (cB y)) : ↥O ⧸ N)
        = QuotientGroup.mk (cB (cB y) * y⁻¹ * y) := by congr 1; group
      _ = QuotientGroup.mk (cB (cB y) * y⁻¹) * QuotientGroup.mk y := by
            rw [QuotientGroup.mk_mul N (cB (cB y) * y⁻¹) y]
      _ = 1 * QuotientGroup.mk y := by rw [h1]
      _ = QuotientGroup.mk y := one_mul _
  have hαβ : ∀ x, α (β x) = β (α x) := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    rw [hmkB y, hmkA (cB y), hmkA y, hmkB (cA y)]
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have h2 := hcomm (a * b * a⁻¹ * b⁻¹) hab
      ((↑(cB (cA y)) : G)⁻¹) (O.inv_mem (cB (cA y)).2)
    convert h2 using 1 <;>
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcA, hcB] <;> group
  obtain ⟨F, hFcard, hFfix⟩ :=
    exists_fixed_subgroup_of_commuting_involutions hEsq hEcard α β hα hβ hαβ
  let A₀ : Subgroup ↥O := F.comap π
  let A : Subgroup G := A₀.map O.subtype
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    rw [Subgroup.mem_map]
    refine ⟨⟨v, hVO hv⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : π (⟨v, hVO hv⟩ : ↥O) = 1 := by
      change (QuotientGroup.mk (⟨v, hVO hv⟩ : ↥O) : ↥O ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_subgroupOf]
      exact hv
    rw [h1]
    exact F.one_mem
  ·
    rintro y ⟨z, _, rfl⟩
    exact z.2
  ·
    have hA0card : Nat.card A₀ = Nat.card F * Nat.card N := by
      have h1 : A₀.index * Nat.card A₀ = Nat.card ↥O :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup A₀).symm
      have h2 : Nat.card ↥O = Nat.card (↥O ⧸ N) * Nat.card N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have h3 : Nat.card (↥O ⧸ N) = A₀.index * Nat.card F := by
        rw [show A₀.index = Nat.card ((↥O ⧸ N) ⧸ F) from
          Subgroup.index_comap_of_surjective (H := F) (f := π)
            (QuotientGroup.mk'_surjective N)]
        exact Subgroup.card_eq_card_quotient_mul_card_subgroup F
      have h4 : A₀.index * Nat.card A₀ = A₀.index * (Nat.card F * Nat.card N) := by
        calc A₀.index * Nat.card A₀ = Nat.card ↥O := h1
          _ = Nat.card (↥O ⧸ N) * Nat.card N := h2
          _ = (A₀.index * Nat.card F) * Nat.card N := by rw [h3]
          _ = A₀.index * (Nat.card F * Nat.card N) := Nat.mul_assoc _ _ _
      exact Nat.mul_left_cancel (Nat.card_pos (α := ↥O ⧸ A₀)) h4
    have hAcard : Nat.card A = Nat.card A₀ :=
      Subgroup.card_map_of_injective (K := A₀) O.subtype_injective
    rw [hAcard, hA0card, hNcard]
    exact Nat.mul_le_mul_right (Nat.card V) hFcard
  ·
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Subgroup.mem_comap] at hx'
    have hfix : α (QuotientGroup.mk x') = QuotientGroup.mk x' := (hFfix (π x') hx').1
    rw [hmkA x'] at hfix
    have hmemN : x'⁻¹ * cA x' ∈ N := QuotientGroup.eq.mp hfix.symm
    have hwV : (↑(x'⁻¹ * cA x') : G) ∈ V := by
      rwa [Subgroup.mem_subgroupOf] at hmemN
    have hgx' : ((↑(cA x') : G) * (↑x')⁻¹) ∈ V := by
      have hconj := hVn (↑x') x'.2 (↑(x'⁻¹ * cA x')) hwV
      convert hconj using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcA x'] at hgx'
    exact hgx'
  ·
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Subgroup.mem_comap] at hx'
    have hfix : β (QuotientGroup.mk x') = QuotientGroup.mk x' := (hFfix (π x') hx').2
    rw [hmkB x'] at hfix
    have hmemN : x'⁻¹ * cB x' ∈ N := QuotientGroup.eq.mp hfix.symm
    have hwV : (↑(x'⁻¹ * cB x') : G) ∈ V := by
      rwa [Subgroup.mem_subgroupOf] at hmemN
    have hgx' : ((↑(cB x') : G) * (↑x')⁻¹) ∈ V := by
      have hconj := hVn (↑x') x'.2 (↑(x'⁻¹ * cB x')) hwV
      convert hconj using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcB x'] at hgx'
    exact hgx'

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
