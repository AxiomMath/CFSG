module

public import CFSG.LieType.D4Small.WeightBasic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
public import CFSG.LieType.D4Small.WeightClass

public section

open Matrix
open scoped commutatorElement

attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace CFSG.LieType.D4Small
namespace IsD4Root

theorem sub_of_dotProduct_eq_one {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root γ) (hγ' : IsD4Root γ')
    (h : γ ⬝ᵥ γ' = 1) : IsD4Root (γ' - γ) := by
  rw [sub_eq_add_neg]
  refine IsD4Root.add hγ' hγ.neg ?_
  have h' : γ' ⬝ᵥ γ = 1 := by rw [dotProduct_comm]; exact h
  rw [dotProduct_neg, h']

end IsD4Root

end CFSG.LieType.D4Small

namespace CFSG.LieType.D4Small.D4Datum

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {D : D4Datum G K} {X : Type*} [AddCommGroup X] [Module K X] {ρ : Representation K G X}
  {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))}

local notation "P[" α "]" => rootOp D ρ α 1
local notation "Q[" α "]" => rootOp D ρ α 2

private theorem three_eq_zero (hN : Nat.card Kˣ = 3) : (3 : ZMod (Nat.card Kˣ)) = 0 := by
  rw [hN]
  exact ZMod.natCast_self 3

private theorem two_eq_neg_one (hN : Nat.card Kˣ = 3) : (2 : ZMod (Nat.card Kˣ)) = -1 := by
  rw [hN]
  decide

private theorem two_natCast_eq_neg_one (hN : Nat.card Kˣ = 3) :
    ((2 : ℕ) : ZMod (Nat.card Kˣ)) = -1 := by
  rw [hN]
  decide

private theorem add_self_castW (hN : Nat.card Kˣ = 3) (α : Fin 4 → ℤ) :
    castW (Nat.card Kˣ) α + castW (Nat.card Kˣ) α = -castW (Nat.card Kˣ) α := by
  rw [← two_smul (ZMod (Nat.card Kˣ)) (castW (Nat.card Kˣ) α), two_eq_neg_one hN,
    neg_one_smul]

private theorem two_smul_castW_neg (hN : Nat.card Kˣ = 3) (β : Fin 4 → ℤ) :
    ((2 : ℕ) : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) (-β) =
      castW (Nat.card Kˣ) β := by
  have h2 : ((2 : ℕ) : ZMod (Nat.card Kˣ)) = -1 := by rw [hN]; decide
  rw [h2, smul_castW_neg, neg_neg, one_smul]

private theorem rootOp_one_mem_wtSpace {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} (hx : x ∈ D.wtSpace ρ a) :
    P[α] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) := by
  simpa using rootOp_mem_wtSpace D ρ α hα a hx 1

private theorem rootOp_one_neg_mem_wtSpace {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} (hx : x ∈ D.wtSpace ρ a) :
    P[(-α)] x ∈ D.wtSpace ρ (a - castW (Nat.card Kˣ) α) := by
  have h := rootOp_mem_wtSpace D ρ (-α) hα.neg a hx 1
  simpa [castW_neg, sub_eq_add_neg] using h

private theorem rootOp_two_mem_wtSpace (hN : Nat.card Kˣ = 3) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} (hx : x ∈ D.wtSpace ρ a) :
    Q[α] x ∈ D.wtSpace ρ (a - castW (Nat.card Kˣ) α) := by
  have h := rootOp_mem_wtSpace D ρ α hα a hx 2
  rw [two_natCast_eq_neg_one hN, neg_one_smul] at h
  rwa [sub_eq_add_neg]

private theorem rootOp_two_neg_mem_wtSpace (hN : Nat.card Kˣ = 3) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} (hx : x ∈ D.wtSpace ρ a) :
    Q[(-α)] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) := by
  have h := rootOp_two_mem_wtSpace (D := D) (ρ := ρ) hN hα.neg hx
  rwa [castW_neg, sub_neg_eq_add] at h

private theorem rootOp_two_mul_self (hN : Nat.card Kˣ = 3) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    Q[α] * Q[α] = 0 := by
  rw [rootOp_mul D ρ α hα 2 2, hN, if_neg (by norm_num), zero_smul]

private theorem add_castW_add_self (hN : Nat.card Kˣ = 3) (a : Fin 4 → ZMod (Nat.card Kˣ))
    (α : Fin 4 → ℤ) :
    a + castW (Nat.card Kˣ) α + castW (Nat.card Kˣ) α = a - castW (Nat.card Kˣ) α := by
  rw [add_assoc, add_self_castW hN, sub_eq_add_neg]

private theorem rho_n_apply (α : Fin 4 → ℤ) (x : X) :
    ρ (D.n α) x = ρ (D.x α 1) (ρ (D.x (-α) 1) (ρ (D.x α 1) x)) := by
  have h : ρ (D.n α) = ρ (D.x α 1) * ρ (D.x (-α) 1) * ρ (D.x α 1) := by
    rw [D4Datum.n, map_mul, map_mul]
  rw [h]
  simp [Module.End.mul_apply]

private theorem rho_x_one_apply (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    {α : Fin 4 → ℤ} (hα : IsD4Root α) (y : X) :
    ρ (D.x α 1) y = y + P[α] y + Q[α] y := by
  rw [hform α hα 1]
  simp

private theorem x_one_inv {α : Fin 4 → ℤ} (hα : IsD4Root α) : D.x α 1 = (D.x α 1)⁻¹ := by
  have h := D.x_neg hα 1
  rwa [show (-1 : K) = 1 from CharTwo.neg_eq 1] at h

private theorem rho_n_one_two_expansion (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C)
    (hmem : a + castW (Nat.card Kˣ) α ∈ C) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    ρ (D.n α) x =
      ((x + Q[α] (Q[(-α)] x) + P[(-α)] (P[α] x)) +
        (Q[(-α)] x + P[α] (P[(-α)] (P[α] x)))) + (P[α] x + P[α] x) := by
  have hmem1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∈ C := by simpa using hmem
  have hsub : a - castW (Nat.card Kˣ) α ∉ C := by
    simpa using hC.sub_not_mem a ha α hα hmem1
  have hPx : P[α] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) := rootOp_one_mem_wtSpace hα hx
  have hQ'x : Q[(-α)] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) :=
    rootOp_two_neg_mem_wtSpace hN hα hx
  have hP'Px : P[(-α)] (P[α] x) ∈ D.wtSpace ρ a := by
    have h := rootOp_one_neg_mem_wtSpace hα hPx
    rwa [add_sub_cancel_right] at h
  have zP'x : P[(-α)] x = 0 :=
    eq_zero_of_mem_wtSpace_of_not_mem hCw hsub (rootOp_one_neg_mem_wtSpace hα hx)
  have zQx : Q[α] x = 0 :=
    eq_zero_of_mem_wtSpace_of_not_mem hCw hsub (rootOp_two_mem_wtSpace hN hα hx)
  have zQ'Px : Q[(-α)] (P[α] x) = 0 := by
    refine eq_zero_of_mem_wtSpace_of_not_mem hCw ?_ (rootOp_two_neg_mem_wtSpace hN hα hPx)
    rwa [add_castW_add_self hN]
  have zPPx : P[α] (P[α] x) = 0 := by
    refine eq_zero_of_mem_wtSpace_of_not_mem hCw ?_ (rootOp_one_mem_wtSpace hα hPx)
    rwa [add_castW_add_self hN]
  have zPQ'x : P[α] (Q[(-α)] x) = 0 := by
    refine eq_zero_of_mem_wtSpace_of_not_mem hCw ?_ (rootOp_one_mem_wtSpace hα hQ'x)
    rwa [add_castW_add_self hN]
  have zQP'Px : Q[α] (P[(-α)] (P[α] x)) = 0 :=
    eq_zero_of_mem_wtSpace_of_not_mem hCw hsub (rootOp_two_mem_wtSpace hN hα hP'Px)
  have zQPx : Q[α] (P[α] x) = 0 := by
    have h := congrArg (fun f : Module.End K X => f x) (h21 α hα)
    simpa [Module.End.mul_apply] using h
  have hdecomp0 : ρ (D.n α) x =
      ((x + Q[α] (Q[(-α)] x) + P[(-α)] (P[α] x)) +
        (Q[(-α)] x + P[α] (P[(-α)] (P[α] x)))) + (P[α] x + P[α] x) := by
    rw [rho_n_apply, rho_x_one_apply hform hα, rho_x_one_apply hform hα.neg,
      rho_x_one_apply hform hα]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
      zP'x, zQx, zQ'Px, zPPx, zPQ'x, zQP'Px, zQPx, zero_add, add_zero]
    abel
  exact hdecomp0

private theorem rootOp_one_two_eq_zero (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C)
    (hmem : a + castW (Nat.card Kˣ) α ∈ C) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    x + Q[α] (Q[(-α)] x) + P[(-α)] (P[α] x) = 0 := by
  have hdecomp0 := rho_n_one_two_expansion (D := D) (ρ := ρ) hN hCw hC hform h21 hα ha hmem hx
  have hmem1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∈ C := by simpa using hmem
  have hmemrefl : reflW α a = a + castW (Nat.card Kˣ) α := by
    simpa using hC.reflW_eq a ha α hα hmem1
  have hPx : P[α] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) := rootOp_one_mem_wtSpace hα hx
  have hQ'x : Q[(-α)] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) :=
    rootOp_two_neg_mem_wtSpace hN hα hx
  have hP'Px : P[(-α)] (P[α] x) ∈ D.wtSpace ρ a := by
    have h := rootOp_one_neg_mem_wtSpace hα hPx
    rwa [add_sub_cancel_right] at h
  have hQQ'x : Q[α] (Q[(-α)] x) ∈ D.wtSpace ρ a := by
    have h := rootOp_two_mem_wtSpace hN hα hQ'x
    rwa [add_sub_cancel_right] at h
  have hPP'Px : P[α] (P[(-α)] (P[α] x)) ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) :=
    rootOp_one_mem_wtSpace hα hP'Px
  have hdecomp : ρ (D.n α) x =
      (x + Q[α] (Q[(-α)] x) + P[(-α)] (P[α] x)) +
        (Q[(-α)] x + P[α] (P[(-α)] (P[α] x))) := by
    rw [hdecomp0, add_self_eq_zero K (P[α] x), add_zero]
  have hnmem : ρ (D.n α) x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) α) := by
    have h := Submodule.mem_map_of_mem (f := ρ (D.n α)) hx
    rw [map_n_wtSpace D ρ α hα a] at h
    rwa [hmemrefl] at h
  have huv : (x + Q[α] (Q[(-α)] x) + P[(-α)] (P[α] x)) +
      (Q[(-α)] x + P[α] (P[(-α)] (P[α] x))) ∈
      D.wtSpace ρ (a + castW (Nat.card Kˣ) α) := by
    rw [← hdecomp]
    exact hnmem
  have hu : x + Q[α] (Q[(-α)] x) + P[(-α)] (P[α] x) ∈ D.wtSpace ρ a :=
    Submodule.add_mem _ (Submodule.add_mem _ hx hQQ'x) hP'Px
  have hv : Q[(-α)] x + P[α] (P[(-α)] (P[α] x)) ∈
      D.wtSpace ρ (a + castW (Nat.card Kˣ) α) :=
    Submodule.add_mem _ hQ'x hPP'Px
  have hne : a ≠ a + castW (Nat.card Kˣ) α := by
    intro h
    apply castW_ne_zero hC.three_le hα
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  exact eq_zero_of_add_mem D ρ hne hu hv huv

theorem rootOp_one_two_eq (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C)
    (hmem : a + castW (Nat.card Kˣ) α ∈ C) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    P[(-α)] (P[α] x) + Q[α] (Q[(-α)] x) = x := by
  have hu0 := rootOp_one_two_eq_zero (D := D) (ρ := ρ) hN hCw hC hform h21 hα ha hmem hx
  have h2 : x + (P[(-α)] (P[α] x) + Q[α] (Q[(-α)] x)) = 0 := by
    rw [← hu0]
    abel
  have hx2 : x + x = 0 := add_self_eq_zero K x
  exact add_left_cancel (h2.trans hx2.symm)

private theorem rho_x_neg_comm {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root γ) (hγ' : IsD4Root γ')
    (hdot : γ ⬝ᵥ γ' = 1) (x : X) :
    ρ (D.x (-γ') 1) x =
      ρ (D.x (-γ) 1) (ρ (D.x (-(γ' - γ)) 1)
        (ρ (D.x (-γ) 1) (ρ (D.x (-(γ' - γ)) 1) x))) := by
  have hδ : IsD4Root (γ' - γ) := IsD4Root.sub_of_dotProduct_eq_one hγ hγ' hdot
  have hdot' : (-γ) ⬝ᵥ (-(γ' - γ)) = -1 := by
    rw [neg_dotProduct, dotProduct_neg, neg_neg]
    have hγ2 : γ ⬝ᵥ γ = 2 := hγ
    rw [dotProduct_sub, hdot, hγ2]
    norm_num
  have hcomm : ⁅D.x (-γ) 1, D.x (-(γ' - γ)) 1⁆ = D.x (-γ') 1 := by
    have h := D.comm_eq (-γ) (-(γ' - γ)) hγ.neg hδ.neg hdot' 1 1
    rw [mul_one] at h
    have harg : -γ + -(γ' - γ) = -γ' := by abel
    rwa [harg] at h
  have hfour : D.x (-γ') 1 =
      D.x (-γ) 1 * D.x (-(γ' - γ)) 1 * D.x (-γ) 1 * D.x (-(γ' - γ)) 1 := by
    rw [← hcomm, commutatorElement_def]
    rw [← x_one_inv hγ.neg, ← x_one_inv hδ.neg]
  have hfive : ρ (D.x (-γ') 1) =
      ρ (D.x (-γ) 1) * ρ (D.x (-(γ' - γ)) 1) * ρ (D.x (-γ) 1) *
        ρ (D.x (-(γ' - γ)) 1) := by
    rw [hfour]
    simp only [map_mul]
  rw [hfive]
  simp only [Module.End.mul_apply]

private theorem rootOp_two_comp_zeros₁ (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {γ γ' : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (hγ' : IsD4Root γ')
    (hmemγ : a + castW (Nat.card Kˣ) γ ∈ C) (hmemγ' : a + castW (Nat.card Kˣ) γ' ∈ C)
    (hdot : γ ⬝ᵥ γ' = 1) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    P[(-γ)] x = 0 ∧ P[(-(γ' - γ))] x = 0 ∧ Q[(-(γ' - γ))] x = 0 ∧
      P[(-(γ' - γ))] (Q[(-γ)] x) = 0 := by
  have hmemγ1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ ∈ C := by
    simpa using hmemγ
  have hmemγ'1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ' ∈ C := by
    simpa using hmemγ'
  have hsubγ : a - castW (Nat.card Kˣ) γ ∉ C := by
    simpa using hC.sub_not_mem a ha γ hγ hmemγ1
  obtain ⟨he1, he2, he3, -⟩ :=
    hC.raise_edge hN a ha γ γ' hγ hγ' hmemγ1 hmemγ'1 hdot
  simp only [one_smul] at he1 he2 he3
  have hδ : IsD4Root (γ' - γ) := IsD4Root.sub_of_dotProduct_eq_one hγ hγ' hdot
  have hQγx : Q[(-γ)] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) γ) :=
    rootOp_two_neg_mem_wtSpace hN hγ hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact eq_zero_of_mem_wtSpace_of_not_mem hCw hsubγ (rootOp_one_neg_mem_wtSpace hγ hx)
  · exact eq_zero_of_mem_wtSpace_of_not_mem hCw he2 (rootOp_one_neg_mem_wtSpace hδ hx)
  · exact eq_zero_of_mem_wtSpace_of_not_mem hCw he1 (rootOp_two_neg_mem_wtSpace hN hδ hx)
  · exact eq_zero_of_mem_wtSpace_of_not_mem hCw he3 (rootOp_one_neg_mem_wtSpace hδ hQγx)

private theorem rootOp_two_comp_zeros₂ (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {γ γ' : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (hγ' : IsD4Root γ')
    (hmemγ : a + castW (Nat.card Kˣ) γ ∈ C) (hmemγ' : a + castW (Nat.card Kˣ) γ' ∈ C)
    (hdot : γ ⬝ᵥ γ' = 1) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    P[(-γ)] (Q[(-(γ' - γ))] (Q[(-γ)] x)) = 0 ∧
      Q[(-γ)] (Q[(-(γ' - γ))] (Q[(-γ)] x)) = 0 ∧
      P[(-γ)] (Q[(-γ)] x) = 0 ∧ Q[(-γ)] (Q[(-γ)] x) = 0 := by
  have hmemγ1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ ∈ C := by
    simpa using hmemγ
  have hmemγ'1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ' ∈ C := by
    simpa using hmemγ'
  obtain ⟨he1, -, -, he4⟩ :=
    hC.raise_edge hN a ha γ γ' hγ hγ' hmemγ1 hmemγ'1 hdot
  simp only [one_smul] at he1 he4
  have hδ : IsD4Root (γ' - γ) := IsD4Root.sub_of_dotProduct_eq_one hγ hγ' hdot
  have hQγx : Q[(-γ)] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) γ) :=
    rootOp_two_neg_mem_wtSpace hN hγ hx
  have hQδQγx : Q[(-(γ' - γ))] (Q[(-γ)] x) ∈
      D.wtSpace ρ ((a + castW (Nat.card Kˣ) γ) + castW (Nat.card Kˣ) (γ' - γ)) :=
    rootOp_two_neg_mem_wtSpace hN hδ hQγx
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine eq_zero_of_mem_wtSpace_of_not_mem hCw ?_ (rootOp_one_neg_mem_wtSpace hγ hQδQγx)
    rw [show ((a + castW (Nat.card Kˣ) γ) + castW (Nat.card Kˣ) (γ' - γ)) -
        castW (Nat.card Kˣ) γ = a + castW (Nat.card Kˣ) (γ' - γ) from by abel]
    exact he1
  · refine eq_zero_of_mem_wtSpace_of_not_mem hCw ?_ (rootOp_two_neg_mem_wtSpace hN hγ hQδQγx)
    rw [castW_sub]
    rw [show ((a + castW (Nat.card Kˣ) γ) +
        (castW (Nat.card Kˣ) γ' - castW (Nat.card Kˣ) γ)) + castW (Nat.card Kˣ) γ =
        a + castW (Nat.card Kˣ) γ' + castW (Nat.card Kˣ) γ from by abel]
    exact he4
  · have h := congrArg (fun f : Module.End K X => f x) (h12 (-γ) hγ.neg)
    simpa [Module.End.mul_apply] using h
  · have h := congrArg (fun f : Module.End K X => f x)
      (rootOp_two_mul_self (D := D) (ρ := ρ) hN hγ.neg)
    simpa [Module.End.mul_apply] using h

private theorem rootOp_two_comp_left (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root γ) (hδ : IsD4Root (γ' - γ)) {x : X}
    (hsix : ρ (D.x (-γ') 1) x =
      ρ (D.x (-γ) 1) (ρ (D.x (-(γ' - γ)) 1)
        (ρ (D.x (-γ) 1) (ρ (D.x (-(γ' - γ)) 1) x))))
    (zPγx : P[(-γ)] x = 0) (zPδx : P[(-(γ' - γ))] x = 0)
    (zQδx : Q[(-(γ' - γ))] x = 0) (zPδQγx : P[(-(γ' - γ))] (Q[(-γ)] x) = 0)
    (zPγQδQγx : P[(-γ)] (Q[(-(γ' - γ))] (Q[(-γ)] x)) = 0)
    (zQγQδQγx : Q[(-γ)] (Q[(-(γ' - γ))] (Q[(-γ)] x)) = 0)
    (zPγQγx : P[(-γ)] (Q[(-γ)] x) = 0) (zQγQγx : Q[(-γ)] (Q[(-γ)] x) = 0) :
    ρ (D.x (-γ') 1) x =
      x + Q[(-(γ' - γ))] (Q[(-γ)] x) + (Q[(-γ)] x + Q[(-γ)] x) := by
  simp only [hsix, rho_x_one_apply hform hγ.neg, rho_x_one_apply hform hδ.neg,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
    zPγx, zPδx, zQδx, zPδQγx, zPγQγx, zQγQγx, zPγQδQγx, zQγQδQγx, zero_add, add_zero]
  abel

theorem rootOp_two_comp (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {γ γ' : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (hγ' : IsD4Root γ')
    (hmemγ : a + castW (Nat.card Kˣ) γ ∈ C) (hmemγ' : a + castW (Nat.card Kˣ) γ' ∈ C)
    (hdot : γ ⬝ᵥ γ' = 1) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    Q[(-γ')] x = Q[(-(γ' - γ))] (Q[(-γ)] x) := by
  have hmemγ'1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ' ∈ C := by
    simpa using hmemγ'
  have hsubγ' : a - castW (Nat.card Kˣ) γ' ∉ C := by
    simpa using hC.sub_not_mem a ha γ' hγ' hmemγ'1
  have hδ : IsD4Root (γ' - γ) := IsD4Root.sub_of_dotProduct_eq_one hγ hγ' hdot
  have hsix := rho_x_neg_comm (D := D) (ρ := ρ) hγ hγ' hdot x
  obtain ⟨zPγx, zPδx, zQδx, zPδQγx⟩ :=
    rootOp_two_comp_zeros₁ (D := D) (ρ := ρ) hN hCw hC ha hγ hγ' hmemγ hmemγ' hdot hx
  obtain ⟨zPγQδQγx, zQγQδQγx, zPγQγx, zQγQγx⟩ :=
    rootOp_two_comp_zeros₂ (D := D) (ρ := ρ) hN hCw hC h12 ha hγ hγ' hmemγ hmemγ' hdot hx
  have hleft := rootOp_two_comp_left (D := D) (ρ := ρ) hform hγ hδ hsix
    zPγx zPδx zQδx zPδQγx zPγQδQγx zQγQδQγx zPγQγx zQγQγx
  have zPγ'x : P[(-γ')] x = 0 :=
    eq_zero_of_mem_wtSpace_of_not_mem hCw hsubγ' (rootOp_one_neg_mem_wtSpace hγ' hx)
  have hright : ρ (D.x (-γ') 1) x = x + Q[(-γ')] x := by
    rw [rho_x_one_apply hform hγ'.neg x]
    simp only [zPγ'x, add_zero]
  have heq : x + Q[(-(γ' - γ))] (Q[(-γ)] x) + (Q[(-γ)] x + Q[(-γ)] x) =
      x + Q[(-γ')] x := by
    rw [← hleft, hright]
  have hzero : Q[(-γ)] x + Q[(-γ)] x = 0 := add_self_eq_zero K (Q[(-γ)] x)
  have heq' : x + Q[(-(γ' - γ))] (Q[(-γ)] x) = x + Q[(-γ')] x := by
    have h := heq
    rw [hzero, add_zero] at h
    exact h
  exact (add_left_cancel heq').symm

theorem rootOp_two_eq_zero_of (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {γ γ' : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (hγ' : IsD4Root γ')
    (hmemγ : a + castW (Nat.card Kˣ) γ ∈ C) (hmemγ' : a + castW (Nat.card Kˣ) γ' ∈ C)
    {x : X} (hx : x ∈ D.wtSpace ρ a) (hQ : Q[(-γ)] x = 0) :
    Q[(-γ')] x = 0 := by
  by_cases hsame : γ = γ'
  · subst hsame
    exact hQ
  · have hmemγ1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ ∈ C := by
      simpa using hmemγ
    have hmemγ'1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) γ' ∈ C := by
      simpa using hmemγ'
    rcases hC.raise_adj hN a ha γ γ' hγ hγ' hmemγ1 hmemγ'1 hsame with
      hdot | ⟨γ'', hγ'', hmemγ'', hd1, hd2⟩
    · have h := rootOp_two_comp hN hCw hC hform h12 ha hγ hγ' hmemγ hmemγ' hdot hx
      rw [h, hQ, map_zero]
    · have hmemγ''0 : a + castW (Nat.card Kˣ) γ'' ∈ C := by simpa using hmemγ''
      have h1 : Q[(-γ'')] x = 0 := by
        have h := rootOp_two_comp hN hCw hC hform h12 ha hγ hγ'' hmemγ hmemγ''0 hd1 hx
        rw [h, hQ, map_zero]
      have h2 : Q[(-γ')] x = 0 := by
        have hd2' : γ'' ⬝ᵥ γ' = 1 := by rwa [dotProduct_comm] at hd2
        have h := rootOp_two_comp hN hCw hC hform h12 ha hγ'' hγ' hmemγ''0 hmemγ' hd2' hx
        rw [h, h1, map_zero]
      exact h2

@[expose] noncomputable def unSpace (D : D4Datum G K) (ρ : Representation K G X)
    (C : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
    (a : Fin 4 → ZMod (Nat.card Kˣ)) : Submodule K X :=
  D.wtSpace ρ a ⊓
    ⨅ (γ : {γ : Fin 4 → ℤ // IsD4Root γ ∧ a + castW (Nat.card Kˣ) γ ∈ C}),
      LinearMap.ker (rootOp D ρ (-γ.1) 2)

theorem mem_unSpace {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} :
    x ∈ unSpace D ρ C a ↔ x ∈ D.wtSpace ρ a ∧
      ∀ (γ : Fin 4 → ℤ), IsD4Root γ → a + castW (Nat.card Kˣ) γ ∈ C → Q[(-γ)] x = 0 := by
  rw [unSpace, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun γ hγ hmem => h ⟨γ, hγ, hmem⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun γ => h γ.1 γ.2.1 γ.2.2⟩

private theorem mem_unSpace_of_rootOp_eq_zero (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {γ : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (hmem : a + castW (Nat.card Kˣ) γ ∈ C)
    {x : X} (hx : x ∈ D.wtSpace ρ a) (hQ : Q[(-γ)] x = 0) :
    x ∈ unSpace D ρ C a := by
  rw [mem_unSpace]
  exact ⟨hx, fun γ' hγ' hmem' =>
    rootOp_two_eq_zero_of (D := D) (ρ := ρ) hN hCw hC hform h12 ha hγ hγ' hmem hmem'
      hx hQ⟩

private theorem unSpace_iSup_le_comap_rootOp_one (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0)
    {β : Fin 4 → ℤ} (hβ : IsD4Root β) :
    (⨆ a ∈ C, unSpace D ρ C a) ≤
      Submodule.comap (P[β]) (⨆ a ∈ C, unSpace D ρ C a) := by
  refine iSup_le fun a => iSup_le fun ha => ?_
  intro y hy
  have hya : y ∈ D.wtSpace ρ a := (mem_unSpace.mp hy).1
  change P[β] y ∈ ⨆ a ∈ C, unSpace D ρ C a
  by_cases hmem : a + castW (Nat.card Kˣ) β ∈ C
  · have hPy : P[β] y ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) β) :=
      rootOp_one_mem_wtSpace hβ hya
    have hQ : Q[β] (P[β] y) = 0 := by
      have h := congrArg (fun f : Module.End K X => f y) (h21 β hβ)
      simpa [Module.End.mul_apply] using h
    have hmem' : a + castW (Nat.card Kˣ) β + castW (Nat.card Kˣ) (-β) ∈ C := by
      rw [castW_neg, add_neg_cancel_right]
      exact ha
    have hy' : P[β] y ∈ unSpace D ρ C (a + castW (Nat.card Kˣ) β) := by
      refine mem_unSpace_of_rootOp_eq_zero (D := D) (ρ := ρ)
        (a := a + castW (Nat.card Kˣ) β) (γ := -β) hN hCw hC hform h12 hmem hβ.neg
        hmem' hPy ?_
      simpa using hQ
    exact Submodule.mem_iSup_of_mem (a + castW (Nat.card Kˣ) β)
      (Submodule.mem_iSup_of_mem hmem hy')
  · have hzero : P[β] y = 0 := by
      refine rootOp_apply_eq_zero hCw hβ hya ?_
      simpa using hmem
    rw [hzero]
    exact Submodule.zero_mem _

private theorem unSpace_iSup_le_comap_rootOp_two (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {β : Fin 4 → ℤ} (hβ : IsD4Root β) :
    (⨆ a ∈ C, unSpace D ρ C a) ≤
      Submodule.comap (Q[β]) (⨆ a ∈ C, unSpace D ρ C a) := by
  refine iSup_le fun a => iSup_le fun ha => ?_
  intro y hy
  have hya : y ∈ D.wtSpace ρ a := (mem_unSpace.mp hy).1
  change Q[β] y ∈ ⨆ a ∈ C, unSpace D ρ C a
  by_cases hmem : a - castW (Nat.card Kˣ) β ∈ C
  · have hmem' : a + castW (Nat.card Kˣ) (-β) ∈ C := by
      rw [castW_neg]
      simpa [sub_eq_add_neg] using hmem
    have hzero : Q[β] y = 0 := by
      have h := (mem_unSpace.mp hy).2 (-β) hβ.neg hmem'
      simpa using h
    rw [hzero]
    exact Submodule.zero_mem _
  · have hzero : Q[β] y = 0 := by
      refine rootOp_apply_eq_zero hCw hβ hya ?_
      have hw : a + ((2 : ℕ) : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) β =
          a - castW (Nat.card Kˣ) β := by
        rw [two_natCast_eq_neg_one hN, neg_one_smul, sub_eq_add_neg]
      rw [hw]
      exact hmem
    rw [hzero]
    exact Submodule.zero_mem _

theorem unSpace_invariant (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0) :
    ∀ g : G, ∀ x ∈ ⨆ a ∈ C, unSpace D ρ C a, ρ g x ∈ ⨆ a ∈ C, unSpace D ρ C a := by
  refine forall_mem_of_rootElt D ρ ?_
  intro β hβ c x hx
  have hPx := unSpace_iSup_le_comap_rootOp_one hN hCw hC hform h12 h21 hβ hx
  have hQx := unSpace_iSup_le_comap_rootOp_two hN hCw hβ hx
  rw [hform β hβ c]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact Submodule.add_mem _ (Submodule.add_mem _ hx (Submodule.smul_mem _ c hPx))
    (Submodule.smul_mem _ (c ^ 2) hQx)

private theorem rootOp_one_eq_zero_of_unSpace_eq_bot (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0)
    (hbot : (⨆ a ∈ C, unSpace D ρ C a) = ⊥) :
    ∀ α, IsD4Root α → P[α] = 0 := by
  have hun_bot : ∀ a ∈ C, unSpace D ρ C a = ⊥ := by
    intro a ha
    have h : unSpace D ρ C a ≤ ⨆ a ∈ C, unSpace D ρ C a := fun y hy =>
      Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha hy)
    rw [hbot] at h
    exact le_bot_iff.mp h
  intro β hβ
  refine ext_of_wtSpace hCw fun a ha x hx => ?_
  by_cases hmem : a + castW (Nat.card Kˣ) β ∈ C
  · have hPx : P[β] x ∈ D.wtSpace ρ (a + castW (Nat.card Kˣ) β) :=
      rootOp_one_mem_wtSpace hβ hx
    have hy : P[(-β)] (P[β] x) ∈ D.wtSpace ρ a := by
      have h := rootOp_one_neg_mem_wtSpace hβ hPx
      rwa [add_sub_cancel_right] at h
    have hQy : Q[(-β)] (P[(-β)] (P[β] x)) = 0 := by
      have h := congrArg (fun f : Module.End K X => f (P[β] x)) (h21 (-β) hβ.neg)
      simpa [Module.End.mul_apply] using h
    have hyun : P[(-β)] (P[β] x) ∈ unSpace D ρ C a :=
      mem_unSpace_of_rootOp_eq_zero hN hCw hC hform h12 ha hβ hmem hy hQy
    have hy0 : P[(-β)] (P[β] x) = 0 := by
      rw [hun_bot a ha] at hyun
      exact (Submodule.mem_bot K).mp hyun
    have hD1 := rootOp_one_two_eq hN hCw hC hform h21 hβ ha hmem hx
    have hxeq : Q[β] (Q[(-β)] x) = x := by
      rw [hy0, zero_add] at hD1
      exact hD1
    calc P[β] x = P[β] (Q[β] (Q[(-β)] x)) := by rw [hxeq]
      _ = 0 := by
        have h := congrArg (fun f : Module.End K X => f (Q[(-β)] x)) (h12 β hβ)
        simpa [Module.End.mul_apply] using h
  · have hzero : P[β] x = 0 := by
      refine rootOp_apply_eq_zero hCw hβ hx ?_
      simpa using hmem
    exact hzero

private theorem rootOp_two_eq_zero_of_unSpace_eq_top (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (htop : (⨆ a ∈ C, unSpace D ρ C a) = ⊤) :
    ∀ α, IsD4Root α → Q[α] = 0 := by
  intro β hβ
  refine ext_of_wtSpace hCw fun a ha x hx => ?_
  have hxS : x ∈ ⨆ a ∈ C, unSpace D ρ C a := by
    rw [htop]
    exact Submodule.mem_top
  have hmap : (⨆ a ∈ C, unSpace D ρ C a) ≤
      Submodule.comap (wtProj D ρ a) (unSpace D ρ C a) := by
    refine iSup_le fun b => iSup_le fun hb => ?_
    intro y hy
    have hyb : y ∈ D.wtSpace ρ b := (mem_unSpace.mp hy).1
    have h := wtProj_of_mem D ρ (a := a) hyb
    change wtProj D ρ a y ∈ unSpace D ρ C a
    by_cases hab : a = b
    · rwa [h, if_pos hab, hab]
    · rw [h, if_neg hab]
      exact Submodule.zero_mem _
  have hxun : x ∈ unSpace D ρ C a := by
    have h := hmap hxS
    change wtProj D ρ a x ∈ unSpace D ρ C a at h
    rwa [wtProj_of_mem D ρ hx, if_pos rfl] at h
  by_cases hmem : a - castW (Nat.card Kˣ) β ∈ C
  · have hmem' : a + castW (Nat.card Kˣ) (-β) ∈ C := by
      rw [castW_neg]
      simpa [sub_eq_add_neg] using hmem
    have h := (mem_unSpace.mp hxun).2 (-β) hβ.neg hmem'
    simpa using h
  · exact eq_zero_of_mem_wtSpace_of_not_mem hCw hmem (rootOp_two_mem_wtSpace hN hβ hx)

theorem rootOp_two_eq_zero_or_rootOp_one_eq_zero (hN : Nat.card Kˣ = 3)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) 1 C)
    (hform : ∀ α, IsD4Root α → ∀ c : K,
      ρ (D.x α c) = 1 + c • P[α] + c ^ 2 • Q[α])
    (h12 : ∀ α, IsD4Root α → P[α] * Q[α] = 0)
    (h21 : ∀ α, IsD4Root α → Q[α] * P[α] = 0)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) :
    (∀ α, IsD4Root α → Q[α] = 0) ∨ (∀ α, IsD4Root α → P[α] = 0) := by
  rcases hirr (⨆ a ∈ C, unSpace D ρ C a) (unSpace_invariant hN hCw hC hform h12 h21) with
    hbot | htop
  · exact Or.inr (rootOp_one_eq_zero_of_unSpace_eq_bot hN hCw hC hform h12 h21 hbot)
  · exact Or.inl (rootOp_two_eq_zero_of_unSpace_eq_top hN hCw htop)

end CFSG.LieType.D4Small.D4Datum

end
