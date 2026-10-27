module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldNoAbel
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2CardGroup

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem commute_chainProd (A : ℤ → Subgroup X) (g : X) :
    ∀ l : List ℤ, (∀ k ∈ l, ∀ x ∈ A k, g * x = x * g) → ∀ u ∈ chainProd A l, g * u = u * g
  | [], _, u, hu => by
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hu
    rw [hu, mul_one, one_mul]
  | k :: l, hA, u, hu => by
    rw [chainProd_cons] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hu
    have h1 := hA k List.mem_cons_self a ha
    have h2 := commute_chainProd A g l (fun k' hk' => hA k' (List.mem_cons_of_mem _ hk')) b hb
    calc g * (a * b) = (g * a) * b := by rw [mul_assoc]
      _ = (a * g) * b := by rw [h1]
      _ = a * (g * b) := by rw [mul_assoc]
      _ = a * (b * g) := by rw [h2]
      _ = a * b * g := by rw [mul_assoc]

namespace FoldData

variable {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem card_fixed [Finite X] (hf : FoldData R φ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    (hC : ∀ t ∈ H ⊓ foldFix φ, (∀ u ∈ U ⊓ foldFix φ, t * u = u * t) → t = 1) {q : ℕ}
    (hroot : ∀ k : ℤ, IsRoot 3 k → Nat.card ↥(foldRoot φ root k) = q)
    (hU : Nat.card ↥(U ⊓ foldFix φ) = q ^ 3) :
    Nat.card ↥(foldFix φ) =
      Nat.card ↥(H ⊓ foldFix φ) * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := hf.exists_rgd2
  have hr₁ : r₁' ∈ foldFix φ := h1
  have hr₂ : r₂' ∈ foldFix φ := h2
  have hrootle : ∀ i, IsRoot 3 i → foldRoot φ root i ≤ foldFix φ := fun i _ => inf_le_right
  have hgen'' := R'.restrict_gen (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hrootle
    (fun x hx => hf.generation hgen hZ hz h1 h1H h2 h2H hx)
  have R'' := R'.restrict (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hrootle
  have hZ'' : ∀ g ∈ (H ⊓ foldFix φ).subgroupOf (foldFix φ),
      (∀ i, IsRoot 3 i → ∀ x ∈ (foldRoot φ root i).subgroupOf (foldFix φ), g * x = x * g) →
        g = 1 := by
    intro g hg hcomm
    apply Subtype.ext
    refine hC g.1 ⟨(Subgroup.mem_subgroupOf.1 hg).1, g.2⟩ fun u hu => ?_
    have hu' : u ∈ chainProd (foldRoot φ root) (intList 1 ((3 : ℕ) : ℤ)) := by
      rw [← R'.carrier_eq]; exact hu
    refine commute_chainProd (foldRoot φ root) g.1 _ (fun k hk x hx => ?_) u hu'
    have hk' := mem_intList_iff.1 hk
    have := hcomm k (isRoot_of_pos_le hk'.1 hk'.2) ⟨x, hx.2⟩ hx
    exact congrArg Subtype.val this
  have hroot'' : ∀ k : ℤ, IsRoot 3 k →
      Nat.card ↥((foldRoot φ root k).subgroupOf (foldFix φ)) = q := fun k hk =>
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hrootle k hk)).toEquiv).trans (hroot k hk)
  have hU'' : Nat.card ↥((U ⊓ foldFix φ).subgroupOf (foldFix φ)) = q ^ 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ foldFix φ ≤ foldFix φ)).toEquiv).trans hU
  have := R''.card_eq hgen'' hZ'' hroot'' hU''
  rw [this]
  congr 2
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ foldFix φ ≤ foldFix φ)).toEquiv

end FoldData

end CFSG.GH74.GLS.SP
