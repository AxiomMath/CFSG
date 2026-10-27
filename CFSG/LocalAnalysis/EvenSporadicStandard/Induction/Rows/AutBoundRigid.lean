module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

public section

universe u v

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup MulAction

theorem card_le_prod_of_rigid {X : Type v} : ∀ (k : ℕ) (H : Type u) [Group H] [Finite H]
    [MulAction H X] (b : ℕ → X) (S : ℕ → Set X),
      (∀ g : H, (∀ j < k, g • b j = b j) → g = 1) →
      (∀ i < k, ∀ g : H, (∀ j < i, g • b j = b j) → g • b i ∈ S i) →
      (∀ i < k, (S i).Finite) →
      Nat.card H ≤ ∏ i ∈ Finset.range k, (S i).ncard := by
  intro k
  induction k with
  | zero =>
    intro H _ _ _ b S hrig _ _
    have : Subsingleton H := ⟨fun g h => (hrig g (by simp)).trans (hrig h (by simp)).symm⟩
    simp
  | succ k ih =>
    intro H _ _ _ b S hrig hS hfin
    let H' : Subgroup H := stabilizer H (b 0)
    have h1 : Nat.card H' ≤ ∏ i ∈ Finset.range k, (S (i + 1)).ncard := by
      refine ih H' (fun i => b (i + 1)) (fun i => S (i + 1)) ?_ ?_ ?_
      · intro g hg
        have h0 : (g : H) • b 0 = b 0 := g.2
        have hfix : ∀ j < k + 1, (g : H) • b j = b j := by
          intro j hj
          rcases j with _ | j
          · exact h0
          · exact hg j (by omega)
        exact Subtype.ext (hrig g hfix)
      · intro i hi g hg
        have h0 : (g : H) • b 0 = b 0 := g.2
        refine hS (i + 1) (by omega) g ?_
        intro j hj
        rcases j with _ | j
        · exact h0
        · exact hg j (by omega)
      · intro i hi
        exact hfin (i + 1) (by omega)
    have hS0 : (S 0).Finite := hfin 0 (by omega)
    have horb : Nat.card (orbit H (b 0)) ≤ (S 0).ncard := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_mono hS0 ?_
      rintro _ ⟨g, rfl⟩
      exact hS 0 (by omega) g (by simp)
    have hcard : Nat.card (orbit H (b 0)) * Nat.card H' = Nat.card H := by
      rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup H (b 0))]
    rw [Finset.prod_range_succ', mul_comm, ← hcard]
    exact Nat.mul_le_mul horb h1

theorem eq_one_of_fixes_generators {X : Type v} [Group X] {s : Set X}
    (hs : Subgroup.closure s = ⊤) (α : MulAut X) (h : ∀ x ∈ s, α x = x) : α = 1 := by
  have hle : Subgroup.closure s ≤ (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X)) :=
    (Subgroup.closure_le _).2 fun x hx => h x hx
  rw [hs] at hle
  exact MulEquiv.ext fun x => hle (Subgroup.mem_top x)

theorem card_mulAut_le_of_rigid {X : Type u} [Group X] [Finite X] (k : ℕ) (b : ℕ → X)
    (hgen : Subgroup.closure (b '' {j | j < k}) = ⊤) (S : ℕ → Set X)
    (hS : ∀ i < k, ∀ α : MulAut X, (∀ j < i, α (b j) = b j) → α (b i) ∈ S i)
    (hfin : ∀ i < k, (S i).Finite) :
    Nat.card (MulAut X) ≤ ∏ i ∈ Finset.range k, (S i).ncard := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => α.toEquiv) fun α β h => MulEquiv.ext fun x =>
      congrFun (congrArg DFunLike.coe h) x
  refine card_le_prod_of_rigid k (MulAut X) b S (fun α hα => ?_) (fun i hi α hα => ?_) hfin
  · refine eq_one_of_fixes_generators hgen α ?_
    rintro _ ⟨j, hj, rfl⟩
    exact hα j hj
  · simpa using hS i hi α (fun j hj => by simpa using hα j hj)

def conjClass {X : Type u} [Group X] (u : X) : Set X := {w | ∃ g : X, w = g * u * g⁻¹}

theorem mem_conjClass_iff {X : Type u} [Group X] {u w : X} :
    w ∈ conjClass u ↔ ∃ g : X, w = g * u * g⁻¹ := Iff.rfl

theorem image_conjClass {X : Type u} [Group X] (α : MulAut X) (u : X) :
    (α : X → X) '' conjClass u = conjClass (α u) := by
  ext w
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨α g, by simp⟩
  · rintro ⟨g, rfl⟩
    exact ⟨α.symm g * u * (α.symm g)⁻¹, ⟨α.symm g, rfl⟩, by simp⟩

theorem aut_preserves_class {X : Type u} [Group X] [Finite X] {u v : X} (α : MulAut X)
    (hfus : ∀ z : X, z * z = 1 → z ≠ 1 → (∃ g : X, g * z * g⁻¹ = u) ∨ ∃ g : X, g * z * g⁻¹ = v)
    (hcard : (conjClass u).ncard < (conjClass v).ncard) (hu : u * u = 1) (hu1 : u ≠ 1) :
    α u ∈ conjClass u := by
  have hsq : α u * α u = 1 := by rw [← map_mul, hu, map_one]
  have hne : α u ≠ 1 := fun h => hu1 (α.injective (by rw [h, map_one]))
  rcases hfus _ hsq hne with ⟨g, hg⟩ | ⟨g, hg⟩
  · refine ⟨g⁻¹, ?_⟩
    rw [inv_inv]
    calc α u = g⁻¹ * (g * α u * g⁻¹) * g := by group
      _ = g⁻¹ * u * g := by rw [hg]
  · exfalso
    have hcl : conjClass (α u) = conjClass v := by
      ext w
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨h * g⁻¹, by rw [← hg]; group⟩
      · rintro ⟨h, rfl⟩
        exact ⟨h * g, by rw [← hg]; group⟩
    have h1 := image_conjClass α u
    rw [hcl] at h1
    have h2 : ((α : X → X) '' conjClass u).ncard = (conjClass u).ncard :=
      Set.ncard_image_of_injective _ α.injective
    rw [h1] at h2
    omega

end CFSG.EvenSporadicStandard.Induction.AutBound
