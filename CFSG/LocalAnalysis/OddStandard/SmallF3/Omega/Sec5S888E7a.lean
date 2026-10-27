module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E5b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

theorem eq_of_card_le [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hC : ∀ y ∈ normalizer (V : Set X), y * y = 1 → y ∈ centralizer (V : Set X) → y ∈ V)
    {E : Subgroup X} (hE : E ≤ normalizer (V : Set X)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEs : ∀ a ∈ E, a * a = 1) (hcard : 2 ^ 8 ≤ Nat.card E) : E = V := by
  classical
  let H := planeImage hS E
  let C := suppSet hS E
  let E₀ := E ⊓ centralizer (V : Set X)
  have hE' : ActsElemAb V E := ActsElemAb.of_exact hE hEc hEs
  have hord : Nat.card E = H.card * C.card * Nat.card E₀ :=
    card_eq_planeImage_mul hS hE'
  have hE₀V : E₀ ≤ V := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    exact hC y (hE hy.1) (hEs y hy.1) hy.2
  have hE₀bound : Nat.card E₀ ≤ fixedBound H C := by
    let f : E₀ → {v : V // ∀ y' ∈ E, y' * (v : X) * y'⁻¹ = v} := fun y =>
      ⟨⟨(y : X), hE₀V y.2⟩, fun y' hy' => by
        show (y' : X) * (y : X) * (y' : X)⁻¹ = (y : X)
        rw [hEc (y' : X) hy' (y : X) y.2.1]
        group⟩
    have hinj : Function.Injective f := by
      intro y z hyz
      exact Subtype.ext (congrArg
        (fun t : {v : V // ∀ y' ∈ E, y' * (v : X) * y'⁻¹ = v} => ((t : V) : X)) hyz)
    calc Nat.card E₀ ≤ Nat.card {v : V // ∀ y' ∈ E, y' * (v : X) * y'⁻¹ = v} :=
          Nat.card_le_card_of_injective f hinj
      _ ≤ fixedBound H C := card_fixed_le hS hE'
  obtain ⟨hH1, hmul, hsq⟩ := planeImage_group hS hE'
  obtain ⟨hC0, hadd⟩ := suppSet_subspace hS hE'
  have htab : H.card * C.card * fixedBound H C ≤ 2 ^ 7 ∨ (H.card = 1 ∧ C.card = 1) :=
    table71 hH1 hmul hsq hC0 hadd (suppSet_even hS hpar hE') (suppSet_fixed hS hE')
  rcases htab with htab | ⟨hH1', hC1'⟩
  ·
    exfalso
    have hle : Nat.card E ≤ 2 ^ 7 := by
      rw [hord]
      exact le_trans (Nat.mul_le_mul_left (H.card * C.card) hE₀bound) htab
    exact absurd hle (not_le_of_gt (lt_of_lt_of_le (by norm_num) hcard))
  ·
    have hcardE : Nat.card E = Nat.card E₀ := by
      rw [hord, hH1', hC1']
      ring
    have hEeq : E₀ = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcardE)
    have hEV : E ≤ V := by rw [← hEeq]; exact hE₀V
    have hVE : Nat.card V ≤ Nat.card E := by rw [hS.card_D]; exact hcard
    exact Subgroup.eq_of_le_of_card_ge hEV hVE

end CFSG.OddStandard.SmallF3.Omega
