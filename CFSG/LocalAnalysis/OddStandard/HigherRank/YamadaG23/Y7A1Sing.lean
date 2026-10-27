module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Cfg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

theorem y7a_triv_of_sing (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxz : x * z * x⁻¹ = z)
    (hsing : ∀ a ∈ A, a * a = 1 → a⁻¹ * (x * a * x⁻¹) ∈ zpowers z) :
    ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ zpowers z := by
  have hzA : ∀ y ∈ A, y * z = z * y := by
    intro y hy
    rw [h.cfg.hA] at hy
    exact y6q8_z_central h.cfg.rel y hy
  have hzpow : ∀ w ∈ zpowers z, ∀ y ∈ A, w * y = y * w := by
    intro w hw y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (show Commute z y from (hzA y hy).symm) k).eq
  let S : Subgroup G :=
    { carrier := {a : G | a ∈ A ∧ a⁻¹ * (x * a * x⁻¹) ∈ zpowers z}
      one_mem' := ⟨A.one_mem, by simpa using Subgroup.one_mem (zpowers z)⟩
      mul_mem' := by
        rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
        refine ⟨A.mul_mem ha hb, ?_⟩
        have hcommb : b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * b = a⁻¹ * (x * a * x⁻¹) := by
          calc b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * b
              = b⁻¹ * ((a⁻¹ * (x * a * x⁻¹)) * b) := by group
            _ = b⁻¹ * (b * (a⁻¹ * (x * a * x⁻¹))) := by
                  rw [hzpow (a⁻¹ * (x * a * x⁻¹)) hza b hb]
            _ = a⁻¹ * (x * a * x⁻¹) := by group
        have hEq : (a * b)⁻¹ * (x * (a * b) * x⁻¹)
            = (a⁻¹ * (x * a * x⁻¹)) * (b⁻¹ * (x * b * x⁻¹)) := by
          calc (a * b)⁻¹ * (x * (a * b) * x⁻¹)
              = b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
            _ = b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) *
                  (b * (b⁻¹ * (x * b * x⁻¹))) := by group
            _ = (b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * b) *
                  (b⁻¹ * (x * b * x⁻¹)) := by group
            _ = (a⁻¹ * (x * a * x⁻¹)) * (b⁻¹ * (x * b * x⁻¹)) := by rw [hcommb]
        rw [hEq]
        exact Subgroup.mul_mem _ hza hzb
      inv_mem' := by
        rintro a ⟨ha, hza⟩
        refine ⟨A.inv_mem ha, ?_⟩
        rw [inv_inv]
        have hcomm := hzpow (a⁻¹ * (x * a * x⁻¹))⁻¹ (Subgroup.inv_mem _ hza) a ha
        have hEq : a * (x * a⁻¹ * x⁻¹) = (a⁻¹ * (x * a * x⁻¹))⁻¹ := by
          calc a * (x * a⁻¹ * x⁻¹)
              = a * (x * a * x⁻¹)⁻¹ := by group
            _ = a * (a * (a⁻¹ * (x * a * x⁻¹)))⁻¹ := by group
            _ = a * ((a⁻¹ * (x * a * x⁻¹))⁻¹ * a⁻¹) := by group
            _ = (a * (a⁻¹ * (x * a * x⁻¹))⁻¹) * a⁻¹ := by group
            _ = ((a⁻¹ * (x * a * x⁻¹))⁻¹ * a) * a⁻¹ := by rw [hcomm]
            _ = (a⁻¹ * (x * a * x⁻¹))⁻¹ := by group
        rw [hEq]
        exact Subgroup.inv_mem _ hza }
  have hgen := y6q8_gen_sq1 h.cfg.rel h.cfg.z_ne (by rw [← h.cfg.hA]; exact h.cfg.card_A)
  have hcl : closure {a : G | a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) ∧ a ^ 2 = 1} ≤ S := by
    rw [Subgroup.closure_le]
    intro a ha
    refine ⟨?_, ?_⟩
    · rw [h.cfg.hA]; exact ha.1
    · rw [← h.cfg.hA] at ha
      exact hsing a ha.1 (by simpa [pow_two] using ha.2)
  intro a ha
  have ha' : a ∈ closure {a : G | a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) ∧ a ^ 2 = 1} := by
    rw [hgen, ← h.cfg.hA]; exact ha
  exact (hcl ha').2

end CFSG.OddStandard.HigherRank.YamadaG23
