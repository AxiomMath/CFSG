module

public import CFSG.ClassicalInvolution.Asc77.AscC25H3
public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25V30

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem eq_one_or_eq_z_of_mem_S (h11 : C25_11 p f)
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hs : s ∈ Triv hp hq e z t' h.ht'2) : s = 1 ∨ s = z := by
  obtain ⟨hsN, -, hsN', hsν, hsν'⟩ := hs
  have hc1 := commutes_R_of_nuG_eq_one h hp hq e hsS hsN hsν
  have hS2 : t' * s * t' ∈ (S : Subgroup G) := S.mul_mem (S.mul_mem h.ht'S hsS) h.ht'S
  have hc2 := commutes_R_of_nuG_eq_one h hp hq e hS2 hsN' hsν'
  have hcent : s ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : R ⊔ R' ≤ Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc1 r hr).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hr' : r ∈ conjSub t' R := by
          rw [h.ht'R]
          exact hr
        have hr0 : t' * r * t' ∈ R := by
          have := mem_conjSub_iff.mp hr'
          rwa [h.ht'inv] at this
        have e3 := hc2 (t' * r * t') hr0
        have e4 : t' * (s * r) * t' = t' * (r * s) * t' := by
          calc t' * (s * r) * t' = t' * s * t' * (t' * r * t') := by
                calc t' * (s * r) * t' = t' * s * (t' * t') * r * t' := by rw [h.ht'2]; group
                  _ = t' * s * t' * (t' * r * t') := by group
            _ = t' * r * t' * (t' * s * t') := e3
            _ = t' * (r * s) * t' := by
                calc t' * r * t' * (t' * s * t') = t' * r * (t' * t') * s * t' := by group
                  _ = t' * (r * s) * t' := by rw [h.ht'2]; group
        exact (mul_left_cancel (mul_right_cancel e4)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hmem : s ∈ Subgroup.zpowers z := by
    rw [← h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp]
    exact Subgroup.mem_inf.mpr ⟨hsS, hcent⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact zpow_eq_one_or_self h.hz.sq j

theorem eq_one_or_eq_z_of_triv (h11 : C25_11 p f)
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {y : G}
    (hy : y ∈ Triv hp hq e z t' h.ht'2) {i : ℕ} (hord : orderOf y = 2 ^ i) : y = 1 ∨ y = z := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (h.hyp.hzS s hs)
  have hyC : y ∈ C := (hmemC y).mpr hy.2.1
  obtain ⟨c, hcC, hcS⟩ := C25V.exists_conj_mem_sylow S hSC hyC hord
  have hcz : c * z = z * c := (hmemC c).mp hcC
  have hy1 := triv_conj_mem h hp hq e hcz hy
  rcases eq_one_or_eq_z_of_mem_S h11 h hp hq e hcS hy1 with h1 | h1
  · left
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  · right
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [h1]
      _ = c⁻¹ * (z * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
