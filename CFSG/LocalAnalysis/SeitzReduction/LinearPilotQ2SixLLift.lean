module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (oddCoreLift HasBLift)

section Commutator

variable {G : Type*} [Group G]

theorem commutator_le_centralizer_of_commutatorElement_mem {A Z M : Subgroup G} {x : G}
    (hxA : x ∈ A) (hMA : M ≤ A) (hAZ : A ≤ centralizer (Z : Set G))
    (hMZ : ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ Z) : ⁅M, M⁆ ≤ centralizer ({x} : Set G) := by
  have hfA : ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ A := fun m hm =>
    A.mul_mem (A.mul_mem (A.mul_mem (hMA hm) hxA) (A.inv_mem (hMA hm))) (A.inv_mem hxA)
  have hcomm : ∀ a ∈ A, ∀ z ∈ Z, z * a = a * z := fun a ha z hz =>
    mem_centralizer_iff.1 (hAZ ha) z hz
  let φ : M →* G :=
    { toFun := fun m => (m : G) * x * (m : G)⁻¹ * x⁻¹
      map_one' := by simp
      map_mul' := by
        rintro ⟨m, hm⟩ ⟨m', hm'⟩
        simp only [Subgroup.coe_mul]
        have h1 := hcomm m (hMA hm) _ (hMZ m' hm')
        have h2 := hcomm _ (hfA m hm) _ (hMZ m' hm')
        calc m * m' * x * (m * m')⁻¹ * x⁻¹
            = m * (m' * x * m'⁻¹ * x⁻¹) * m⁻¹ * (m * x * m⁻¹ * x⁻¹) := by group
          _ = (m' * x * m'⁻¹ * x⁻¹) * (m * x * m⁻¹ * x⁻¹) := by rw [← h1]; group
          _ = (m * x * m⁻¹ * x⁻¹) * (m' * x * m'⁻¹ * x⁻¹) := h2 }
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have hφ : φ ⁅(⟨g₁, h₁⟩ : M), ⟨g₂, h₂⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (hcomm _ (hfA g₁ h₁) _ (hMZ g₂ h₂)).symm
  have hφ' : ⁅g₁, g₂⁆ * x * ⁅g₁, g₂⁆⁻¹ * x⁻¹ = 1 := hφ
  rw [mem_centralizer_singleton_iff]
  have h3 : ⁅g₁, g₂⁆ * x * ⁅g₁, g₂⁆⁻¹ = x := by
    calc ⁅g₁, g₂⁆ * x * ⁅g₁, g₂⁆⁻¹ = ⁅g₁, g₂⁆ * x * ⁅g₁, g₂⁆⁻¹ * x⁻¹ * x := by group
      _ = x := by rw [hφ', one_mul]
  calc ⁅g₁, g₂⁆ * x = ⁅g₁, g₂⁆ * x * ⁅g₁, g₂⁆⁻¹ * ⁅g₁, g₂⁆ := by group
    _ = x * ⁅g₁, g₂⁆ := by rw [h3]

end Commutator

section Coprime

variable {H : Type*} [Group H] [Finite H]

theorem exists_perfect_le_centralizer_map_eq_of_coprime (p : ℕ) [Fact p.Prime] (W : Subgroup H)
    [W.Normal] (hW : ¬ p ∣ Nat.card W) {X : Subgroup H} (hX : IsPGroup p X)
    {Pb : Subgroup (H ⧸ W)} (hPb : ⁅Pb, Pb⁆ = Pb)
    (hPbX : Pb ≤ centralizer ((X.map (QuotientGroup.mk' W) : Subgroup (H ⧸ W)) : Set (H ⧸ W))) :
    ∃ P : Subgroup H, P ≤ centralizer (X : Set H) ∧ ⁅P, P⁆ = P ∧
      P.map (QuotientGroup.mk' W) = Pb := by
  have hmapC := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p W hW X hX
  set Q : Subgroup H := centralizer (X : Set H) ⊓ Pb.comap (QuotientGroup.mk' W) with hQ
  have hQmap : Q.map (QuotientGroup.mk' W) = Pb := by
    refine le_antisymm ((map_mono inf_le_right).trans (map_comap_le _ _)) fun y hy => ?_
    have hy' : y ∈ (centralizer (X : Set H)).map (QuotientGroup.mk' W) := by
      rw [hmapC]
      exact hPbX hy
    obtain ⟨z, hz, rfl⟩ := hy'
    exact ⟨z, mem_inf.2 ⟨hz, hy⟩, rfl⟩
  refine ⟨perfectCore Q, (CFSG.Quasithin.perfectCore_le Q).trans inf_le_left,
    CFSG.Quasithin.perfectCore_perfect Q, ?_⟩
  rw [CFSG.Quasithin.map_perfectCore, hQmap, CFSG.Quasithin.perfectCore_eq_self_of_perfect hPb]

theorem exists_perfect_le_centralizer_map_map_eq_of_hasBLift (p : ℕ) [Fact p.Prime]
    (W : Subgroup H) [W.Normal] (hW : ¬ p ∣ Nat.card W) {X : Subgroup H} (hX : IsPGroup p X)
    {Kc : Subgroup ((H ⧸ W) ⧸ oddCore (H ⧸ W))} (hKp : ⁅Kc, Kc⁆ = Kc) (hB : HasBLift Kc)
    (hXK : X.map (QuotientGroup.mk' W) ≤ oddCoreLift Kc)
    {S : Subgroup ((H ⧸ W) ⧸ oddCore (H ⧸ W))} (hSp : ⁅S, S⁆ = S) (hSK : S ≤ Kc)
    (hSX : S ≤ centralizer (((X.map (QuotientGroup.mk' W)).map
      (QuotientGroup.mk' (oddCore (H ⧸ W))) : Subgroup ((H ⧸ W) ⧸ oddCore (H ⧸ W))) :
        Set ((H ⧸ W) ⧸ oddCore (H ⧸ W)))) :
    ∃ P : Subgroup H, P ≤ centralizer (X : Set H) ∧ ⁅P, P⁆ = P ∧
      (P.map (QuotientGroup.mk' W)).map (QuotientGroup.mk' (oddCore (H ⧸ W))) = S := by
  set π₂ := QuotientGroup.mk' (oddCore (H ⧸ W)) with hπ₂
  set M : Subgroup (H ⧸ W) := S.comap π₂ ⊓ oddCoreLift Kc with hM
  have hMmap : M.map π₂ = S := by
    refine le_antisymm ((map_mono inf_le_left).trans (map_comap_le _ _)) fun y hy => ?_
    have hy' : y ∈ (oddCoreLift Kc).map π₂ := by
      rw [F4Pilot.map_oddCoreLift hKp]
      exact hSK hy
    obtain ⟨k, hk, rfl⟩ := hy'
    exact ⟨k, mem_inf.2 ⟨hy, hk⟩, rfl⟩
  have hMC : ⁅M, M⁆ ≤
      centralizer ((X.map (QuotientGroup.mk' W) : Subgroup (H ⧸ W)) : Set (H ⧸ W)) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro x hx
    have hMZ : ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ oddCore (H ⧸ W) := by
      intro m hm
      have hcomm : π₂ x * π₂ m = π₂ m * π₂ x :=
        mem_centralizer_iff.1 (hSX (mem_inf.1 hm).1) (π₂ x) ⟨x, hx, rfl⟩
      have h1 : π₂ (m * x * m⁻¹ * x⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      rwa [hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h := commutator_le_centralizer_of_commutatorElement_mem (hXK hx) inf_le_right hB hMZ hg
    exact (mem_centralizer_singleton_iff.1 h).symm
  have hPbX : perfectCore M ≤
      centralizer ((X.map (QuotientGroup.mk' W) : Subgroup (H ⧸ W)) : Set (H ⧸ W)) := by
    refine le_trans ?_ hMC
    rw [← CFSG.Quasithin.perfectCore_perfect M]
    exact Subgroup.commutator_mono (CFSG.Quasithin.perfectCore_le M)
      (CFSG.Quasithin.perfectCore_le M)
  obtain ⟨P, hPX, hPp, hPmap⟩ := exists_perfect_le_centralizer_map_eq_of_coprime p W hW hX
    (CFSG.Quasithin.perfectCore_perfect M) hPbX
  refine ⟨P, hPX, hPp, ?_⟩
  rw [hPmap, CFSG.Quasithin.map_perfectCore, hMmap,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hSp]

end Coprime

end CFSG.SeitzReduction.LinearPilot
