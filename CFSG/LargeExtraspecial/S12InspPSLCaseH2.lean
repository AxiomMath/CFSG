module

public import CFSG.LargeExtraspecial.S12InspPSLCaseH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem psl_finrank_le_finrank_inf_ker_add_one (U : Submodule (ZMod 2) S.Qt)
    (f : S.Qt →ₗ[ZMod 2] ZMod 2) :
    finrank (ZMod 2) U ≤ finrank (ZMod 2) ↥(U ⊓ LinearMap.ker f) + 1 := by
  have h1 := finrank_sup_add_finrank_inf_eq U (LinearMap.ker f)
  have h2 := Submodule.finrank_le (U ⊔ LinearMap.ker f)
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  have h4 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  omega

theorem psl_card_Lbar_mul_card_clSub {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.Lbar g) * (2 * Nat.card (S.clSub (S.QG ⊓ S.Qa g))) = 2 ^ (2 * S.width) := by
  have h1 := S.card_Lbar_mul g
  rw [S.card_L0 haQ hne] at h1
  have hz : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl haQ hne⟩
  have h2 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
  rw [S.clPre_clSub inf_le_left hz] at h2
  rw [← h2]
  exact h1

theorem psl_card_Lbar_le_two_mul {g : G} (hidx : (S.Xbar12 g).relIndex S.Mbar ≤ 2) :
    Nat.card (S.Lbar g) ≤ 2 * Nat.card ↥(S.Xbar12 g ⊓ S.Lbar g) := by
  have h1 := s12_card_mul_relIndex_of_le (inf_le_right : S.Xbar12 g ⊓ S.Lbar g ≤ S.Lbar g)
  rw [Subgroup.inf_relIndex_right] at h1
  have hr0 : (S.Xbar12 g).relIndex S.Mbar ≠ 0 := by
    intro h
    have h2 := s12_card_mul_relIndex_of_le (Xbar12_le_Mbar (S := S) (g := g))
    rw [h, mul_zero] at h2
    exact (Nat.card_pos (α := S.Mbar)).ne' h2.symm
  have h3 := Subgroup.relIndex_le_of_le_right (S.Lbar_le_Mbar g) hr0
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ (h3.trans hidx)

theorem psl_card_le_two_of_subset {K : Subgroup S.O} {t : S.O} (h : ∀ x ∈ K, x = 1 ∨ x = t) :
    Nat.card K ≤ 2 := by
  have hsub : (K : Set S.O) ⊆ {1, t} := fun x hx => by
    rcases h x hx with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  calc Nat.card K = Nat.card (K : Set S.O) := rfl
    _ ≤ Nat.card ({1, t} : Set S.O) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

theorem sub_mem_H {e : S.Qt} (he : e ∈ P.W) (he1 : polar S.q e P.c' = 1) {w : S.Qt}
    (hw : w ∈ P.W) : w - polar S.q w P.c' • e ∈ P.H := by
  refine ⟨P.W.sub_mem hw (P.W.smul_mem _ he), ?_⟩
  change polar S.q P.c' (w - polar S.q w P.c' • e) = 0
  rw [polar_sub_right, polar_smul_right, polar_comm S.q P.c' e, he1, polar_comm S.q P.c' w,
    smul_eq_mul, mul_one, sub_self]

theorem exists_mixed (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g)
    (hℓX : ℓ ∈ S.Xbar12 g) (hℓ1 : ℓ ≠ 1) (hℓt : ℓ ≠ t) {e : S.Qt} (he : e ∈ P.W)
    (he1 : polar S.q e P.c' = 1) :
    (∃ h₁ ∈ P.H, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) h₁ = h₁ + P.c) ∧
      (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e ∉ span (ZMod 2) {P.c} := by
  have hH := P.comm_H_le haQ hne hn ha hℓ hℓX
  constructor
  · by_contra hcon
    push Not at hcon
    rcases P.eq_one_or_eq_of_fix_H haQ hne htA htX ha hℓ hℓX (fun h hh => by
        have h2 := hH h hh
        rw [mem_span_singleton_iff] at h2
        rcases h2 with h2 | h2
        · exact sub_eq_zero.mp h2
        · exact absurd (by rw [← h2, add_sub_cancel]) (hcon h hh)) with h | h
    · exact hℓ1 h
    · exact hℓt h
  · intro hspan
    rcases P.eq_one_or_eq_of_comm_le haQ hne htA htX ha hℓ hℓX (fun w hw => by
        have h1 := hH _ (P.sub_mem_H he he1 hw)
        have e1 : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
            ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (w - polar S.q w P.c' • e) - (w - polar S.q w P.c' • e)) +
              polar S.q w P.c' • ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e) := by
          rw [map_sub, map_smul, smul_sub]
          abel
        rw [e1]
        exact add_mem h1 (smul_mem _ _ hspan)) with h | h
    · exact hℓ1 h
    · exact hℓt h

end PSLPair

end Setting

end CFSG.LargeExtraspecial
