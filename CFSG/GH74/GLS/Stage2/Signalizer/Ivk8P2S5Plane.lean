module

public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

section Plane

variable {G : Type} [Group G] [Finite G]

theorem exists_plane_fixing {p : ℕ} (hp : p.Prime) {E₃ X : Subgroup G}
    (hE : IsElementaryAbelian p ↥E₃) (hcard : Nat.card ↥E₃ = p ^ 3)
    (hn : E₃ ≤ normalizer (X : Set G)) (hcop : ¬ p ∣ Nat.card ↥X) (hX : X ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ E₃ ∧ Nat.card ↥D = p ^ 2 ∧
      ∃ x ∈ X, x ≠ 1 ∧ x ∈ centralizer (D : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p ↥E₃ := hE
  have hnt : Nontrivial ↥E₃ := by
    have h1 : 1 < Nat.card ↥E₃ := by
      rw [hcard]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  let _ : MulDistribMulAction ↥E₃ ↥X := MulDistribMulAction.compHom ↥X (Subgroup.inclusion hn)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥E₃) (H := ↥X) hcop
  have hXnt : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hX
  have hex : ∃ B : Subgroup ↥E₃, B.index = p ∧ fixedPointSubgroup ↥B ↥X ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have hbot : (⨆ (B : Subgroup ↥E₃) (_ : B.index = p), fixedPointSubgroup ↥B ↥X) = ⊥ :=
      le_bot_iff.1 (iSup₂_le fun B hB => (hall B hB).le)
    rw [hbot] at hgen
    exact bot_ne_top hgen
  obtain ⟨B, hBidx, hBne⟩ := hex
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  have hfix : ∀ b ∈ B, b • (a : ↥X) = (a : ↥X) := fun b hb => a.2 ⟨b, hb⟩
  refine ⟨B.map E₃.subtype, Subgroup.map_subtype_le B, ?_, ((a : ↥X) : G), (a : ↥X).2, ?_, ?_⟩
  · have h1 := B.card_mul_index
    rw [hBidx, hcard] at h1
    rw [Subgroup.card_map_of_injective E₃.subtype_injective]
    have h2 : Nat.card ↥B * p = p ^ 2 * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  · intro h1
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hbx := congrArg Subtype.val (hfix b hb)
    have hbx' : ((b : ↥E₃) : G) * ((a : ↥X) : G) * ((b : ↥E₃) : G)⁻¹ = ((a : ↥X) : G) := hbx
    calc ((b : ↥E₃) : G) * ((a : ↥X) : G) = ((b : ↥E₃) : G) * ((a : ↥X) : G) *
          ((b : ↥E₃) : G)⁻¹ * ((b : ↥E₃) : G) := by group
      _ = ((a : ↥X) : G) * ((b : ↥E₃) : G) := by rw [hbx']

end Plane

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
