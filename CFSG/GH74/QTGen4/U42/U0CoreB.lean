module

public import CFSG.GH74.QTGen4.U42.U0Core
public meta import CFSG.GH74.QTGen4.U42.U0Core
public meta import CFSG.Quasithin.H13.A5Setting
public meta import CFSG.Quasithin.Background.G2A5
public meta import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5 Subgroup
open scoped commutatorElement

theorem comm_inl_inr (u : W5) (σ : Equiv.Perm (Fin 5)) :
    ⁅(SemidirectProduct.inl u : Mc), (SemidirectProduct.inr σ : Mc)⁆ =
      (SemidirectProduct.inl (u * pact σ u⁻¹) : Mc) := by
  rw [commutatorElement_def]
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right]

theorem inl_mem_Bc (u : W5) : (SemidirectProduct.inl u : Mc) ∈ Bc := by
  show (SemidirectProduct.inl u : Mc).right.sign = 1 ∧ (SemidirectProduct.inl u : Mc).right 4 = 4
  exact ⟨Equiv.Perm.sign_one, rfl⟩

theorem inr_mem_Bc {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) (h4 : σ 4 = 4) :
    (SemidirectProduct.inr σ : Mc) ∈ Bc := by
  show (SemidirectProduct.inr σ : Mc).right.sign = 1 ∧ (SemidirectProduct.inr σ : Mc).right 4 = 4
  exact ⟨hσ, h4⟩

@[expose] def Lc : Subgroup W5 := (⁅Bc, Bc⁆).comap (SemidirectProduct.inl : W5 →* Mc)

theorem mem_Lc_of (u : W5) {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) (h4 : σ 4 = 4) :
    u * pact σ u⁻¹ ∈ Lc := by
  show (SemidirectProduct.inl (u * pact σ u⁻¹) : Mc) ∈ ⁅Bc, Bc⁆
  rw [← comm_inl_inr u σ]
  exact commutator_mem_commutator (inl_mem_Bc u) (inr_mem_Bc hσ h4)

theorem exists_W4 : ∃ u : W5, ∃ σ : Equiv.Perm (Fin 5),
    σ.sign = 1 ∧ σ 4 = 4 ∧ u * pact σ u⁻¹ = W4 := by
  decide +kernel

theorem exists_y0 : ∃ u : W5, ∃ σ : Equiv.Perm (Fin 5),
    σ.sign = 1 ∧ σ 4 = 4 ∧ u * pact σ u⁻¹ = Multiplicative.ofAdd (e2 0 2) := by
  decide +kernel

theorem exists_pY : ∃ u : W5, ∃ σ : Equiv.Perm (Fin 5),
    σ.sign = 1 ∧ σ 4 = 4 ∧
      u * pact σ u⁻¹ = pact c3p (Multiplicative.ofAdd (e2 0 2)) := by
  decide +kernel

theorem W3_le_Lc : W3 ≤ Lc := by
  intro x hx
  have hy0 : c4 (Multiplicative.ofAdd (e2 0 2)) = 1 := by decide +kernel
  have hy0one : (Multiplicative.ofAdd (e2 0 2) : W5) ≠ 1 := by decide +kernel
  have hy0W4 : (Multiplicative.ofAdd (e2 0 2) : W5) ≠ W4 := by decide +kernel
  have hyL : (Multiplicative.ofAdd (e2 0 2) : W5) ∈ Lc := by
    obtain ⟨u, σ, h1, h2, h3⟩ := exists_y0
    rw [← h3]
    exact mem_Lc_of u h1 h2
  have hW4L : W4 ∈ Lc := by
    obtain ⟨u, σ, h1, h2, h3⟩ := exists_W4
    rw [← h3]
    exact mem_Lc_of u h1 h2
  have hpL : pact c3p (Multiplicative.ofAdd (e2 0 2)) ∈ Lc := by
    obtain ⟨u, σ, h1, h2, h3⟩ := exists_pY
    rw [← h3]
    exact mem_Lc_of u h1 h2
  have hl := W3_gen (Multiplicative.ofAdd (e2 0 2)) x hy0 hy0one hy0W4 (mem_W3.1 hx)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lc.one_mem
  · exact hW4L
  · exact hyL
  · exact Lc.mul_mem hyL hW4L
  · exact hpL
  · exact Lc.mul_mem hpL hW4L
  · exact Lc.mul_mem hyL hpL
  · exact Lc.mul_mem (Lc.mul_mem hyL hpL) hW4L

theorem K4_comm_cover : ∀ σ : Equiv.Perm (Fin 5), InK4 σ →
    ∃ τ ρ : Equiv.Perm (Fin 5), τ.sign = 1 ∧ τ 4 = 4 ∧ ρ.sign = 1 ∧ ρ 4 = 4 ∧
      ⁅τ, ρ⁆ = σ := by
  decide +kernel

theorem inr_comm_mem {τ ρ : Equiv.Perm (Fin 5)} (hτ : τ.sign = 1) (hτ4 : τ 4 = 4)
    (hρ : ρ.sign = 1) (hρ4 : ρ 4 = 4) :
    (SemidirectProduct.inr ⁅τ, ρ⁆ : Mc) ∈ ⁅Bc, Bc⁆ := by
  rw [map_commutatorElement]
  exact commutator_mem_commutator (inr_mem_Bc hτ hτ4) (inr_mem_Bc hρ hρ4)

theorem inr_K4_mem {σ : Equiv.Perm (Fin 5)} (hσ : InK4 σ) :
    (SemidirectProduct.inr σ : Mc) ∈ ⁅Bc, Bc⁆ := by
  obtain ⟨τ, ρ, h1, h2, h3, h4, h5⟩ := K4_comm_cover σ hσ
  subst h5
  exact inr_comm_mem h1 h2 h3 h4

theorem U0_le_comm_Bc : U0 ≤ ⁅Bc, Bc⁆ := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (SemidirectProduct.inl x.left : Mc) ∈ ⁅Bc, Bc⁆ := W3_le_Lc hx1
  have h2 : (SemidirectProduct.inr x.right : Mc) ∈ ⁅Bc, Bc⁆ := inr_K4_mem hx2
  have h := (⁅Bc, Bc⁆).mul_mem h1 h2
  rwa [SemidirectProduct.inl_left_mul_inr_right] at h

theorem Bc_le_Bhc : Bc ≤ Bhc := by
  intro x hx
  obtain ⟨_, h4⟩ := hx
  exact h4

open Subgroup in
theorem U0_le_comm_Bhc : U0 ≤ ⁅Bhc, Bhc⁆ :=
  U0_le_comm_Bc.trans (commutator_mono Bc_le_Bhc Bc_le_Bhc)

end CFSG.GH74.QTGen4.U42
