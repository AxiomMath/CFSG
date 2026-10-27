module


public import Mathlib.GroupTheory.PGroup

public section

open Subgroup

namespace CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter

theorem inf_center_ne_bot {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hE : IsPGroup p E) (N : Subgroup E) [N.Normal] (hN : N ≠ ⊥) :
    N ⊓ Subgroup.center E ≠ ⊥ := by
  classical
  letI : MulAction E N := MulAction.compHom N (MulAut.conjNormal : E →* MulAut N)
  have hsm : ∀ (g : E) (n : N), ((g • n : N) : E) = g * n * g⁻¹ := fun g n => rfl
  have hNp : IsPGroup p N := hE.to_subgroup N
  have hdvd : p ∣ Nat.card N := by
    have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
    obtain ⟨n, hn0, hn⟩ := hNp.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  have h1 : (1 : N) ∈ MulAction.fixedPoints E N := fun g => by
    apply Subtype.ext; simp [hsm]
  obtain ⟨a, ha, hne⟩ := hE.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd h1
  intro hbot
  apply hne
  have hmem : (a : E) ∈ N ⊓ Subgroup.center E := by
    refine ⟨a.2, ?_⟩
    show (a:E) ∈ Subgroup.center E
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg Subtype.val (ha g)
    rw [hsm] at this
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [this]
  rw [hbot] at hmem
  exact (Subtype.ext (by simpa using hmem)).symm

theorem eq_bot_of_inf_center_eq_bot {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hE : IsPGroup p E) (N : Subgroup E) [N.Normal]
    (h : N ⊓ Subgroup.center E = ⊥) : N = ⊥ := by
  by_contra hN
  exact inf_center_ne_bot hE N hN h

end CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
