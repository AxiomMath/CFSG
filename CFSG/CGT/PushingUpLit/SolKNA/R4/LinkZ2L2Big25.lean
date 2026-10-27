module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big28
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big5

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section L1Abstract

variable {F : Type} [Field F] [Finite F] {p f : ℕ}

theorem normal_of_psl_le [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    (N : Subgroup (PGammaL2 F))
    (hN : ∀ g : PGammaL2 F, g.right = 1 → g.left ∈ pslRange F → g ∈ N) : N.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨γ, hγ⟩ := pgammaL2_commutator_mem (field_facts (Fact.out : p.Prime) hp2 hF h4).1 g n
  have hc : g * n * g⁻¹ * n⁻¹ ∈ N := by
    apply hN
    · rw [hγ, SemidirectProduct.right_inl]
    · rw [hγ, SemidirectProduct.left_inl]
      exact ⟨γ, rfl⟩
  have hgn : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
  rw [hgn]
  exact N.mul_mem hc hn

theorem l1_of_sylow {N : Subgroup (PGammaL2 F)} [N.Normal] {P : Subgroup (PGammaL2 F)}
    (hP : IsSylow2In P (monGrp F)) {m : ℕ}
    (hkey : ∀ y ∈ P, ∃ ζ ∈ P, y⁻¹ * ζ ∈ N ∧ m < orderOf ζ)
    {H S : Subgroup (PGammaL2 F)} (hH : IsPGroup 2 ↥H) (hHM : H ≤ monGrp F) (hSH : S ≤ H)
    (hS : IsSylow2In S N) {y : PGammaL2 F} (hy : y ∈ H) :
    ∃ s ∈ S, m < orderOf (y * s) := by
  obtain ⟨g, hg⟩ := exists_conj_le_of_isSylow2In hP hH hHM
  set P' : Subgroup (PGammaL2 F) := conjSub g P with hP'def
  have hP'grp : IsPGroup 2 ↥P' := by
    rw [hP'def]
    exact hP.2.1.map (MulAut.conj g).toMonoidHom
  have hSP' : S ≤ P' := hSH.trans hg
  have hSN : S ≤ N := hS.1
  have hP'N_grp : IsPGroup 2 ↥(P' ⊓ N) := hP'grp.to_le inf_le_left
  have hP'N_eq : P' ⊓ N = S :=
    hS.2.2 (P' ⊓ N) inf_le_right hP'N_grp (le_inf hSP' hSN)
  have hy'P : g⁻¹ * y * g ∈ P := mem_conjSub_iff.1 (hg hy)
  obtain ⟨ζ', hζ'P, hζ'N, hζ'ord⟩ := hkey (g⁻¹ * y * g) hy'P
  have hζP' : g * ζ' * g⁻¹ ∈ P' := by
    rw [hP'def]
    exact conj_mem_conjSub hζ'P
  refine ⟨y⁻¹ * (g * ζ' * g⁻¹), ?_, ?_⟩
  · have hsP' : y⁻¹ * (g * ζ' * g⁻¹) ∈ P' :=
      P'.mul_mem (P'.inv_mem (hg hy)) hζP'
    have hsN : y⁻¹ * (g * ζ' * g⁻¹) ∈ N := by
      have heq : y⁻¹ * (g * ζ' * g⁻¹) = g * ((g⁻¹ * y * g)⁻¹ * ζ') * g⁻¹ := by group
      rw [heq]
      exact (inferInstance : N.Normal).conj_mem ((g⁻¹ * y * g)⁻¹ * ζ') hζ'N g
    rw [← hP'N_eq]
    exact ⟨hsP', hsN⟩
  · have hmul : y * (y⁻¹ * (g * ζ' * g⁻¹)) = g * ζ' * g⁻¹ := mul_inv_cancel_left y _
    rw [hmul]
    have horder : orderOf (g * ζ' * g⁻¹) = orderOf ζ' := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective ζ'
      simpa [MulAut.conj_apply] using this
    rw [horder]
    exact hζ'ord

end L1Abstract

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
