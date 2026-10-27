module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.FpfInvolution
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.RadicalLemmas

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

theorem radical_structure {X : Type} [Group X] [Finite X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : X →* (W ≃ₗ[ZMod 2] W)} {w : W} {P F : Subgroup X} {v : X}
    (h : WrData X ρ w P F v) :
    v ∉ CFSG.solvableRadical X ∧
      (∀ s ∈ CFSG.solvableRadical X, v * s = s * v → s = 1) ∧
      (∀ s ∈ CFSG.solvableRadical X, v * s * v⁻¹ = s⁻¹) ∧
      (∀ a ∈ CFSG.solvableRadical X, ∀ b ∈ CFSG.solvableRadical X, a * b = b * a) ∧
      Odd (Nat.card (CFSG.solvableRadical X)) := by
  obtain ⟨eP⟩ := h.P_iso
  obtain ⟨eF⟩ := h.F_iso
  have hSsolv : Group.IsSolvable (CFSG.solvableRadical X) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hPS : P ⊓ CFSG.solvableRadical X = ⊥ :=
    inf_eq_bot_of_equiv_perm_five P eP (CFSG.solvableRadical X) hSsolv
  have hPcard : Nat.card P = 120 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  have hCcard : Nat.card (Subgroup.centralizer ({v} : Set X)) ≤ 120 :=
    card_centralizer_le_one_twenty F eF h.v_sq h.F_comm h.centralizer_le
  have hvS : v ∉ CFSG.solvableRadical X :=
    not_mem_solvableRadical P hPS h.v_ne_one (by simpa [hPcard] using hCcard)
  have hC : ∀ s ∈ CFSG.solvableRadical X, v * s = s * v → s = 1 :=
    eq_one_of_commute_of_normal_solvable F eF h.v_sq h.F_comm h.centralizer_le
      (CFSG.solvableRadical X) hSsolv hvS
  obtain ⟨hinv, hab, hodd⟩ :=
    normal_fpf_involution (X := X) (S := CFSG.solvableRadical X) h.v_sq hC
  exact ⟨hvS, hC, hinv, hab, hodd⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
