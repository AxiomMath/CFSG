module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Sec
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8W

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {R T : Subgroup G}

theorem sX_normalizes_JE {S₂ : Sylow 2 G} (hcl : ConjInvariant Ω)
    (hR8 : ∀ {R₀ : Subgroup G}, R₀ ∈ RSet Ω → 8 ≤ Nat.card R₀) (hJ : J ∈ omegaNbr Ω K)
    (hT1 : T ∈ RSet Ω) (hTJ : T ≤ J) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (heqJ : ∀ {L : Subgroup G}, L ∈ Ω → L ≤ omegaNbrGen Ω K →
      2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G)) → L = J)
    {s : G} (hsS : s ∈ (S₂ : Subgroup G)) (hsX : s ∈ omegaNbrGen Ω K) : conjSub s J = J := by
  have hJΩ : J ∈ Ω := hJ.1
  have hJX : J ≤ omegaNbrGen Ω K := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hJ
  have hX := omegaNbrGen Ω K
  have hJsΩ : conjSub s J ∈ Ω := hcl s J hJΩ
  have hJsX : conjSub s J ≤ omegaNbrGen Ω K := by
    intro y hy
    have h1 := (mem_conjSub_iff.mp hy)
    have h2 : s⁻¹ * y * s ∈ omegaNbrGen Ω K := hJX h1
    have := (omegaNbrGen Ω K).mul_mem ((omegaNbrGen Ω K).mul_mem hsX h2)
      ((omegaNbrGen Ω K).inv_mem hsX)
    simpa [mul_assoc] using this
  have h8 : 8 ≤ Nat.card T := hR8 hT1
  have hle : conjSub s (J ⊓ (S₂ : Subgroup G)) ≤ conjSub s J ⊓ (S₂ : Subgroup G) := by
    intro y hy
    have h1 := mem_conjSub_iff.mp hy
    refine ⟨mem_conjSub_iff.mpr h1.1, ?_⟩
    have h2 := h1.2
    have : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
    rw [this]
    exact (S₂ : Subgroup G).mul_mem ((S₂ : Subgroup G).mul_mem hsS h2)
      ((S₂ : Subgroup G).inv_mem hsS)
  have hcardT : Nat.card T ≤ Nat.card ↥(J ⊓ (S₂ : Subgroup G)) :=
    Subgroup.card_le_of_le (le_inf hTJ hTS₂)
  have hcard : 2 < Nat.card ↥(conjSub s J ⊓ (S₂ : Subgroup G)) := by
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(conjSub s (J ⊓ (S₂ : Subgroup G))) =
        Nat.card ↥(J ⊓ (S₂ : Subgroup G)) := T8S2.natCard_conjSub_eq s _
    omega
  exact heqJ hJsΩ hJsX hcard

theorem exists_sylow_RTE {S : Sylow 2 G}
    (hconjX : ∀ {K₀ : Subgroup G} {b : G}, conjSub b K₀ = K₀ →
      conjSub b (omegaNbrGen Ω K₀) = omegaNbrGen Ω K₀)
    (hJ : J ∈ omegaNbr Ω K) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G)) (hTJ : T ≤ J)
    (hTS : T ≤ (S : Subgroup G)) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧ T ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K) := by
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hRN : ∀ r ∈ R, conjSub r X = X := fun r hr =>
    hconjX (conjSub_eq_self_of_mem (hRK hr))
  have hYN : X ⊔ R ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer
      (fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRN r hr))
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hJ
  have hTX : T ≤ X := hTJ.trans hJX
  have hRT : IsPGroup 2 ↥(R ⊔ T) :=
    S.isPGroup'.to_le (sup_le hRS hTS)
  have hRTle : R ⊔ T ≤ X ⊔ R := sup_le le_sup_right (hTX.trans le_sup_left)
  obtain ⟨V, hV, hRTV⟩ := IsSylow2In.exists_ge hRT hRTle
  have hVX : IsSylow2In (V ⊓ X) X :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hYN
  obtain ⟨S₂, hS₂⟩ := hV.2.1.exists_le_sylow
  have heq : (S₂ : Subgroup G) ⊓ X = V ⊓ X :=
    hVX.2.2 _ inf_le_right S₂.isPGroup'.to_inf_left (inf_le_inf_right X hS₂)
  exact ⟨S₂, le_sup_left.trans (hRTV.trans hS₂), le_sup_right.trans (hRTV.trans hS₂),
    heq ▸ hVX⟩

end T8W

end CFSG.ClassicalInvolution.Asc77
