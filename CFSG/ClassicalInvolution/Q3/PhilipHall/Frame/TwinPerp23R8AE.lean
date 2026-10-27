module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23RE78
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Sigma

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Gen

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)]

theorem ne_top_of_le_normalizer (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    {V X : Subgroup Y} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hXV : X ≤ Subgroup.normalizer (V : Set Y)) : X ≠ ⊤ := by
  intro hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (hX ▸ hXV))
  have hFV : genFittingFStar Y ≤ V := fstar_le_of_normal hnab hVn hV1
  have hF2 : IsPGroup 2 ↥(genFittingFStar Y) := hV2.to_le hFV
  have hZ : Nontrivial ↥(Subgroup.center ↥(genFittingFStar Y)) := hF2.center_nontrivial
  obtain ⟨a, b, hab⟩ := hnab
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar Y))
    with h | h
  · rw [h] at hZ
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ
  · have ha : a ∈ Subgroup.center ↥(genFittingFStar Y) := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

end Gen


section E8A

variable {n : ℕ}

@[expose] def p23XE {Y : Type} [Group Y] (R : Subgroup Y) (e b : Y) : Subgroup Y :=
  rLayer (Om R) e ⊔ conjSub b (rLayer (Om R) e)

@[expose] def P23E8ANorm (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      Subgroup.centralizer ({u} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) ∧
        Subgroup.centralizer ({t} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y)

@[expose] def P23E8AAE7 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
        ∃ (b : Y) (V : Subgroup Y), V ≠ ⊥ ∧ IsPGroup 2 V ∧
          p23XE R e b ≤ Subgroup.normalizer (V : Set Y) ∧
          Nonempty (TC.Thin.AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) ∧
          tightCore R ≤ p23XE R e b

@[expose] def P23E8ASigma (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ → ∀ b : Y,
        Nonempty (TC.Thin.AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) →
        tightCore R ≤ p23XE R e b →
          (∀ J ∈ dstarComp (Om R) (tightCore R), J ≤ p23XE R e b) ∧
            ∀ J ∈ tqMembers3 (Om R) u, J ∈ dstarComp (Om R) (tightCore R)

theorem p23_alpha_eq_bot {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g)
    (hTwo : Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤)
    (hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, t} : Set Y)))))
    (hN : Subgroup.centralizer ({u} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) ∧
        Subgroup.centralizer ({t} : Set Y) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y)) :
    alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ := by
  have hn : (alphaOf (Subgroup.closure ({u, t} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (hTwo ▸ sup_le hN.1 hN.2))
  have hle : alphaOf (Subgroup.closure ({u, t} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hn, hodd⟩
  rw [hc.std.perp.core.oddFree] at hle
  exact le_bot_iff.mp hle

theorem p23E8A_of_steps (hE : TwinThmEW.ThmEQ8) (hα : P23Alpha n) (hN : P23E8ANorm n)
    (hX : P23E8AAE7 n) (hS : P23E8ASigma n) : P23E8A n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6
  exfalso
  haveI := hc.std.perp.core.simple
  have hTwo := p23Two_of_thmEQ8 hE hcit hP Y R S t K' W u e g hc
  have hodd := (hα Y R S t K' W u e g hc (Or.inr (Or.inr (Or.inr hA5)))).1
  have hα1 := p23_alpha_eq_bot hc hTwo hodd (hN hcit hP Y R S t K' W u e g hc hno hA5 hA6)
  obtain ⟨b, V, hV1, hV2, hXV, hId, hKX⟩ := hX hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα1
  have hne := ne_top_of_le_normalizer hc.std.perp.core.nonab hV1 hV2 hXV
  obtain ⟨hsub, hlay⟩ := hS hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα1 b hId hKX
  exact R56.p23_false_of_dstar_proper hc (R56.p23_sigmaStarNorm_eq_top_of_layer hc hTwo hlay)
    hsub hne

end E8A

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
