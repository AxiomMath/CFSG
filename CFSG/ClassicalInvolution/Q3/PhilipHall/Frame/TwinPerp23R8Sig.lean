module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23SigC
public import CFSG.ClassicalInvolution.Q3.Sec13L94Tight

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Sig

variable {n : ℕ}

@[expose] def P23E8AWTr (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ → ∀ b : Y,
        Nonempty (TC.Thin.AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) →
        tightCore R ≤ p23XE R e b →
          ∀ W₁ ∈ WSet (Om R), t ∈ W₁ → ∃ c ∈ p23XE R e b, conjSub c W = W₁

@[expose] def P23E8ALay (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ → ∀ b : Y,
        Nonempty (TC.Thin.AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) →
        tightCore R ≤ p23XE R e b →
          ∀ J ∈ tqMembers3 (Om R) u, J ∈ dstarComp (Om R) (tightCore R)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y}
  {u e g : Y}

theorem p23_mGrp_le_XE (hc : P23Cfg n Y R S t K' W u e g) (b : Y) :
    MGrp (Om R) W ≤ p23XE R e b := by
  have hNe := normalizer_le_centralizer_e hc.data
  refine le_trans ?_ le_sup_left
  unfold MGrp
  refine iSup₂_le fun R' hR' => ?_
  unfold rLayer
  exact le_iSup₂_of_le (f := fun R'' (_ : R'' ∈ RSet (Om R)) =>
    ⨆ (_ : R'' ≤ Subgroup.centralizer ({e} : Set Y)), R'') R' hR'.1
    (le_iSup_of_le (hR'.2.trans hNe) le_rfl)

theorem p23_conj_of_D (hc : P23Cfg n Y R S t K' W u e g) (b : Y) :
    ∀ J ∈ Om R, (∃ T ∈ DSet (Om R) W, IsSylow2In T J) →
      ∃ m ∈ p23XE R e b, conjSub m (tightCore R) = J := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have htrans : ∀ J ∈ Om R, ∃ a : Y, conjSub a (tightCore R) = J := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨R₁, -, -, -, hR₁, -, hR₁D, -⟩ := e_decomp hc
  rintro J hJ ⟨T, hTD, hTJ⟩
  obtain ⟨a, rfl⟩ := htrans J hJ
  obtain ⟨m, hm, hmK, -⟩ := Sec13.L94T.exists_mGrp_conj hPG hd.hW hK htrans hz hc.std.hK'
    hc.std.hne hperp hd.hS4 hR₁ hR₁D hJ hTJ hTD (hz.conj a)
  exact ⟨m, p23_mGrp_le_XE hc b hm, hmK⟩

theorem p23E8ASigma_of_wtr (hW : P23E8AWTr n) (hL : P23E8ALay n) : P23E8ASigma n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 hα b hId hKX
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  refine ⟨SigC.le_of_mem_dstarComp hΩ hK hz hKX
    (SigC.key_of_trans hΩ (hW hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα b hId hKX)
      (p23_conj_of_D hc b)), hL hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα b hId hKX⟩

end Sig

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
