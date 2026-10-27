module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23CtKey
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56YExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf14Narrow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Y5C0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4I1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Y5D0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

section Main

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem ct_core (hT : Thm4RTwinBelow 3 n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      ∃ d ∈ Subgroup.centralizer ((tightCore R ⊔ K' : Subgroup Y) : Set Y),
        c * d⁻¹ ∈ Subgroup.centralizer ({e} : Set Y) := by
  obtain ⟨-, -, q₁, q₂, hcomm, -, -, -⟩ := ct_data hP hc hno hα
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  exact decomp_of_twinData hz hz' hc.std.hne q₁ q₂ hcomm (ct_hperm hc) (ct_htrans hP hc hno hα)
    (ct_hswap hT hP hc hno hα) (ct_hsyl hT hP hc hno hα)

theorem p23CtDec_proved (hE : TwinThmE.TwinThmEP n) (hT : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hAE : R56.P23YExitAE n) : R56.P23CtDec n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hEorth c hct
  have hY5x : P23Y5Exit n := p23Y5Exit_of_secMuE4Ex hT hmodel hD4 (p23Y5SecMuE4Ex_proved n)
  have hY5i : P23Y5Ident n := p23Y5Ident_of_trans_type (p23Y5Trans_of_t4 hT)
    (p23Y5Type_of_dimC (p23Y5DimC n) (p23Y5Trans_of_t4 hT))
  have hTwo := p23TwoN_of_fuseN hE hcit hP (p23FuseN hP) Y R S t K' W u e g hc hno
  have hΓz := gamma_t hP hc hno
  have hO := (CoreData.of_S hc.std.perp.core).oddFree
  by_cases hnoU : SecNoExit R u
  ·
    obtain ⟨D⟩ := secDecomp_of_noExit hcit hP hc.std.perp hc.data.hu2 hc.data.hu1
      (p23Members n Y R S t K' W u e g hc).2 hnoU
    have hYo : YOrth R u := by
      rcases hY5i hcit hP Y R S t K' W u e g hc hnoU D with h | h
      · exact Or.inl ⟨D, h⟩
      · exact Or.inr ⟨D, h⟩
    have hY : YType R u e := by
      rcases hYo with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨hodd, halpha⟩ := p23Alpha_proved hD4 hM12 hT hcit hP Y R S t K' W u e g hc hY
    have hΓu := gamma_u (hT n hcit hP) hP hc hnoU hYo
    exact ct_core (hT n hcit hP) hP hc hno
      (alpha_eq_bot_of_gamma hO hTwo hΓz hΓu hodd halpha) c hct
  · rcases hY5x hcit hP Y R S t K' W u e g hc hnoU with hZ | h5
    · have hY : YType R u e := Or.inl hZ
      obtain ⟨hodd, halpha⟩ := p23Alpha_proved hD4 hM12 hT hcit hP Y R S t K' W u e g hc hY
      have hΓu := R56.p23_gamma_u_of_zstar (hT n hcit hP) hc hZ
      exact ct_core (hT n hcit hP) hP hc hno
        (alpha_eq_bot_of_gamma hO hTwo hΓz hΓu hodd halpha) c hct
    · exact (hAE hcit hP Y R S t K' W u e g hc hnoU h5 hno hEorth).elim

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec
