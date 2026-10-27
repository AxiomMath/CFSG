module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigCtx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoI1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZOdd
import CFSG.ClassicalInvolution.Sp62Rec.OddB
import CFSG.ClassicalInvolution.Sp62Rec.SylowCentral
import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance


section Hat

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

theorem zHat_of_I1 {Z : Subgroup Y} (hc : P23Cfg n Y R S t K' W u e g) (hAE : SecAE R e 6)
    (hI : I1In R t e Z) (hoddC : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (heO2 : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set Y))).map
      (Subgroup.centralizer ({t} : Set Y)).subtype) :
    ZHat R e := by
  obtain ⟨f, Θ, φ, D, M⟩ := i1_action_memberLabels_final hc.std.perp hAE hI hoddC
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzsq : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hze : t ≠ e := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hz.mem)
  have hesq : e * e = 1 := hc.data.he2
  have P := D.toI1Six
  obtain ⟨φ', hsurj, hker, -, -, hoddidx⟩ := P.hat
  have hEB : oddCoreIn (rLayer (Om R) e) ≤ Z ⊔ rLayer (Om R) e :=
    (oddCoreIn_le _).trans P.E_le_B
  have hK : Odd (Nat.card φ'.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv]
    exact odd_card_oddCoreIn _
  obtain ⟨TB, hzT, hzc⟩ := exists_sylow_central_of_surjective φ' hsurj hK
    (b := (⟨t, P.z_mem⟩ : ↥(Z ⊔ rLayer (Om R) e))) (Subtype.ext hzsq) hoddidx
  have hodd_e : oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ :=
    P.oddCoreIn_centralizer_eq_bot TB hzT hzc hzsq hz1 hze hesq hoddC heO2 card_S0 card_Hhat
      eq_of_mem_center_S0 Hhat_le_centralizer_alpha (fun x hx => exists_four_conj hx)
  have hodd_E : oddCoreIn (rLayer (Om R) e) = ⊥ := D.oddCoreIn_eq_bot hodd_e
  refine ⟨D.e_mem, fun h hh => D.E_normal h hh, hodd_E, f, ?_, D.f_range, M, D.kappa⟩
  have : f.ker = ⊥ := by
    rw [D.f_ker, hodd_E]
    exact Subgroup.bot_subgroupOf _
  exact (MonoidHom.ker_eq_bot_iff f).mp this

theorem zCtx_of_inputs (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) (hZ2 : P23E8ZTwo n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hz : u * e ∈ zStarOf (rLayer (Om R) u)) (hA6 : SecAE R e 6)
    (hne : conjSub x (rLayer (Om R) e) ≠ rLayer (Om R) e) (htop : p23XE R e x ≠ ⊤) :
    ZCtx n Y R S t K' W u e g x := by
  have hα' := p23E8ZAlpha_of_normT hE hT hα hN hcit hP hc hno hz hA6
  obtain ⟨hodd, heO2⟩ := p23E8Z_oddC_of_normT hE hT hα hN hcit hP hc hno hz hA6
  obtain ⟨Z, hI⟩ := exists_i1In_of_zTwo hZ2 hcit hP Y R S t K' W u e g hc hno hz hA6
  exact ⟨hc, p23E8Z_members_isPGroup_of_alpha hE hT hcit hP hc hz hα', hA6, heO2,
    zHat_of_I1 hc hA6 hI hodd heO2, hne, htop⟩

end Hat

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
