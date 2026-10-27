module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf2P23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


section Exit

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem e_exit_frame_fine (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    (∃ M ∈ TwinDisc.secFam (Om R) e, ∃ N : Subgroup (SecQ R e),
      N ∈ omegaNbr (TwinDisc.secFam (Om R) e) M) ∧
    (∃ A ∈ TwinDisc.secFam (Om R) e, ∃ B ∈ twinSet (TwinDisc.secFam (Om R) e) A, B ≠ A) ∧
    ((∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
        ∃ x : SecQ R e, conjSub x K = L) ∨
      ∀ M ∈ TwinDisc.secFam (Om R) e,
        M = TwinDisc.secImg (Om R) e (tightCore R) ∨ M = TwinDisc.secImg (Om R) e K') := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  obtain ⟨hedge, hdich⟩ := layer_exit_frame hT hc.std.perp hd.he2 hd.he1 hK hc.std.hK'.1
    hc.std.hne hz hz' hR₁ hR₁' hR₁e hR₁'e hcomm hp₁ hp₂
  have hJ₁ : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁e⟩⟩
  have hJ₂ : K' ∈ tqMembers3 (Om R) e :=
    ⟨hc.std.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hc.std.hK'.1 ⟨R₁', hR₁', hR₁'e⟩⟩
  obtain ⟨hC₁, hY₁, hzz₁⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₁ hz
  obtain ⟨hC₂, hY₂, hzz₂⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₂ hz'
  exact ⟨⟨_, secImg_mem_secFam hJ₁, _, hedge⟩,
    ⟨_, secImg_mem_secFam hJ₁, _, ⟨secImg_mem_secFam hJ₂, _, hzz₁, hzz₂⟩,
      (secImg_ne_of_twins hΩ hc2' hJ₁ hJ₂ hc.std.hne hz hz').symm⟩, hdich⟩

theorem p23E4ExitCases_of_mu (hT : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) :
    CIT3Below n → TL4.TightBelowRPlus 3 n →
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
      (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
        (∀ M ∈ TwinDisc.secFam (Om R) e,
          M = TwinDisc.secImg (Om R) e (tightCore R) ∨ M = TwinDisc.secImg (Om R) e K') ∨
        ((∃ V : Subgroup (SecQ R e), WSet (TwinDisc.secFam (Om R) e) = {V}) ∧
          ∀ L ∈ TwinDisc.secFam (Om R) e, IsPGroup 2 ↥L) ∨ SecAE R e 5 ∨ SecAE R e 6 := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno
  obtain ⟨hedge, htw, hdich⟩ := e_exit_frame_fine (hT n hcit hP) hc
  rcases hdich with htrans | hpair
  swap
  · exact Or.inl hpair
  right
  have hS := p23_q8Section hc.std.perp hc.data.he2
  have hlt := secQ_card_lt hc.std.perp hc.data.he1
  have hodd := oddCent_exit_gen2 hD4 hcit hP hc.std.perp hc.data.he2 hc.data.he1 htrans hedge htw
  have hdist : ∃ A ∈ TwinDisc.secFam (Om R) e, ∃ B ∈ TwinDisc.secFam (Om R) e, A ≠ B := by
    obtain ⟨A, hA, B, hB, hBA⟩ := htw
    exact ⟨A, hA, B, hB.1, hBA.symm⟩
  have hcls : ∀ hconn : T3.DStarConnected (TwinDisc.secFam (Om R) e),
      (∃ K ∈ TwinDisc.secFam (Om R) e, ∃ z : SecQ R e, IsUniqueInvolution K z ∧ TightInO2 z) →
      ((∃ V : Subgroup (SecQ R e), WSet (TwinDisc.secFam (Om R) e) = {V}) ∧
        ∀ L ∈ TwinDisc.secFam (Om R) e, IsPGroup 2 ↥L) ∨ SecAE R e 5 ∨ SecAE R e 6 := by
    intro hconn ⟨K, hK, z, hz, hO⟩
    have F := TwinDisc.ExitU.q8Fam_of_q8Section hS htrans hK hz (hodd K hK z hz) hO
    rcases conn_o2_classify_mu hP.thmD.d2 hlt hS htrans hK hz (hodd K hK z hz) hO hdist
        (hMu hcit hP Y R S t K' W u e g hc hno hconn) with hWc | h5 | h6
    · exact Or.inl ⟨hWc, F.two⟩
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h6)
  by_cases hconn : T3.DStarConnected (TwinDisc.secFam (Om R) e)
  · rcases TwinDisc.ExitU.noExit_or_o2_or_e4 hS htrans hedge hodd with h | ho | hE
    · exact absurd h hno
    · exact hcls hconn ho
    · by_cases hO2 : ∃ K ∈ TwinDisc.secFam (Om R) e, ∃ z : SecQ R e,
          IsUniqueInvolution K z ∧ TightInO2 z
      · exact hcls hconn hO2
      · exact absurd hE ((hMu hcit hP Y R S t K' W u e g hc hno hconn).noE4 hO2)
  · rcases TwinDisc.ExitU.noExit_or_ae5 hmodel hP.thmD.d2 hlt hS htrans hedge hodd hconn with
      h | ⟨-, I⟩
    · exact absurd h hno
    · exact Or.inr (Or.inl I)

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
