module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU9
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Y5C0

variable {n : ℕ}

@[expose] def P23Y5SecMuE4 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' Wg : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' Wg u e g → ¬ SecNoExit R u →
      ∀ V ∈ WSet (TwinDisc.secFam (Om R) u), MuIsoE4 (TwinDisc.secFam (Om R) u) V

@[expose] def P23Y5SecMuE4Ex (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' Wg : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' Wg u e g → ¬ SecNoExit R u →
      ∃ V ∈ WSet (TwinDisc.secFam (Om R) u), MuIsoE4 (TwinDisc.secFam (Om R) u) V

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem u_pair_frame (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ A ∈ TwinDisc.secFam (Om R) u, ∃ B ∈ TwinDisc.secFam (Om R) u, A ≠ B ∧
      (∀ M ∈ TwinDisc.secFam (Om R) u, M ∈ omegaNbr (TwinDisc.secFam (Om R) u) A → M = B) ∧
      (∀ M ∈ TwinDisc.secFam (Om R) u, M ∈ omegaNbr (TwinDisc.secFam (Om R) u) B → M = A) ∧
      ((∀ M ∈ TwinDisc.secFam (Om R) u, M = A ∨ M = B) → u * e ∈ zStarOf (rLayer (Om R) u)) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hR₃u := conj_cent_u hc hR₁e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz (hR₁.1 hx)))
  have hR₃'u := conj_cent_u hc hR₁'e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz' (hR₁'.1 hx)))
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hc.std.hK'.1
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  have hJ₁tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hR₃u⟩⟩
  have hJ₂tq : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩
  have hq₁ := perp_conj_pair hΩ hp₁ g
  have hq₂ := perp_conj_pair hΩ hp₂ g
  refine ⟨_, secImg_mem_secFam hJ₁tq, _, secImg_mem_secFam hJ₂tq,
    secImg_ne_of_twins hΩ hc2' hJ₁tq hJ₂tq hne₂ hτ₁ hτ₂, ?_, ?_, ?_⟩
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hJ₁tq hJ₀
      (fun J₀' hJ₀' hp => hq₁ J₀' hJ₀'.1 hp) hMn
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hJ₂tq hJ₀
      (fun J₀' hJ₀' hp => hq₂ J₀' hJ₀'.1 hp) hMn
  · intro hpair
    exact layer_pair_zstar hΩ h2 hc2' hJ₁tq hJ₂tq hτ₁ hτ₂ hR₃ hR₃u hpair

theorem p23Y5Exit_of_secMuE4Ex (hT : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23Y5SecMuE4Ex n) : P23Y5Exit n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno
  obtain ⟨hedge, htw, hdich⟩ := u_exit_frame3 (hT n hcit hP) hc
  rcases hdich with htrans | hz
  swap
  · exact Or.inl hz
  have hS := p23_q8Section hc.std.perp hc.data.hu2
  have hlt := secQ_card_lt hc.std.perp hc.data.hu1
  have hodd := oddCent_exit_gen2 hD4 hcit hP hc.std.perp hc.data.hu2 hc.data.hu1 htrans hedge htw
  by_cases hconn : T3.DStarConnected (TwinDisc.secFam (Om R) u)
  · left
    obtain ⟨A, hA, B, hB, -, hnb, hnb', hpair⟩ := u_pair_frame hc
    refine hpair fun M hM => ?_
    obtain ⟨V, hV, hμ⟩ := hMu hcit hP Y R S t K' W u e g hc hno
    have h2Φ : ∀ K ∈ TwinDisc.secFam (Om R) u, IsPGroup 2 ↥K := by
      intro K hK
      obtain ⟨z, hz⟩ := (hS.hyp.omega1 K hK).1
      exact isPGroup_of_oddCent hS.hyp hK hz (hodd K hK z hz) (hS.two K hK)
    have hPΦ : Q3CL.PartIHypG (TwinDisc.secFam (Om R) u) :=
      ⟨hS.hyp, TC.Thin.classicalClause_of_two hS.hyp h2Φ, hS.aEmpty⟩
    have hcomp : dComp (TwinDisc.secFam (Om R) u) A = dstarComp (TwinDisc.secFam (Om R) u) A := by
      by_contra hne
      exact s26_not_comm_of_muIso
        (Q3T8.Asc77.l7_10_proved _ _ hPΦ _ hV (Q3T6.Mu.thompsonGraphAll hPΦ hA hne hV))
        (s26_comm_of_muIsoE4 hμ)
    have hM' : M ∈ dComp (TwinDisc.secFam (Om R) u) A := by
      rw [hcomp]
      exact hconn A hA M hM
    exact TwinPerpV3.Sec.dComp_subset_pair hS.hyp hA hB hnb hnb' hM'
  · rcases TwinDisc.ExitU.noExit_or_ae5 hmodel hP.thmD.d2 hlt hS htrans hedge hodd hconn with
      h | ⟨-, I⟩
    · exact absurd h hno
    · exact Or.inr I

end Y5C0

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
