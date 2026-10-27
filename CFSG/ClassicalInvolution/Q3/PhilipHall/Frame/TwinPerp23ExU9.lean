module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14Step
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf5Trans

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

section U9

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem u_exit_frame3 (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    (∃ M ∈ TwinDisc.secFam (Om R) u, ∃ N : Subgroup (SecQ R u),
      N ∈ omegaNbr (TwinDisc.secFam (Om R) u) M) ∧
    (∃ A ∈ TwinDisc.secFam (Om R) u, ∃ B ∈ twinSet (TwinDisc.secFam (Om R) u) A, B ≠ A) ∧
    ((∀ K ∈ TwinDisc.secFam (Om R) u, ∀ L ∈ TwinDisc.secFam (Om R) u,
        ∃ x : SecQ R u, conjSub x K = L) ∨ u * e ∈ zStarOf (rLayer (Om R) u)) := by
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
  obtain ⟨hedge, hdich⟩ := layer_exit_frame hT hc.std.perp hd.hu2 hd.hu1 hJ₁ hJ₂ hne₂ hτ₁ hτ₂
    hR₃ hR₃' hR₃u hR₃'u (hcomm.conjSub g) (perp_conj_pair hΩ hp₁ g) (perp_conj_pair hΩ hp₂ g)
  have hJ₁tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hR₃u⟩⟩
  have hJ₂tq : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩
  obtain ⟨hC₁, hY₁, hzz₁⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₁tq hτ₁
  obtain ⟨hC₂, hY₂, hzz₂⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₂tq hτ₂
  refine ⟨⟨_, secImg_mem_secFam hJ₁tq, _, hedge⟩,
    ⟨_, secImg_mem_secFam hJ₁tq, _, ⟨secImg_mem_secFam hJ₂tq, _, hzz₁, hzz₂⟩,
      (secImg_ne_of_twins hΩ hc2' hJ₁tq hJ₂tq hne₂ hτ₁ hτ₂).symm⟩, ?_⟩
  rcases hdich with h | h
  · exact Or.inl h
  · right
    exact layer_pair_zstar hΩ h2 hc2' ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁
      ⟨conjSub g R₁, hR₃, hR₃u⟩⟩ ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂
      ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩ hτ₁ hτ₂ hR₃ hR₃u h

theorem e_exit_frame3 (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    (∃ M ∈ TwinDisc.secFam (Om R) e, ∃ N : Subgroup (SecQ R e),
      N ∈ omegaNbr (TwinDisc.secFam (Om R) e) M) ∧
    (∃ A ∈ TwinDisc.secFam (Om R) e, ∃ B ∈ twinSet (TwinDisc.secFam (Om R) e) A, B ≠ A) ∧
    ((∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
        ∃ x : SecQ R e, conjSub x K = L) ∨ ECase1 R W e) := by
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
  refine ⟨⟨_, secImg_mem_secFam hJ₁, _, hedge⟩,
    ⟨_, secImg_mem_secFam hJ₁, _, ⟨secImg_mem_secFam hJ₂, _, hzz₁, hzz₂⟩,
      (secImg_ne_of_twins hΩ hc2' hJ₁ hJ₂ hc.std.hne hz hz').symm⟩, ?_⟩
  rcases hdich with h | h
  · exact Or.inl h
  · exact Or.inr (layer_pair_case1 hΩ h2 hc2' (p23_q8Section hc.std.perp hd.he2) hJ₁ hJ₂ hz hz'
      hR₁ hR₁' hR₁e hR₁'e hRD.2 hR'D.2 h)

theorem oddCent_exit_gen2 (hD4 : TwinCentRes.ModelFactD42) {n : ℕ} {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h : PerpHypS n Y R S t) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (htrans : ∀ K ∈ TwinDisc.secFam (Om R) c, ∀ L ∈ TwinDisc.secFam (Om R) c,
      ∃ x : SecQ R c, conjSub x K = L)
    (hedge : ∃ M ∈ TwinDisc.secFam (Om R) c, ∃ N : Subgroup (SecQ R c),
      N ∈ omegaNbr (TwinDisc.secFam (Om R) c) M)
    (htw : ∃ A ∈ TwinDisc.secFam (Om R) c, ∃ B ∈ twinSet (TwinDisc.secFam (Om R) c) A, B ≠ A) :
    ∀ K ∈ TwinDisc.secFam (Om R) c, ∀ z : SecQ R c, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set (SecQ R c))) = ⊥ := by
  have hS := p23_q8Section h hc2
  have hlt := secQ_card_lt h hc1
  have hF : TwinDisc.Q8TwinFamT (SecQ R c) (TwinDisc.secFam (Om R) c) :=
    ⟨hS, htrans, htw, fun K hK => TwinExitPf11.tightCore_of_mem_secFam hK⟩
  intro K hK z hz
  rcases TwinDisc.oddCent_dichotomy TwinCentRes.modelFactSp62 hD4 hcit hP hlt hF hedge with
    ⟨P, hPn, hP2, hmem⟩ | hall
  · exact TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal hS.oddFree hPn hP2 (hmem K hK z hz)
  · exact hall z hz.sq

variable {n : ℕ}

end U9

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
