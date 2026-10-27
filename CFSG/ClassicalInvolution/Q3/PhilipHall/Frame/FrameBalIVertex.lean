module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameBalIVertexDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GBar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205QMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Vertex

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' R R' : Subgroup G} {z t a c : G}

theorem hyp51At_of_liftedAtW (hcit : CIT3Below (Nat.card G)) (hw : VertexW K K' R R' z t a c)
    (l : LiftedAt K c z) (l' : LiftedAt K' c z) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hB := hw.isElemAbelian_B
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have hz1 : z ≠ 1 := hw.hzK.ne_one
  have hZ : Subgroup.center G = ⊥ := FrameCore.center hw.nonabelian
  obtain ⟨M, hM, hKM⟩ := l
  obtain ⟨M', hM', hKM'⟩ := l'
  rw [tgt_coreAt_eq] at hKM hKM'
  refine TwinFrame.hyp51At_of_classicalOrQuiet_inner hcit hZ TL4.d4OddAutInnerNC3_proved hB
    hw.gen hw.ne_one hz1 hw.z_ne hw.z_cent hw.t_cent (Or.inl ⟨M, hM⟩) ?_
  intro L hL hmov
  have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hw.ne_one (by
    have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton _)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 hM hM' hM
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hcit hsnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c M M' M)
  have hMz : IsUniqueInvolution M z := isUniqueInvolution_of_sectionMember3 hM
  have hM'z : IsUniqueInvolution M' z := isUniqueInvolution_of_sectionMember3 hM'
  have hzj : oddQuotMk c ⟨z, hw.z_cent⟩ ∈ secComp hΦ D j :=
    hj (oddQuotMk_mem_modOdd hMz.mem hw.z_cent)
  have hzmov : ∃ w ∈ L, oddQuotMk c ⟨z, hw.z_cent⟩ * w ≠ w * oddQuotMk c ⟨z, hw.z_cent⟩ :=
    hmov _ (oddQuotMk_mem_modOdd hzB hw.z_cent)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hw.mem hw.ne_one hzB hz1 hw.z_ne hw.z_cent)
  have hLj : L = secComp hΦ D j := eq_secComp_of_not_commute hΦ D hzj hL hzmov
  subst hLj
  have hM'j : modOdd c M' ≤ secComp hΦ D j :=
    Q3T7.modOdd_twin_le_secComp3 hΦ D hB hw.mem hw.ne_one hzB hz1 hw.z_ne hw.z_cent hmov hL
      (mem_sFamily3_two c M M' M) hM'z.mem
  have hRj : ∀ r ∈ R, ∀ hrC : r ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨r, hrC⟩ ∈ secComp hΦ D j := by
    intro r hr hrC
    have hcore : r ∈ TwinADescent.coreAt c K :=
      le_tightCore_of_isPGroup (le_inf hw.hR.1 hw.R_le) hw.hR.2.1 hr
    exact hj (oddQuotMk_mem_modOdd (hKM hcore) hrC)
  have hR'j : ∀ r ∈ R', ∀ hrC : r ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨r, hrC⟩ ∈ secComp hΦ D j := by
    intro r hr hrC
    have hcore : r ∈ TwinADescent.coreAt c K' :=
      le_tightCore_of_isPGroup (le_inf hw.hR'.1 hw.R'_le) hw.hR'.2.1 hr
    exact hM'j (oddQuotMk_mem_modOdd (hKM' hcore) hrC)
  have hRQ : R.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      (secComp hΦ D j).comap (oddQuotMk c) := fun x hx =>
    hRj x.1 (Subgroup.mem_subgroupOf.mp hx) x.2
  have hR'Q : R'.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      (secComp hΦ D j).comap (oddQuotMk c) := fun x hx =>
    hR'j x.1 (Subgroup.mem_subgroupOf.mp hx) x.2
  have hsup : (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      (secComp hΦ D j).comap (oddQuotMk c) := by
    rw [Subgroup.subgroupOf_sup hw.R_le hw.R'_le]
    exact sup_le hRQ hR'Q
  exact hsup (Subgroup.mem_subgroupOf.mpr hw.t_mem :
    (⟨t, hw.t_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)))

theorem hyp51At_of_quotEmptyW (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hT4 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n)
    (hcit : CIT3Below (Nat.card G)) (hP : TL4.TightBelowRPlus 3 (Nat.card G))
    (hw : VertexW K K' R R' z t a c)
    (hKe : AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K c).map (oqMk ↥(Subgroup.centralizer ({c} : Set G)))))
    (hK'e : AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K' c).map (oqMk ↥(Subgroup.centralizer ({c} : Set G))))) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hB := hw.isElemAbelian_B
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have hz1 : z ≠ 1 := hw.hzK.ne_one
  have hc2' := hw.isPGroup_zpowers
  have hΛeq := omegaAFam_centralizer_eq_cFam hw.hyp
    (TwinADescent3.isPGroup_two_quotient_conjClass hw.twoGroup) hc2'
  have hKm := frameKa_mem_omegaAFamW hw
  have hK'm := frameKa'_mem_omegaAFamW hw
  rw [hΛeq] at hKe hK'e hKm hK'm
  have hΛ : HypOmegaGen (TwinDisc.cFam (CoreAssembly.conjClass K) c) :=
    TwinADescent.hypOmegaGen_coreFamily hw.hyp hc2'
  have hPB : PairBarEmpty (frameKa K c) (frameKa K' c) :=
    pairBarEmpty_of_bar hΛ hKm hK'm hKe hK'e
  have hPB' : PairBarEmpty (frameKa K' c) (frameKa K c) :=
    pairBarEmpty_of_bar hΛ hK'm hKm hK'e hKe
  have hPB₁ : PairBarEmpty (tightCore (K.subgroupOf (Subgroup.centralizer ({c} : Set G))))
      ((TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
    rw [TwinExitPf2.tightCore_subgroupOf_cent]
    exact hPB
  have hPB₂ : PairBarEmpty (tightCore (K'.subgroupOf (Subgroup.centralizer ({c} : Set G))))
      ((TwinADescent.coreAt c K).subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
    rw [TwinExitPf2.tightCore_subgroupOf_cent]
    exact hPB'
  have h4 := hT4 _ hcit hP
  obtain ⟨ψ⟩ := hw.typeRHyp.sylow K (CoreAssembly.mem_conjClass_self K) R hw.hR
  obtain ⟨ψ'⟩ := hw.typeRHyp.sylow K' hw.mem_K' R' hw.hR'
  have tK := tri_of_pair_bar hSp hD4 h4 hP hw.hyp hw.twoGroup (CoreAssembly.mem_conjClass_self K)
    hw.mem_K' hw.ne hw.hzK hw.hzK' hw.hR ⟨ψ⟩ hw.sq hw.ne_one
    (by simpa using hw.card_lt) hw.tqK hw.tqK' hw.z_cent hPB₁
  have tK' := tri_of_pair_bar hSp hD4 h4 hP hw.hyp hw.twoGroup hw.mem_K'
    (CoreAssembly.mem_conjClass_self K) (fun h => hw.ne h.symm) hw.hzK' hw.hzK hw.hR' ⟨ψ'⟩ hw.sq
    hw.ne_one (by simpa using hw.card_lt) hw.tqK' hw.tqK hw.z_cent hPB₂
  rcases tK with q | l | ⟨e, m⟩
  · exact hyp51At_of_quiet hB hw.mem hzB hw.ne_one hz1 hw.z_ne hw.z_cent q
  · rcases tK' with q' | l' | ⟨e', m'⟩
    · exact hyp51At_of_quiet hB hw.mem hzB hw.ne_one hz1 hw.z_ne hw.z_cent q'
    · obtain ⟨-, S₁, h₁⟩ := secCoreHyp_of_member hP hw.hyp hw.twoGroup
        (CoreAssembly.mem_conjClass_self K) hw.hzK hw.hR ⟨ψ⟩
      obtain ⟨-, S₂, h₂⟩ := secCoreHyp_of_member hP hw.hyp hw.twoGroup hw.mem_K'
        hw.hzK' hw.hR' ⟨ψ'⟩
      exact hyp51At_of_liftedAtW hcit hw (AzTri.liftedAt_of_liftedAtSec h₁ l)
        (AzTri.liftedAt_of_liftedAtSec h₂ l')
    · exact hyp51At_of_exit hSp hD4 hM12 hB hw.mem hzB hw.ne_one hz1 hw.z_ne hw.z_cent e' m'
  · exact hyp51At_of_exit hSp hD4 hM12 hB hw.mem hzB hw.ne_one hz1 hw.z_ne hw.z_cent e m

theorem hyp51At_of_moved_vertexGW (hw : VertexW K K' R R' z t a c)
    {T : Subgroup (Balance.OddQuot c)}
    (hzT : Balance.oddQuotMk c ⟨z, hw.z_cent⟩ ∈ T)
    (htT : Balance.oddQuotMk c ⟨t, hw.t_cent⟩ ∈ T)
    (hU : ∀ L₁ L₂ : Subgroup (Balance.OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, Balance.oddQuotMk c ⟨z, hw.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hw.z_cent⟩) →
      (∃ y ∈ L₂, Balance.oddQuotMk c ⟨z, hw.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hw.z_cent⟩) →
        L₁ = L₂)
    (hAO : ∀ L : Subgroup (Balance.OddQuot c), CFSG.IsComponent L →
      (∃ y ∈ L, Balance.oddQuotMk c ⟨z, hw.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hw.z_cent⟩) →
        Q3NM.AutOddFree ↥L ∨ (Q3NM.AutOddFreeInner ↥L ∧
          ∀ y ∈ T, ∃ l ∈ L, ∀ w ∈ L, y * w * y⁻¹ = l * w * l⁻¹)) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hB := hw.isElemAbelian_B
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have hBle := modOdd_B_le_sup_centerW hw hzT htT
  refine TL4.hyp51At_of_moved (fun b hb => (pow_two b).symm.trans (hB.2 b hb))
    (fun b hb b' hb' => congrArg Subtype.val
      (hB.1.is_comm.comm (⟨b, hb⟩ : Subgroup.closure ({z, t, a} : Set G)) ⟨b', hb'⟩))
    ⟨Balance.oddQuotMk c ⟨z, hw.z_cent⟩, Balance.oddQuotMk_mem_modOdd hzB hw.z_cent,
      Lemma52Proof.oddQuotMk_not_mem_zpowers hB hw.mem hw.ne_one hzB hw.hzK.ne_one hw.z_ne
        hw.z_cent, hU⟩ ?_
  intro L hL hm x hx hxN hxmv
  rcases hAO L hL (exists_not_comm_of_movedByAllW hw hm) with h | ⟨hin, hact⟩
  · exact h.on _
  · obtain ⟨l, hlL, hl⟩ := exists_inner_of_mem_sup_center hact (hBle hx)
    exact hin.toOn.mono fun σ hσ => mem_innSubgroup_of_isInducedAut hσ hlL hl

theorem hyp51At_of_quotViolGW_aux (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hw : VertexW K K' R R' z t a c) (hB : Thm3A.Thm3RBelowG (Nat.card G))
    {M₀ : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    (hM₀ : M₀ = frameKa K c ∨ M₀ = frameKa K' c)
    (hA : ¬ AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(Subgroup.centralizer ({c} : Set G)))))) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hTR := typeRHyp_omegaAFam hw.typeRHyp (Subgroup.centralizer ({c} : Set G))
  have hz2 : (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨z, hw.z_cent⟩ = 1 :=
    Subtype.ext hw.hzK.sq
  have hz1' : (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ≠ 1 := fun e =>
    hw.hzK.ne_one (congrArg Subtype.val e)
  have hMmem : M₀ ∈ omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G)) := by
    rcases hM₀ with rfl | rfl
    · exact frameKa_mem_omegaAFamW hw
    · exact frameKa'_mem_omegaAFamW hw
  have hzM : (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ M₀ := by
    rcases hM₀ with rfl | rfl
    · exact z_mem_frameKaW hw
    · exact z_mem_frameKa'W hw
  have hconcl := thm3RConclG_oddQuot_of_quotViol hB hw.card_lt hTR hMmem hA
  obtain ⟨hUq, hAOq⟩ :=
    hyp51_of_thm3BarG hU hM12 hM12fin hM12nab hG2 hTR hMmem hconcl hzM hz2 hz1'
  obtain ⟨hK₁, hK₂⟩ := frameKa_map_mem_aStarW hw hM₀
  have hMT := le_omegaGen (self_mem_aStar (Ω := oddQuotientFamily (omegaAFam
    (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G))))
    (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G))))))
  exact hyp51At_of_moved_vertexGW hw (hMT (Subgroup.mem_map_of_mem _ hzM))
    (oddQuotMk_t_memW hw (le_omegaGen hK₁) (le_omegaGen hK₂)) hUq hAOq

theorem hyp51At_of_quotViolGW (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hw : VertexW K K' R R' z t a c) (hB : Thm3A.Thm3RBelowG (Nat.card G))
    (hA : (¬ AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K c).map (QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(Subgroup.centralizer ({c} : Set G)))))) ∨
      (¬ AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K' c).map (QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(Subgroup.centralizer ({c} : Set G))))))) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c :=
  hA.elim
    (fun h => hyp51At_of_quotViolGW_aux hU hM12 hM12fin hM12nab hG2 hw hB (Or.inl rfl) h)
    (fun h => hyp51At_of_quotViolGW_aux hU hM12 hM12fin hM12nab hG2 hw hB (Or.inr rfl) h)

theorem hyp51At_of_vertexW (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hT4 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n)
    (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hB : Thm3A.Thm3RBelowG (Nat.card G)) (hcit : CIT3Below (Nat.card G))
    (hP : TL4.TightBelowRPlus 3 (Nat.card G)) (hw : VertexW K K' R R' z t a c) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  by_cases h1 : AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
      (Subgroup.centralizer ({c} : Set G))))
        ((frameKa K c).map (oqMk ↥(Subgroup.centralizer ({c} : Set G))))
  · by_cases h2 : AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K' c).map (oqMk ↥(Subgroup.centralizer ({c} : Set G))))
    · exact hyp51At_of_quotEmptyW hSp hD4 hM12 hT4 hcit hP hw h1 h2
    · exact hyp51At_of_quotViolGW hU hM12 hM12fin hM12nab hG2 hw hB (Or.inr h2)
  · exact hyp51At_of_quotViolGW hU hM12 hM12fin hM12nab hG2 hw hB (Or.inl h1)

end Vertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
