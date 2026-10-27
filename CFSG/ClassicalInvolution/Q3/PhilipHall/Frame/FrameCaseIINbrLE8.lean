module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameBalIVertexDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSP
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameBalIVertex
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem FrameTwins.exists_sylow_centralized {Ω : Set (Subgroup G)} {M M' : Subgroup G} {m : G}
    (dM : FrameTwins Ω M M' m) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ Subgroup.normalizer (M : Set G)) (hTM' : T ≤ Subgroup.normalizer (M' : Set G))
    (hcM : ∀ y ∈ T, ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M)
    (hcM' : ∀ y ∈ T, ∀ k ∈ M', ⁅y, k⁆ ∈ oddCoreOf M')
    {x : G} (hx : x ∈ M ⊔ M') (hx2 : x * x = 1)
    (hTx : T ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ P : Subgroup G, IsSylow2In P (M ⊔ M') ∧ x ∈ P ∧ ∀ y ∈ T, ∀ p ∈ P, y * p = p * y := by
  have hTN : T ≤ Subgroup.normalizer ((M ⊔ M' : Subgroup G) : Set G) :=
    fun y hy => T3CII.mem_normalizer_sup (hTM hy) (hTM' hy)
  have hX2 : IsPGroup 2 (Subgroup.zpowers x) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hx2
  have hxT : x ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hTx hy))
  have hW2 : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers x) :=
    IsPGroup.to_sup_of_normal_left' hT2 hX2 (Subgroup.zpowers_le.mpr hxT)
  have hWN : T ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer ((M ⊔ M' : Subgroup G) : Set G) :=
    sup_le hTN (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hx))
  obtain ⟨P, hP, hPfix⟩ := Asc77.exists_sylow_normalized hW2 hWN
  have hNP : ∀ w ∈ T ⊔ Subgroup.zpowers x, w ∈ Subgroup.normalizer (P : Set G) :=
    fun w hw => mem_normalizer_iff_conjSub_eq.mpr (hPfix w hw)
  have hPx2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers x) :=
    IsPGroup.to_sup_of_normal_left' hP.2.1 hX2
      (Subgroup.zpowers_le.mpr (hNP x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
  have hPx : P ⊔ Subgroup.zpowers x = P :=
    hP.eq_of_le hPx2 (sup_le hP.1 (Subgroup.zpowers_le.mpr hx)) le_sup_left
  have hxP : x ∈ P := hPx ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hcN := commutator_mem_oddCore_sup dM.K'_le dM.K_le hcM hcM'
  refine ⟨P, hP, hxP, fun y hy p hp => ?_⟩
  have h1 : ⁅y, p⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNP y (Subgroup.mem_sup_left hy)) p).mp hp)
      (P.inv_mem hp)
  have h3 : ⁅y, p⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _)
    (hcN y hy p (hP.1 hp)) (hP.2.1.to_le (Subgroup.zpowers_le.mpr h1))
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem not_mem_twinSet_of_aviol {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {K L J₁ : Subgroup G} {z u : G} (hK : K ∈ Ω) (hL : L ∈ omegaNbr Ω K)
    (hv : AViol Ω K J₁ z u) : L ∉ twinSet Ω J₁ := by
  intro hLJ
  have h1 : K ∈ omegaNbr Ω L := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hL.1 hL
  have hKP := (Q3T7M.l6_3 G Ω hΩ J₁ hv.mem L hLJ).1
  have h2 : K ∈ KPerp Ω J₁ := by
    rw [hKP]
    exact Or.inr h1
  rcases h2 with h | h
  · exact hv.star.2.1 h.symm
  · exact hv.not_nbr (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hv.mem hK h)

end Sylow

section Vertex

variable {G : Type} [Group G] [Finite G]

theorem closure_triple_eq_mul_right (m x ℓ : G) :
    Subgroup.closure ({m, x, ℓ} : Set G) = Subgroup.closure ({m, x, ℓ * m} : Set G) := by
  have hm : m ∈ Subgroup.closure ({m, x, ℓ * m} : Set G) := Subgroup.subset_closure (by simp)
  have hc : ℓ * m ∈ Subgroup.closure ({m, x, ℓ * m} : Set G) := Subgroup.subset_closure (by simp)
  have hℓ : ℓ ∈ Subgroup.closure ({m, x, ℓ * m} : Set G) := by
    have := (Subgroup.closure ({m, x, ℓ * m} : Set G)).mul_mem hc
      ((Subgroup.closure ({m, x, ℓ * m} : Set G)).inv_mem hm)
    simpa using this
  have hm' : m ∈ Subgroup.closure ({m, x, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  have hℓ' : ℓ ∈ Subgroup.closure ({m, x, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro y (rfl | rfl | rfl)
    · exact hm
    · exact Subgroup.subset_closure (by simp)
    · exact hℓ
  · rintro y (rfl | rfl | rfl)
    · exact hm'
    · exact Subgroup.subset_closure (by simp)
    · exact (Subgroup.closure ({m, x, ℓ} : Set G)).mul_mem hℓ' hm'

theorem mem_trivialOnQuot_of_isUniqueInvolution {M : Subgroup G} {m : G}
    (hm : IsUniqueInvolution M m) : m ∈ Balance.Bootstrap.trivialOnQuot M := by
  refine ⟨Subgroup.le_normalizer hm.mem, fun y hy => ?_⟩
  have hc : m * y = y * m :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Sec6Gen.le_centralizer_of_isUniqueInvolution hm hy)).symm
  have : ⁅m, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
  rw [this]
  exact Subgroup.one_mem _

theorem vertexW_of_twins [FrameCore G] (hnab : ∃ x y : G, x * y ≠ y * x) {K₀ : Subgroup G}
    {M M' R R' : Subgroup G} {m x ℓ c : G}
    (dM : FrameTwins (CoreAssembly.conjClass K₀) M M' m)
    (hM : M ∈ CoreAssembly.conjClass K₀)
    (hR : IsSylow2In R M) (hR' : IsSylow2In R' M') (hxR : x ∈ R ⊔ R') (hx2 : x * x = 1)
    (hℓ2 : ℓ * ℓ = 1) (hℓ1 : ℓ ≠ 1) (hℓm : ℓ ≠ m) (hℓmc : ℓ * m = m * ℓ)
    (hℓx : ℓ * x = x * ℓ)
    (hℓM : ℓ ∈ Balance.Bootstrap.trivialOnQuot M) (hℓM' : ℓ ∈ Balance.Bootstrap.trivialOnQuot M')
    (hℓR : R ≤ Subgroup.centralizer ({ℓ} : Set G))
    (hℓR' : R' ≤ Subgroup.centralizer ({ℓ} : Set G))
    (hc : c = ℓ ∨ c = ℓ * m) :
    VertexW M M' R R' m x ℓ c := by
  have hm2 : m * m = 1 := dM.hz.sq
  have hMC : M ≤ Subgroup.centralizer ({m} : Set G) :=
    Sec6Gen.le_centralizer_of_isUniqueInvolution dM.hz
  have hM'C : M' ≤ Subgroup.centralizer ({m} : Set G) :=
    Sec6Gen.le_centralizer_of_isUniqueInvolution dM.hz'
  have hxM : x ∈ M ⊔ M' := sup_le_sup hR.1 hR'.1 hxR
  have hmx : m * x = x * m :=
    (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hMC hM'C hxM)).symm
  have hΩeq : CoreAssembly.conjClass M = CoreAssembly.conjClass K₀ :=
    TwinVtx.conjClass_eq_of_mem hM
  have hcomm2 : ∀ y : G, y * ℓ = ℓ * y → y * m = m * y → y * (ℓ * m) = (ℓ * m) * y := by
    intro y h1 h2
    calc y * (ℓ * m) = (y * ℓ) * m := by group
      _ = (ℓ * y) * m := by rw [h1]
      _ = ℓ * (y * m) := by group
      _ = ℓ * (m * y) := by rw [h2]
      _ = (ℓ * m) * y := by group
  have hcent_c : ∀ y : G, y * ℓ = ℓ * y → y * m = m * y → y ∈ Subgroup.centralizer ({c} : Set G) := by
    intro y h1 h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hc with rfl | rfl
    · exact h1
    · exact hcomm2 y h1 h2
  have hR_le : ∀ {Q : Subgroup G}, Q ≤ M ⊔ M' → Q ≤ Subgroup.centralizer ({ℓ} : Set G) →
      Q ≤ Subgroup.centralizer ({c} : Set G) := by
    intro Q hQ hQℓ y hy
    exact hcent_c y (Subgroup.mem_centralizer_singleton_iff.mp (hQℓ hy))
      (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hMC hM'C (hQ hy)))
  refine
    { nonabelian := hnab
      hyp := hΩeq ▸ dM.hyp
      twoGroup := dM.two M dM.mem
      card8 := dM.card8 M dM.mem R hR
      hzK := dM.hz
      hzK' := dM.hz'
      mem_K' := hΩeq ▸ dM.mem'
      ne := dM.ne
      hR := hR
      hR' := hR'
      t_mem := hxR
      tsq := hx2
      zt := hmx
      mem := ?_
      sq := ?_
      ne_one := ?_
      z_ne := ?_
      z_cent := hcent_c m hℓmc.symm rfl
      t_cent := hcent_c x hℓx.symm hmx.symm
      tqK := ?_
      tqK' := ?_
      R_le := hR_le (hR.1.trans le_sup_left) hℓR
      R'_le := hR_le (hR'.1.trans le_sup_right) hℓR'
      card_lt := ?_
      gen := ?_ }
  · rcases hc with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rcases hc with rfl | rfl
    · exact hℓ2
    · calc ℓ * m * (ℓ * m) = ℓ * (m * ℓ) * m := by group
        _ = ℓ * (ℓ * m) * m := by rw [hℓmc]
        _ = (ℓ * ℓ) * (m * m) := by group
        _ = 1 := by rw [hℓ2, hm2, one_mul]
  · rcases hc with rfl | rfl
    · exact hℓ1
    · intro h1
      apply hℓm
      calc ℓ = ℓ * m * m := by rw [mul_assoc, hm2, mul_one]
        _ = m := by rw [h1, one_mul]
  · rcases hc with rfl | rfl
    · exact fun h => hℓm h.symm
    · intro h1
      apply hℓ1
      calc ℓ = ℓ * m * m⁻¹ := by group
        _ = m * m⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel m
  · rcases hc with rfl | rfl
    · exact hℓM
    · exact Subgroup.mul_mem _ hℓM (mem_trivialOnQuot_of_isUniqueInvolution dM.hz)
  · rcases hc with rfl | rfl
    · exact hℓM'
    · exact Subgroup.mul_mem _ hℓM' (mem_trivialOnQuot_of_isUniqueInvolution dM.hz')
  ·
    have hc1 : c ≠ 1 := by
      rcases hc with rfl | rfl
      · exact hℓ1
      · intro h1
        apply hℓm
        calc ℓ = ℓ * m * m := by rw [mul_assoc, hm2, mul_one]
          _ = m := by rw [h1, one_mul]
    have hCtop : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
      intro htop
      have hz : c ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
      rw [FrameCore.center hnab, Subgroup.mem_bot] at hz
      exact hc1 hz
    exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
      (fun h' => hCtop ((Subgroup.card_eq_iff_eq_top _).mp h'))
  · rcases hc with rfl | rfl
    · rfl
    · exact closure_triple_eq_mul_right m x ℓ

theorem closure_mul_triple_eq (z u ℓ : G) :
    Subgroup.closure ({z * u, z, ℓ} : Set G) = Subgroup.closure ({z, u, ℓ} : Set G) := by
  have hz : z ∈ Subgroup.closure ({z * u, z, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  have hzu : z * u ∈ Subgroup.closure ({z * u, z, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  have hu : u ∈ Subgroup.closure ({z * u, z, ℓ} : Set G) := by
    have := (Subgroup.closure ({z * u, z, ℓ} : Set G)).mul_mem
      ((Subgroup.closure ({z * u, z, ℓ} : Set G)).inv_mem hz) hzu
    simpa using this
  have hz' : z ∈ Subgroup.closure ({z, u, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  have hu' : u ∈ Subgroup.closure ({z, u, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro y (rfl | rfl | rfl)
    · exact (Subgroup.closure ({z, u, ℓ} : Set G)).mul_mem hz' hu'
    · exact hz'
    · exact Subgroup.subset_closure (by simp)
  · rintro y (rfl | rfl | rfl)
    · exact hz
    · exact hu
    · exact Subgroup.subset_closure (by simp)

end Vertex

section Assembly

theorem hyp51At_of_frameL {G : Type} [Group G] [Finite G] [FrameCore G] (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (hM12 : ModelFactM12) (hT4 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n)
    (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hB : Thm3A.Thm3RBelowG (Nat.card G)) (hcit : CIT3Below (Nat.card G))
    (hP : TL4.TightBelowRPlus 3 (Nat.card G))
    (hnab : ∃ x y : G, x * y ≠ y * x) {K₀ : Subgroup G}
    {M M' L T : Subgroup G} {m x ℓ c : G}
    (dM : FrameTwins (CoreAssembly.conjClass K₀) M M' m) (hM : M ∈ CoreAssembly.conjClass K₀)
    (hLΩ : L ∈ CoreAssembly.conjClass K₀) (hTsyl : IsSylow2In T L) (hℓ : IsUniqueInvolution L ℓ)
    (hℓm : ℓ ≠ m) (hTm : T ≤ Subgroup.centralizer ({m} : Set G))
    (hxM : x ∈ M ⊔ M') (hx2 : x * x = 1) (hTx : T ≤ Subgroup.centralizer ({x} : Set G))
    (hc : c = ℓ ∨ c = ℓ * m) :
    Hyp51At (Subgroup.closure ({m, x, ℓ} : Set G)) c := by
  have hΩ := dM.hyp
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hT8 : Nat.card T = 8 := dM.card8 L hLΩ T hTsyl
  have hℓT : ℓ ∈ T := mem_of_isPGroup hℓ hTsyl.1 hT2 (by omega)
  have hLM : L ≠ M := fun e => hℓm (hℓ.eq (by rw [e]; exact dM.hz))
  have hLM' : L ≠ M' := fun e => hℓm (hℓ.eq (by rw [e]; exact dM.hz'))
  have hTM : T ≤ Subgroup.normalizer (M : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ dM.mem hLΩ hLM.symm dM.hz hTsyl.1 hT2 (by omega) hTm
  have hTM' : T ≤ Subgroup.normalizer (M' : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ dM.mem' hLΩ hLM'.symm dM.hz' hTsyl.1 hT2 (by omega)
      hTm
  have hcM : ∀ y ∈ T, ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M := fun y hy k hk =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ dM.mem hLΩ hLM.symm
      dM.hz hℓ hTsyl hTm (Subgroup.commutator_mem_commutator hy hk)
  have hcM' : ∀ y ∈ T, ∀ k ∈ M', ⁅y, k⁆ ∈ oddCoreOf M' := fun y hy k hk =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ dM.mem' hLΩ hLM'.symm
      dM.hz' hℓ hTsyl hTm (Subgroup.commutator_mem_commutator hy hk)
  obtain ⟨P, hPsyl, hxP, hTP⟩ := dM.exists_sylow_centralized hT2 hTM hTM' hcM hcM' hxM hx2 hTx
  obtain ⟨hR, hR'⟩ := dM.isSylow2In_inf_of_isSylow2In_sup hPsyl
  have hxR : x ∈ (M ⊓ P) ⊔ (M' ⊓ P) := by
    rw [← dM.eq_sup_inf hPsyl]
    exact hxP
  have hℓR : ∀ {Q : Subgroup G}, Q ≤ P → Q ≤ Subgroup.centralizer ({ℓ} : Set G) :=
    fun hQ r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hTP ℓ hℓT r (hQ hr)).symm
  have hw := vertexW_of_twins hnab dM hM hR hR' hxR hx2 hℓ.sq hℓ.ne_one hℓm
    (Subgroup.mem_centralizer_singleton_iff.mp (hTm hℓT))
    (Subgroup.mem_centralizer_singleton_iff.mp (hTx hℓT))
    ⟨hTM hℓT, fun k hk => hcM ℓ hℓT k hk⟩ ⟨hTM' hℓT, fun k hk => hcM' ℓ hℓT k hk⟩
    (hℓR inf_le_right) (hℓR inf_le_right) hc
  exact hyp51At_of_vertexW hSp hD4 hM12 hT4 hU hM12fin hM12nab hG2 hB hcit hP hw

theorem frameHyp51L_holds : FrameHyp51L := by
  intro G _ _ _ K J z t a g h hT hcit hP L T ℓ hL hLtw hTsyl hTN hℓ J₁ u hv hTu
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := h.hyp
  have d := h.twin_facts
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hLΩ : L ∈ CoreAssembly.conjClass K := hL.1
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hT8 : Nat.card T = 8 := d.card8 L hLΩ T hTsyl
  have hℓT : ℓ ∈ T := mem_of_isPGroup hℓ hTsyl.1 hT2 (by omega)
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' d.hz hTN
  obtain ⟨huK, hu2, hu1, huz, huzc⟩ := d.isAInv_facts ⟨J₁, hv⟩
  obtain ⟨M₁, hvM⟩ := IsAInv.mul_involution hΩ hK ⟨J₁, hv⟩
  have hℓz : ℓ ≠ z := fun e => hLtw ⟨hLΩ, z, d.hz, e ▸ hℓ⟩
  have hℓu : ℓ ≠ u := fun e =>
    not_mem_twinSet_of_aviol hΩ hK hL hv ⟨hLΩ, u, hv.hzJ, e ▸ hℓ⟩
  have hℓzu : ℓ ≠ z * u := fun e =>
    not_mem_twinSet_of_aviol hΩ hK hL hvM ⟨hLΩ, z * u, hvM.hzJ, e ▸ hℓ⟩
  have hzℓ : z * ℓ = ℓ * z := (Subgroup.mem_centralizer_singleton_iff.mp (hTz hℓT)).symm
  have huℓ : u * ℓ = ℓ * u := (Subgroup.mem_centralizer_singleton_iff.mp (hTu hℓT)).symm
  have hzu : z * u = u * z := huzc.symm
  have hTzu : T ≤ Subgroup.centralizer ({z * u} : Set G) := by
    intro y hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hTz hy)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hTu hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (z * u) = (y * z) * u := by group
      _ = (z * y) * u := by rw [h1]
      _ = z * (y * u) := by group
      _ = z * (u * y) := by rw [h2]
      _ = z * u * y := by group
  have hmod := And.intro TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
  have hKfr : ∀ {c : G}, c = ℓ ∨ c = ℓ * z →
      Hyp51At (Subgroup.closure ({z, u, ℓ} : Set G)) c := fun hc =>
    hyp51At_of_frameL hmod.1 hmod.2 TwinCentRes.modelFactM12_of_certs
      TwinThmEW.t4Supply_of_twoClass frameOuterFixedOddFree_PSU3
      (CFSG.Sporadic.Mathieu.fam_m12_simplicity).1 m12_nonabelian g2ModelInnerOddFree_holds
      hT hcit hP h.nonabelian d hK hLΩ hTsyl hℓ hℓz hTz huK hu2 hTu hc
  have hvJ : AViol (CoreAssembly.conjClass K) J₁ K u z := aviol_symm_of_hypOmegaGen hΩ hK hv
  obtain ⟨J₁', dJ⟩ := h.twinPair_of_aviol hv.mem hvJ
  have hzJ : z ∈ J₁ ⊔ J₁' := IsAInv.mem_sup dJ ⟨K, hvJ⟩
  have hJfr : Hyp51At (Subgroup.closure ({u, z, ℓ} : Set G)) (ℓ * u) :=
    hyp51At_of_frameL hmod.1 hmod.2 TwinCentRes.modelFactM12_of_certs
      TwinThmEW.t4Supply_of_twoClass frameOuterFixedOddFree_PSU3
      (CFSG.Sporadic.Mathieu.fam_m12_simplicity).1 m12_nonabelian g2ModelInnerOddFree_holds
      hT hcit hP h.nonabelian dJ hv.mem hLΩ hTsyl hℓ hℓu hTu hzJ d.hz.sq hTz (Or.inr rfl)
  have hvM' : AViol (CoreAssembly.conjClass K) M₁ K (z * u) z :=
    aviol_symm_of_hypOmegaGen hΩ hK hvM
  obtain ⟨M₁', dM⟩ := h.twinPair_of_aviol hvM.mem hvM'
  have hzM : z ∈ M₁ ⊔ M₁' := IsAInv.mem_sup dM ⟨K, hvM'⟩
  have hMfr : Hyp51At (Subgroup.closure ({z * u, z, ℓ} : Set G)) (ℓ * (z * u)) :=
    hyp51At_of_frameL hmod.1 hmod.2 TwinCentRes.modelFactM12_of_certs
      TwinThmEW.t4Supply_of_twoClass frameOuterFixedOddFree_PSU3
      (CFSG.Sporadic.Mathieu.fam_m12_simplicity).1 m12_nonabelian g2ModelInnerOddFree_holds
      hT hcit hP h.nonabelian dM hvM.mem hLΩ hTsyl hℓ hℓzu hTzu hzM d.hz.sq hTz (Or.inr rfl)
  have hBJ : Subgroup.closure ({u, z, ℓ} : Set G) = Subgroup.closure ({z, u, ℓ} : Set G) := by
    rw [Set.insert_comm]
  rw [hBJ] at hJfr
  rw [closure_mul_triple_eq] at hMfr
  have hBE : IsElemAbelian 2 (Subgroup.closure ({z, u, ℓ} : Set G)) :=
    T8T.isElemAbelian_closure_three d.hz.sq hu2 hℓ.sq hzu hzℓ huℓ
  have hnot : ℓ ∉ Subgroup.closure ({z, u} : Set G) := by
    intro hmem
    rcases ChainFrame.mem_closure_four d.hz.sq hu2 hzu hmem with e | e | e | e
    · exact hℓ.ne_one e
    · exact hℓz e
    · exact hℓu e
    · exact hℓzu e
  have hB8 : Nat.card ↥(Subgroup.closure ({z, u, ℓ} : Set G)) = 8 :=
    T7B.natCard_closure_three_eq_eight d.hz.sq hu2 hℓ.sq d.hz.ne_one hu1 (Ne.symm huz)
      hℓ.ne_one hzu hzℓ huℓ hnot
  have hcent : ∀ x ∈ Subgroup.closure ({z, u, ℓ} : Set G),
      ∀ y ∈ Subgroup.closure ({z, u, ℓ} : Set G), x ∈ Subgroup.centralizer ({y} : Set G) :=
    fun x hx y hy => Lemma52Proof.le_centralizer_of_mem hBE hy hx
  have hzB : z ∈ Subgroup.closure ({z, u, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, ℓ} : Set G) := Subgroup.subset_closure (by simp)
  have hzuB : z * u ∈ Subgroup.closure ({z, u, ℓ} : Set G) := Subgroup.mul_mem _ hzB huB
  have hzu1 : z * u ≠ 1 := fun e => huz (by
    calc u = z * (z * u) := by rw [← mul_assoc, d.hz.sq, one_mul]
      _ = z := by rw [e, mul_one])
  have hzuz : z ≠ z * u := fun e => hu1 (by
    calc u = z⁻¹ * (z * u) := by group
      _ = z⁻¹ * z := by rw [← e]
      _ = 1 := inv_mul_cancel z)
  have hVz : Hyp51At (Subgroup.closure ({z, u, ℓ} : Set G)) z :=
    hyp51At_of_tightInO2_image hBE hzB d.hz.ne_one huB hu1 huz (hcent u huB z hzB)
      (tightInO2_of_twinProduct h hK d.hz d.ne d.twins huK (hcent u huB z hzB))
  have hVu : Hyp51At (Subgroup.closure ({z, u, ℓ} : Set G)) u :=
    hyp51At_of_tightInO2_image hBE huB hu1 hzB d.hz.ne_one (Ne.symm huz) (hcent z hzB u huB)
      (tightInO2_of_twinProduct h hv.mem hv.hzJ dJ.ne dJ.twins hzJ (hcent z hzB u huB))
  have hVzu : Hyp51At (Subgroup.closure ({z, u, ℓ} : Set G)) (z * u) :=
    hyp51At_of_tightInO2_image hBE hzuB hzu1 hzB d.hz.ne_one hzuz (hcent z hzB (z * u) hzuB)
      (tightInO2_of_twinProduct h hvM.mem hvM.hzJ dM.ne dM.twins hzM (hcent z hzB (z * u) hzuB))
  refine ⟨hBE, hB8, fun c hcB hc1 => ?_⟩
  rcases T8T.mem_closure_three_involutions d.hz.sq hu2 hℓ.sq hzu hzℓ huℓ hcB with
    e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · rw [e]; exact hVz
  · rw [e]; exact hVu
  · exact hKfr (Or.inl e)
  · rw [e]; exact hVzu
  · rw [e, hzℓ]; exact hKfr (Or.inr rfl)
  · rw [e, huℓ]; exact hJfr
  · have e' : z * u * ℓ = ℓ * (z * u) := by
      calc z * u * ℓ = z * (u * ℓ) := by group
        _ = z * (ℓ * u) := by rw [huℓ]
        _ = (z * ℓ) * u := by group
        _ = (ℓ * z) * u := by rw [hzℓ]
        _ = ℓ * (z * u) := by group
    rw [e, e']; exact hMfr

theorem frameCaseIITG_proved : FrameCaseIITG :=
  frameCaseIITG_of_hyp51L frameHyp51L_holds

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
