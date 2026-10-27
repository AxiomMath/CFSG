module

public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwSp
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwSpin
public import CFSG.ClassicalInvolution.AschTight.S19KUni
public import CFSG.ClassicalInvolution.AschTight.S19KUniFL
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTri

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Q3.Q3NS CFSG.Assembly.LowTwoRank CFSG.Assembly.Dichotomy

section Twin


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

theorem oddCoreIn_layer_fixed_le_of_conj_N [Finite ι] (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hk : FixedOddFree ((D.kind i).G ⧸ Subgroup.center (D.kind i).G) ∨
      FixedOddFreeFund (D.kind i))
    {g : G} (hne : g * z₁ * g⁻¹ ≠ z₁)
    (hKb : K₁ ≤ Subgroup.centralizer ({g * z₁ * g⁻¹} : Set G))
    (hzb : z₂ * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * z₂) :
    oddCoreIn (centralizingLayer (conjClass3 K) {g * z₁ * g⁻¹} ⊓
        Subgroup.centralizer ({z₁ * z₂} : Set G)) ≤
      oddCoreIn (centralizingLayer (conjClass3 K) {g * z₁ * g⁻¹}) := by
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  obtain ⟨i₁, -, -, -, -, hoth, hz1⟩ := layer_of_N hR hnab h hN hXN D hi
  have hK₁b : K₁ ∈ centralizingMembers (conjClass3 K) {g * z₁ * g⁻¹} := ⟨h.mem₁, hKb⟩
  rw [centralizingMembers_conj hΩ.conjInvariant g z₁] at hK₁b
  obtain ⟨K', hK'm, hK'eq⟩ := hK₁b
  obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K', hK'm, rfl⟩)
  have hjeq : j = i := by
    by_contra hji
    obtain ⟨m', hm'⟩ := hΩ.classical K' hK'm.1
    have hcls : IsClassicalMember3 K₁ (g * m' * g⁻¹) := by
      have := hm'.conj g
      rwa [hK'eq] at this
    have hm'z : g * m' * g⁻¹ = z₁ := involution_unique3 hcls h.cls₁
    have hm'z1 : m' = z₁ := hz1 j hji K' ⟨hK'm, hj⟩ m' hm'
    rw [hm'z1] at hm'z
    exact hne hm'z
  have hK'c : K' ∈ compMembers3 (conjClass3 K) z₁ D i := ⟨hK'm, hjeq ▸ hj⟩
  obtain ⟨R, -, hRf, hRK⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hK'c
  have hxb : (z₁ * z₂) * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * (z₁ * z₂) := by
    have hz1' : z₁ * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * z₁ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKb h.cls₁.mem)
    calc z₁ * z₂ * (g * z₁ * g⁻¹) = z₁ * (z₂ * (g * z₁ * g⁻¹)) := mul_assoc _ _ _
      _ = z₁ * ((g * z₁ * g⁻¹) * z₂) := by rw [hzb]
      _ = (z₁ * (g * z₁ * g⁻¹)) * z₂ := (mul_assoc _ _ _).symm
      _ = ((g * z₁ * g⁻¹) * z₁) * z₂ := by rw [hz1']
      _ = (g * z₁ * g⁻¹) * (z₁ * z₂) := mul_assoc _ _ _
  have hab : g⁻¹ * (z₁ * z₂) * g ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (z₁ * z₂) * g * z₁ = g⁻¹ * ((z₁ * z₂) * (g * z₁ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z₁ * g⁻¹) * (z₁ * z₂)) * g := by rw [hxb]
      _ = z₁ * (g⁻¹ * (z₁ * z₂) * g) := by group
  have ha2 : orderOf (g⁻¹ * (z₁ * z₂) * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (z₁ * z₂)
    rw [h.orderOf_prod] at this
    simpa [MulAut.conj_apply] using this
  have hK'a : K' ≤ Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' : g * y * g⁻¹ ∈ K₁ := by
      rw [← hK'eq]
      exact conj_mem_conjSub hy
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_prod₁ hy')
    calc y * (g⁻¹ * (z₁ * z₂) * g) = g⁻¹ * ((g * y * g⁻¹) * (z₁ * z₂)) * g := by group
      _ = g⁻¹ * ((z₁ * z₂) * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * (z₁ * z₂) * g * y := by group
  have hO' := oddCoreIn_layer_fixed_le_of_components hΩ.conjInvariant ModelFacts.modelClauseZero
    m11Facts hab ha2 D fun j => by
      by_cases hji : j = i
      · subst hji
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr ⟨hk, R, hRf, K', hK'm, hK'a, hRK⟩
      · exact Or.inl (fixedOddFree_of_kind_sl23 (hoth j hji))
  have hlay : centralizingLayer (conjClass3 K) {g * z₁ * g⁻¹} =
      conjSub g (centralizingLayer (conjClass3 K) {z₁}) :=
    centralizingLayer_conj hΩ.conjInvariant g z₁
  have hcen : Subgroup.centralizer ({z₁ * z₂} : Set G) =
      conjSub g (Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G)) := by
    ext y
    rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      calc g⁻¹ * y * g * (g⁻¹ * (z₁ * z₂) * g) = g⁻¹ * (y * (z₁ * z₂)) * g := by group
        _ = g⁻¹ * ((z₁ * z₂) * y) * g := by rw [hy]
        _ = g⁻¹ * (z₁ * z₂) * g * (g⁻¹ * y * g) := by group
    · intro hy
      calc y * (z₁ * z₂) = g * ((g⁻¹ * y * g) * (g⁻¹ * (z₁ * z₂) * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * (z₁ * z₂) * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hy]
        _ = (z₁ * z₂) * y := by group
  have hinf : conjSub g (centralizingLayer (conjClass3 K) {z₁} ⊓
        Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G)) =
      conjSub g (centralizingLayer (conjClass3 K) {z₁}) ⊓
        conjSub g (Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G)) := by
    ext y
    simp only [mem_conjSub_iff, Subgroup.mem_inf]
  rw [hlay, hcen, ← hinf, oddCoreIn_conjSub_eq, oddCoreIn_conjSub_eq]
  exact conjSub_mono hO'

theorem involutionOddCore_prod_eq_bot_of_parity_N [Finite ι] (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hk : FixedOddFree ((D.kind i).G ⧸ Subgroup.center (D.kind i).G) ∨
      FixedOddFreeFund (D.kind i))
    (hP : ParityAt K K₁ z₁ z₂) : involutionOddCore (z₁ * z₂) = ⊥ := by
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  refine involutionOddCore_prod_eq_bot_of_parityAt hOA hR hnab h hP
    fun w hw hne hKw hwz => ?_
  obtain ⟨M, hM, hclM⟩ := hw
  obtain ⟨g, hg⟩ : M ∈ conjClass3 K₁ := hcl ▸ hM
  have hg' : conjSub g K₁ = M := hg
  have hwg : w = g * z₁ * g⁻¹ := by
    have := h.cls₁.conj g
    rw [hg'] at this
    exact involution_unique3 hclM this
  subst hwg
  exact oddCoreIn_layer_fixed_le_of_conj_N hR hnab h hN hXN D hi hk hne hKw hwz.symm

theorem parityAt_of_kleinAt (h : EdgeData K K₁ K₂ z₁ z₂)
    (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂)) (hKl : KleinAt K K₁ z₂) :
    ParityAt K K₁ z₁ z₂ := by
  obtain ⟨M₁, M₂, w₁, hM₁, hM₂, c₁, c₂, hK₁, hcomm, -⟩ := hKl
  have hxx : z₁ * z₂ = z₂ * z₁ := h.mul_comm₁₂
  have hw1 : w₁ * w₁ = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two c₁.orderOf_eq_two
  have hK₁₂ : K₁ ≤ Subgroup.centralizer ({z₂ * w₁} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have a1 : y * z₂ = z₂ * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer₂ hy)
    have a2 : y * w₁ = w₁ * y := Subgroup.mem_centralizer_singleton_iff.mp (hK₁ hy)
    calc y * (z₂ * w₁) = (y * z₂) * w₁ := (mul_assoc _ _ _).symm
      _ = z₂ * (y * w₁) := by rw [a1, mul_assoc]
      _ = z₂ * (w₁ * y) := by rw [a2]
      _ = (z₂ * w₁) * y := (mul_assoc _ _ _).symm
  have hz₂₂ : (z₂ * w₁) * z₂ = z₂ * (z₂ * w₁) := by
    calc (z₂ * w₁) * z₂ = z₂ * (w₁ * z₂) := mul_assoc _ _ _
      _ = z₂ * (z₂ * w₁) := by rw [hcomm]
  have hprod : w₁ * (z₂ * w₁) = z₂ := by
    calc w₁ * (z₂ * w₁) = (w₁ * z₂) * w₁ := (mul_assoc _ _ _).symm
      _ = (z₂ * w₁) * w₁ := by rw [hcomm]
      _ = z₂ * (w₁ * w₁) := mul_assoc _ _ _
      _ = z₂ := by rw [hw1, mul_one]
  refine ⟨{w₁, z₂ * w₁}, ?_, Subgroup.subset_closure ⟨w₁, by simp, z₂ * w₁, by simp, hprod⟩⟩
  intro w hw
  rcases hw with hw | hw
  · rw [hw]
    refine ⟨⟨M₁, hM₁, c₁⟩, ?_, hK₁, hcomm⟩
    intro heq
    apply hXN M₂ hM₂ (z₂ * w₁) c₂
    rw [heq]
    exact hxx.symm
  · rw [Set.mem_singleton_iff] at hw
    rw [hw]
    refine ⟨⟨M₂, hM₂, c₂⟩, ?_, hK₁₂, hz₂₂⟩
    intro heq
    apply hXN M₁ hM₁ w₁ c₁
    calc w₁ = z₂ * (z₂ * w₁) := by rw [← mul_assoc, h.sq₂, one_mul]
      _ = z₂ * z₁ := by rw [heq]
      _ = z₁ * z₂ := hxx.symm

@[expose] def TwinKindsMF : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), ListedTwin3 t n → StatedLieAdmissible t n 3 1 →
    MFComp (CompData.model t n)

theorem parityData_bot_odd {c : CompData} {n : ℕ} (hc : c = CompData.model .POmegaOdd n)
    (hadm : StatedLieAdmissible .POmegaOdd n 3 1) : ParityData c ⊥ := by
  subst hc
  exact parityData_pOmegaOdd hadm

theorem parityData_bot_plus {c : CompData} {n : ℕ} (hc : c = CompData.model .POmegaPlus n)
    (hadm : StatedLieAdmissible .POmegaPlus n 3 1) : ParityData c ⊥ := by
  subst hc
  exact parityData_pOmegaPlus hadm

theorem parityData_bot_minus {c : CompData} {n : ℕ} (hc : c = CompData.model .POmegaMinus n)
    (hadm : StatedLieAdmissible .POmegaMinus n 3 1) : ParityData c ⊥ := by
  subst hc
  exact parityData_pOmegaMinus hadm

theorem parityAt_and_mf_of_N [Finite ι] (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hG2 : MFComp (CompData.model .G2 0)) (hTD4 : MFComp (CompData.model .trialityD4 0))
    (hTw : TwinKindsMF) : ParityAt K K₁ z₁ z₂ ∧ MFComp (D.kind i) := by
  obtain ⟨-, -, -, -, hnA1, -, -⟩ := layer_of_N hR hnab h hN hXN D hi
  rcases D.valid i with ⟨t, n, hfund, hadm, hk⟩ | hsl | hm
  · by_cases hexc : t = .G2 ∨ t = .trialityD4
    · rcases hexc with rfl | rfl
      · exact ⟨parityAt_of_kleinAt h hXN (h.kleinAt_of_kleinData hR D hi
          (by rw [hk]; exact kleinData_g2 hadm)), by rw [hk]; exact hG2⟩
      · exact ⟨parityAt_of_kleinAt h hXN (h.kleinAt_of_kleinData hR D hi
          (by rw [hk]; exact kleinData_trialityD4 hadm)), by rw [hk]; exact hTD4⟩
    · push Not at hexc
      obtain ⟨hG2', hD4⟩ := hexc
      rcases tag_cases3 hfund hadm hG2' hD4 (not_psl_two_of_admissible hadm) with hconn | hsmall
      · exact (false_of_connected_third hR hnab h hN hXN D hi hk hfund hadm hG2' hD4 hconn).elim
      · rcases hsmall with ⟨ht, hn3⟩ | hlisted
        · subst hn3
          refine ⟨parityAt_of_kleinAt h hXN (kleinAt_of_chainKleinData hR h D hi
            (by rw [hk]; exact chainKleinData_model ht le_rfl)), ?_⟩
          rcases ht with rfl | rfl
          · rw [hk]
            exact mfComp_psl3
          · rw [hk]
            exact mfComp_psu3
        · refine ⟨?_, by rw [hk]; exact hTw t n hlisted hadm⟩
          rcases hlisted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩
          · obtain ⟨N, R₀, S₀, r₀, s₀, hPD, hR₀f, hS₀f, hcomm, hr₀R, hr₀2, hr₀1, hs₀S, hs₀2, hs₀1,
              hcen, hNdef⟩ := psp_data hk hadm
            have hker := commKer_of_third hR hnab h hN hXN D hi hPD.fund hPD.conj hPD.single
              hR₀f hS₀f hcomm hr₀R hr₀2 hr₀1 hs₀S hs₀2 hs₀1 hcen
            have hNker : N ≤ (D.hom i).ker := by
              rw [hNdef]
              exact Subgroup.zpowers_le.mpr hker
            exact parityAt_of_parityData hR h D hi hNker hnA1 hPD
          · exact parityAt_of_kleinAt h hXN (kleinAt_of_chainKleinData hR h D hi
              (by rw [hk]; exact chainKleinData_model (Or.inl rfl) (by norm_num)))
          · exact parityAt_of_kleinAt h hXN (kleinAt_of_chainKleinData hR h D hi
              (by rw [hk]; exact chainKleinData_model (Or.inr rfl) (by norm_num)))
          · exact parityAt_of_parityData hR h D hi (N := ⊥) bot_le hnA1
              (parityData_bot_odd hk hadm)
          · exact parityAt_of_parityData hR h D hi (N := ⊥) bot_le hnA1
              (parityData_bot_plus hk hadm)
          · exact parityAt_of_parityData hR h D hi (N := ⊥) bot_le hnA1
              (parityData_bot_minus hk hadm)
  · exact absurd hsl hnA1
  · exact ⟨parityAt_of_kleinAt h hXN (h.kleinAt_of_m11 hR D hi hm), by rw [hm]; exact mfComp_m11⟩

theorem involutionOddCore_prod_eq_bot_of_N [Finite ι] (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hG2 : MFComp (CompData.model .G2 0)) (hTD4 : MFComp (CompData.model .trialityD4 0))
    (hTw : TwinKindsMF) : involutionOddCore (z₁ * z₂) = ⊥ := by
  obtain ⟨hP, hk⟩ := parityAt_and_mf_of_N hR hnab h hN hXN D hi hG2 hTD4 hTw
  exact involutionOddCore_prod_eq_bot_of_parity_N hOA hR hnab h hN hXN D hi hk hP

theorem alphaCore_edge_eq_bot_of_twin_N (hOA : OddAutLayerRigidHyp) (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (hG2 : MFComp (CompData.model .G2 0)) (hTD4 : MFComp (CompData.model .trialityD4 0))
    (hTw : TwinKindsMF) : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ := by
  obtain ⟨ι, hι, ⟨D⟩⟩ := h.exists_lieSystem_z₁ hR hnab
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  obtain ⟨i, hi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₂, hK₂, rfl⟩)
  have hP := involutionOddCore_prod_eq_bot_of_N hOA hR hnab h hN hXN D hi hG2 hTD4 hTw
  have hlay := oddCoreIn_centralizingLayer_le hR.inClass.conjInvariant (z₁ * z₂)
  rw [hP] at hlay
  exact h.alphaCore_edge_eq_bot_of_oddCoreIn_layer_eq_bot hR (le_bot_iff.mp hlay)

end Twin

theorem hTwin_of_mfComp
    (hOA : OddAutLayerRigidHyp) (hG2 : MFComp (CompData.model .G2 0))
    (hTD4 : MFComp (CompData.model .trialityD4 0)) (hTw : TwinKindsMF) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
      RouteD3Setup K z → (∃ a b : G, a * b ≠ b * a) →
        ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), EdgeData K K₁ K₂ z₁ z₂ →
          EdgeThirdFree K K₁ K₂ z₁ z₂ → NonClassicalAt (conjClass3 K) (z₁ * z₂) →
          ¬ (TwinFreeAt (conjClass3 K) K₁ z₁ ∧ TwinFreeAt (conjClass3 K) K₂ z₂) →
            alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ := by
  intro G _ _ _ K z hR hnab K₁ K₂ z₁ z₂ h hN hXN _
  exact alphaCore_edge_eq_bot_of_twin_N hOA hR hnab h hN hXN hG2 hTD4 hTw

end CFSG.ClassicalInvolution.Q3.Q3OF
