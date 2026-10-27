module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Conn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

section Triple

variable {H : Type} [Group H] [Finite H] {Λ : Set (Subgroup H)} {N : Subgroup H} [N.Normal]

theorem map_ne_of_commutes_sylow_gen (hΛ' : HypOmegaGen (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {M₁ M₂ V₁ V₂ : Subgroup H} (hM₁ : M₁ ∈ Λ)
    (hV₁ : IsSylow2In V₁ M₁) (hV₂ : IsSylow2In V₂ M₂) (hc : Commutes V₁ V₂) :
    M₁.map (QuotientGroup.mk' N) ≠ M₂.map (QuotientGroup.mk' N) := by
  intro heq
  set mk := QuotientGroup.mk' N with hmk
  have h1 : IsSylow2In (V₁.map mk) (M₁.map mk) := isSylow2In_map_mk hN hV₁
  have h2 : IsSylow2In (V₂.map mk) (M₁.map mk) := heq ▸ isSylow2In_map_mk hN hV₂
  have hc' : Commutes (V₁.map mk) (V₂.map mk) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have hP : IsPGroup 2 ↥(V₁.map mk ⊔ V₂.map mk) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes hc'.symm)
  have hsup : V₁.map mk ⊔ V₂.map mk ≤ M₁.map mk := sup_le h1.1 h2.1
  have hle : V₂.map mk ≤ V₁.map mk := by
    have := h1.eq_of_le hP hsup le_sup_left
    rw [← this]
    exact le_sup_right
  have heqV : V₁.map mk = V₂.map mk := h2.eq_of_le h1.2.1 h1.1 hle
  have hRset : V₁.map mk ∈ RSet (quotFamily Λ N) :=
    mem_RSet_of_isSylow2In (map_mem_quotFamily hM₁) h1
  obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΛ' hRset).exists_not_commute
  exact hxy (hc' x hx y (heqV ▸ hy))

theorem twinTriple_quot_gen (hΛ' : HypOmegaGen (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {K K' J R R' T : Subgroup H} (hK : K ∈ Λ) (hK' : K' ∈ twinSet Λ K)
    (hJ : J ∈ Λ) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hT : IsSylow2In T J)
    (hRR' : Commutes R R') (hRT : Commutes R T) (hR'T : Commutes R' T)
    (hTK : T ≤ Subgroup.normalizer (K : Set H)) (hTK' : T ≤ Subgroup.normalizer (K' : Set H)) :
    TwinTriple (quotFamily Λ N) := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hK'Λ, z, hzK, hzK'⟩ := hK'
  have hKK' : K'.map mk ≠ K.map mk :=
    map_ne_of_commutes_sylow_gen hΛ' hN hK'Λ hR' hR hRR'.symm
  have hJK : J.map mk ≠ K.map mk := map_ne_of_commutes_sylow_gen hΛ' hN hJ hT hR hRT.symm
  have hJK' : J.map mk ≠ K'.map mk := map_ne_of_commutes_sylow_gen hΛ' hN hJ hT hR' hR'T.symm
  have hTset : T.map mk ∈ RSet (quotFamily Λ N) :=
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJ) (isSylow2In_map_mk hN hT)
  refine ⟨K.map mk, map_mem_quotFamily hK, K'.map mk,
    ⟨map_mem_quotFamily hK'Λ, mk z, isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
      isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩, hKK',
    J.map mk, ⟨map_mem_quotFamily hJ, hJK, T.map mk, hTset, Subgroup.map_mono hT.1, ?_⟩,
    ⟨map_mem_quotFamily hJ, hJK', T.map mk, hTset, Subgroup.map_mono hT.1, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_map (hTK hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_map (hTK' hx)

end Triple

section SecTriple

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem twinTriple_secFam (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K K' J R R' T : Subgroup G} {z : G} (hK : K ∈ tqMembers3 Ω c) (hK'tq : K' ∈ tqMembers3 Ω c)
    (hJ : J ∈ tqMembers3 Ω c) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K)
    (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hT : IsSylow2In T J)
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G)) (hR'c : R' ≤ Subgroup.centralizer ({c} : Set G))
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G))
    (hRR' : Commutes R R') (hRT : Commutes R T) (hR'T : Commutes R' T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTK' : T ≤ Subgroup.normalizer (K' : Set G)) :
    TwinTriple (secFam Ω c) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := coreHull Ω c with hX
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ' : HypOmegaGen (secFam Ω c) := hypOmegaGen_secFam hΩ hc2
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have e1 : TwinADescent.coreAt c K' ∈
      twinSet (TwinADescent.coreFamily Ω c) (TwinADescent.coreAt c K) :=
    ⟨TwinADescent.coreAt_mem_coreFamily hK'tq, z, isUniqueInvolution_coreAt_of_tq hΩ hc2 hK hz,
      isUniqueInvolution_coreAt_of_tq hΩ hc2 hK'tq hzK'⟩
  have e2 := twinSet_subgroupOf (TwinADescent.coreAt_le_centralizer c K)
    (TwinADescent.coreAt_le_centralizer c K') e1
  have e3 := twinSet_subgroupOf (le_coreHull hK) (le_coreHull hK'tq) e2
  have hRs : IsSylow2In R (TwinADescent.coreAt c K) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hK.2).mpr ⟨hR, hRc⟩
  have hR's : IsSylow2In R' (TwinADescent.coreAt c K') :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hK'tq.2).mpr ⟨hR', hR'c⟩
  have hTs : IsSylow2In T (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hT, hTc⟩
  have hRX := (hRs.subgroupOf (TwinADescent.coreAt_le_centralizer c K)).subgroupOf (le_coreHull hK)
  have hR'X := (hR's.subgroupOf (TwinADescent.coreAt_le_centralizer c K')).subgroupOf
    (le_coreHull hK'tq)
  have hTX := (hTs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf (le_coreHull hJ)
  have hTn : ∀ {L : Subgroup G}, T ≤ Subgroup.normalizer (L : Set G) →
      T ≤ Subgroup.normalizer ((TwinADescent.coreAt c L : Subgroup G) : Set G) := by
    intro L hTL x hx
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have h6 := TwinADescent.conjSub_coreAt (hTc hx) L
    rw [mem_normalizer_iff_conjSub_eq.mp (hTL hx)] at h6
    exact h6
  have hTKX := le_normalizer_subgroupOf_of_le (le_coreHull hK)
    (le_normalizer_subgroupOf_of_le (TwinADescent.coreAt_le_centralizer c K) (hTn hTK))
  have hTK'X := le_normalizer_subgroupOf_of_le (le_coreHull hK'tq)
    (le_normalizer_subgroupOf_of_le (TwinADescent.coreAt_le_centralizer c K') (hTn hTK'))
  exact twinTriple_quot_gen hΛ' hodd (subgroupOf_mem_hullFam hK) e3 (subgroupOf_mem_hullFam hJ)
    hRX hR'X hTX (commutes_subgroupOf (commutes_subgroupOf hRR'))
    (commutes_subgroupOf (commutes_subgroupOf hRT))
    (commutes_subgroupOf (commutes_subgroupOf hR'T)) hTKX hTK'X

end SecTriple

section Main


variable {n : ℕ}

@[expose] def DStarConnectedTwinQ8Below (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), HypOmegaGen Φ →
    (∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) →
    (∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2)) →
    classicalInvolutionOddCore X = ⊥ → (∀ J ∈ Φ, AEmpty Φ J) → omegaGen Φ = ⊤ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → TwinTriple Φ → T3.DStarConnected Φ

theorem discSecConnTz_of (hT4 : Thm4RTwinBelow 3 n) (hMF : DStarConnectedTwinQ8Below n) :
    DiscSecConnTz n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα M hM N hN
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, hRR', hRT, hR'T⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hf.mem hf.hz hf.hK' hf.hne hf.hJ
  have h8R : 8 ≤ Nat.card R₀ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.mem hR₀)
  have h8T : 8 ≤ Nat.card T₀ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.hJ.1 hT₀)
  have hzR : z ∈ R₀ := mem_of_isUniqueInvolution_of_isPGroup hf.hz hR₀.1 hR₀.2.1 (by omega)
  have htT : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup hf.ht hT₀.1 hT₀.2.1 (by omega)
  have hzt : z * t = t * z := hRT z hzR t htT
  have hcsq : (t * z) * (t * z) = 1 := by
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hzt]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [hf.ht.sq, hf.hz.sq, one_mul]
  have hc2 : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcsq
  have hcomm : ∀ x : Y, x * t = t * x → x * z = z * x → x * (t * z) = (t * z) * x := by
    intro x hxt hxz
    calc x * (t * z) = (x * t) * z := by group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = (t * z) * x := by group
  have hRc : R₀ ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hRT x hx t htT) (hf.hz.commute_of_mem (hR₀.1 hx)).symm
      exact this)
  have hR'c : R₀' ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hR'T x hx t htT) (hK'.commute_of_mem (hR₀'.1 hx)).symm
      exact this)
  have hTc : T₀ ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hf.ht.commute_of_mem (hT₀.1 hx)).symm (hRT z hzR x hx).symm
      exact this)
  have hKtq : K ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.mem, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.mem ⟨R₀, hR₀, hRc⟩⟩
  have hK'tq : K' ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.hK'.1 ⟨R₀', hR₀', hR'c⟩⟩
  have hJtq : J ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.hJ.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.hJ.1 ⟨T₀, hT₀, hTc⟩⟩
  have hJK : J ≠ K := (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)).2.1
  have hJK' : J ≠ K' := (hf.hJ.2 K' hf.hK').2.1
  have hTz : T₀ ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTK : T₀ ≤ Subgroup.normalizer (K : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hf.mem hf.hJ.1 hJK.symm hf.hz hT₀.1 hT₀.2.1
      (by omega) hTz
  have hTK' : T₀ ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hf.hK'.1 hf.hJ.1 hJK'.symm hK' hT₀.1 hT₀.2.1
      (by omega) hTz
  have htt : TwinTriple (secFam Ω (t * z)) :=
    twinTriple_secFam hΩ hc2 hKtq hK'tq hJtq hf.hz hf.hK' hR₀ hR₀' hT₀ hRc hR'c hTc hRR' hRT hR'T
      hTK hTK'
  have hMtq : M ∈ tqMembers3 Ω (t * z) := ⟨hM.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hM.1 hM.2⟩
  have hNtq : N ∈ tqMembers3 Ω (t * z) := ⟨hN.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hN.1 hN.2⟩
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2' : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2']; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hlt : Nat.card (↥(coreHull Ω (t * z)) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω (t * z))) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s htz1)
  have hconn : ∀ M' ∈ secFam Ω (t * z),
      M' ∈ dstarComp (secFam Ω (t * z)) (secImg Ω (t * z) M) := by
    rcases dichotomy_secFam hT4 hlt hΩ hc2 h2 hq hA hMtq with hconn | horb
    · exact hconn
    · have htrans : ∀ K₁ ∈ secFam Ω (t * z), ∀ L ∈ secFam Ω (t * z),
          ∃ g : ↥(coreHull Ω (t * z)) ⧸ classicalInvolutionOddCore ↥(coreHull Ω (t * z)),
            conjSub g K₁ = L := by
        intro K₁ hK₁ L hL
        obtain ⟨y₁, hy₁⟩ := horb K₁ hK₁
        obtain ⟨y₂, hy₂⟩ := horb L hL
        exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
      have hgen : omegaGen (secFam Ω (t * z)) = ⊤ :=
        omegaGen_quotFamily_eq_top _ _
          (omegaGen_restrictFamily_eq_top (cFam Ω (t * z)) (coreHull Ω (t * z)) rfl)
      have hD := hMF _ hlt (secFam Ω (t * z)) (hypOmegaGen_secFam hΩ hc2) (secFam_twoGroup h2)
        (secFam_q8 hc2 hq) oddCore_quot_eq_bot (secFam_aEmpty hΩ hA hc2) hgen htrans htt
      intro M' hM'
      exact hD _ (secImg_mem_secFam hMtq) M' hM'
  exact secPath_of_connected hΩ hc2 hMtq le_rfl hconn N hNtq

end Main

section Assembly


variable {n : ℕ}

structure TwinDiscInputsPf5 (n : ℕ) : Prop where
  thmE : TwinThmE n
  base : TwinDiscBase n
  c13Exc : Disc13NExc n
  c14Exc : Disc14NExc n
  c14AltExc : Disc14AltExc n
  normCent : DiscNormCent n
  thm4 : Thm4RTwinBelow 3 n
  model : DStarConnectedTwinQ8Below n

theorem TwinDiscInputsPf5.toPf4 (I : TwinDiscInputsPf5 n) : Pf2.TwinDiscInputsPf4 n where
  thmE := I.thmE
  base := I.base
  c13Exc := I.c13Exc
  c14Exc := I.c14Exc
  c14AltExc := I.c14AltExc
  normCent := I.normCent
  secConnTz := discSecConnTz_of I.thm4 I.model
  secConnU := discSecConnU_of I.thm4

end Assembly

end TwinDisc


theorem twinCoreDiscPerp_of_inputsPf5 {n : ℕ} (I : TwinDisc.TwinDiscInputsPf5 n) :
    TwinCoreDiscPerp n :=
  twinCoreDiscPerp_of_inputsPf4 I.toPf4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
