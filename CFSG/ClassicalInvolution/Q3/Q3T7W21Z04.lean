module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z03
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z01
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z02
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Zt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.zt_of_not_sectionConnected (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hdisc : ¬ SectionConnected Ω u) :
    (∀ y ∈ ExactLayer.exactLayer Ω u,
        z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω u)) ∨
      (∀ y ∈ ExactLayer.exactLayer Ω u,
        (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω u)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hΩg : Disconnected.AschTight.HypOmegaGen Ω := Q3T7.modU_toGen3 hΩ
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hu2 : u * u = 1 := h.hu2
  have hu1 : u ≠ 1 := h.hu1
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.std.stand.below
  have hIH : Uniform.IH8T 3 1 (Nat.card G) := h.std.stand.ih
  have h3s : Q3T8.Asc77.T3.Thm3SectBelow (Nat.card G) :=
    Q3T7E.thm3SectBelow3_of_ih hBelow
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  obtain ⟨J', R, R', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := h.exists_frame
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hxC : x ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hF.hxy]
    have hc : x * y = y * x := hF.cRR' x hF.hx y hF.hy
    calc x * (x * y) = x * (y * x) := by rw [hc]
      _ = (x * y) * x := by group
  have hzC : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (T7A.z_comm_of_mem_sup hz (isUniqueInvolution_of_mem_twinSet hz h.std.hK') h.hu)
  have htC : t ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.htu
  set Y : Subgroup G := ExactLayer.exactLayer Ω u with hYdef
  set Λ : Set (Subgroup ↥Y) := ExactLayer.exactPair Ω u with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({u} : Set G) :=
      ExactLayer.exactLayer_le_centralizer Ω u
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * u = u * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x₁, -, y₁, -, hxy₁⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
    exact hu1 (T7A.eq_one_of_central ⟨x₁, y₁, hxy₁⟩ hcomm)
  have hΛ : Q3T7M.HM Λ := ExactLayer.hypOmegaMod_exactPair hΩ hcA
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : Q3T7M.HM (quotFamily Λ N₀) := oddQuotHyp ↥Y Λ hΛ N₀ hN₀odd
  have hltY : Nat.card ↥Y < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      fun h' => hYtop (Subgroup.eq_top_of_card_eq _ h')
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hgenΛ : omegaGen Λ = ⊤ :=
    omegaGen_restrictFamily_eq_top (ExactLayer.exactFamily Ω u) Y
      (ExactLayer.exactLayer_eq_iSup Ω u).symm
  have hgenQ : omegaGen (quotFamily Λ N₀) = ⊤ := omegaGen_quotFamily_eq_top Λ N₀ hgenΛ
  have hdis : ¬ CFSG.ClassicalInvolution.Asc77.T3.DStarConnected (quotFamily Λ N₀) := hdisc
  have hΛA : ∀ L ∈ Λ, AEmpty Λ L := h3s ↥Y hltY Λ hΛ hdis
  have hAΛ' : ∀ L ∈ quotFamily Λ N₀, AEmpty (quotFamily Λ N₀) L :=
    aEmpty_quotFamily hΛ hΛ' hN₀odd hΛA
  have hJmem : J ∈ ExactLayer.tqMembers Ω u :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hJΩ, T, hF.hT,
      hF.le_centralizer_u.1⟩
  have hJ'mem : J' ∈ ExactLayer.tqMembers Ω u :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hJ'Ω, T', hF.hT',
      hF.le_centralizer_u.2⟩
  have hJY : ExactLayer.exactCore u J ≤ Y := ExactLayer.exactCore_le_exactLayer hJmem
  have hJ'Y : ExactLayer.exactCore u J' ≤ Y := ExactLayer.exactCore_le_exactLayer hJ'mem
  have htJu : t ∈ ExactLayer.exactCore u J := by
    rw [ExactLayer.exactCore_def]
    exact ⟨h.ht.mem, htC⟩
  have htY : t ∈ Y := hJY htJu
  have hAΦ : T7H.exactImg Ω u J ∈ quotFamily Λ N₀ := T7H.exactImg_mem hJmem
  have hBΦ : T7H.exactImg Ω u J' ∈ quotFamily Λ N₀ := T7H.exactImg_mem hJ'mem
  have hAx : IsUniqueInvolution (T7H.exactImg Ω u J) (T7H.toBar Ω u t htY) :=
    T7H.exactImg_isUnique hΩ hcA hJmem h.ht htY
  have hBx : IsUniqueInvolution (T7H.exactImg Ω u J') (T7H.toBar Ω u t htY) :=
    T7H.exactImg_isUnique hΩ hcA hJ'mem hJ't htY
  have hTA : IsSylow2In T (ExactLayer.exactCore u J) :=
    (ExactLayer.isSylow2In_exactCore_iff hΩg hcA hJΩ hJmem.2).mpr ⟨hF.hT, hF.le_centralizer_u.1⟩
  have hT'A : IsSylow2In T' (ExactLayer.exactCore u J') :=
    (ExactLayer.isSylow2In_exactCore_iff hΩg hcA hJ'Ω hJ'mem.2).mpr
      ⟨hF.hT', hF.le_centralizer_u.2⟩
  have hJ'NJ : J' ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_twin hJ'Ω hJΩ hJ'ne hJ't h.ht
  have hT'N : T' ≤ Subgroup.normalizer ((ExactLayer.exactCore u J : Subgroup G) : Set G) :=
    fun s hs => mem_normalizer_iff_conjSub_eq.mpr (by
      have h6 := ExactLayer.exactCore_conjSub s u J
      rw [Balance.Bootstrap.conj_eq_of_mem_centralizer_singleton (hF.le_centralizer_u.2 hs),
        mem_normalizer_iff_conjSub_eq.mp (hJ'NJ (hF.hT'.1 hs))] at h6
      exact h6.symm)
  have hmemΛ : ∀ {M : Subgroup G}, M ∈ ExactLayer.tqMembers Ω u →
      (ExactLayer.exactCore u M).subgroupOf Y ∈ Λ := fun {M} hM =>
    ⟨ExactLayer.exactCore u M, ExactLayer.exactCore_mem_exactFamily hM,
      ExactLayer.exactCore_le_exactLayer hM, rfl⟩
  have hBnbr : T7H.exactImg Ω u J' ∈
      omegaNbr (quotFamily Λ N₀) (T7H.exactImg Ω u J) :=
    omegaNbr_map_of_commutes hΛ' hN₀odd (hmemΛ hJmem) (hmemΛ hJ'mem) (hTA.subgroupOf hJY)
      (hT'A.subgroupOf hJ'Y) (commutes_subgroupOf hF.cTT') (le_normalizer_subgroupOf_of_le hJY hT'N)
  have hxJ : x ∈ Balance.Bootstrap.trivialOnQuot J := by
    have hc2x : IsPGroup 2 (Subgroup.zpowers x) :=
      hF.hR.2.1.to_le (Subgroup.zpowers_le.mpr hF.hx)
    exact (ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2x hJΩ).mpr ⟨T, hF.hT, fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hF.cRT x hF.hx s hs).symm⟩
  have hxJ' : x ∈ Balance.Bootstrap.trivialOnQuot J' := by
    have hc2x : IsPGroup 2 (Subgroup.zpowers x) :=
      hF.hR.2.1.to_le (Subgroup.zpowers_le.mpr hF.hx)
    exact (ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2x hJ'Ω).mpr ⟨T', hF.hT', fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hF.cRT' x hF.hx s hs).symm⟩
  set α := CX.actW hΩ.conjInvariant u ⟨x, hxC⟩ with hαdef
  have hαα : α * α = CX.actW hΩ.conjInvariant u ⟨z, hzC⟩ := by
    rw [hαdef, ← map_mul]
    congr 1
    exact Subtype.ext hF.hx2
  have hα4 : α * α * (α * α) = 1 := by
    rw [hαα, ← map_mul]
    have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) = 1 :=
      Subtype.ext hz.sq
    rw [this, map_one]
  have key := sq_dichotomy_of_twin_pair (n := Nat.card G) hBelow hIH hlt hΛ' hOq hgenQ hAΛ' hdis
    hAΦ hBnbr hAx hBx α hα4 (actW_mul_inv_mem_oddCore hΩ hcA hJmem hxC hxJ)
    (actW_mul_inv_mem_oddCore hΩ hcA hJ'mem hxC hxJ')
  rcases key with h1 | h1
  · left
    exact (layerAut_eq_one_iff hΩ.conjInvariant hzC).mp (hαα ▸ h1)
  · right
    have htz : CX.actW hΩ.conjInvariant u ⟨t, htC⟩ = CX.actW hΩ.conjInvariant u ⟨z, hzC⟩ := by
      rw [CX.actW_eq_conj hΩ.conjInvariant htC htY, ← hαα, h1]
    have htzC : t * z ∈ Subgroup.centralizer ({u} : Set G) := Subgroup.mul_mem _ htC hzC
    refine (layerAut_eq_one_iff hΩ.conjInvariant htzC).mp ?_
    have e : (⟨t * z, htzC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) = ⟨t, htC⟩ * ⟨z, hzC⟩ := rfl
    rw [e, map_mul, ← htz, ← map_mul]
    have : (⟨t, htC⟩ * ⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) = 1 :=
      Subtype.ext h.ht.sq
    rw [this, map_one]

theorem c21_14_zt_proved : C21_14_ZT := fun _ _ _ _ _ _ _ _ _ _ _ _ h hdisc =>
  h.zt_of_not_sectionConnected hdisc

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
