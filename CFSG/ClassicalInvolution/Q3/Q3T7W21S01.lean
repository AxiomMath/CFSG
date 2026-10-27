module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z01
public import CFSG.ClassicalInvolution.Asc77.AscT7PA
public import CFSG.ClassicalInvolution.Q3.Q3T7W21B01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def SectionDConnected (Ω : Set (Subgroup G)) (c : G) : Prop :=
  CFSG.ClassicalInvolution.Disconnected.DConnected (quotFamily (ExactLayer.exactPair Ω c)
    (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)))

section Dconn


theorem dAdj_of_exactFamily (hΩ : Q3T7M.HM Ω) {c : G} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ ExactLayer.tqMembers Ω c) (hJ : J ∈ ExactLayer.tqMembers Ω c)
    (h : Disconnected.dAdj (ExactLayer.exactFamily Ω c) (ExactLayer.exactCore c K)
      (ExactLayer.exactCore c J)) : Disconnected.dAdj Ω K J := by
  rcases h with h1 | h1
  · exact Or.inl (ExactLayer.mem_omegaNbr_of_exactFamily hΩ hc2 hK hJ h1)
  · exact Or.inr (ExactLayer.mem_omegaNbr_of_exactFamily hΩ hc2 hJ hK h1)

theorem exists_conj_tqMembers_of_dconn (hΩ : Q3T7M.HM Ω) {c : G} (hc2 : c * c = 1)
    {B : Subgroup G} (hB : B ∈ ExactLayer.tqMembers Ω c) (hconn : SectionDConnected Ω c) :
    ∀ M ∈ ExactLayer.tqMembers Ω c, ∃ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)),
      ∃ J' ∈ ExactLayer.tqMembers Ω c, J' ∈ dComp Ω B ∧ M = conjSub n J' := by
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have hΩg : HypOmegaGen Ω := Q3T7.modU_toGen3 hΩ
  set Y := ExactLayer.exactLayer Ω c with hYdef
  set Λ : Set (Subgroup ↥Y) := ExactLayer.exactPair Ω c with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM Λ := ExactLayer.hypOmegaMod_exactPair hΩ hcA
  have hΛ' : Q3T7M.HM (quotFamily Λ N₀) := oddQuotHyp ↥Y Λ hΛ N₀ hN₀odd
  have hmemΛ : ∀ {J : Subgroup G}, J ∈ ExactLayer.tqMembers Ω c →
      (ExactLayer.exactCore c J).subgroupOf Y ∈ Λ := fun {J} hJ =>
    ⟨ExactLayer.exactCore c J, ExactLayer.exactCore_mem_exactFamily hJ,
      ExactLayer.exactCore_le_exactLayer hJ, rfl⟩
  have hexΛ : ∀ {L : Subgroup ↥Y}, L ∈ Λ → ∃ J ∈ ExactLayer.tqMembers Ω c,
      L = (ExactLayer.exactCore c J).subgroupOf Y := by
    rintro L ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩
    exact ⟨J, hJ, rfl⟩
  let good : Subgroup ↥Y → Prop := fun L => ∃ J ∈ ExactLayer.tqMembers Ω c,
    L = (ExactLayer.exactCore c J).subgroupOf Y ∧ J ∈ dComp Ω B
  have hstepΛ : ∀ {L L' : Subgroup ↥Y}, L' ∈ Λ → good L → Disconnected.dAdj Λ L L' → good L' := by
    intro L L' hL' hgood hadj
    obtain ⟨J, hJ, rfl, hJB⟩ := hgood
    obtain ⟨J', hJ', rfl⟩ := hexΛ hL'
    have h1 := T7P.dAdj_map hadj
    rw [Subgroup.map_subgroupOf_eq_of_le (ExactLayer.exactCore_le_exactLayer hJ),
      Subgroup.map_subgroupOf_eq_of_le (ExactLayer.exactCore_le_exactLayer hJ')] at h1
    exact ⟨J', hJ', rfl, hJB.tail ⟨hJ'.1, dAdj_of_exactFamily hΩ hcA hJ hJ' h1⟩⟩
  have hBΛ := hmemΛ hB
  intro M hM
  have hMΛ := hmemΛ hM
  obtain ⟨M', hM', hMeq, hMgood⟩ := T7P.exists_good_lift_D (N := N₀) good hBΛ
    ⟨B, hB, rfl, Relation.ReflTransGen.refl⟩
    (fun L hL L' hL' hgL hadj => by
      rcases hadj with hadj | hadj
      · obtain ⟨n, hn, hn'⟩ := C25J.exists_conj_omegaNbr_gen hΛ.toGen hΛ'.toGen hN₀odd hL hL' hadj
        have h1 := omegaNbr_conj hΛ.toGen.conjInvariant hn' (n⁻¹ : ↥Y)
        rw [conjSub_inv_conjSub] at h1
        have hnn : QuotientGroup.mk' N₀ n⁻¹ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (N₀.inv_mem hn)
        refine ⟨conjSub n⁻¹ L', hΛ.toGen.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact hstepΛ (hΛ.toGen.conjInvariant _ L' hL') hgL (Or.inl h1)
      · obtain ⟨n, hn, hn'⟩ := C25J.exists_conj_omegaNbr_gen hΛ.toGen hΛ'.toGen hN₀odd hL' hL hadj
        have hnn : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
        refine ⟨conjSub n L', hΛ.toGen.conjInvariant _ L' hL', ?_, ?_⟩
        · rw [AscQuot.map_conjSub, hnn, conjSub_one]
        · exact hstepΛ (hΛ.toGen.conjInvariant _ L' hL') hgL (Or.inr hn'))
    (hconn _ (map_mem_quotFamily hBΛ) _ (map_mem_quotFamily hMΛ))
  obtain ⟨n, hn, hMn⟩ := exists_conj_of_map_eq hΛ hN₀odd hM' hMΛ hMeq
  obtain ⟨J, hJ, rfl, hJB⟩ := hMgood
  have hnC : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    ExactLayer.exactLayer_le_centralizer Ω c n.2
  have hnO : (n : G) ∈ oddCoreOf Y := ⟨n, hn, rfl⟩
  refine ⟨(n : G), oddCoreOf_exactLayer_le hΩ.conjInvariant c hnO, J, hJ, hJB, ?_⟩
  have h3 : conjSub n ((ExactLayer.exactCore c J).subgroupOf Y) =
      (conjSub (n : G) (ExactLayer.exactCore c J)).subgroupOf Y := conjSub_subgroupOf Y n _
  rw [h3] at hMn
  have hle1 : ExactLayer.exactCore c M ≤ Y := ExactLayer.exactCore_le_exactLayer hM
  have hle2 : conjSub (n : G) (ExactLayer.exactCore c J) ≤ Y := by
    have := conjSub_mono (n := (n : G)) (ExactLayer.exactCore_le_exactLayer hJ)
    rwa [conjSub_eq_self_of_mem n.2] at this
  have h4 := congrArg (Subgroup.map Y.subtype) hMn
  rw [Subgroup.map_subgroupOf_eq_of_le hle1, Subgroup.map_subgroupOf_eq_of_le hle2] at h4
  have h5 : ExactLayer.exactCore c M = ExactLayer.exactCore c (conjSub (n : G) J) := by
    have h6 := ExactLayer.exactCore_conjSub (n : G) c J
    rw [conj_eq_of_mem_centralizer_singleton hnC] at h6
    rw [h4, h6]
  exact Q3T7.eq_of_exactCore3_eq hΩg hcA hM
    (ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hnC hJ) h5

variable {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.conjSub_mem_dComp_of_comm (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) {g : G}
    (hg : g * z = z * g) : conjSub g K ∈ dComp Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hg]
      _ = z := by group
  have hzg : IsUniqueInvolution (conjSub g K) z := by
    have := hz.conj g
    rwa [hgz] at this
  exact T7A.mem_dComp_of_mem_kPerp
    (Q3T7M.mem_kPerp_of_twin hΩ.toGen (hΩ.conjInvariant g K hK) hK hzg hz)

theorem Hyp21.exactLayer_u_le_sigmaGen_of_dconn (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) (hconn : SectionDConnected Ω u) :
    ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hJt : J ∈ ExactLayer.tqMembers Ω u := h.mem_tqMembers_u_J
  have hJd : J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (h.hJ.2 K (mem_twinSet_self hK hz))
  rw [ExactLayer.exactLayer_eq_iSup]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨M, hMt, rfl⟩ := hL
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ := exists_conj_tqMembers_of_dconn hΩ h.hu2 hJt hconn M hMt
  have hnz : n * z = z * n := h.oddCore_centralizer_u_comm hα hn
  have hnz' : n⁻¹ * z = z * n⁻¹ := by
    have h1 := congrArg (fun y => n⁻¹ * y * n⁻¹) hnz
    simpa [mul_assoc] using h1.symm
  have hg : conjSub n K ∈ dComp Ω K := h.conjSub_mem_dComp_of_comm hnz
  have hg' : conjSub n⁻¹ K ∈ dComp Ω K := h.conjSub_mem_dComp_of_comm hnz'
  have hσ := T7A.conjSub_sigmaGen_eq hΩ.conjInvariant hK hg hg'
  have hJ'K : J' ∈ dComp Ω K := hJd.trans hJ'd
  have hJ'le : J' ≤ sigmaGen Ω K := le_iSup₂_of_le J' hJ'K le_rfl
  have h2 := conjSub_mono (n := n) hJ'le
  rw [hσ, ← hM] at h2
  exact (ExactLayer.exactCore_le_left u M).trans h2

end Dconn

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
