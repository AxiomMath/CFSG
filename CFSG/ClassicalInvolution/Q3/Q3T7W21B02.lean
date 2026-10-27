module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2207
public import CFSG.ClassicalInvolution.Q3.Q3T7W21B01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
section Tz
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}
omit [IsSimpleGroup G] in

theorem Hyp21.mem_tqMembers_tz_K
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8T : 8 ≤ Nat.card T :=
    hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In h.hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  refine (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ
      (Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.tz_sq)).mpr
    ⟨hK, R, hRsyl, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hxz : x * z = z * x := (hz.commute_of_mem (hRsyl.1 hx)).symm
  have hxt : x * t = t * x := hRT x hx t htT
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [hxt]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [hxz]
    _ = (t * z) * x := by group

theorem Hyp21.sectionConnected_tz
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) :
        Q3T8.Asc77.SectionConnected Ω (t * z) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.std.stand.below
  set c : G := t * z with hcdef
  have hc2 : c * c = 1 := h.tz_sq
  have hc1 : c ≠ 1 := h.tz_ne_one
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
      hc2
  set A : Subgroup G := Subgroup.zpowers c with hAdef

  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hRsyl)
  have h8T : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJΩ hTsyl)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRsyl.1 hRsyl.2.1 (by omega)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  have hcomm_tz : ∀ x : G, x * t = t * x → x * z = z * x → x * c = c * x := by
    intro x hxt hxz
    calc x * c = (x * t) * z := by rw [hcdef]; group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = c * x := by rw [hcdef]; group
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz r (hRT r hr t htT) (hz.commute_of_mem (hRsyl.1 hr)).symm)
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz r (hR'T r hr t htT) (hzK'.commute_of_mem (hR'syl.1 hr)).symm)
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz x (h.ht.commute_of_mem (hTsyl.1 hx)).symm (hRT z hzR x hx).symm)

  have hKt : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hK, R, hRsyl, hRc⟩
  have hK't : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hK'Ω, R', hR'syl, hR'c⟩
  have hJt : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hJΩ, T, hTsyl, hTc⟩
  have hΩg : Disconnected.AschTight.HypOmegaGen Ω := Q3T7.modU_toGen3 hΩ
  have hRA : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore c K) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩg hcA hK hKt.2).mpr ⟨hRsyl, hRc⟩
  have hR'A : IsSylow2In R' (Q3T8.Asc77.ExactLayer.exactCore c K') :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩg hcA hK'Ω hK't.2).mpr ⟨hR'syl, hR'c⟩
  have hTA : IsSylow2In T (Q3T8.Asc77.ExactLayer.exactCore c J) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩg hcA hJΩ hJt.2).mpr ⟨hTsyl, hTc⟩

  have hJK : J ≠ K := (h.hJ.2 K (mem_twinSet_self hK hz)).2.1
  have hJK' : J ≠ K' := (h.hJ.2 K' h.std.hK').2.1
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTNK : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hJΩ (Ne.symm hJK) hz hTsyl.1 hT2 (by omega) hTz
  have hTNK' : T ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK'Ω hJΩ (Ne.symm hJK') hzK' hTsyl.1 hT2
      (by omega) hTz
  have hTNKA : T ≤ Subgroup.normalizer
      ((Q3T8.Asc77.ExactLayer.exactCore c K : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_iff_conjSub_eq.mpr (by
      have h6 := Q3T8.Asc77.ExactLayer.exactCore_conjSub x c K
      rw [Balance.Bootstrap.conj_eq_of_mem_centralizer_singleton (hTc hx),
        mem_normalizer_iff_conjSub_eq.mp (hTNK hx)] at h6
      exact h6.symm)
  have hTNK'A : T ≤ Subgroup.normalizer
      ((Q3T8.Asc77.ExactLayer.exactCore c K' : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_iff_conjSub_eq.mpr (by
      have h6 := Q3T8.Asc77.ExactLayer.exactCore_conjSub x c K'
      rw [Balance.Bootstrap.conj_eq_of_mem_centralizer_singleton (hTc hx),
        mem_normalizer_iff_conjSub_eq.mp (hTNK' hx)] at h6
      exact h6.symm)
  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hYdef
  have hKY : Q3T8.Asc77.ExactLayer.exactCore c K ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hKt
  have hK'Y : Q3T8.Asc77.ExactLayer.exactCore c K' ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK't
  have hJY : Q3T8.Asc77.ExactLayer.exactCore c J ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJt
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω c) :=
    Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hcA
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : Q3T7M.HM (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      (classicalInvolutionOddCore ↥Y)) :=
    Q3T8.Asc77.oddQuotHyp ↥Y _ hΛ _ hN₀odd
  have hmemΛ : ∀ {M : Subgroup G}, M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c →
      (Q3T8.Asc77.ExactLayer.exactCore c M).subgroupOf Y ∈
        Q3T8.Asc77.ExactLayer.exactPair Ω c :=
    fun {M} hM => ⟨Q3T8.Asc77.ExactLayer.exactCore c M,
      Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hM,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hM, rfl⟩
  have htt : TwinTriple (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      (classicalInvolutionOddCore ↥Y)) :=
    Q3T8.Asc77.twinTriple_quot hΛ' hN₀odd (hmemΛ hKt)
      (twinSet_subgroupOf hKY hK'Y (Q3T7.exactCore3_mem_twinSet hΩ hcA hKt hK't h.std.hK'))
      (hmemΛ hJt) (hRA.subgroupOf hKY) (hR'A.subgroupOf hK'Y) (hTA.subgroupOf hJY)
      (commutes_subgroupOf hRR') (commutes_subgroupOf hRT) (commutes_subgroupOf hR'T)
      (le_normalizer_subgroupOf_of_le hKY hTNKA) (le_normalizer_subgroupOf_of_le hK'Y hTNK'A)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({c} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * c = c * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
    exact hc1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)
  have hconn : Q3T8.Asc77.SectionConnected Ω c :=
    Q3T8.Asc77.dstarConnected_quot_of_twinTriple_gen hΩ hcA hYtop h.std.stand.ih hBelow
      (h3s _ hBelow) hMF htt
  exact hconn

theorem Hyp21.centralizer_tz_le_normalizer_alpha
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen) (h3s : ∀ n, Q3T8.Generic.CITBelowU n →
        Q3T8.Asc77.T3.Thm3SectBelow n)
    (hs : Q3T8.Asc77.AlphaSteps) (heq : dComp Ω K = dstarComp Ω K) :
    Subgroup.centralizer ({t * z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  intro c' hc'
  have h1 : conjSub c' K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc' h.mem_tqMembers_tz_K
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ := Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ h.tz_sq
    h.mem_tqMembers_tz_K (h.sectionConnected_tz hMF h3s) _ h1
  have hnα : n ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
    have hzt : z * t = t * z := h.twinFrameData.comm_zt hΩ
    have hcz : (t * z) * z = z * (t * z) := by
      calc (t * z) * z = (z * t) * z := by rw [hzt]
        _ = z * (t * z) := by group
    have h2 := oddCoreOf_centralizer_le_normalizer_alphaOf (c := t * z) (z := z) h.std.hz.sq
      h.tz_ne_one hcz hn
    rwa [closure_tz_pair, hs.alpha_zt h] at h2
  have hJ'dc : J' ∈ dComp Ω K := by rw [heq]; exact hJ'd
  obtain ⟨x, hxN, hx⟩ := hs.exists_mem_normalizer h hJ'dc
  have hc'eq : conjSub c' K = conjSub (n * x) K := by rw [hM, ← hx, conjSub_mul]
  have hm : conjSub ((n * x)⁻¹ * c') K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmα : (n * x)⁻¹ * c' ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq hm)))
  have e : c' = (n * x) * ((n * x)⁻¹ * c') := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnα hxN) hmα
end Tz
section UFrame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}
omit [IsSimpleGroup G] in

theorem Hyp21.u_comm_z
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) : u * z = z * u :=
  (T7A.z_comm_of_mem_sup h.std.hz (isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK') h.hu).symm

theorem Hyp21.centralizer_u_le_normalizer_alpha
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hs : Q3T8.Asc77.AlphaSteps) (heq : dComp Ω K = dstarComp Ω K) (hconn :
        Q3T8.Asc77.SectionConnected Ω u) :
    Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := Q3T8.Asc77.exists_mem_tqMembers_u hΩ hK hz h.std.hK' h.std.hne
      h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := by rw [← heq]; exact hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ :=
    Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ h.hu2 hJ₀t hconn _ h1
  have hnα : n ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    oddCoreOf_centralizer_le_normalizer_alphaOf h.std.hz.sq h.hu1 h.u_comm_z hn
  have hJ'dc : J' ∈ dComp Ω K := by rw [heq, ← T7A.dstarComp_eq_of_mem hK hJ₀ds]; exact hJ'd
  obtain ⟨x, hxN, hx⟩ := hs.exists_mem_normalizer h hJ'dc
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer h hJ₀d
  have hc'eq : conjSub (c' * x₀) K = conjSub (n * x) K := by
    rw [conjSub_mul, hx₀, hM, ← hx, conjSub_mul]
  have hm : conjSub ((n * x)⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmα : (n * x)⁻¹ * (c' * x₀) ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (hz.conj_eq hm)))
  have e : c' = ((n * x) * ((n * x)⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnα hxN) hmα)
    (Subgroup.inv_mem _ hx₀N)
omit [IsSimpleGroup G] in

theorem Hyp21.rLayer_u_le_sigmaGen
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (heq : dComp Ω K = dstarComp Ω K) (hconn : SectionConnected Ω u) :
    ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hΩ hK hz h.std.hK' h.std.hne h.hu h.hu2
    h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := by rw [← heq]; exact hJ₀d
  rw [ExactLayer.exactLayer_eq_iSup]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨M, hMt, rfl⟩ := hL
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ :=
    exists_conj_tqMembers_of_connected hΩ h.hu2 hJ₀t hconn M hMt
  have hnz : n * z = z * n := h.oddCore_centralizer_u_comm hα hn
  have hnzn : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
      _ = z := by group
  have hKn : conjSub n K ∈ twinSet Ω K := ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj n⟩
  have hnσ : n ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (AscE186.mem_dstarComp_of_twin hΩ hK hKn)
  have hJ'ds : J' ∈ dstarComp Ω K := by rw [← T7A.dstarComp_eq_of_mem hK hJ₀ds]; exact hJ'd
  have hMd : M ∈ dComp Ω K := by
    rw [heq, hM]
    exact ((mem_sigmaStarNorm_iff.mp hnσ) J').mp hJ'ds
  exact (ExactLayer.exactCore_le_left u M).trans (le_iSup₂_of_le M hMd le_rfl)

end UFrame
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def C21_13_N_ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K →
        Subgroup.centralizer ({t * z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      ¬ (dComp Ω K = dstarComp Ω K ∧ Q3T8.Asc77.SectionConnected Ω u) →
        Subgroup.centralizer ({u} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_alt_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ →
        ¬ (dComp Ω K = dstarComp Ω K ∧ Q3T8.Asc77.SectionConnected Ω u) →
          ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K ∨
            Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)

theorem c21_13_N_of_ne
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (hC3 : Q3T8.Asc77.C21_3)
    (h : Q3T8.Asc77.C21_13_N_ne) : Q3T8.Asc77.C21_13_N := by
  intro G _ _ _ Ω K K' z u J t W hh
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact hh.centralizer_tz_le_normalizer_alpha hMF h3s ⟨hC3, Q3T8.Asc77.twinNormAlpha_of hC3⟩ heq
  · exact h G Ω K K' z u J t W hh heq

theorem c21_14_N_of_rest
    (hC3 : Q3T8.Asc77.C21_3) (h : Q3T8.Asc77.C21_14_N_rest) : Q3T8.Asc77.C21_14_N := by
  intro G _ _ _ Ω K K' z u J t W hh
  by_cases hgood : dComp Ω K = dstarComp Ω K ∧ Q3T8.Asc77.SectionConnected Ω u
  · exact hh.centralizer_u_le_normalizer_alpha ⟨hC3, Q3T8.Asc77.twinNormAlpha_of hC3⟩ hgood.1
      hgood.2
  · exact h G Ω K K' z u J t W hh hgood

theorem c21_14_alt_of_rest
    (h
    : Q3T8.Asc77.C21_14_alt_rest) : Q3T8.Asc77.C21_14_alt := by
  intro G _ _ _ Ω K K' z u J t W hh hα
  by_cases hgood : dComp Ω K = dstarComp Ω K ∧ Q3T8.Asc77.SectionConnected Ω u
  · exact Or.inl (hh.rLayer_u_le_sigmaGen hα hgood.1 hgood.2)
  · exact h G Ω K K' z u J t W hh hα hgood
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
theorem c21_E_star_of_starCent
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (h3 : Q3T8.Asc77.C21_3)
    (hStar : Q3T8.Asc77.C21_StarCent) : Q3T8.Asc77.C21_E_star := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu M
  constructor
  · intro hM
    exact ⟨(T3.mem_dstarComp_symm h.std.stand.mem hM).1,
      hStar G Ω K K' z u J t W h hα hD hSigC hmu M hM⟩
  · rintro ⟨hMΩ, hMc⟩
    exact Q3T8.Asc77.tqMembers_subset_dstarComp_gen h hMF h3s h3 hα M
      ⟨hMΩ, ExactLayer.mem_trivialOnQuot_of_le_centralizer hMc⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}

theorem Hyp21.oddCore_centralizer_tz_le_normalizer_alpha
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hs : Q3T8.Asc77.AlphaSteps) :
    oddCoreOf (Subgroup.centralizer ({t * z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  intro n hn
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hΩ
  have hcz : (t * z) * z = z * (t * z) := by
    calc (t * z) * z = (z * t) * z := by rw [hzt]
      _ = z * (t * z) := by group
  have h2 := oddCoreOf_centralizer_le_normalizer_alphaOf (c := t * z) (z := z) h.std.hz.sq
    h.tz_ne_one hcz hn
  rwa [closure_tz_pair, hs.alpha_zt h] at h2

theorem Hyp21.normalizer_le_normalizer_alpha
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hs : Q3T8.Asc77.AlphaSteps) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := fun _ hn =>
  mem_normalizer_iff_conjSub_eq.mpr (hs.conj_alpha_of_mem_centralizer h
    (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn))))

theorem Hyp21.centralizer_tz_le_normalizer_alpha_of_M
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen) (h3s : ∀ n, Q3T8.Generic.CITBelowU n →
        Q3T8.Asc77.T3.Thm3SectBelow n)
    (hs : Q3T8.Asc77.AlphaSteps) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hM : MGrp Ω W ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) :
    Subgroup.centralizer ({t * z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  intro c' hc'
  have h1 : conjSub c' K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc' h.mem_tqMembers_tz_K
  obtain ⟨n, hn, J', -, hJ'd, hMeq⟩ := Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ h.tz_sq
    h.mem_tqMembers_tz_K (h.sectionConnected_tz hMF h3s) _ h1
  have hnα := h.oddCore_centralizer_tz_le_normalizer_alpha hs hn
  obtain ⟨x, hxN, hx⟩ :=
    h.exists_mem_conj_of_dstarComp hne hM (h.normalizer_le_normalizer_alpha hs) J' hJ'd
  have hc'eq : conjSub c' K = conjSub (n * x) K := by rw [hMeq, ← hx, conjSub_mul]
  have hm : conjSub ((n * x)⁻¹ * c') K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmα : (n * x)⁻¹ * c' ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq hm)))
  have e : c' = (n * x) * ((n * x)⁻¹ * c') := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnα hxN) hmα

theorem Hyp21.centralizer_u_le_normalizer_alpha_of_M
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hs : Q3T8.Asc77.AlphaSteps) (hne : dComp Ω K ≠ dstarComp Ω K) (hconn :
        Q3T8.Asc77.SectionConnected Ω u)
    (hM : MGrp Ω W ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := Q3T8.Asc77.exists_mem_tqMembers_u hΩ hK hz h.std.hK' h.std.hne
      h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := Q3T8.Asc77.T7A.mem_dstarComp_of_mem_dComp (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨n, hn, J', -, hJ'd, hMeq⟩ :=
    Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ h.hu2 hJ₀t hconn _ h1
  have hnα : n ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    oddCoreOf_centralizer_le_normalizer_alphaOf h.std.hz.sq h.hu1 h.u_comm_z hn
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hK hJ₀ds] at hJ'd
    exact hJ'd
  obtain ⟨x, hxN, hx⟩ :=
    h.exists_mem_conj_of_dstarComp hne hM (h.normalizer_le_normalizer_alpha hs) J' hJ'ds
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer h hJ₀d
  have hc'eq : conjSub (c' * x₀) K = conjSub (n * x) K := by
    rw [conjSub_mul, hx₀, hMeq, ← hx, conjSub_mul]
  have hm : conjSub ((n * x)⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmα : (n * x)⁻¹ * (c' * x₀) ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (hz.conj_eq hm)))
  have e : c' = ((n * x) * ((n * x)⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnα hxN) hmα)
    (Subgroup.inv_mem _ hx₀N)
end Frame

@[expose] def C21_13_M_ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K →
        MGrp Ω W ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

@[expose] def C21_14_N_disc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      ¬ Q3T8.Asc77.SectionConnected Ω u →
        Subgroup.centralizer ({u} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

theorem c21_13_N_ne_of_M
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (hC3 : Q3T8.Asc77.C21_3)
    (h : Q3T8.Asc77.C21_13_M_ne) : Q3T8.Asc77.C21_13_N_ne := by
  intro G _ _ _ Ω K K' z u J t W hh hne
  exact hh.centralizer_tz_le_normalizer_alpha_of_M hMF h3s ⟨hC3, Q3T8.Asc77.twinNormAlpha_of hC3⟩
      hne
    (h G Ω K K' z u J t W hh hne)

theorem c21_14_N_rest_of
    (hC3 : Q3T8.Asc77.C21_3) (hM : Q3T8.Asc77.C21_13_M_ne) (hd : Q3T8.Asc77.C21_14_N_disc) :
    Q3T8.Asc77.C21_14_N_rest := by
  intro G _ _ _ Ω K K' z u J t W hh hgood
  by_cases hconn : Q3T8.Asc77.SectionConnected Ω u
  · have hne : dComp Ω K ≠ dstarComp Ω K := fun heq => hgood ⟨heq, hconn⟩
    exact hh.centralizer_u_le_normalizer_alpha_of_M ⟨hC3, Q3T8.Asc77.twinNormAlpha_of hC3⟩ hne hconn
      (hM G Ω K K' z u J t W hh hne)
  · exact hd G Ω K K' z u J t W hh hconn
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.mul_four_eq_one (hclC :
    Q3CL.ClassicalClause Ω)
    (hnc : ¬ DbarConnected Ω W) (ρ₁ ρ₂ ρ₃ ρ₄ : Rep Ω W)
    (h₁₂ : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (h₁₃ : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h₂₃ : ρ₃.K ∈ omegaNbr Ω ρ₂.K) (h₁₄ : ρ₄.K ∈ omegaNbr Ω ρ₁.K) (h₂₄ : ρ₄.K ≠ ρ₂.K)
    (h₃₄ : ρ₄.K ≠ ρ₃.K) {z₁ z₂ z₃ z₄ : G} (hz₁ : IsUniqueInvolution ρ₁.K z₁)
    (hz₂ : IsUniqueInvolution ρ₂.K z₂) (hz₃ : IsUniqueInvolution ρ₃.K z₃)
    (hz₄ : IsUniqueInvolution ρ₄.K z₄) : z₁ * z₂ * z₃ * z₄ = 1 := by
  classical
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  obtain ⟨ρ₅, hK51, hK52, hK53, hn51, -, -, hprod⟩ :=
    c.exists_fourth hclC hnc ρ₁ ρ₂ ρ₃ h₁₂ h₁₃ h₂₃ hz₁ hz₂ hz₃
  obtain ⟨z₅, hz₅⟩ := c.hΩ.exists_uniqueInvolution ρ₅.hK
  have hK45 : ρ₄.K = ρ₅.K := by
    by_contra hK45
    have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
      hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
    have hmemC : ∀ σ : Rep Ω W, σ.K ∈ omegaNbr Ω ρ₁.K →
        T7D.imgQ σ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := fun σ hσ =>
      ⟨T7D.imgQ_mem σ, (Subtype.ext (c.comm_of_omega ρ₁ σ hσ)).symm⟩
    have hx₁C : T7D.imgQ ρ₁ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) :=
      Star3T.self_mem_cent (T7D.imgQ_mem ρ₁)
    have h12 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₂ := hne_of _ _ h₁₂.2.1.symm
    have h13 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₃ := hne_of _ _ h₁₃.2.1.symm
    have h14 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₄ := hne_of _ _ h₁₄.2.1.symm
    have h15 : T7D.imgQ ρ₁ ≠ T7D.imgQ ρ₅ := hne_of _ _ (fun e => hK51 e.symm)
    have h23 : T7D.imgQ ρ₂ ≠ T7D.imgQ ρ₃ := hne_of _ _ h₂₃.2.1.symm
    have h24 : T7D.imgQ ρ₂ ≠ T7D.imgQ ρ₄ := hne_of _ _ h₂₄.symm
    have h25 : T7D.imgQ ρ₂ ≠ T7D.imgQ ρ₅ := hne_of _ _ (fun e => hK52 e.symm)
    have h34 : T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₄ := hne_of _ _ h₃₄.symm
    have h35 : T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₅ := hne_of _ _ (fun e => hK53 e.symm)
    have h45 : T7D.imgQ ρ₄ ≠ T7D.imgQ ρ₅ := hne_of _ _ hK45
    have hC3 : 3 ≤ (Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁)).ncard := by
      have hsub : (↑({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃} : Finset ↥(muGroup Ω W)) :
          Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := by
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hx₁C
        · exact hmemC ρ₂ h₁₂
        · exact hmemC ρ₃ h₁₃
      have h3 : ({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃} : Finset ↥(muGroup Ω W)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, h3] at this
    have hC4 : (Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁)).ncard = 4 := by
      rcases Q3T8.Asc77.thompsonClique G Ω hP W c.hW hnc (T7D.imgQ ρ₁) (T7D.imgQ_mem ρ₁) with h | h
          | ⟨h, -⟩
      · omega
      · omega
      · exact h
    have hsub5 : (↑({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃, T7D.imgQ ρ₄, T7D.imgQ ρ₅} :
        Finset ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
          Star3T.cent (muDelta Ω W) (T7D.imgQ ρ₁) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hx₁C
      · exact hmemC ρ₂ h₁₂
      · exact hmemC ρ₃ h₁₃
      · exact hmemC ρ₄ h₁₄
      · exact hmemC ρ₅ hn51
    have h5 : ({T7D.imgQ ρ₁, T7D.imgQ ρ₂, T7D.imgQ ρ₃, T7D.imgQ ρ₄, T7D.imgQ ρ₅} :
        Finset ↥(muGroup Ω W)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15]),
        Finset.card_insert_of_notMem (by simp [h23, h24, h25]),
        Finset.card_insert_of_notMem (by simp [h34, h35]),
        Finset.card_insert_of_notMem (by simp [h45]), Finset.card_singleton]
    have := Set.ncard_le_ncard hsub5 (Set.toFinite _)
    rw [Set.ncard_coe_finset, h5, hC4] at this
    omega
  have hz45 : z₄ = z₅ := hz₄.eq (by rw [hK45]; exact hz₅)
  rw [hz45]
  exact hprod z₅ hz₅
end Ctx
end Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.involution_eq_of_mem_omegaNbr
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSigC : ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G))
    {J₁ : Subgroup G} {t₁ : G} (hJ₁ : J₁ ∈ omegaNbr Ω K) (ht₁ : IsUniqueInvolution J₁ t₁)
    (hJ₁K' : J₁ ≠ K') (hJ₁J : J₁ ≠ J) : t₁ = t := by
  classical
  have hst := h.std.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJK : J ∈ omegaNbr Ω K := h.hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := h.hJ.2 K' h.std.hK'
  have hK'K : K' ∈ omegaNbr Ω K := Q3CL.T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
  have hJ₁Ω : J₁ ∈ Ω := hJ₁.1

  have hdc : ∀ L ∈ omegaNbr Ω K, L ≤ Subgroup.centralizer ({t * z} : Set G) := fun L hL =>
    hSigC L (Relation.ReflTransGen.single ⟨hL.1, Or.inl hL⟩)
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set G) := hSigC K Relation.ReflTransGen.refl
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul hKc fun x hx =>
      commute_involution_of_conjSub_eq hz (conjSub_eq_self_of_mem hx)
  have hK't : K' ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul (hdc K' hK'K) fun x hx =>
      commute_involution_of_conjSub_eq hzK' (conjSub_eq_self_of_mem hx)
  have hdJ₁ := hdc J₁ hJ₁
  have hJ₁K : J₁ ∈ omegaNbr Ω K := hJ₁

  obtain ⟨-, -, R₁, hR₁, hR₁J₁, hR₁N⟩ := hJ₁
  have hR₁S : IsSylow2In R₁ J₁ := hΩ.isSylow2In_of_mem_RSet_of_le hJ₁Ω hR₁ hR₁J₁
  have hR₁2 : IsPGroup 2 R₁ := hR₁S.2.1
  have h8₁ : 8 ≤ Nat.card R₁ := hΩ.eight_le_of_mem_RSet hR₁
  have hR₁z : R₁ ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
  have hR₁t : R₁ ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul (hR₁J₁.trans hdJ₁) fun x hx =>
      commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))

  have hR₁K' : R₁ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK'Ω hJ₁Ω (fun e => hJ₁K' e.symm) hzK' hR₁J₁ hR₁2
      (by omega) hR₁z
  have hR₁J : R₁ ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJΩ hJ₁Ω (fun e => hJ₁J e.symm) h.ht hR₁J₁ hR₁2
      (by omega) hR₁t

  obtain ⟨R_K, hRKS, hP₁⟩ := exists_isPGroup_sup_sylow hR₁2 hR₁N
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω h.std.hne.symm hz hzK'
  have hP₁N : R₁ ⊔ R_K ≤ Subgroup.normalizer (K' : Set G) := sup_le hR₁K' (hRKS.1.trans hKN)
  obtain ⟨R_K', hRK'S, hP₂⟩ := exists_isPGroup_sup_sylow hP₁ hP₁N
  have hRKset : R_K ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRKS
  have hRK'set : R_K' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hRK'S
  have h8K : 8 ≤ Nat.card R_K := hΩ.eight_le_of_mem_RSet hRKset
  have h8K' : 8 ≤ Nat.card R_K' := hΩ.eight_le_of_mem_RSet hRK'set
  have hRKJ : R_K ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJΩ hK hJK.2.1 h.ht hRKS.1 hRKS.2.1 (by omega)
      (hRKS.1.trans hKt)
  have hRK'J : R_K' ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJΩ hK'Ω hJK'.2.1 h.ht hRK'S.1 hRK'S.2.1
      (by omega) (hRK'S.1.trans hK't)
  have hP₂N : R₁ ⊔ R_K ⊔ R_K' ≤ Subgroup.normalizer (J : Set G) :=
    sup_le (sup_le hR₁J hRKJ) hRK'J
  obtain ⟨R_J, hRJS, hP₃⟩ := exists_isPGroup_sup_sylow hP₂ hP₂N
  have hRJset : R_J ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hRJS

  obtain ⟨W₁, hW₁, hD⟩ := Q3T8.Asc77.exists_W_of_isPGroup (Q3T7.modU_toGen3 hΩ) hP₃
  have hR₁D : R₁ ∈ DSet Ω W₁ :=
    hD R₁ hR₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hRKD : R_K ∈ DSet Ω W₁ :=
    hD R_K hRKset (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hRK'D : R_K' ∈ DSet Ω W₁ := hD R_K' hRK'set (le_sup_right.trans le_sup_left)
  have hRJD : R_J ∈ DSet Ω W₁ := hD R_J hRJset le_sup_right
  obtain ⟨ρK, hρK, -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW₁ hK hRKS hRKD
  obtain ⟨ρK', hρK', -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW₁ hK'Ω hRK'S
      hRK'D
  obtain ⟨ρJ, hρJ, -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW₁ hJΩ hRJS hRJD
  obtain ⟨ρJ₁, hρJ₁, -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW₁ hJ₁Ω hR₁S
      hR₁D
  have c₁ : Q3CL.Thompson.Ctx Ω W₁ := Q3T8.Asc77.T7D.ctx_of_stand hst hW₁
  have hnc₁ : ¬ DbarConnected Ω W₁ :=
    Q3T8.Asc77.thompsonGraphAll G Ω ⟨hst.hyp, hst.cls, hst.aEmpty⟩ hst.mem hne hW₁
  have h4 := c₁.mul_four_eq_one hst.cls hnc₁ ρK ρK' ρJ ρJ₁ (by rw [hρK, hρK']; exact hK'K)
    (by rw [hρK, hρJ]; exact hJK) (by rw [hρK', hρJ]; exact hJK') (by rw [hρK, hρJ₁]; exact hJ₁K)
    (by rw [hρK', hρJ₁]; exact hJ₁K') (by rw [hρJ, hρJ₁]; exact hJ₁J)
    (by rw [hρK]; exact hz) (by rw [hρK']; exact hzK') (by rw [hρJ]; exact h.ht)
    (by rw [hρJ₁]; exact ht₁)
  rw [hz.sq, one_mul] at h4
  have h5 : t₁ = t⁻¹ := eq_inv_of_mul_eq_one_right h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_left h.ht.sq

theorem Hyp21.normalizer_le_centralizer_tz
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSigC : ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have hst := h.std.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have htz : t ≠ z := by
    intro htz
    have hJV : J ∈ twinSet Ω K := ⟨h.hJ.1, z, hz, htz ▸ h.ht⟩
    exact (h.hJ.2 J hJV).2.1 rfl
  intro n hn
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hnz : n * z = z * n := commute_involution_of_conjSub_eq hz hnK
  have hJ₁ : conjSub n J ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant (h.hJ.2 K (mem_twinSet_self hK hz)) n
    rwa [hnK] at this
  have ht₁ : IsUniqueInvolution (conjSub n J) (n * t * n⁻¹) := h.ht.conj n
  have htt : n * t * n⁻¹ = t := by
    by_cases hJK' : conjSub n J = K'
    · exfalso
      have e1 : n * t * n⁻¹ = z := ht₁.eq (by rw [hJK']; exact hzK')
      apply htz
      have e2 : n * t = z * n := (mul_inv_eq_iff_eq_mul.mp e1).trans rfl
      calc t = n⁻¹ * (n * t) := by group
        _ = n⁻¹ * (z * n) := by rw [e2]
        _ = n⁻¹ * (n * z) := by rw [hnz]
        _ = z := by group
    · by_cases hJJ : conjSub n J = J
      · exact (h.ht.eq (by rw [← hJJ]; exact ht₁)).symm
      · exact h.involution_eq_of_mem_omegaNbr hne hSigC hJ₁ ht₁ hJK' hJJ
  have hnt : n * t = t * n := mul_inv_eq_iff_eq_mul.mp htt
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * (t * z) = (n * t) * z := by rw [mul_assoc]
    _ = (t * n) * z := by rw [hnt]
    _ = t * (n * z) := by rw [mul_assoc]
    _ = t * (z * n) := by rw [hnz]
    _ = (t * z) * n := by rw [mul_assoc]
end Frame
section Final

theorem c21_starCent_proved :
    Q3T8.Asc77.C21_StarCent := by
  intro G _ _ _ Ω K K' z u J t W h _ _ hSigC _ M hM
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set G) := hSigC K Relation.ReflTransGen.refl
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact hSigC M (by rw [heq]; exact hM)
  · have hN := h.normalizer_le_centralizer_tz heq hSigC
    have hM' : MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set G) :=
      (h.mGrp_le_rLayer_tz heq).trans (rLayer_le_centralizer Ω (t * z))
    obtain ⟨x, hx, rfl⟩ := h.exists_mem_conj_of_dstarComp heq hM' hN M hM
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hy' := hKc hy
    have hyx : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [hyx]
    exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
      ((Subgroup.centralizer ({t * z} : Set G)).mul_mem hx hy')
      ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hx)
end Final
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77.T7R
namespace Thompson
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.good_of_mem_inf
    (σ : Rep Ω W) {v : G} (hv : v ∈
    σ.K ⊓ W) : GoodElt Ω W v := by
  refine ⟨hv.2, fun ρ => ?_⟩
  by_cases hK : ρ.K = σ.K
  · have hvρ : v ∈ ρ.K ⊓ W := hK ▸ hv
    rw [c.conj_inv ρ hvρ]
    exact (ρ.K ⊓ W).mul_mem ((ρ.K ⊓ W).inv_mem hvρ) ((ρ.K ⊓ W).inv_mem hvρ)
  · exact c.comm_mem ρ σ hK hv

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.good_mul
    {a b : G} (ha : GoodElt Ω W a) (hb : GoodElt Ω W b) :
    GoodElt Ω W (a * b) := by
  refine ⟨W.mul_mem ha.1 hb.1, fun ρ => ?_⟩
  have h := comm_mul_of_commute (n := ρ.r) (a := a) (b := b)
    (c.comm_W a ha.1 _ (hb.2 ρ).2)
  rw [h]
  exact (ρ.K ⊓ W).mul_mem (ha.2 ρ) (hb.2 ρ)

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.comm_eq_one_or
    (ρ : Rep Ω W) {ζ : G} (hζ :
    IsUniqueInvolution ρ.K ζ) {a : G}
    (ha : GoodElt Ω W a) (ha2 : a * a = 1) :
    ρ.r * a * ρ.r⁻¹ * a⁻¹ = 1 ∨ ρ.r * a * ρ.r⁻¹ * a⁻¹ = ζ := by
  have hb : ρ.r * a * ρ.r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp ρ.r_mem_normalizer a).mp ha.1
  have hb2 : (ρ.r * a * ρ.r⁻¹) * (ρ.r * a * ρ.r⁻¹) = 1 := by
    calc (ρ.r * a * ρ.r⁻¹) * (ρ.r * a * ρ.r⁻¹) = ρ.r * (a * a) * ρ.r⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hd2 : (ρ.r * a * ρ.r⁻¹ * a⁻¹) * (ρ.r * a * ρ.r⁻¹ * a⁻¹) = 1 := by
    have hcomm := c.comm_W _ hb a ha.1
    rw [hinv]
    calc (ρ.r * a * ρ.r⁻¹ * a) * (ρ.r * a * ρ.r⁻¹ * a)
        = (ρ.r * a * ρ.r⁻¹) * (a * (ρ.r * a * ρ.r⁻¹)) * a := by group
      _ = (ρ.r * a * ρ.r⁻¹) * ((ρ.r * a * ρ.r⁻¹) * a) * a := by rw [← hcomm]
      _ = ((ρ.r * a * ρ.r⁻¹) * (ρ.r * a * ρ.r⁻¹)) * (a * a) := by group
      _ = 1 := by rw [hb2, ha2, one_mul]
  exact hζ.unique _ (ha.2 ρ).1 hd2

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_fourGroup_centralized
    (ρ : Rep Ω W) {a b d : G}
    (ha : GoodElt Ω W a) (hb : GoodElt Ω W b) (hd : GoodElt Ω W d)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hd2 : d * d = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hdab : d ∉ Subgroup.closure ({a, b} : Set G)) :
    ∃ A : Subgroup G, A ≤ Subgroup.closure ({a, b, d} : Set G) ∧ IsElemAbelian2 A 2 ∧
      ∀ w ∈ A, ρ.r * w = w * ρ.r := by
  obtain ⟨ζ, hζ⟩ := c.hΩ.exists_uniqueInvolution ρ.hK
  have hζW : ζ ∈ W := c.mem_W_of_isUniqueInvolution ρ hζ
  exact exists_fourGroup_fixed ha2 hb2 hd2 (c.comm_W a ha.1 b hb.1) (c.comm_W a ha.1 d hd.1)
    (c.comm_W b hb.1 d hd.1) ha1 hb1 hab hdab (c.comm_W ζ hζW a ha.1) (c.comm_W ζ hζW b hb.1)
    hζ.sq (c.comm_eq_one_or ρ hζ ha ha2) (c.comm_eq_one_or ρ hζ hb hb2)
    (c.comm_eq_one_or ρ hζ hd hd2)

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_mul_self_eq
    (ρ : Rep Ω W) {z : G} (hz :
    IsUniqueInvolution ρ.K z) :
    ∃ w ∈ ρ.R ⊓ W, w * w = z ∧ orderOf w = 4 := by
  obtain ⟨w, hwRW, hw4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four c.hΩ c.hW ρ.hR
  refine ⟨w, hwRW, ?_, hw4⟩
  have hw4' : w ^ 4 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw4] at this
  have hw2 : w * w ≠ 1 := fun h => by
    have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hw4] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hwwsq : (w * w) * (w * w) = 1 := by
    calc (w * w) * (w * w) = w ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hw4'
  have hwwR : w * w ∈ ρ.R := ρ.R.mul_mem hwRW.1 hwRW.1
  have hwwK : w * w ∈ ρ.K := ρ.hRK.1 hwwR
  exact (hz.unique (w * w) hwwK hwwsq).resolve_left hw2
end Ctx
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.exists_good_frame
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    ∃ u' : G, TwinFrameData Ω K K' z u' J t ∧ Thompson.GoodElt Ω W u' ∧
      Thompson.GoodElt Ω W z ∧ Thompson.GoodElt Ω W t := by
  have hst := h.std.stand
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hst.hyp
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst h.hW
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  obtain ⟨ρK, hρK⟩ := c.exists_rep_of_involution_mem hst.cls hst.mem hz h.hzW
  obtain ⟨ρK', hρK'⟩ := c.exists_rep_of_involution_mem hst.cls hK'Ω hzK' h.hzW
  obtain ⟨ρJ, hρJ⟩ := c.exists_rep_of_involution_mem hst.cls h.hJ.1 h.ht h.htW
  have hzρ : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρK'.K z := by rw [hρK']; exact hzK'
  have htρ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact h.ht
  obtain ⟨w, hwRW, hwz, hw4⟩ := c.exists_mul_self_eq ρK hzρ
  obtain ⟨w', hw'RW, hw'z, hw'4⟩ := c.exists_mul_self_eq ρK' hzρ'
  have hwK : w ∈ K := by
    have := ρK.hRK.1 hwRW.1
    rwa [hρK] at this
  have hw'K' : w' ∈ K' := by
    have := ρK'.hRK.1 hw'RW.1
    rwa [hρK'] at this
  have hwW : w ∈ W := hwRW.2
  have hw'W : w' ∈ W := hw'RW.2
  have hno4 : ∀ x ∈ K ⊓ K', orderOf x ≠ 4 := by
    intro x hx hx4
    have hcard : Nat.card ↥(Subgroup.zpowers x) = 2 ^ 2 := by
      rw [Nat.card_zpowers, hx4]
      norm_num
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers x) := IsPGroup.of_card hcard
    have := hΩ.card_le_two_of_le_inf hst.mem hK'Ω h.std.hne.symm h2
      (Subgroup.zpowers_le.mpr hx.1) (Subgroup.zpowers_le.mpr hx.2)
    rw [hcard] at this
    omega
  have hcomm : w * w' = w' * w := c.comm_W w hwW w' hw'W
  have hw'w : w' ≠ w := fun heq => hno4 w ⟨hwK, heq ▸ hw'K'⟩ hw4
  have hu2 : (w * w') * (w * w') = 1 := by
    calc (w * w') * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← hcomm]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [hwz, hw'z, hz.sq]
  have hu1 : w * w' ≠ 1 := by
    intro h1
    have h2 : w = w'⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hno4 w ⟨hwK, h2 ▸ K'.inv_mem hw'K'⟩ hw4
  have huz : w * w' ≠ z := by
    intro h1
    apply hw'w
    have h2 : w * w' = w * w := by rw [h1, hwz]
    exact mul_left_cancel h2
  have hfr : TwinFrameData Ω K K' z (w * w') J t :=
    { mem := hst.mem
      hz := hz
      hK' := h.std.hK'
      hne := h.std.hne
      hu := Subgroup.mul_mem_sup hwK hw'K'
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := h.hJ
      ht := h.ht
      htu := c.comm_W t h.htW (w * w') (W.mul_mem hwW hw'W) }
  have hgw : Thompson.GoodElt Ω W w :=
    c.good_of_mem_inf ρK ⟨ρK.hRK.1 hwRW.1, hwW⟩
  have hgw' : Thompson.GoodElt Ω W w' :=
    c.good_of_mem_inf ρK' ⟨ρK'.hRK.1 hw'RW.1, hw'W⟩
  have hzin := c.mem_inf_W_of_isUniqueInvolution ρK hzρ
  have htin := c.mem_inf_W_of_isUniqueInvolution ρJ htρ
  exact ⟨w * w', hfr, c.good_mul hgw hgw', c.good_of_mem_inf ρK ⟨ρK.hRK.1 hzin.1, hzin.2⟩,
    c.good_of_mem_inf ρJ ⟨ρJ.hRK.1 htin.1, htin.2⟩⟩

theorem c21_13_M_ne_of_c21_3
    (hC3 : Q3T8.Asc77.C21_3) : Q3T8.Asc77.C21_13_M_ne := by
  intro G _ _ _ Ω K K' z u J t W h _
  have hst := h.std.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst h.hW
  obtain ⟨u', hfr, hgu, hgz, hgt⟩ := h.exists_good_frame
  have h' : Q3T8.Asc77.Hyp21 Ω K K' z u' J t W := Q3T8.Asc77.Hyp21.of_twinFrameData h.std hfr h.hW
      h.hzW h.htW
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hΩ
  have hA0 : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.ht.sq h.std.hz.sq h.ht.ne_one h.std.hz.ne_one
      h.twinFrameData.t_ne_z hzt.symm
  have hA0B : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hA0B' : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u', t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hα := (hC3 G Ω K K' z u J t W h).2 _ hA0B hA0
  have hα' := (hC3 G Ω K K' z u' J t W h').2
  have hA0W : Subgroup.closure ({t, z} : Set G) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.htW
    · exact h.hzW
  refine iSup₂_le fun R hR => ?_
  obtain ⟨K₁, hK₁, hRK₁⟩ := exists_isSylow2In_of_mem_RSet hR.1
  intro n hn
  by_cases hnW : n ∈ W
  · have hcent : n ∈ Subgroup.centralizer ((Subgroup.closure ({t, z} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact c.comm_W x (hA0W hx) n hnW
    have := T7B.centralizer_le_normalizer_alphaOf _ hcent
    rwa [hα] at this
  · let ρ : Thompson.Rep Ω W := ⟨K₁, R, n, hK₁, hR, hRK₁, hn, hnW⟩
    obtain ⟨A, hAB, hA4, hAc⟩ := c.exists_fourGroup_centralized ρ hgz hgu hgt h.std.hz.sq hfr.hu2
      h.ht.sq h.std.hz.ne_one hfr.hu1 hfr.huz.symm (hfr.t_not_mem_closure hΩ)
    have hcent : n ∈ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hAc x hx).symm
    have h1 := T7B.centralizer_le_normalizer_alphaOf A hcent
    have h2 : alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
      rw [hα' A hAB hA4, ← hα' _ hA0B' hA0, hα]
    rwa [h2] at h1
end Frame
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
