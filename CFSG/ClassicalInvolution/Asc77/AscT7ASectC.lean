module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectB
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal2
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

section Facts

variable (h : Hyp21 p f Ω K K' z u J t W)
include h

omit [IsSimpleGroup G] in
theorem Hyp21.tz_sq : (t * z) * (t * z) = 1 := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp h.std.stand.hyp
  calc (t * z) * (t * z) = t * (z * t) * z := by group
    _ = t * (t * z) * z := by rw [hzt]
    _ = (t * t) * (z * z) := by group
    _ = 1 := by rw [h.ht.sq, h.std.hz.sq, one_mul]

omit [IsSimpleGroup G] in
theorem Hyp21.tz_ne_one : t * z ≠ 1 := by
  intro h1
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.std.hz.sq
  exact h.twinFrameData.t_ne_z (h2.trans h3)

theorem Hyp21.oddCore_centralizer_tz_comm (h3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({t * z} : Set G))) : n * z = z * n := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp h.std.stand.hyp
  have hE : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.ht.sq h.std.hz.sq h.ht.ne_one h.std.hz.ne_one
      h.twinFrameData.t_ne_z hzt.symm
  have hsub : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hA' : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ :=
    ((h3 G Ω K K' z u J t W h).2 _ hsub hE).trans hα
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have hcA : t * z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mul_mem _ htA hzA
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({t * z} : Set G)),
      Subgroup.closure ({t, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({t * z} : Set G)),
      Subgroup.closure ({t, z} : Set G)⁆ ≤ alphaOf (Subgroup.closure ({t, z} : Set G)) := by
    unfold alphaOf
    exact le_sup_of_le_left (le_iSup₂_of_le (t * z) hcA
      (le_iSup_of_le h.tz_ne_one le_rfl))
  rw [hA'] at hle
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))

end Facts

section Main

variable (h : Hyp21 p f Ω K K' z u J t W)
include h

theorem tqMembers_subset_dstarComp (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    ∀ M ∈ tqMembers Ω (t * z), M ∈ dstarComp Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hBelow : CITBelowU p f (Nat.card G) := h.std.stand.below f hq
  set c : G := t * z with hcdef
  have hc2 : c * c = 1 := h.tz_sq
  have hc1 : c ≠ 1 := h.tz_ne_one
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  set A : Subgroup G := Subgroup.zpowers c with hAdef
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hRsyl)
  have h8T : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJΩ hTsyl)
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
  have hKt : K ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hK, R, hRsyl, hRc⟩
  have hK't : K' ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hK'Ω, R', hR'syl, hR'c⟩
  have hJt : J ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hJΩ, T, hTsyl, hTc⟩
  have hKm : K ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hKt
  have hK'm : K' ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hK't
  have hJm : J ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hJt
  have hRA : IsSylow2In R (secMember A K) :=
    (isSylow2In_secMember_iff hcA hKm.2).mpr (mem_fixedSylows_zpowers_iff.mpr ⟨hRsyl, hRc⟩)
  have hR'A : IsSylow2In R' (secMember A K') :=
    (isSylow2In_secMember_iff hcA hK'm.2).mpr (mem_fixedSylows_zpowers_iff.mpr ⟨hR'syl, hR'c⟩)
  have hTA : IsSylow2In T (secMember A J) :=
    (isSylow2In_secMember_iff hcA hJm.2).mpr (mem_fixedSylows_zpowers_iff.mpr ⟨hTsyl, hTc⟩)
  have hJK : J ≠ K := (h.hJ.2 K (mem_twinSet_self hK hz)).2.1
  have hJK' : J ≠ K' := (h.hJ.2 K' h.std.hK').2.1
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTNK : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK hJΩ (Ne.symm hJK) hz hTsyl.1 hT2 (by omega) hTz
  have hTNK' : T ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK'Ω hJΩ (Ne.symm hJK') hzK' hTsyl.1 hT2
      (by omega) hTz
  have hcent : Subgroup.centralizer ((A : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [hAdef, CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton']
  have hTCA : T ≤ Subgroup.centralizer ((A : Subgroup G) : Set G) := by rw [hcent]; exact hTc
  have hTNKA : T ≤ Subgroup.normalizer ((secMember A K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_secMember_of_normalizer (hTCA hx) (hTNK hx))
  have hTNK'A : T ≤ Subgroup.normalizer ((secMember A K' : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_secMember_of_normalizer (hTCA hx) (hTNK' hx))
  set Y : Subgroup G := sectionHull Ω A with hYdef
  have hKY : secMember A K ≤ Y := le_sectionHull hKm
  have hK'Y : secMember A K' ≤ Y := le_sectionHull hK'm
  have hJY : secMember A J ≤ Y := le_sectionHull hJm
  have hΛ : HypOmegaMod p f (restrictFamily (sectionFamily Ω A) Y) :=
    hypOmegaMod_sectionFamily hp hq hΩ hcA
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : HypOmegaMod p f (quotFamily (restrictFamily (sectionFamily Ω A) Y)
      (classicalInvolutionOddCore ↥Y)) :=
    oddQuotHyp p f hp hq ↥Y _ hΛ _ hN₀odd
  have htt : TwinTriple (quotFamily (restrictFamily (sectionFamily Ω A) Y)
      (classicalInvolutionOddCore ↥Y)) :=
    twinTriple_quot hp hΛ' hN₀odd (subgroupOf_secMember_mem hKm)
      (twinSet_subgroupOf hKY hK'Y (secMember_mem_twinSet hp hΩ hcA hKm hK'm h.std.hK'))
      (subgroupOf_secMember_mem hJm) (hRA.subgroupOf hKY) (hR'A.subgroupOf hK'Y)
      (hTA.subgroupOf hJY) (commutes_subgroupOf hRR') (commutes_subgroupOf hRT)
      (commutes_subgroupOf hR'T) (le_normalizer_subgroupOf_of_le hKY hTNKA)
      (le_normalizer_subgroupOf_of_le hK'Y hTNK'A)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({c} : Set G) := by
      have := sectionHull_le_centralizer Ω A
      rwa [hcent] at this
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * c = c * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
    exact hc1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)
  have hconn := dstarConnected_quot_of_twinTriple hp hq hΩ hcA hYtop hBelow (h3s _ hBelow) hMF htt
  have hinv : ∀ n : ↥Y, n ∈ classicalInvolutionOddCore ↥Y → (n : G) ∈ sigmaStarNorm Ω K := by
    intro n hn
    have hnO : (n : G) ∈ oddCoreOf Y := ⟨n, hn, rfl⟩
    have hnC := oddCoreOf_sectionHull_le hΩ A hnO
    rw [hcent] at hnC
    have hnz : (n : G) * z = z * (n : G) := h.oddCore_centralizer_tz_comm h3 hα hnC
    have hnzn : (n : G) * z * (n : G)⁻¹ = z := by
      calc (n : G) * z * (n : G)⁻¹ = (z * (n : G)) * (n : G)⁻¹ := by rw [hnz]
        _ = z := by group
    have hKn : conjSub (n : G) K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj (n : G)⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (AscE186.mem_dstarComp_of_twin hp hΩ hK hKn)
  have hJd : J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJΩ, Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ K
      (h.hJ.2 K (mem_twinSet_self hK hz)))⟩
  intro M hM
  have hMs : M ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hM
  obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
    exists_conj_mem_dstarComp_of_conn hp hq hΩ hcA hJm hconn hMs
  exact ((mem_sigmaStarNorm_iff.mp (hinv n hn)) J').mp (hJd.trans hJ'd)

omit [IsSimpleGroup G] in
theorem Hyp21.mem_tqMembers_tz_J : J ∈ tqMembers Ω (t * z) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hRsyl)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRsyl.1 hRsyl.2.1 (by omega)
  refine (mem_tqMembers_iff_exists_sylow hp hq hΩ (isPGroup_zpowers_of_sq_eq_one h.tz_sq)).mpr
    ⟨h.hJ.1, T, hTsyl, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hxt : x * t = t * x := (h.ht.commute_of_mem (hTsyl.1 hx)).symm
  have hxz : x * z = z * x := (hRT z hzR x hx).symm
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [hxt]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [hxz]
    _ = (t * z) * x := by group

theorem centralizer_tz_le_sigmaStarNorm (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJd : J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJΩ, Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ K
      (h.hJ.2 K (mem_twinSet_self hK h.std.hz)))⟩
  intro g hg
  have hgJ : conjSub g J ∈ tqMembers Ω (t * z) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hg h.mem_tqMembers_tz_J
  have h1 : conjSub g J ∈ dstarComp Ω K :=
    tqMembers_subset_dstarComp h hMF h3s h3 hα _ hgJ
  have hJJ : conjSub g J ∈ dstarComp Ω J := (T3.mem_dstarComp_symm hK hJd).2.trans h1
  have hgJn : g ∈ sigmaStarNorm Ω J :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJΩ hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJd)] at hgJn

end Main

variable (p f) in
theorem c21_13_star_of_sections (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f) :
    C21_13_star p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD heq
  apply hD
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hcA : IsPGroup 2 (Subgroup.zpowers (t * z)) := isPGroup_zpowers_of_sq_eq_one h.tz_sq
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J', hJ'Ω, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ't : J' ∈ tqMembers Ω (t * z) :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hJ'Ω, R, hRJ', hRc⟩
  have hdst := tqMembers_subset_dstarComp h hMF h3s h3 hα J' hJ't
  rw [← heq] at hdst
  exact hRJ'.1.trans (le_iSup₂_of_le J' hdst le_rfl)

variable (p f) in
theorem c21_17_tz_of_sections (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f) :
    C21_17_tz p f := by
  intro G _ _ _ Ω K K' z u J t W h hα _ _
  exact centralizer_tz_le_sigmaStarNorm h hMF h3s h3 hα

variable (p f) in
theorem c21_E_star_of_wylTrans (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hWyl : C21_WylTrans p f) : C21_E_star p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD hSigC hmu M
  constructor
  · intro hM
    refine ⟨(T3.mem_dstarComp_symm h.std.stand.mem hM).1, ?_⟩
    obtain ⟨c, hc, rfl⟩ := hWyl G Ω K K' z u J t W h hmu _ (rLayer_le_centralizer Ω (t * z)) M hM
    have hK : K ≤ Subgroup.centralizer ({t * z} : Set G) := hSigC K Relation.ReflTransGen.refl
    have hcc : c * (t * z) = (t * z) * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : (c⁻¹ * x * c) * (t * z) = (t * z) * (c⁻¹ * x * c) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hK hx)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hcinv : c⁻¹ * (t * z) = (t * z) * c⁻¹ := by
      calc c⁻¹ * (t * z) = c⁻¹ * ((t * z) * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * (t * z)) * c⁻¹ := by rw [hcc]
        _ = (t * z) * c⁻¹ := by group
    calc x * (t * z) = (c * (c⁻¹ * x * c) * c⁻¹) * (t * z) := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * (t * z))) := by group
      _ = c * (((c⁻¹ * x * c) * (t * z)) * c⁻¹) := by rw [hcinv]; group
      _ = c * (((t * z) * (c⁻¹ * x * c)) * c⁻¹) := by rw [h1]
      _ = (c * (t * z)) * (c⁻¹ * x * c * c⁻¹) := by group
      _ = ((t * z) * c) * (c⁻¹ * x * c * c⁻¹) := by rw [hcc]
      _ = (t * z) * x := by group
  · rintro ⟨hMΩ, hMc⟩
    exact tqMembers_subset_dstarComp h hMF h3s h3 hα M
      ⟨hMΩ, mem_trivialOnQuot_of_le_centralizer hMc⟩

end CFSG.ClassicalInvolution.Asc77
