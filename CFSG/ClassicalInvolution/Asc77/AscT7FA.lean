module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectF

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
open scoped commutatorElement

section AlphaNormalizes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_alphaOf_of_centralizes {c z g : G} (hgc : g * c = c * g)
    (hgz : g * z = z * g) :
    g ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({c, z} : Set G)) : Set G) := by
  have hc : g * c * g⁻¹ = c := by
    calc g * c * g⁻¹ = (c * g) * g⁻¹ := by rw [hgc]
      _ = c := by group
  have hz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [← alphaOf_conjSub, T7A.conjSub_closure_pair, hc, hz]

omit [Finite G] in
theorem commutator_oddCore_le_alphaOf {c : G} (hc1 : c ≠ 1) (A₀ : Subgroup G) (hcA : c ∈ A₀) :
    ⁅oddCoreOf (Subgroup.centralizer ({c} : Set G)), A₀⁆ ≤ alphaOf A₀ := by
  unfold alphaOf
  exact le_sup_of_le_left (le_iSup₂_of_le c hcA (le_iSup_of_le hc1 le_rfl))

theorem oddCoreOf_centralizer_le_normalizer_alphaOf {c z : G} (hz2 : z * z = 1) (hc1 : c ≠ 1)
    (hcz : c * z = z * c) :
    oddCoreOf (Subgroup.centralizer ({c} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({c, z} : Set G)) : Set G) := by
  set Q := oddCoreOf (Subgroup.centralizer ({c} : Set G)) with hQ
  set A₀ : Subgroup G := Subgroup.closure ({c, z} : Set G) with hA₀
  have hcA : c ∈ A₀ := Subgroup.subset_closure (by simp)
  have hzA : z ∈ A₀ := Subgroup.subset_closure (by simp)
  have hzc : z * c * z⁻¹ = c := by
    calc z * c * z⁻¹ = (c * z) * z⁻¹ := by rw [hcz]
      _ = c := by group
  have hzN : z ∈ Subgroup.normalizer (Q : Set G) := by
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    rw [hQ, ← oddCoreOf_conjSub, T7A.conjSub_centralizer_singleton_eq, hzc]
  have hP : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one hz2
  have hPN : Subgroup.zpowers z ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr hzN
  have hQodd : Odd (Nat.card Q) := oddCoreOf_odd_natCard _
  intro n hn
  obtain ⟨p', hp', q, hq, hpq⟩ := Lemma54Proof.exists_mul_of_mem hP hPN hQodd hn
  have hp'α : p' ∈ alphaOf A₀ := by
    refine commutator_oddCore_le_alphaOf hc1 A₀ hcA ?_
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hzA) hp'
  have hqc : q * c = c * q :=
    Subgroup.mem_centralizer_singleton_iff.mp (oddCoreOf_le_self _ hq.1)
  have hqz : q * z = z * q := by
    have := Subgroup.mem_centralizer_iff.mp hq.2 z (Subgroup.mem_zpowers z)
    exact this.symm
  rw [← hpq]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hp'α)
    (mem_normalizer_alphaOf_of_centralizes hqc hqz)

omit [Finite G] in
theorem closure_tz_pair (t z : G) :
    Subgroup.closure ({t * z, z} : Set G) = Subgroup.closure ({z, t} : Set G) := by
  have hz : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hz' : z ∈ Subgroup.closure ({t * z, z} : Set G) := Subgroup.subset_closure (by simp)
  have htz : t * z ∈ Subgroup.closure ({t * z, z} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mul_mem _ ht hz
    · rw [hx]
      exact hz
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact hz'
    · have h2 : (t * z) * z⁻¹ ∈ Subgroup.closure ({t * z, z} : Set G) :=
        Subgroup.mul_mem _ htz (Subgroup.inv_mem _ hz')
      rw [hx]
      simpa using h2

end AlphaNormalizes

section Connected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def SectionConnected (Ω : Set (Subgroup G)) (c : G) : Prop :=
  T3.DStarConnected (quotFamily (restrictFamily (sectionFamily Ω (Subgroup.zpowers c))
    (sectionHull Ω (Subgroup.zpowers c)))
    (classicalInvolutionOddCore ↥(sectionHull Ω (Subgroup.zpowers c))))

theorem exists_conj_tqMembers_of_connected (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {c : G} (hc2 : c * c = 1) {B : Subgroup G}
    (hB : B ∈ tqMembers Ω c) (hconn : SectionConnected Ω c) :
    ∀ M ∈ tqMembers Ω c, ∃ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)),
      ∃ J' ∈ tqMembers Ω c, J' ∈ dstarComp Ω B ∧ M = conjSub n J' := by
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hcent : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton']
  have hBm : B ∈ sectionMembers Ω (Subgroup.zpowers c) := by
    rw [sectionMembers_zpowers]; exact hB
  intro M hM
  have hMs : M ∈ sectionMembers Ω (Subgroup.zpowers c) := by
    rw [sectionMembers_zpowers]; exact hM
  obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
    exists_conj_mem_dstarComp_of_conn hp hq hΩ hcA hBm hconn hMs
  refine ⟨(n : G), ?_, J', ?_, hJ'd, rfl⟩
  · have hnO : (n : G) ∈ oddCoreOf (sectionHull Ω (Subgroup.zpowers c)) := ⟨n, hn, rfl⟩
    have hnC := oddCoreOf_sectionHull_le hΩ (Subgroup.zpowers c) hnO
    rw [hcent] at hnC
    exact hnC
  · rw [sectionMembers_zpowers] at hJ'
    exact hJ'

end Connected

section Tz

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

omit [IsSimpleGroup G] in
theorem Hyp21.mem_tqMembers_tz_K (h : Hyp21 p f Ω K K' z u J t W) : K ∈ tqMembers Ω (t * z) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8T : 8 ≤ Nat.card T :=
    hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In h.hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  refine (mem_tqMembers_iff_exists_sylow hp hq hΩ (isPGroup_zpowers_of_sq_eq_one h.tz_sq)).mpr
    ⟨hK, R, hRsyl, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hxz : x * z = z * x := (hz.commute_of_mem (hRsyl.1 hx)).symm
  have hxt : x * t = t * x := hRT x hx t htT
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [hxt]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [hxz]
    _ = (t * z) * x := by group

theorem Hyp21.sectionConnected_tz (h : Hyp21 p f Ω K K' z u J t W)
    (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) : SectionConnected Ω (t * z) := by
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
  exact dstarConnected_quot_of_twinTriple_gen hp hq hΩ hcA hYtop hBelow (h3s _ hBelow) hMF htt

theorem Hyp21.centralizer_tz_le_normalizer_alpha (h : Hyp21 p f Ω K K' z u J t W)
    (hMF : DStarConnectedTwinGen p f) (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n)
    (hs : AlphaSteps p f) (heq : dComp Ω K = dstarComp Ω K) :
    Subgroup.centralizer ({t * z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  intro c' hc'
  have h1 : conjSub c' K ∈ tqMembers Ω (t * z) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hc' h.mem_tqMembers_tz_K
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ := exists_conj_tqMembers_of_connected hp hq hΩ h.tz_sq
    h.mem_tqMembers_tz_K (h.sectionConnected_tz hMF h3s) _ h1
  have hnα : n ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
    have hzt : z * t = t * z := h.twinFrameData.comm_zt hp hΩ
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

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

omit [IsSimpleGroup G] in
theorem Hyp21.u_comm_z (h : Hyp21 p f Ω K K' z u J t W) : u * z = z * u :=
  (T7A.z_comm_of_mem_sup h.std.hz (isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK') h.hu).symm

theorem Hyp21.centralizer_u_le_normalizer_alpha (h : Hyp21 p f Ω K K' z u J t W)
    (hs : AlphaSteps p f) (heq : dComp Ω K = dstarComp Ω K) (hconn : SectionConnected Ω u) :
    Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := by rw [← heq]; exact hJ₀d
  intro c' hc'
  have h1 : conjSub c' (conjSub g₀ J) ∈ tqMembers Ω u :=
    conjSub_mem_tqMembers hΩ.conjInvariant hc' hJ₀t
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ :=
    exists_conj_tqMembers_of_connected hp hq hΩ h.hu2 hJ₀t hconn _ h1
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
theorem Hyp21.rLayer_u_le_sigmaGen (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (heq : dComp Ω K = dstarComp Ω K) (hconn : SectionConnected Ω u) :
    rLayer Ω u ≤ sigmaGen Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one h.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    h.hu2 h.hu1 h.hJ h.ht
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hK hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := by rw [← heq]; exact hJ₀d
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨M, hMΩ, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
  have hMt : M ∈ tqMembers Ω u :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hMΩ, R, hRM, hRc⟩
  obtain ⟨n, hn, J', -, hJ'd, hM⟩ :=
    exists_conj_tqMembers_of_connected hp hq hΩ h.hu2 hJ₀t hconn M hMt
  have hnz : n * z = z * n := h.oddCore_centralizer_u_comm hα hn
  have hnzn : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
      _ = z := by group
  have hKn : conjSub n K ∈ twinSet Ω K := ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj n⟩
  have hnσ : n ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (AscE186.mem_dstarComp_of_twin hp hΩ hK hKn)
  have hJ'ds : J' ∈ dstarComp Ω K := by rw [← T7A.dstarComp_eq_of_mem hK hJ₀ds]; exact hJ'd
  have hMd : M ∈ dComp Ω K := by
    rw [heq, hM]
    exact ((mem_sigmaStarNorm_iff.mp hnσ) J').mp hJ'ds
  exact hRM.1.trans (le_iSup₂_of_le M hMd le_rfl)

end UFrame

end CFSG.ClassicalInvolution.Asc77
