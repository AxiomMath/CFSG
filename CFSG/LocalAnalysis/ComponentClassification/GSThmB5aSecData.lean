module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec59
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bSection
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7KProper

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

variable {G : Type*} [Group G] [Finite G]

theorem isPComponent_subgroupOf_top_iff {K : Subgroup G} :
    IsPComponent 2 (K.subgroupOf ⊤) ↔ IsPComponent 2 K := by
  rw [(LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    (Subgroup.topEquiv (G := G))).1]
  congr! 1
  ext x
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    exact ⟨⟨x, mem_top x⟩, hx, rfl⟩

omit [Finite G] in
theorem centralizer_bot : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [mem_centralizer_iff]
  intro x hx
  rw [SetLike.mem_coe, mem_bot] at hx
  rw [hx, one_mul, mul_one]

omit [Finite G] in
theorem exists_isPComponent_of_le_pLayer {L : Subgroup G} (hL : L ≤ pLayer G 2) (hne : L ≠ ⊥) :
    ∃ M : Subgroup G, IsPComponent 2 M := by
  by_contra hno
  push Not at hno
  apply hne
  rw [eq_bot_iff]
  refine hL.trans (le_of_eq ?_)
  show sSup {M : Subgroup G | IsPComponent 2 M} = ⊥
  have hempty : {M : Subgroup G | IsPComponent 2 M} = ∅ :=
    Set.eq_empty_of_forall_notMem fun M hM => hno M hM
  rw [hempty, sSup_empty]

end B5a

namespace Hyp59

variable {H : Type} [Group H] [Finite H]

theorem nonempty_fusionZStar_equiv_of_isPComponent (h : Hyp59 H) {G' : Type*} [Group G']
    {M : Subgroup H}
    (hM : IsPComponent 2 M) (e : ↥(generalizedFitting H) ≃* G') :
    Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* G') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, hsimple, -, -, huniq⟩ := h.generalizedFitting_simple
  have hMc : IsComponent M := B5a.isComponent_of_isPComponent h.oddCore_eq_bot hM
  have hMF : M = generalizedFitting H := (huniq M hMc).trans hF.symm
  have hO : pPrimeCore 2 ↥M = ⊥ := by
    obtain ⟨hs, -, -⟩ :=
      (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).1 hM
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
    rw [h.oddCore_eq_bot, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1
  have : IsSimpleGroup ↥M := hMF ▸ hsimple
  have hZ : center ↥M = ⊥ := B5a.center_eq_bot_of_isSimpleGroup' hMc.1
  have hZs : Open.fusionZStar ↥M = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [OddQuot.mem_fusionZStar_iff, hO] at hl
    rw [← hZ, mem_center_iff]
    intro m
    have hlm := hl m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at hlm
    exact hlm.symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZs).trans
    (QuotientGroup.quotientBot.trans ((MulEquiv.subgroupCongr hMF).trans e))⟩

end Hyp59

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem a_mem_centralizer_secB0 : h.a ∈ centralizer (h.secB0 y : Set X) := by
  rw [mem_centralizer_iff]
  intro b hb
  have hbS : b ∈ h.S := (h.B_le.trans inf_le_left) (h.secB0_le_B y hb)
  exact mem_centralizer_singleton_iff.mp ((h.S_le.trans inf_le_left) hbS)

theorem exists_isPComponent_centralizer_secB0 :
    ∃ M : Subgroup X, M ≤ centralizer (h.secB0 y : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer (h.secB0 y : Set X) with hY
  have haY : h.a ∈ Y := a_mem_centralizer_secB0
  have hza : IsPGroup 2 (zpowers h.a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  have hA : IsPGroup 2 ((zpowers h.a).subgroupOf Y) := hza.comap_subtype
  have hcA : centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) =
      (centralizer ({h.a} : Set X) ⊓ Y).subgroupOf Y := by
    rw [B5a.centralizer_subgroupOf (zpowers_le.mpr haY), centralizer_zpowers_eq,
      inf_subgroupOf_right]
  have hJ0Y : h.secJ0 y ≤ Y := (h.secJ0_le y).trans inf_le_right
  have hJA : (h.secJ0 y).subgroupOf Y ≤
      centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [hcA]
    intro j hj
    exact mem_subgroupOf.mpr (h.secJ0_le y hj)
  have hJc : IsPComponent 2 (((h.secJ0 y).subgroupOf Y).subgroupOf
      (centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y))) := by
    rw [hcA, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact isPComponent_secJ0
  have hle : (h.secJ0 y).subgroupOf Y ≤ pLayer ↥Y 2 := by
    have h1 : ((h.secJ0 y).subgroupOf Y).subgroupOf
        (centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) ≤
        pLayer ↥(centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) 2 :=
      le_sSup hJc
    have h2 := map_mono (f := (centralizer (((zpowers h.a).subgroupOf Y : Subgroup ↥Y) :
      Set ↥Y)).subtype) h1
    rw [map_subgroupOf_eq_of_le hJA] at h2
    exact h2.trans (ClassicalInvolution.l2PrimeBalance ↥Y _ hA)
  have hne : (h.secJ0 y).subgroupOf Y ≠ ⊥ := by
    intro hbot
    have hnt := B5a.nontrivial_of_isPComponent_subgroupOf (h.secJ0_le y) isPComponent_secJ0
    obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : ↥(h.secJ0 y))
    have h1 : (⟨u, hJ0Y hu⟩ : ↥Y) ∈ (h.secJ0 y).subgroupOf Y := mem_subgroupOf.mpr hu
    rw [hbot, mem_bot] at h1
    exact hu1 (Subtype.ext (show u = 1 from congrArg Subtype.val h1))
  obtain ⟨M, hM⟩ := B5a.exists_isPComponent_of_le_pLayer hle hne
  refine ⟨M.map Y.subtype, map_subtype_le _, ?_⟩
  rwa [show (M.map Y.subtype).subgroupOf Y = M from
    comap_map_eq_self_of_injective Y.subtype_injective M]

theorem isPComponent_map_secQ {M : Subgroup X} (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) :
    IsPComponent 2 ((M.subgroupOf (h.secG0 y)).map (h.secQ y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCG : centralizer (h.secB0 y : Set X) ≤ h.secG0 y := h.centralizer_le_G0 y
  have hMG : M ≤ h.secG0 y := hMC.trans hCG
  have h1 : IsPComponent 2 (M.subgroupOf (h.secG0 y)) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hMC hCG
      (Subgroup.Normal.isSubnormal (Subgroup.normal_subgroupOf_centralizer_normalizer _)) hM
  have h2 := secImage_isPComponent hMG le_rfl hMC
    (show IsPComponent 2 (M.subgroupOf (h.secG0 y)) from h1)
  have htop : h.secImage y (h.secG0 y) = ⊤ := by
    show ((h.secG0 y).subgroupOf (h.secG0 y)).map (h.secMk y) = ⊤
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [htop, B5a.isPComponent_subgroupOf_top_iff] at h2
  have h3 := OddQuot.isPComponent_map (QuotientGroup.mk' (pPrimeCore 2 (h.secBar y)))
    OddQuot.not_two_dvd_card_ker le_top
    (show IsPComponent 2 ((h.secImage y M).subgroupOf ⊤) from
      B5a.isPComponent_subgroupOf_top_iff.mpr h2)
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    B5a.isPComponent_subgroupOf_top_iff, map_secImage] at h3
  exact h3

theorem nonempty_secImage_fusionZStar_equiv {L : Subgroup X} (hLG : L ≤ h.secG0 y)
    (hLC : L ≤ centralizer (h.secB0 y : Set X)) (hq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) :
    Nonempty (↥(h.secImage y L) ⧸ Open.fusionZStar ↥(h.secImage y L) ≃*
      ↥L ⧸ Open.fusionZStar ↥L) := by
  let e₁ : ↥(L.subgroupOf (h.secG0 y)) ≃* ↥L := subgroupOfEquivOfLe hLG
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  have hq' : IsQuasisimple (↥(L.subgroupOf (h.secG0 y)) ⧸
      pPrimeCore 2 ↥(L.subgroupOf (h.secG0 y))) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr e₂).2 hq
  obtain ⟨e₃⟩ := TwoQuot.nonempty_fusionZStar_equiv_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y hLC) hq'
  obtain ⟨e₄⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv e₂
  exact ⟨e₃.symm.trans e₄⟩

theorem exists_isPComponent_centralizer_of_hyp59 (h' : Hyp59 (h.secQuot y)) {G' : Type*}
    [Group G'] (e : ↥(generalizedFitting (h.secQuot y)) ≃* G') :
    ∃ M : Subgroup X, M ≤ centralizer (h.secB0 y : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))) ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* G') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMC, hM⟩ := exists_isPComponent_centralizer_secB0 (h := h) (y := y)
  refine ⟨M, hMC, hM, ?_⟩
  have hMG : M ≤ h.secG0 y := hMC.trans (h.centralizer_le_G0 y)
  have hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hM).2.2
  obtain ⟨e₁⟩ := nonempty_secImage_fusionZStar_equiv hMG hMC hq
  obtain ⟨e₂⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv
    (QuotientGroup.mk' (pPrimeCore 2 (h.secBar y))) OddQuot.not_two_dvd_card_ker (h.secImage y M)
  have hM' := isPComponent_map_secQ hMC hM
  rw [← map_secImage] at hM'
  obtain ⟨e₃⟩ := h'.nonempty_fusionZStar_equiv_of_isPComponent hM' e
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

theorem sectionData_of_secCond (hc : h.SecCond y) (hSyl : h.SecSylow y) : h.SectionData := by
  obtain ⟨h', -, -, -, -, -, -, eK, eJ, hOJ, hOK, hconj, hinner, -, eT, -⟩ :=
    exists_hyp59_section hc.mem_P hc.not_mem_T hc.sq_mem_T hc.Q_le hc.mem_normalizer_Q hSyl
  refine ⟨h.secQuot y, inferInstance, inferInstance, h', eT, eK, eJ, hOK, hOJ, hconj, hinner,
    fun ⟨e⟩ => ?_, fun hKP => HSFLit.HS7.kProper_quotient_catalog
      (HSFLit.HS7.kProper_quotient_catalog (HSFLit.HS7.kProper_subgroup_catalog hKP _) _) _⟩
  obtain ⟨M, hMC, hM, eM⟩ := exists_isPComponent_centralizer_of_hyp59 h' e
  exact ⟨h.secB0 y, M, h.isPGroup_secB0 y, hMC, hM, eM⟩

theorem sectionData_of_normal (hBP : h.P ≤ normalizer (h.B : Set X)) (hx2 : h.x ^ 2 = 1) :
    h.SectionData := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h', -, -, -, -, -, -, eT, eK, eJ, eK', eJ', hconj, hinner⟩ :=
    h.exists_hyp59_of_normal hBP hx2
  refine ⟨X ⧸ pPrimeCore 2 X, inferInstance, inferInstance, h', eT, eK, eJ, fun _ => eK',
    fun _ => eJ', hconj, hinner, fun ⟨e⟩ => ?_,
    fun hKP => HSFLit.HS7.kProper_quotient_catalog hKP _⟩
  have hJne : h.J ≠ ⊥ := by
    intro hbot
    have hnt := B5a.nontrivial_of_isPComponent_subgroupOf h.J_le h.isPComponent_J
    rw [hbot] at hnt
    exact not_nontrivial (⊥ : Subgroup X) hnt
  obtain ⟨M, hM⟩ := B5a.exists_isPComponent_of_le_pLayer (B5a.J_le_pLayer h) hJne
  refine ⟨⊥, M, IsPGroup.of_bot, by rw [B5a.centralizer_bot]; exact le_top, ?_, ?_⟩
  · rw [B5a.centralizer_bot]
    exact B5a.isPComponent_subgroupOf_top_iff.mpr hM
  · have hO := OddQuot.not_two_dvd_card_ker (H := X)
    have h3 := OddQuot.isPComponent_map (QuotientGroup.mk' (pPrimeCore 2 X)) hO le_top
      (show IsPComponent 2 (M.subgroupOf ⊤) from B5a.isPComponent_subgroupOf_top_iff.mpr hM)
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      B5a.isPComponent_subgroupOf_top_iff] at h3
    obtain ⟨e₁⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv
      (QuotientGroup.mk' (pPrimeCore 2 X)) hO M
    obtain ⟨e₂⟩ := h'.nonempty_fusionZStar_equiv_of_isPComponent h3 e
    exact ⟨e₁.trans e₂⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
