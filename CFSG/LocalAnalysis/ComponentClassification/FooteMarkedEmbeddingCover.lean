module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Beta
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedEmbeddingAlpha
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.Sol76
open CFSG.ComponentClassification.Sol76T13
open CFSG.ComponentClassification.UnbalancedCorr
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem perfectResidual_cover_of_marked {S : Set (Subgroup G)} {T : Type} [Group T]
    {hFam : IsomorphicFamily S T} {M K X : Subgroup G}
    (hK : K ∈ markedComponents S T M)
    (hcov : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (markedLayer S T M), a = x * o) :
    ((K ⊓ X) ⊔ oddCoreIn K = K) ∧
      IsTwoComponentIn (oddResidualIn (K ⊓ X)) (K ⊓ X) ∧
      oddResidualIn (K ⊓ X) ⊔ oddCoreIn K = K ∧
      Nonempty ((oddResidualIn (K ⊓ X)) ⧸
          pPrimeCore 2 (oddResidualIn (K ⊓ X)) ≃*
        K ⧸ pPrimeCore 2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := markedLayer S T M with hD
  have hKD : K ≤ D := le_sSup hK
  have hKc : IsTwoComponentIn K D :=
    ⟨hKD, GSThmB.B5a.isPComponent_subgroupOf_of_le hKD (markedLayer_le S T M) hK.1.2⟩
  have hsup : K ≤ (K ⊓ X) ⊔ oddCoreIn K :=
    le_inf_sup_oddCoreIn_of_covers_components hKc hcov
  have hsupEq : (K ⊓ X) ⊔ oddCoreIn K = K :=
    le_antisymm (sup_le inf_le_left (map_subtype_le _)) hsup
  obtain ⟨hX₀2, -, hX₀sup, eX₀⟩ :=
    cover_facts (Marked.quotient_quasisimple hFam hK.2) inf_le_left hsupEq
  exact ⟨hsupEq, hX₀2, hX₀sup, eX₀⟩

theorem markedLayer_conjugate_general {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (M : Subgroup G) (g : G) :
    CFSG.conjugate (markedLayer S T M) g =
      markedLayer S T (CFSG.conjugate M g) := by
  classical
  let φ : G ≃* G := MulAut.conj g⁻¹
  let φ' : G ≃* G := MulAut.conj g
  have hφM : CFSG.conjugate M g = M.map φ.toMonoidHom := rfl
  have hcomp : ∀ {A : Subgroup G} {K : Subgroup G}, K ∈ markedComponents S T A →
      K.map φ.toMonoidHom ∈ markedComponents S T (A.map φ.toMonoidHom) := by
    intro A K hK
    refine ⟨⟨Subgroup.map_mono hK.1.1,
      CatFactsSp4.isPComponent_map_subgroupOf 2 φ hK.1.1 hK.1.2⟩, ?_⟩
    have h := Marked.conjugate hFam hK.2 g
    simpa [CFSG.conjugate, φ] using h
  have hcomp' : ∀ {A : Subgroup G} {K : Subgroup G}, K ∈ markedComponents S T A →
      K.map φ'.toMonoidHom ∈ markedComponents S T (A.map φ'.toMonoidHom) := by
    intro A K hK
    refine ⟨⟨Subgroup.map_mono hK.1.1,
      CatFactsSp4.isPComponent_map_subgroupOf 2 φ' hK.1.1 hK.1.2⟩, ?_⟩
    have h := Marked.conjugate hFam hK.2 g⁻¹
    simpa [CFSG.conjugate, φ'] using h
  have hcompφ : (M.map φ.toMonoidHom).map φ'.toMonoidHom = M := by
    have h := UnbalancedLayer.conjugate_conjugate M g g⁻¹
    rw [mul_inv_cancel, conjugate_one_eq] at h
    simpa [CFSG.conjugate, φ, φ'] using h
  change (sSup (markedComponents S T M)).map φ.toMonoidHom =
    sSup (markedComponents S T (M.map φ.toMonoidHom))
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    refine sSup_le fun K hK => ?_
    exact (Subgroup.map_le_iff_le_comap).mp (le_sSup (hcomp hK))
  · refine sSup_le fun J hJ => ?_
    have hJmem : J.map φ'.toMonoidHom ∈ markedComponents S T M := by
      have h := hcomp' hJ
      rw [hcompφ] at h
      exact h
    have hJeq : (J.map φ'.toMonoidHom).map φ.toMonoidHom = J := by
      have h := UnbalancedLayer.conjugate_conjugate J g⁻¹ g
      rw [inv_mul_cancel, conjugate_one_eq] at h
      simpa [CFSG.conjugate, φ, φ'] using h
    calc J = (J.map φ'.toMonoidHom).map φ.toMonoidHom := hJeq.symm
      _ ≤ (sSup (markedComponents S T M)).map φ.toMonoidHom :=
          Subgroup.map_mono (le_sSup hJmem)

theorem mem_markedComponents_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    {hFam : IsomorphicFamily S T} {M K : Subgroup G}
    (hK : K ∈ markedComponents S T M) (g : G) :
    CFSG.conjugate K g ∈ markedComponents S T (CFSG.conjugate M g) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  refine ⟨⟨Subgroup.map_mono hK.1.1,
    CatFactsSp4.isPComponent_map_subgroupOf 2 φ hK.1.1 hK.1.2⟩, ?_⟩
  have h := Marked.conjugate hFam hK.2 g
  simpa [CFSG.conjugate, φ] using h

@[expose] def MarkedAlphaCase (S : Set (Subgroup G)) (T : Type*) [Group T]
    (M : Subgroup G) (g : G) : Prop :=
  (∃ K ∈ markedComponents S T M, ∃ s ∈ K, orderOf s = 2 ∧
      ∃ J ∈ markedComponents S T (CFSG.conjugate M g), s ∈ coreActionKernel J) ∨
    (∃ J ∈ markedComponents S T (CFSG.conjugate M g), ∃ s ∈ J, orderOf s = 2 ∧
      ∃ K ∈ markedComponents S T M, s ∈ coreActionKernel K)

theorem mem_of_covers_of_marked_beta
    {S : Set (Subgroup G)} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hFam : IsomorphicFamily S T)
    (hTrank : 2 ≤ CFSG.pRank 2 T)
    (hTnonab : ∃ a b : T, a * b ≠ b * a)
    (hOutT : Group.IsSolvable (OuterAutomorphisms.Outer T))
    {M : Subgroup G} {g : G}
    (hAlphaCase : MarkedAlphaCase S T M g → g ∈ M)
    (hMbal : Balanced S T M)
    (hDnorm : Subgroup.normalizer (markedLayer S T M : Set G) = M)
    (hCpure : ∀ K' ∈ markedComponents S T M, ∀ x ∈ K', orderOf x = 2 →
      centralizer ({x} : Set G) ≤ M)
    {K : Subgroup G} (hK : K ∈ markedComponents S T M)
    {X : Subgroup G} (hX : X ≤ CFSG.conjugate M g)
    (hcov : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (markedLayer S T M), a = x * o) :
    g ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hα : MarkedAlphaCase S T M g
  · exact hAlphaCase hα
  exfalso
  have hβ1 : ∀ K' ∈ markedComponents S T M, ∀ s ∈ K', orderOf s = 2 →
      ∀ J ∈ markedComponents S T (CFSG.conjugate M g), s ∉ coreActionKernel J := by
    intro K' hK' s hs hs2 J hJ hmem
    exact hα (Or.inl ⟨K', hK', s, hs, hs2, J, hJ, hmem⟩)
  have hβ2 : ∀ J ∈ markedComponents S T (CFSG.conjugate M g), ∀ s ∈ J, orderOf s = 2 →
      ∀ K' ∈ markedComponents S T M, s ∉ coreActionKernel K' := by
    intro J hJ s hs hs2 K' hK' hmem
    exact hα (Or.inr ⟨J, hJ, s, hs, hs2, K', hK', hmem⟩)
  set D := markedLayer S T M with hD
  set O := oddCoreIn D with hO
  set Mg := CFSG.conjugate M g with hMg
  have hKgc : CFSG.conjugate K g ∈ markedComponents S T Mg :=
    mem_markedComponents_conjugate (hFam := hFam) hK g
  have hKrank : 2 ≤ CFSG.Open.pRank 2 K := by
    obtain ⟨eK⟩ := hK.2.2.1
    have hker : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (pPrimeCore_coprime_card (p := 2) (G := ↥K))
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      ← CFSG.SectionRank.pRank_quotient_eq (p := 2) (N := pPrimeCore 2 ↥K) hker,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) eK,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 T]
    exact hTrank
  have hncK : ∃ q : ↥K ⧸ pPrimeCore 2 ↥K, orderOf q = 2 ∧
      q ∉ Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K) := by
    obtain ⟨eK⟩ := hK.2.2.1
    have hTrankOpen : 1 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup T) := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 2 T]
      omega
    obtain ⟨q, -, hq2⟩ := exists_orderOf_eq_two_of_pRank (K := ⊤) hTrankOpen
    refine ⟨eK.symm q, by rw [MulEquiv.orderOf_eq]; exact hq2, ?_⟩
    intro hq
    have hqT : q ∈ Subgroup.center T := by
      rw [← Subgroup.map_center_eq (f := eK)]
      exact Subgroup.mem_map.mpr ⟨eK.symm q, hq, eK.apply_symm_apply q⟩
    have hcenterT : Subgroup.center T = ⊥ :=
      CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hTnonab
    rw [hcenterT, Subgroup.mem_bot] at hqT
    have : orderOf q = 1 := by rw [hqT, orderOf_one]
    omega
  have hsupX : (K ⊓ X) ⊔ oddCoreIn K = K :=
    (perfectResidual_cover_of_marked (hFam := hFam) (M := M) (K := K) (X := X) hK hcov).1
  have hsup : (K ⊓ Mg) ⊔ oddCoreIn K = K := by
    refine le_antisymm (sup_le inf_le_left (map_subtype_le _)) ?_
    calc K = (K ⊓ X) ⊔ oddCoreIn K := hsupX.symm
      _ ≤ (K ⊓ Mg) ⊔ oddCoreIn K :=
          sup_le_sup_right (inf_le_inf_left K hX) _
  obtain ⟨hX₀2, -, hX₀sup, ⟨eX₀⟩⟩ :=
    cover_facts (Marked.quotient_quasisimple hFam hK.2) inf_le_left hsup
  set X₀ := oddResidualIn (K ⊓ Mg) with hX₀def
  have hX₀C : IsTwoComponentIn X₀ (M ⊓ Mg) :=
    isTwoComponentIn_inf_of_isTwoComponentIn hK.1 hX₀2
  have hX₀K : X₀ ≤ K := hX₀2.1.trans inf_le_left
  have hX₀Mg : X₀ ≤ Mg := hX₀2.1.trans inf_le_right
  have hX₀M : X₀ ≤ M := hX₀C.1.trans inf_le_left
  have hX₀r : 2 ≤ CFSG.Open.pRank 2 X₀ :=
    hKrank.trans (pRank_le_of_sup_oddCoreIn hX₀K hX₀sup)
  have hX₀q : IsQuasisimple (↥X₀ ⧸ pPrimeCore 2 ↥X₀) :=
    isQuasisimple_quotient_of_isPComponent hX₀C.1 hX₀C.2
  have hX₀res : oddResidualIn X₀ = X₀ :=
    oddResidualIn_eq_self_of_isPComponent hX₀C.1 hX₀C.2
  have hX₀perf : ⁅X₀, X₀⁆ = X₀ :=
    UnbalancedCorr.commutator_eq_of_isPComponent hX₀C.1 hX₀C.2
  have hnc : ∃ q : ↥X₀ ⧸ pPrimeCore 2 ↥X₀, orderOf q = 2 ∧
      q ∉ Subgroup.center (↥X₀ ⧸ pPrimeCore 2 ↥X₀) :=
    exists_noncentral_involution_of_mulEquiv eX₀ hncK
  have hCX₀ : ∀ s ∈ X₀, orderOf s = 2 → centralizer ({s} : Set G) ≤ M := fun s hs hs2 =>
    hCpure K hK s (hX₀K hs) hs2
  have hOMg : oddCoreIn Mg ≤ M :=
    le_of_coprime_of_pRank hX₀r hCX₀ (coprime_card_oddCoreIn Mg)
      (hX₀Mg.trans (le_normalizer_oddCoreIn Mg))
  have hnorm : ∀ J ∈ markedComponents S T Mg, X₀ ≤ normalizer (J : Set G) :=
    le_normalizer_of_permutes_of_inf hX₀C hX₀r hnc hOMg hCX₀ (fun J hJ => hJ.1)
      (fun k hk J hJ => by
        have hkMg : k ∈ Mg := hX₀Mg hk
        have hkinv : k⁻¹ ∈ Mg := Mg.inv_mem hkMg
        have h := (markedComponents_conjugate_iff hFam Mg ⟨k⁻¹, hkinv⟩ J).mp hJ
        simpa [CFSG.conjugate] using h)
  obtain ⟨s, hsX₀, hs2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hX₀r)
  have hmove : ¬ X₀ ≤ coreActionKernel (CFSG.conjugate K g) := fun h =>
    hβ1 K hK s (hX₀K hsX₀) hs2 (CFSG.conjugate K g) hKgc (h hsX₀)
  have hKgperf : ⁅CFSG.conjugate K g, CFSG.conjugate K g⁆ = CFSG.conjugate K g :=
    UnbalancedCorr.commutator_eq_of_isPComponent hKgc.1.1 hKgc.1.2
  have hX₀N : X₀ ≤ normalizer (CFSG.conjugate K g : Set G) := hnorm _ hKgc
  have hOutKg : Group.IsSolvable (OuterAutomorphisms.Outer
      (↥(CFSG.conjugate K g) ⧸ pPrimeCore 2 ↥(CFSG.conjugate K g))) := by
    obtain ⟨eKg⟩ := hKgc.2.2.1
    exact OuterAutomorphisms.solvable_of_equiv eKg.symm
  have hinner : X₀ ≤ CFSG.conjugate K g ⊔ coreActionKernel (CFSG.conjugate K g) :=
    le_sup_coreActionKernel_of_outer_solvable hOutKg hX₀perf hX₀N
  set Qg := coreActionKernel (CFSG.conjugate K g) with hQg
  have hKgQ : CFSG.conjugate K g ≤ normalizer (Qg : Set G) := fun k hk =>
    FooteLit.mem_normalizer_coreActionKernel (le_normalizer hk)
  have hX₀Q : X₀ ≤ normalizer (Qg : Set G) := fun k hk =>
    FooteLit.mem_normalizer_coreActionKernel (hX₀N hk)
  have hcard : Nat.card (↥(CFSG.conjugate K g) ⧸
        Open.fusionZStar ↥(CFSG.conjugate K g)) =
      Nat.card (↥X₀ ⧸ Open.fusionZStar ↥X₀) := by
    set e : ↥K ≃* ↥(CFSG.conjugate K g) :=
      MulEquiv.subgroupMap (MulAut.conj g⁻¹) K with he
    rw [← Nat.card_congr (Sol78.fusionZStarQuotCongr e).toEquiv,
      Nat.card_congr (Sol78.fusionZStarQuotOfCore eX₀).toEquiv]
  have hall : CFSG.conjugate K g ≤ X₀ ⊔ Qg :=
    le_sup_coreActionKernel_of_card_fusionZStar hX₀q hX₀res hKgQ hX₀Q hinner hmove hcard
  have hOKg : oddCoreIn (CFSG.conjugate K g) ≤ M :=
    le_of_coprime_of_pRank hX₀r hCX₀ (coprime_card_oddCoreIn _) fun x hx =>
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hX₀N hx))
  have hKgM : CFSG.conjugate K g ≤ M :=
    le_of_mutual_cover hKgperf hX₀N hX₀M hOKg hCX₀ hX₀res hX₀q hnc hinner hall
  have hKgC : IsTwoComponentIn (CFSG.conjugate K g) (M ⊓ Mg) :=
    ⟨le_inf hKgM hKgc.1.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (le_inf hKgM hKgc.1.1) inf_le_right hKgc.1.2⟩
  have hX₀eq : CFSG.conjugate K g = X₀ := by
    by_contra hne
    exact hmove (GSThmB.B5a.le_coreActionKernel_of_ne hKgC.1 hX₀C.1 hKgC.2 hX₀C.2 hne)
  have h1 : 1 < markedCount S T M := by
    have h2 := hMbal.1
    omega
  obtain ⟨K', hK', hK'K⟩ := Set.exists_ne_of_one_lt_ncard h1 K
  have hsKg : s ∈ CFSG.conjugate K g := hX₀eq ▸ hsX₀
  exact hβ2 (CFSG.conjugate K g) hKgc s hsKg hs2 K' hK'
    (GSThmB.B5a.le_coreActionKernel_of_ne hK'.1.1 hK.1.1 hK'.1.2 hK.1.2 hK'K
      (hX₀K hsX₀))

theorem conjugate_ne_top {M : Subgroup G} (hM : M ≠ ⊤) (g : G) :
    CFSG.conjugate M g ≠ ⊤ := by
  intro h
  apply hM
  have h2 : CFSG.conjugate (CFSG.conjugate M g) g⁻¹ = M := by
    rw [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, conjugate_one_eq]
  rw [h, conjugate_top] at h2
  exact h2.symm

theorem exists_mem_markedComponents_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    {hFam : IsomorphicFamily S T} {M J : Subgroup G} {g : G}
    (hJ : J ∈ markedComponents S T (CFSG.conjugate M g)) :
    ∃ K ∈ markedComponents S T M, CFSG.conjugate K g = J := by
  refine ⟨CFSG.conjugate J g⁻¹, ?_, ?_⟩
  · have h := mem_markedComponents_conjugate (hFam := hFam)
      (M := CFSG.conjugate M g) hJ g⁻¹
    rwa [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, conjugate_one_eq] at h
  · rw [UnbalancedLayer.conjugate_conjugate, inv_mul_cancel, conjugate_one_eq]

theorem pureCentralizers_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    {hFam : IsomorphicFamily S T} {M : Subgroup G} {g : G}
    (hC : ∀ K ∈ markedComponents S T M, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M) :
    ∀ J ∈ markedComponents S T (CFSG.conjugate M g), ∀ x ∈ J, orderOf x = 2 →
      centralizer ({x} : Set G) ≤ CFSG.conjugate M g := by
  intro J hJ x hx hx2
  obtain ⟨K, hK, hKJ⟩ := exists_mem_markedComponents_conjugate (hFam := hFam) hJ
  subst hKJ
  obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hx
  have hxeq : g⁻¹ * y * g = x := by
    simpa [CFSG.conjugate, MulAut.conj_apply] using hyx
  have hy2 : orderOf y = 2 := by
    have h1 : orderOf (MulAut.conj g⁻¹ y) = 2 := by
      rw [show (MulAut.conj g⁻¹) y = x by simpa [MulAut.conj_apply] using hxeq]
      exact hx2
    have h2 : orderOf (MulAut.conj g⁻¹ y) = orderOf y := MulEquiv.orderOf_eq _ y
    omega
  have hcent : centralizer ({y} : Set G) ≤ M := hC K hK y hyK hy2
  rw [← hxeq, ← centralizer_singleton_conjugate y g]
  exact Subgroup.map_mono hcent

theorem mem_of_markedComponents_eq {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) {M : Subgroup G}
    (hDnorm : Subgroup.normalizer (markedLayer S T M : Set G) = M) {g : G}
    (heq : markedComponents S T M = markedComponents S T (CFSG.conjugate M g)) :
    g ∈ M := by
  have hD : markedLayer S T M = markedLayer S T (CFSG.conjugate M g) := by
    unfold markedLayer
    rw [heq]
  have hconj : CFSG.conjugate (markedLayer S T M) g⁻¹ = markedLayer S T M := by
    calc CFSG.conjugate (markedLayer S T M) g⁻¹
        = CFSG.conjugate (markedLayer S T (CFSG.conjugate M g)) g⁻¹ := by rw [hD]
      _ = markedLayer S T M := by
          rw [markedLayer_conjugate_general hFam (CFSG.conjugate M g) g⁻¹]
          have hMg : CFSG.conjugate (CFSG.conjugate M g) g⁻¹ = M := by
            rw [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, conjugate_one_eq]
          rw [hMg]
  rw [← hDnorm]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
    simpa [CFSG.conjugate] using hconj)

theorem mem_of_markedAlphaCase {S : Set (Subgroup G)} {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hFam : IsomorphicFamily S T)
    (hAbs : MarkedAbsorptionLocal S T) (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M : Subgroup G} {g : G} (hMne : M ≠ ⊤) (hMbal : Balanced S T M)
    (hMbalg : Balanced S T (CFSG.conjugate M g))
    (hC : ∀ K ∈ markedComponents S T M, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M)
    (hCg : ∀ K ∈ markedComponents S T (CFSG.conjugate M g), ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ CFSG.conjugate M g)
    (hDnorm : Subgroup.normalizer (markedLayer S T M : Set G) = M)
    (hα : MarkedAlphaCase S T M g) :
    g ∈ M := by
  have hMgne : CFSG.conjugate M g ≠ ⊤ := conjugate_ne_top hMne g
  rcases hα with h | h
  · obtain ⟨K, hK, s, hsK, hs2, J, hJ, hsKer⟩ := h
    have hJ₁ : J ∈ markedComponents S T M :=
      markedComponent_of_coreActionKernel_involution hFam hAbs hTrank hMne hMbal hMgne hMbalg
        hC hCg hK hJ hs2 hsK hsKer
    exact mem_of_markedComponents_eq hFam hDnorm
      (markedComponents_eq_of_shared_component hFam hAbs hTrank hMne hMbal hMgne hMbalg
        hC hCg hJ₁ hJ)
  · obtain ⟨J, hJ, s, hsJ, hs2, K, hK, hsKer⟩ := h
    have hK₂ : K ∈ markedComponents S T (CFSG.conjugate M g) :=
      markedComponent_of_coreActionKernel_involution hFam hAbs hTrank hMgne hMbalg hMne hMbal
        hCg hC hJ hK hs2 hsJ hsKer
    exact mem_of_markedComponents_eq hFam hDnorm
      (markedComponents_eq_of_shared_component hFam hAbs hTrank hMne hMbal hMgne hMbalg
        hC hCg hK hK₂)

theorem markedCoverControl_of_absorption {S : Set (Subgroup G)} {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hFam : IsomorphicFamily S T)
    (hAbs : MarkedAbsorptionLocal S T) (hTrank : 2 ≤ CFSG.pRank 2 T)
    (hTnonab : ∃ a b : T, a * b ≠ b * a)
    (hOutT : Group.IsSolvable (OuterAutomorphisms.Outer T))
    {M : Subgroup G} (hMne : M ≠ ⊤) (hMbal : Balanced S T M)
    (hMbalg : ∀ g : G, Balanced S T (CFSG.conjugate M g))
    (hDnorm : Subgroup.normalizer (markedLayer S T M : Set G) = M)
    (hC : ∀ K ∈ markedComponents S T M, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M) :
    ∀ K ∈ markedComponents S T M, ∀ (g : G) (X : Subgroup G),
      X ≤ CFSG.conjugate M g →
      (∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (markedLayer S T M), a = x * o) → g ∈ M := by
  intro K hK g X hX hcov
  refine mem_of_covers_of_marked_beta hFam hTrank hTnonab hOutT ?_ hMbal hDnorm hC hK hX hcov
  intro hα
  exact mem_of_markedAlphaCase hFam hAbs hTrank hMne hMbal (hMbalg g) hC
    (pureCentralizers_conjugate (hFam := hFam) hC) hDnorm hα

end CFSG.ComponentClassification.FooteMarked
