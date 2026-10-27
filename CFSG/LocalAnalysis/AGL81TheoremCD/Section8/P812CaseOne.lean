module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812A
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Five
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.GroupTheory.PComponentInvert
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSzCore
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddNormalizerOrderThreeCentralizes
import CFSG.LocalAnalysis.SteinbergBQControlSylowPromotion
import CFSG.GH74.Generic.BProg.BpGeneral
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812Glue
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}


private theorem centralizes_of_card_three {S L A : Subgroup G} (hS : IsPGroup 3 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hL : CFSG.Open.pRank 3 L ≤ 1)
    (hA : A ≤ L) (hAS : A ≤ S) (hA3 : Nat.card A = 3) :
    ∀ x ∈ A, ∀ s ∈ S, x * s = s * x := by
  classical
  let K : Subgroup G := S ⊓ L
  have hK3 : IsPGroup 3 K := IsPGroup.to_le hS inf_le_left
  have hKcyc : IsCyclic ↥K := by
    refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      Nat.prime_three (by norm_num) hK3 ?_
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_right).trans hL
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    intro s hs
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
  have hN : S ≤ Subgroup.normalizer (A : Set G) :=
    hSK.trans (CFSG.LocalAnalysis.SteinbergBQ.normalizer_le_normalizer_of_le_isCyclic
      (le_inf hAS hA) hKcyc)
  have hSodd : Odd (Nat.card S) := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    exact hn ▸ Odd.pow (n := n) (by norm_num)
  have hcent :=
    CFSG.GorensteinWalter.odd_subgroup_le_centralizer_of_le_normalizer_card_three
      S A hSodd hA3 hN
  intro x hx s hs
  exact Subgroup.mem_centralizer_iff.mp (hcent hs) x hx


private theorem commutator_le_pPrimeCore_of_subgroupOf {B K : Subgroup G} (hBM : B ≤ M)
    (hKM : K ≤ M)
    (h : ⁅B.subgroupOf M, K.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(K.subgroupOf M)).map (K.subgroupOf M).subtype) :
    ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype := by
  have hmap : (⁅B.subgroupOf M, K.subgroupOf M⁆ : Subgroup ↥M).map M.subtype = ⁅B, K⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBM,
      Subgroup.map_subgroupOf_eq_of_le hKM]
  have hcore :
      ((CFSG.pPrimeCore p ↥(K.subgroupOf M)).map (K.subgroupOf M).subtype).map M.subtype =
        (CFSG.pPrimeCore p ↥K).map K.subtype :=
    CFSG.GH74.Generic.BProg.map_pPrimeCoreOf_subgroupOf p hKM
  rw [← hmap, ← hcore]
  exact Subgroup.map_mono h

private theorem le_normalizer_of_subgroupOf {N K : Subgroup G} (hNM : N ≤ M) (hKM : K ≤ M)
    (h : N.subgroupOf M ≤ Subgroup.normalizer (K.subgroupOf M : Set ↥M)) :
    N ≤ Subgroup.normalizer (K : Set G) := by
  have h' : N.subgroupOf M ≤ (Subgroup.normalizer (K : Set G)).subgroupOf M := by
    intro x hx
    have hx' := h hx
    rwa [← Subgroup.subgroupOf_normalizer_eq hKM] at hx'
  intro x hx
  have hxN : (⟨x, hNM hx⟩ : ↥M) ∈ N.subgroupOf M := hx
  exact Subgroup.mem_subgroupOf.mp (h' hxN)

private theorem card_pPrimeCore_subgroupOf_eq {K : Subgroup G} (hKM : K ≤ M) :
    Nat.card (CFSG.pPrimeCore p ↥(K.subgroupOf M)) =
      Nat.card (CFSG.pPrimeCore p ↥K) := by
  let e : ↥(K.subgroupOf M) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKM
  rw [← CFSG.pPrimeCore_map_iso p e]
  exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm

private theorem exists_inv_mem_inf_centralizer_sup_of_le_aux {K : Subgroup G} (hp : p.Prime)
    (hKM : K ≤ M) (hK : CFSG.IsPComponent p (K.subgroupOf M))
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    {B₁ B₂ A : Subgroup G} (hB₁ : IsPGroup 3 B₁) (hB₂ : IsPGroup 3 B₂)
    (hB₁M : B₁ ≤ M) (hB₂M : B₂ ≤ M)
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set G))
    (hB₂K : B₂ ≤ Subgroup.normalizer (K : Set G))
    (hcomm₁ : ⁅B₁, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcomm₂ : ⁅B₂, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hAc : A ≤ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup G) : Set G)) :
    ∃ t ∈ K.subgroupOf M ⊓ Subgroup.centralizer
      (((B₁.subgroupOf M) ⊔ (B₂.subgroupOf M) : Subgroup ↥M) : Set ↥M),
      ∀ a ∈ A.subgroupOf M, t * a * t⁻¹ = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K' : Subgroup ↥M := K.subgroupOf M
  let B₁' : Subgroup ↥M := B₁.subgroupOf M
  let B₂' : Subgroup ↥M := B₂.subgroupOf M
  let A' : Subgroup ↥M := A.subgroupOf M
  have hKrank : CFSG.Open.pRank 3 K' = 1 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three K M
      hKM).trans hr
  have hKcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K') := by
    rw [show K' = K.subgroupOf M from rfl, card_pPrimeCore_subgroupOf_eq hKM]
    exact hcop
  have hB₁' : IsPGroup 3 B₁' := hB₁.comap_of_injective M.subtype M.subtype_injective
  have hB₂' : IsPGroup 3 B₂' := hB₂.comap_of_injective M.subtype M.subtype_injective
  have hc' : ∀ x ∈ B₁', ∀ y ∈ B₂', x * y = y * x := by
    intro x hx y hy
    change (x : G) ∈ B₁ at hx
    change (y : G) ∈ B₂ at hy
    exact Subtype.ext (hc (x : G) hx (y : G) hy)
  have hB₁K' : B₁' ≤ Subgroup.normalizer (K' : Set ↥M) := by
    rw [show K' = K.subgroupOf M from rfl, ← Subgroup.subgroupOf_normalizer_eq hKM]
    intro x hx
    change (x : G) ∈ B₁ at hx
    exact Subgroup.mem_subgroupOf.mpr (hB₁K hx)
  have hB₂K' : B₂' ≤ Subgroup.normalizer (K' : Set ↥M) := by
    rw [show K' = K.subgroupOf M from rfl, ← Subgroup.subgroupOf_normalizer_eq hKM]
    intro x hx
    change (x : G) ∈ B₂ at hx
    exact Subgroup.mem_subgroupOf.mpr (hB₂K hx)
  have hcomm₁' : ⁅B₁', K'⁆ ≤ (CFSG.pPrimeCore p ↥K').map K'.subtype :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section8.commutator_subgroupOf_le_pPrimeCore hB₁M hKM hcomm₁
  have hcomm₂' : ⁅B₂', K'⁆ ≤ (CFSG.pPrimeCore p ↥K').map K'.subtype :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section8.commutator_subgroupOf_le_pPrimeCore hB₂M hKM hcomm₂
  have hAK' : A' ≤ K' := by
    intro x hx
    change (x : G) ∈ A at hx
    change (x : G) ∈ K
    exact hAK hx
  have hA3' : Nat.card A' = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAK.trans hKM)).toEquiv).trans hA3
  have hAc' : A' ≤ Subgroup.centralizer ((B₁' ⊔ B₂' : Subgroup ↥M) : Set ↥M) := by
    have hsub : B₁' ⊔ B₂' = (B₁ ⊔ B₂).subgroupOf M :=
      (Subgroup.subgroupOf_sup hB₁M hB₂M).symm
    intro x hx
    change (x : G) ∈ A at hx
    have hx' : (x : G) ∈ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) := hAc hx
    rw [hsub, CFSG.QuasiDihedralFusion.centralizer_subgroupOf (sup_le hB₁M hB₂M)]
    exact hx'
  obtain ⟨t, ht, htinv⟩ := CFSG.GroupTheory.exists_inv_mem_inf_centralizer_sup
    hp hK hKrank hKcop hB₁' hB₂' hc' hB₁K' hB₂K' hcomm₁' hcomm₂' hAK' hA3' hAc'
  exact ⟨t, ht, htinv⟩

theorem exists_inv_mem_inf_centralizer_sup_of_le {K : Subgroup G} (hp : p.Prime) (hKM : K ≤ M)
    (hK : CFSG.IsPComponent p (K.subgroupOf M)) (hr : CFSG.Open.pRank 3 K = 1)
    (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    {B₁ B₂ A : Subgroup G} (hB₁ : IsPGroup 3 B₁) (hB₂ : IsPGroup 3 B₂)
    (hB₁M : B₁ ≤ M) (hB₂M : B₂ ≤ M)
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set G))
    (hB₂K : B₂ ≤ Subgroup.normalizer (K : Set G))
    (hcomm₁ : ⁅B₁, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcomm₂ : ⁅B₂, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hAc : A ≤ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup G) : Set G)) :
    ∃ t ∈ K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup G) : Set G),
      ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  classical
  obtain ⟨t, ht, htinv⟩ := exists_inv_mem_inf_centralizer_sup_of_le_aux hp hKM hK hr hcop
    hB₁ hB₂ hB₁M hB₂M hc hB₁K hB₂K hcomm₁ hcomm₂ hAK hA3 hAc
  have htK : (t : G) ∈ K := Subgroup.mem_subgroupOf.mp ht.1
  refine ⟨(t : G), ⟨htK, ?_⟩, ?_⟩
  · have hsub : ((B₁ ⊔ B₂).subgroupOf M : Subgroup ↥M) =
        B₁.subgroupOf M ⊔ B₂.subgroupOf M :=
      Subgroup.subgroupOf_sup hB₁M hB₂M
    have hcent := ht.2
    rw [← hsub, CFSG.QuasiDihedralFusion.centralizer_subgroupOf (sup_le hB₁M hB₂M)] at hcent
    exact hcent
  · intro a ha
    exact congrArg Subtype.val (htinv ⟨a, hKM (hAK ha)⟩ (Subgroup.mem_subgroupOf.mpr ha))

private theorem caseOne_left (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₀S : A₀ ≤ S) (hA₀3 : Nat.card A₀ = 3)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hA₀Z : ∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :
    ∃ t : G, t ∈ L₁ ∧ t ∈ Subgroup.centralizer ((A₀ ⊔ A₂ : Subgroup G) : Set G) ∧
      ∀ a ∈ A₁, t * a * t⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀M : A₀ ≤ M := hA₀S.trans hS.le
  have hA₂M : A₂ ≤ M := hA₂.trans h.le₂
  have hSL₁ : S ≤ Subgroup.normalizer (L₁ : Set G) :=
    hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  have hKd :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) (L₂.subgroupOf M) h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hB₁ : IsPGroup 3 A₀ :=
    IsPGroup.of_card (n := 1) (by rw [hA₀3]; norm_num)
  have hB₂ : IsPGroup 3 A₂ :=
    IsPGroup.of_card (n := 1) (by rw [hA₂3]; norm_num)
  have hc : ∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x :=
    fun x hx y hy => hA₀Z x hx y (hA₂S hy)
  have hB₁K : A₀ ≤ Subgroup.normalizer (L₁ : Set G) := hA₀S.trans hSL₁
  have hB₂K : A₂ ≤ Subgroup.normalizer (L₁ : Set G) :=
    hA₂.trans (le_normalizer_of_subgroupOf h.le₂ h.le₁ hKd.1)
  have hA₂L₂ : A₂.subgroupOf M ≤ L₂.subgroupOf M := by
    intro x hx
    change (x : G) ∈ A₂ at hx
    change (x : G) ∈ L₂
    exact hA₂ hx
  have hcomm₂M : ⁅A₂.subgroupOf M, L₁.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L₁.subgroupOf M)).map (L₁.subgroupOf M).subtype := by
    refine (Subgroup.commutator_mono hA₂L₂ le_rfl).trans ?_
    rw [Subgroup.commutator_comm (L₂.subgroupOf M) (L₁.subgroupOf M)]
    exact hKd.2.2.1.trans inf_le_left
  have hcomm₂ : ⁅A₂, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype :=
    commutator_le_pPrimeCore_of_subgroupOf hA₂M h.le₁ hcomm₂M
  have hAc : A₁ ≤ Subgroup.centralizer ((A₀ ⊔ A₂ : Subgroup G) : Set G) :=
    CFSG.le_centralizer_sup_of_commute_both
      (fun b hb c hc' => (show Commute b c from hA₀Z b hb c (hA₂S hc')))
      (fun a ha b hb => (show Commute a b from
        centralizes_of_card_three hS.isPGroup hSL₁ (le_of_eq h.rank_three₁)
          hA₁ hA₁S hA₁3 a ha b (hA₀S hb)))
      (fun a ha c hc' => (show Commute a c from
        centralizes_of_card_three hS.isPGroup hSL₁ (le_of_eq h.rank_three₁)
          hA₁ hA₁S hA₁3 a ha c (hA₂S hc')))
  obtain ⟨t, ht, htinv⟩ := exists_inv_mem_inf_centralizer_sup_of_le h.prime h.le₁ h.comp₁
    h.rank_three₁ (h.not_three_dvd_card_pPrimeCore₁ hSch) hB₁ hB₂ hA₀M hA₂M hc hB₁K hB₂K
    h₁ hcomm₂ hA₁ hA₁3 hAc
  exact ⟨t, ht.1, ht.2, htinv⟩

private theorem caseOne_right (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₀S : A₀ ≤ S) (hA₀3 : Nat.card A₀ = 3)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hA₀Z : ∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :
    ∃ t : G, t ∈ L₂ ∧ t ∈ Subgroup.centralizer ((A₀ ⊔ A₁ : Subgroup G) : Set G) ∧
      ∀ a ∈ A₂, t * a * t⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀M : A₀ ≤ M := hA₀S.trans hS.le
  have hA₁M : A₁ ≤ M := hA₁.trans h.le₁
  have hSL₂ : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hS.le hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS.isPGroup hs)
  have hKd :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) (L₂.subgroupOf M) h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hB₁ : IsPGroup 3 A₀ :=
    IsPGroup.of_card (n := 1) (by rw [hA₀3]; norm_num)
  have hB₂ : IsPGroup 3 A₁ :=
    IsPGroup.of_card (n := 1) (by rw [hA₁3]; norm_num)
  have hc : ∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x :=
    fun x hx y hy => hA₀Z x hx y (hA₁S hy)
  have hB₁K : A₀ ≤ Subgroup.normalizer (L₂ : Set G) :=
    h.le_normalizer_two_of_card_three hSch hA₀M hA₀3
  have hB₂K : A₁ ≤ Subgroup.normalizer (L₂ : Set G) :=
    hA₁.trans (le_normalizer_of_subgroupOf h.le₁ h.le₂ hKd.2.1)
  have hcomm₂M : ⁅A₁.subgroupOf M, L₂.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)).map (L₂.subgroupOf M).subtype := by
    refine (Subgroup.commutator_mono ?_ le_rfl).trans (hKd.2.2.1.trans inf_le_right)
    intro x hx
    change (x : G) ∈ A₁ at hx
    change (x : G) ∈ L₁
    exact hA₁ hx
  have hcomm₂ : ⁅A₁, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype :=
    commutator_le_pPrimeCore_of_subgroupOf hA₁M h.le₂ hcomm₂M
  have hAc : A₂ ≤ Subgroup.centralizer ((A₀ ⊔ A₁ : Subgroup G) : Set G) :=
    CFSG.le_centralizer_sup_of_commute_both
      (fun b hb c hc' => (show Commute b c from hA₀Z b hb c (hA₁S hc')))
      (fun a ha b hb => (show Commute a b from
        (hA₀Z b hb a (hA₂S ha)).symm))
      (fun a ha c hc' => (show Commute a c from
        centralizes_of_card_three hS.isPGroup hSL₂ (le_of_eq h.rank_three₂)
          hA₂ hA₂S hA₂3 a ha c (hA₁S hc')))
  obtain ⟨t, ht, htinv⟩ := exists_inv_mem_inf_centralizer_sup_of_le h.prime h.le₂ h.comp₂
    h.rank_three₂ (h.not_three_dvd_card_pPrimeCore₂ hSch) hB₁ hB₂ hA₀M hA₁M hc hB₁K hB₂K
    h₂ hcomm₂ hA₂ hA₂3 hAc
  exact ⟨t, ht.1, ht.2, htinv⟩

private theorem inf_eq_bot_of_inverting_centralizer {A B : Subgroup G} {t : G}
    (hA3 : Nat.card A = 3) (hT : t ∈ Subgroup.centralizer (B : Set G))
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hcomm : t * x * t⁻¹ = x := by
    have h : x * t = t * x := (Subgroup.mem_centralizer_iff.mp hT) x hx.2
    rw [h.symm]
    group
  have hxinv : x = x⁻¹ := hcomm.symm.trans (hinv x hx.1)
  have hx2 : x * x = 1 := by
    nth_rewrite 1 [hxinv]
    exact inv_mul_cancel x
  have hx3 : x ^ 3 = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard A hx.1
    rw [hA3] at hdvd
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hx2' : x ^ 2 = 1 := by rw [pow_two, hx2]
  have h3 : x ^ 3 = x := by rw [pow_succ, hx2', one_mul]
  calc x = x ^ 3 := h3.symm
    _ = 1 := hx3

private theorem omega_le_sup_of_card_27 {S A : Subgroup G} (hS3 : IsPGroup 3 S)
    (hAS : A ≤ S) (hAel : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (hSC : S ≤ Subgroup.centralizer (A : Set G)) (hAM : A ≤ M) (hSM : S ≤ M)
    (hrank : CFSG.Open.pRank 3 M ≤ 3) :
    ∀ x ∈ S, x ^ 3 = 1 → x ∈ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hxS hx3
  by_contra hxA
  have hxne : x ≠ 1 := fun h1 => hxA (h1 ▸ A.one_mem)
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hxne
    · exact h3
  have hzcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hdisj : Subgroup.zpowers x ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hyne
    have hyord : orderOf y = 3 := by
      have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers x) hy.1
      rw [hzcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hyne
      · exact h3
    have hzycard : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
    have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.1) (by rw [hzcard, hzycard])
    exact hxA (Subgroup.zpowers_le.mpr hy.2 (heq.symm ▸ Subgroup.mem_zpowers x))
  have hxCA : x ∈ Subgroup.centralizer (A : Set G) := hSC hxS
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ A, Commute a b := by
    intro a ha b hb
    rw [Subgroup.mem_zpowers_iff] at ha
    obtain ⟨k, rfl⟩ := ha
    have h : Commute x b := (Subgroup.mem_centralizer_iff.mp hxCA b hb).symm
    exact h.zpow_left k
  have hEel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x ⊔ A) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hx3) hAel
      (fun a ha b hb => (hcomm a ha b hb).eq)
  have hEcard : Nat.card (Subgroup.zpowers x ⊔ A : Subgroup G) = 3 ^ 4 := by
    rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers x) A hcomm hdisj, hzcard, hcard]
    norm_num
  have hEM : Subgroup.zpowers x ⊔ A ≤ M :=
    sup_le (Subgroup.zpowers_le.mpr (hSM hxS)) hAM
  have h4 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEM hEel hEcard
  omega

private theorem caseOne_disjoint {A₀ A₁ A₂ : Subgroup G} {t₁ t₂ : G}
    (hA₀3 : Nat.card A₀ = 3) (hA₁3 : Nat.card A₁ = 3) (hA₂3 : Nat.card A₂ = 3)
    (ht₁C : t₁ ∈ Subgroup.centralizer ((A₀ ⊔ A₂ : Subgroup G) : Set G))
    (ht₁inv : ∀ a ∈ A₁, t₁ * a * t₁⁻¹ = a⁻¹)
    (ht₂C : t₂ ∈ Subgroup.centralizer ((A₀ ⊔ A₁ : Subgroup G) : Set G))
    (ht₂inv : ∀ a ∈ A₂, t₂ * a * t₂⁻¹ = a⁻¹) :
    A₁ ⊓ (A₀ ⊔ A₂) = ⊥ ∧ A₂ ⊓ (A₀ ⊔ A₁) = ⊥ ∧ A₀ ⊓ A₂ = ⊥ ∧ A₀ ⊓ A₁ = ⊥ := by
  have hd₁ : A₁ ⊓ (A₀ ⊔ A₂) = ⊥ :=
    inf_eq_bot_of_inverting_centralizer hA₁3 ht₁C ht₁inv
  have hd₂ : A₂ ⊓ (A₀ ⊔ A₁) = ⊥ :=
    inf_eq_bot_of_inverting_centralizer hA₂3 ht₂C ht₂inv
  have ht₂C₀ : t₂ ∈ Subgroup.centralizer (A₀ : Set G) :=
    (CFSG.centralizer_sup_eq A₀ A₁ ▸ ht₂C).1
  have hd₀₂ : A₀ ⊓ A₂ = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_inverting_centralizer hA₂3 ht₂C₀ ht₂inv
  have hd₀₁ : A₀ ⊓ A₁ = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp ((inf_le_inf le_rfl (le_sup_left : A₀ ≤ A₀ ⊔ A₂)).trans_eq hd₁)
  exact ⟨hd₁, hd₂, hd₀₂, hd₀₁⟩

private theorem caseOne_commutations (h : P812Hyp G M p L₁ L₂) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₀S : A₀ ≤ S) (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S)
    (hA₁3 : Nat.card A₁ = 3) (hA₂S : A₂ ≤ S)
    (hA₀Z : ∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x) :
    (∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x) ∧
      (∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x) ∧
      (∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) := by
  have hSL₁ : S ≤ Subgroup.normalizer (L₁ : Set G) :=
    hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  refine ⟨?_, fun x hx y hy => hA₀Z x hx y (hA₂S hy), ?_⟩
  · intro x hx y hy
    exact (centralizes_of_card_three hS.isPGroup hSL₁ (le_of_eq h.rank_three₁)
      hA₁ hA₁S hA₁3 y hy x (hA₀S hx)).symm
  · intro x hx y hy
    exact centralizes_of_card_three hS.isPGroup hSL₁ (le_of_eq h.rank_three₁)
      hA₁ hA₁S hA₁3 x hx y (hA₂S hy)

private theorem caseOne_abelian_card {A₀ A₁ A₂ : Subgroup G}
    (hA₀3 : Nat.card A₀ = 3) (hA₁3 : Nat.card A₁ = 3) (hA₂3 : Nat.card A₂ = 3)
    (hc₀₁ : ∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x)
    (hc₀₂ : ∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x)
    (hc₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hd₀₁ : A₀ ⊓ A₁ = ⊥) (hd₂ : (A₀ ⊔ A₁) ⊓ A₂ = ⊥) :
    CFSG.Open.IsElemAbelian 3 ((A₀ ⊔ A₁) ⊔ A₂) ∧
      Nat.card ((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : CFSG.Open.IsElemAbelian 3 ((A₀ ⊔ A₁) ⊔ A₂) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.IsElemAbelian.sup_of_commute
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₀3)
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₁3) hc₀₁)
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₂3) ?_
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (CFSG.mem_sup_of_commute (A := A₀) (B := A₁) hc₀₁).mp hx
    calc a * b * y = a * (b * y) := by group
      _ = a * (y * b) := by rw [hc₁₂ b hb y hy]
      _ = (a * y) * b := by group
      _ = (y * a) * b := by rw [hc₀₂ a ha y hy]
      _ = y * (a * b) := by group
  have hcard₀₁ : Nat.card (A₀ ⊔ A₁ : Subgroup G) = 9 := by
    rw [CFSG.card_sup_eq_mul_of_commute A₀ A₁ hc₀₁ hd₀₁, hA₀3, hA₁3]
  have hcard : Nat.card ((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) = 27 := by
    have hc : ∀ x ∈ A₀ ⊔ A₁, ∀ y ∈ A₂, Commute x y := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        (CFSG.mem_sup_of_commute (A := A₀) (B := A₁) hc₀₁).mp hx
      exact (show Commute a y from hc₀₂ a ha y hy).mul_left
        (show Commute b y from hc₁₂ b hb y hy)
    rw [CFSG.card_sup_eq_mul_of_commute (A₀ ⊔ A₁) A₂ hc hd₂, hcard₀₁, hA₂3]
  exact ⟨hAel, hcard⟩

private theorem caseOne_centralizer (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₀S : A₀ ≤ S) (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S)
    (hA₁3 : Nat.card A₁ = 3) (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hA₀Z : ∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x) :
    S ≤ Subgroup.centralizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) := by
  have hSL₁ : S ≤ Subgroup.normalizer (L₁ : Set G) :=
    hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  have hSL₂ : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hS.le hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS.isPGroup hs)
  have hSC₀ : S ≤ Subgroup.centralizer (A₀ : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hA₀Z x hx s hs
  have hSC₁ : S ≤ Subgroup.centralizer (A₁ : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact centralizes_of_card_three hS.isPGroup hSL₁ (le_of_eq h.rank_three₁)
      hA₁ hA₁S hA₁3 x hx s hs
  have hSC₂ : S ≤ Subgroup.centralizer (A₂ : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact centralizes_of_card_three hS.isPGroup hSL₂ (le_of_eq h.rank_three₂)
      hA₂ hA₂S hA₂3 x hx s hs
  rw [CFSG.centralizer_sup_eq, CFSG.centralizer_sup_eq]
  exact le_inf (le_inf hSC₀ hSC₁) hSC₂

private theorem caseOne_dvd_data (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₁ : A₁ ≤ L₁) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂3 : Nat.card A₂ = 3) (hA₀S : A₀ ≤ S) (hA₀3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hc₀₁ : ∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x)
    (hc₀₂ : ∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x)
    (hc₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) {a : Fin 3 → G}
    (hz₀ : Subgroup.zpowers (a 0) = A₀) (hz₁ : Subgroup.zpowers (a 1) = A₁)
    (hz₂ : Subgroup.zpowers (a 2) = A₂) :
    (∀ i, Subgroup.normalizer (Subgroup.zpowers (a i) : Set G) ≤ M) ∧
      (∀ i j, i ≠ j → p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer
        ((Subgroup.zpowers (a i) ⊔ Subgroup.zpowers (a j) : Subgroup G) : Set G))) := by
  have hA₀M : A₀ ≤ M := hA₀S.trans hS.le
  have hN : ∀ i, Subgroup.normalizer (Subgroup.zpowers (a i) : Set G) ≤ M := by
    intro i
    fin_cases i
    · simpa only [Fin.reduceFinMk, hz₀] using
        h.normalizer_le_of_commutator_le hSch hA₀M hA₀3 h₁ h₂
    · simpa only [Fin.reduceFinMk, hz₁] using h.normalizer_le_of_le₁ hSch hA₁ hA₁3
    · simpa only [Fin.reduceFinMk, hz₂] using h.normalizer_le_of_le₂ hSch hA₂ hA₂3
  have hC₀₁ : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₀ ⊔ A₁ : Subgroup G) : Set G)) :=
    h.dvd_card_inf_centralizer_sup_of_commutator_le hSch hA₀M hA₀3 h₁ h₂ (Or.inl hA₁) hA₁3
      hc₀₁
  have hC₀₂ : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₀ ⊔ A₂ : Subgroup G) : Set G)) :=
    h.dvd_card_inf_centralizer_sup_of_commutator_le hSch hA₀M hA₀3 h₁ h₂ (Or.inr hA₂) hA₂3
      hc₀₂
  have hC₁₂ : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G)) :=
    h.dvd_card_inf_centralizer_sup hSch hA₁ hA₂ hA₁3 hA₂3 hc₁₂
  have hC₁₀ : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₁ ⊔ A₀ : Subgroup G) : Set G)) := by
    rw [sup_comm]; exact hC₀₁
  have hC₂₀ : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₂ ⊔ A₀ : Subgroup G) : Set G)) := by
    rw [sup_comm]; exact hC₀₂
  have hC₂₁ : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₂ ⊔ A₁ : Subgroup G) : Set G)) := by
    rw [sup_comm]; exact hC₁₂
  have hC : ∀ i j, i ≠ j → p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (a i) ⊔ Subgroup.zpowers (a j) : Subgroup G) : Set G)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try (exfalso; exact hij rfl)
    all_goals simp only [Fin.reduceFinMk, hz₀, hz₁, hz₂]
    all_goals first
      | exact hC₀₁ | exact hC₀₂ | exact hC₁₂
      | exact hC₁₀ | exact hC₂₀ | exact hC₂₁
  exact ⟨hN, hC⟩

private theorem caseOne_t_left {A₀ A₁ A₂ : Subgroup G} {t₁ : G} {a : Fin 3 → G}
    (ht₁C : t₁ ∈ Subgroup.centralizer ((A₀ ⊔ A₂ : Subgroup G) : Set G))
    (ht₁inv : ∀ x ∈ A₁, t₁ * x * t₁⁻¹ = x⁻¹)
    (hz₀ : Subgroup.zpowers (a 0) = A₀) (hz₁ : Subgroup.zpowers (a 1) = A₁)
    (hz₂ : Subgroup.zpowers (a 2) = A₂) :
    t₁ ∈ Subgroup.normalizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) ∧
      t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧ t₁ * a 2 * t₁⁻¹ = a 2 := by
  have hC₀ : t₁ ∈ Subgroup.centralizer (A₀ : Set G) := (CFSG.centralizer_sup_eq A₀ A₂ ▸ ht₁C).1
  have hC₂ : t₁ ∈ Subgroup.centralizer (A₂ : Set G) := (CFSG.centralizer_sup_eq A₀ A₂ ▸ ht₁C).2
  have hN₁ : t₁ ∈ Subgroup.normalizer (A₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      change t₁ * y * t₁⁻¹ ∈ A₁
      rw [ht₁inv y hy]
      exact A₁.inv_mem hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj t₁).injective]
  have hN : t₁ ∈ Subgroup.normalizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup (A₀ ⊔ A₁) A₂
      ⟨Subgroup.inf_normalizer_le_normalizer_sup A₀ A₁
        ⟨Subgroup.centralizer_le_normalizer (A₀ : Set G) hC₀, hN₁⟩,
        Subgroup.centralizer_le_normalizer (A₂ : Set G) hC₂⟩
  have ha0 : a 0 ∈ A₀ := hz₀ ▸ Subgroup.mem_zpowers (a 0)
  have ha1 : a 1 ∈ A₁ := hz₁ ▸ Subgroup.mem_zpowers (a 1)
  have ha2 : a 2 ∈ A₂ := hz₂ ▸ Subgroup.mem_zpowers (a 2)
  refine ⟨hN, ?_, ?_, ?_⟩
  · rw [((Subgroup.mem_centralizer_iff.mp hC₀) (a 0) ha0).symm]
    group
  · exact ht₁inv (a 1) ha1
  · rw [((Subgroup.mem_centralizer_iff.mp hC₂) (a 2) ha2).symm]
    group

private theorem caseOne_t_right {A₀ A₁ A₂ : Subgroup G} {t₂ : G} {a : Fin 3 → G}
    (ht₂C : t₂ ∈ Subgroup.centralizer ((A₀ ⊔ A₁ : Subgroup G) : Set G))
    (ht₂inv : ∀ x ∈ A₂, t₂ * x * t₂⁻¹ = x⁻¹)
    (hz₀ : Subgroup.zpowers (a 0) = A₀) (hz₁ : Subgroup.zpowers (a 1) = A₁)
    (hz₂ : Subgroup.zpowers (a 2) = A₂) :
    t₂ ∈ Subgroup.normalizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) ∧
      t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧ t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹ := by
  have hC₀ : t₂ ∈ Subgroup.centralizer (A₀ : Set G) := (CFSG.centralizer_sup_eq A₀ A₁ ▸ ht₂C).1
  have hC₁ : t₂ ∈ Subgroup.centralizer (A₁ : Set G) := (CFSG.centralizer_sup_eq A₀ A₁ ▸ ht₂C).2
  have hN₂ : t₂ ∈ Subgroup.normalizer (A₂ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      change t₂ * y * t₂⁻¹ ∈ A₂
      rw [ht₂inv y hy]
      exact A₂.inv_mem hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj t₂).injective]
  have hN : t₂ ∈ Subgroup.normalizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup (A₀ ⊔ A₁) A₂
      ⟨Subgroup.inf_normalizer_le_normalizer_sup A₀ A₁
        ⟨Subgroup.centralizer_le_normalizer (A₀ : Set G) hC₀,
          Subgroup.centralizer_le_normalizer (A₁ : Set G) hC₁⟩, hN₂⟩
  have ha0 : a 0 ∈ A₀ := hz₀ ▸ Subgroup.mem_zpowers (a 0)
  have ha1 : a 1 ∈ A₁ := hz₁ ▸ Subgroup.mem_zpowers (a 1)
  have ha2 : a 2 ∈ A₂ := hz₂ ▸ Subgroup.mem_zpowers (a 2)
  refine ⟨hN, ?_, ?_, ?_⟩
  · rw [((Subgroup.mem_centralizer_iff.mp hC₀) (a 0) ha0).symm]
    group
  · rw [((Subgroup.mem_centralizer_iff.mp hC₁) (a 1) ha1).symm]
    group
  · exact ht₂inv (a 2) ha2

private theorem caseOne_normalizer_le_of_data
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₁ : A₁ ≤ L₁) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂3 : Nat.card A₂ = 3) (hA₀S : A₀ ≤ S) (hA₀3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hc₀₁ : ∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x)
    (hc₀₂ : ∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x)
    (hc₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hAel : CFSG.Open.IsElemAbelian 3 ((A₀ ⊔ A₁) ⊔ A₂))
    (hcard : Nat.card ((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) = 27)
    (hSC : S ≤ Subgroup.centralizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G))
    {t₁ t₂ : G}
    (ht₁C : t₁ ∈ Subgroup.centralizer ((A₀ ⊔ A₂ : Subgroup G) : Set G))
    (ht₁inv : ∀ a ∈ A₁, t₁ * a * t₁⁻¹ = a⁻¹)
    (ht₂C : t₂ ∈ Subgroup.centralizer ((A₀ ⊔ A₁ : Subgroup G) : Set G))
    (ht₂inv : ∀ a ∈ A₂, t₂ * a * t₂⁻¹ = a⁻¹) :
    Subgroup.normalizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) ≤ M := by
  obtain ⟨a₀, -, hz₀'⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.exists_zpowers_eq_of_card_prime
      Nat.prime_three hA₀3
  obtain ⟨a₁, -, hz₁'⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.exists_zpowers_eq_of_card_prime
      Nat.prime_three hA₁3
  obtain ⟨a₂, -, hz₂'⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.exists_zpowers_eq_of_card_prime
      Nat.prime_three hA₂3
  have hz₀ : Subgroup.zpowers a₀ = A₀ := hz₀'.symm
  have hz₁ : Subgroup.zpowers a₁ = A₁ := hz₁'.symm
  have hz₂ : Subgroup.zpowers a₂ = A₂ := hz₂'.symm
  let a : Fin 3 → G := ![a₀, a₁, a₂]
  have ha0 : a 0 = a₀ := by simp [a]
  have ha1 : a 1 = a₁ := by simp [a]
  have ha2 : a 2 = a₂ := by simp [a]
  have hzA0 : Subgroup.zpowers (a 0) = A₀ := by rw [ha0]; exact hz₀
  have hzA1 : Subgroup.zpowers (a 1) = A₁ := by rw [ha1]; exact hz₁
  have hzA2 : Subgroup.zpowers (a 2) = A₂ := by rw [ha2]; exact hz₂
  have haA : ∀ i, a i ∈ (A₀ ⊔ A₁) ⊔ A₂ := by
    intro i
    fin_cases i
    · simpa [a] using (Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (hz₀ ▸ Subgroup.mem_zpowers a₀)) : a₀ ∈ (A₀ ⊔ A₁) ⊔ A₂)
    · simpa [a] using (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (hz₁ ▸ Subgroup.mem_zpowers a₁)) : a₁ ∈ (A₀ ⊔ A₁) ⊔ A₂)
    · simpa [a] using (Subgroup.mem_sup_right
        (hz₂ ▸ Subgroup.mem_zpowers a₂) : a₂ ∈ (A₀ ⊔ A₁) ⊔ A₂)
  have hgen : Subgroup.closure {a 0, a 1, a 2} = (A₀ ⊔ A₁) ⊔ A₂ := by
    have hset : ({a 0, a 1, a 2} : Set G) = {a 0} ∪ {a 1} ∪ {a 2} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    rw [hset, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
    simp [a, hz₀, hz₁, hz₂]
  obtain ⟨hN, hC⟩ :=
    caseOne_dvd_data h hSch hS hA₁ hA₁3 hA₂ hA₂3 hA₀S hA₀3 h₁ h₂ hc₀₁ hc₀₂ hc₁₂
      hzA0 hzA1 hzA2
  obtain ⟨hNt₁, hcond₁⟩ := caseOne_t_left ht₁C ht₁inv hzA0 hzA1 hzA2
  obtain ⟨hNt₂, hcond₂⟩ := caseOne_t_right ht₂C ht₂inv hzA0 hzA1 hzA2
  have hM : ∀ g : G, g ∉ M →
      ¬ p ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom) := h.strong.2.2
  have hSidx : ¬ 3 ∣ S.relIndex M := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
  exact CFSG.LocalAnalysis.RankThreeUC.S15.P812.caseI_normalizer_le h.prime hAel hcard haA hgen
    hNt₁ hNt₂ hcond₁ hcond₂ hM hN hC hS.le hS.isPGroup hSidx hSC

namespace P812Hyp

theorem central₁ (h : P812Hyp G M p L₁ L₂) {S A₁ : Subgroup G} (hSM : S ≤ M)
    (hS3 : IsPGroup 3 S) (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3) :
    ∀ x ∈ A₁, ∀ s ∈ S, x * s = s * x := by
  have hNM : M ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁
  exact centralizes_of_card_three hS3 (hSM.trans hNM) (le_of_eq h.rank_three₁)
    hA₁ hA₁S hA₁3

theorem central₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₂ : Subgroup G}
    (hSM : S ≤ M) (hS3 : IsPGroup 3 S) (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S)
    (hA₂3 : Nat.card A₂ = 3) :
    ∀ x ∈ A₂, ∀ s ∈ S, x * s = s * x := by
  have hSL : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hSM hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS3 hs)
  exact centralizes_of_card_three hS3 hSL (le_of_eq h.rank_three₂) hA₂ hA₂S hA₂3


theorem mem_uniqueSet_of_caseOne
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₀ A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3) (hA₀S : A₀ ≤ S)
    (hA₀3 : Nat.card A₀ = 3) (hA₀Z : ∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :
    A₁ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M ∧
      A₂ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀M : A₀ ≤ M := hA₀S.trans hS.le
  have hA₁M : A₁ ≤ M := hA₁.trans h.le₁
  have hA₂M : A₂ ≤ M := hA₂.trans h.le₂
  obtain ⟨t₁, -, ht₁C, ht₁inv⟩ :=
    caseOne_left h hSch hS hA₀S hA₀3 hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hA₀Z h₁
  obtain ⟨t₂, -, ht₂C, ht₂inv⟩ :=
    caseOne_right h hSch hS hA₀S hA₀3 hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hA₀Z h₂
  obtain ⟨hd₁, hd₂, -, hd₀₁⟩ :=
    caseOne_disjoint hA₀3 hA₁3 hA₂3 ht₁C ht₁inv ht₂C ht₂inv
  obtain ⟨hc₀₁, hc₀₂, hc₁₂⟩ :=
    caseOne_commutations h hS hA₀S hA₁ hA₁S hA₁3 hA₂S hA₀Z
  obtain ⟨hAel, hcard⟩ :=
    caseOne_abelian_card hA₀3 hA₁3 hA₂3 hc₀₁ hc₀₂ hc₁₂ hd₀₁ (by rw [inf_comm]; exact hd₂)
  have hSC : S ≤ Subgroup.centralizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) :=
    caseOne_centralizer h hSch hS hA₀S hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hA₀Z
  have hAS : ((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) ≤ S := sup_le (sup_le hA₀S hA₁S) hA₂S
  have hAM : ((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) ≤ M :=
    sup_le (sup_le hA₀M hA₁M) hA₂M
  have hΩ : ∀ x ∈ S, x ^ 3 = 1 → x ∈ (A₀ ⊔ A₁) ⊔ A₂ :=
    omega_le_sup_of_card_27 hS.isPGroup hAS hAel hcard hSC hAM hS.le h.rank_three
  have hNA : Subgroup.normalizer (((A₀ ⊔ A₁) ⊔ A₂ : Subgroup G) : Set G) ≤ M :=
    caseOne_normalizer_le_of_data h hSch hS hA₁ hA₁3 hA₂ hA₂3 hA₀S hA₀3 h₁ h₂
      hc₀₁ hc₀₂ hc₁₂ hAel hcard hSC ht₁C ht₁inv ht₂C ht₂inv
  refine ⟨?_, ?_⟩
  · exact mem_uniqueSet_of_normalizer_le_of_omega hS hAS hAel hΩ hNA
      ((le_sup_right : A₁ ≤ A₀ ⊔ A₁).trans le_sup_left)
      (h.normalizer_le_of_le₁ hSch hA₁ hA₁3)
  · exact mem_uniqueSet_of_normalizer_le_of_omega hS hAS hAel hΩ hNA le_sup_right
      (h.normalizer_le_of_le₂ hSch hA₂ hA₂3)

end P812Hyp
