module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCRankGap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitEverySource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSwapReplacement

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup UnbalancedLayer UnbalancedGS UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem GSWeakCorr.to_gsCorr_of_index_eq {a b : G} {J L : Subgroup G}
    (h : GSWeakCorr a J b L)
    (hd : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) : GSCorr a J b L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hb, hab, hJa, hJ, hLb, hL, hbN, hJb, hTL⟩ := h
  have hJsub : (J.subgroupOf (centralizer ({a} : Set G))).IsSubnormal :=
    hJ.choose_spec.2.1
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J
      (centralizer ({a} : Set G)) hJa).mp hJ).2.2
  have hZb : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hZCa : zpowers b ≤ centralizer ({a} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab.symm)
  have hZK : zpowers b ≤ coreActionKernel J :=
    zpowers_le.mpr (mem_coreActionKernel.mpr ⟨hbN, hJb⟩)
  obtain ⟨hcover, hcore, hTp⟩ := fixedLayer_facts hJa hJsub hZCa
    (hZK.trans (fun _ hx => (mem_coreActionKernel.mp hx).1)) hZb hJq
    (fun z hz => (mem_coreActionKernel.mp (hZK hz)).2)
    (T := gsFixedLayer J b) (by rw [centralizer_zpowers_eq]; rfl)
  rw [centralizer_zpowers_eq] at hTp
  have hTC : gsFixedLayer J b ≤ centralizer ({a} : Set G) ⊓
      centralizer ({b} : Set G) :=
    (gsFixedLayer_le_inf J b).trans (inf_le_inf_right _ hJa)
  obtain ⟨hLab, -⟩ := UGSChain.conjugate_isPComponent_centralizer hab hLb hL
  have hTK : gsFixedLayer J b ≤ (L ⊔ conjugate L a) ⊓
      centralizer ({a} : Set G) := le_inf hTL (hTC.trans inf_le_left)
  have hKCaCb : (L ⊔ conjugate L a) ⊓ centralizer ({a} : Set G) ≤
      centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (sup_le hLb hLab))
  have hTpK := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTK hKCaCb hTp
  obtain ⟨e, _⟩ := exists_quotient_equiv_of_sup
    ((gsFixedLayer_le_inf J b).trans inf_le_left) hcover hcore
  have hidx : (pPrimeCore 2 (gsFixedLayer J b)).index = (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card, Nat.card_congr e.toEquiv,
      ← index_eq_card, hd, index_eq_card]
  have heq := (UGSChain.orbit_fixed_component_comparison ha hab hLb hL hTK hTpK).2.2 hidx
  exact ⟨ha, hb, hab, hJa, hJ, hLb, hL, hbN, hJb, heq.1.symm⟩

theorem swapped_fixed_source_replacement {a b e : G} {J L M : Subgroup G}
    (h1 : GSCorr a J b L) (hne : conjugate L a ≠ L)
    (hd : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index)
    (he : orderOf e = 2) (hae : a * e = e * a) (hbe : b * e = e * b)
    (heJ : e ∈ normalizer (J : Set G))
    (hJe : ∀ j ∈ J, j⁻¹ * e⁻¹ * j * e ∈ (pPrimeCore 2 J).map J.subtype)
    (hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype)
    (h2 : GSWeakCorr a J e M)
    (hdM : (pPrimeCore 2 J).index = (pPrimeCore 2 M).index) :
    conjugate M a ≠ M ∧ ¬ GSIsoCorr a J e M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1' := h1
  obtain ⟨ha, hb, hab, hJa, hJ, hLb, hL, -, -, -⟩ := h1'
  have h2' := h2
  obtain ⟨-, -, -, -, -, hMe, hM, -, -, hUM⟩ := h2'
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  set Hb := centralizer ({b} : Set G)
  set Ce := centralizer ({e} : Set G)
  obtain ⟨heL, heLa, hLe, hLae, hTeHbe, hTepc, hTeV, hVE, -, -, φTe, -⟩ :=
    UGSChain.core_trivial_orbit_fixed_layer_containment hb he hab hbe hLb hL hKe
  have heK : e ∈ normalizer ((L ⊔ conjugate L a : Subgroup G) : Set G) :=
    mem_normalizer_sup heL heLa
  obtain ⟨hWTU, -, -, -, -, hWV, hWcl⟩ :=
    correspondence_nested_fixed_layer_normal_closure h1 he hbe heJ heK hJe hKe
      rfl rfl rfl rfl
  have hMne : conjugate M a ≠ M := by
    intro hMa
    have hUM' : gsFixedLayer J e ≤ M := by
      rwa [hMa, sup_idem] at hUM
    have hVM : gsFixedLayer (L ⊔ conjugate L a) e ≤ M := by
      set V := gsFixedLayer (L ⊔ conjugate L a) e
      have hMn : (M.subgroupOf V).Normal :=
        ⟨fun n hn g => mem_subgroupOf.mpr ((mem_normalizer_iff.mp
          (UGSChain.map_pLayer_le_normalizer hMe hM (hVE g.2)) n).mp
            (mem_subgroupOf.mp hn))⟩
      have hcl : normalClosure (((pLayer ↥(J ⊓ centralizer ({b, e} : Set G)) 2).map
          (J ⊓ centralizer ({b, e} : Set G)).subtype).subgroupOf V : Set V) ≤
          M.subgroupOf V :=
        normalClosure_le_normal fun x hx => hUM' ((hWTU (mem_subgroupOf.mp hx)).2)
      rw [hWcl] at hcl
      intro v hv
      exact hcl (mem_top (⟨v, hv⟩ : V))
    obtain ⟨hLaHb, hLa⟩ := UGSChain.conjugate_isPComponent_centralizer hab hLb hL
    have hKeLa : ∀ k ∈ conjugate L a ⊔ conjugate (conjugate L a) a,
        k⁻¹ * e⁻¹ * k * e ∈ (pPrimeCore 2 Hb).map Hb.subtype := by
      rw [conjugate_conjugate_self_of_mul_self haa, sup_comm]
      exact hKe
    obtain ⟨-, -, -, -, -, hTapc, hTaV, -, -, -, φTa, -⟩ :=
      UGSChain.core_trivial_orbit_fixed_layer_containment hb he hab hbe hLaHb hLa hKeLa
    rw [conjugate_conjugate_self_of_mul_self haa, sup_comm] at hTaV
    have hVle : gsFixedLayer (L ⊔ conjugate L a) e ≤ Hb ⊓ Ce :=
      (gsFixedLayer_le_inf _ e).trans (inf_le_inf_right _ (sup_le hLb hLaHb))
    have hTepcV := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTeV hVle hTepc
    have hTapcV := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTaV hVle hTapc
    have hdL : Nat.card (L ⧸ pPrimeCore 2 L) = Nat.card (M ⧸ pPrimeCore 2 M) := by
      rw [← index_eq_card, ← index_eq_card, ← hd, hdM]
    have hLaL : Nat.card (conjugate L a ⧸ pPrimeCore 2 (conjugate L a)) =
        Nat.card (L ⧸ pPrimeCore 2 L) :=
      (UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr
        ((MulAut.conj a⁻¹).subgroupMap L)).symm
    have hidxTe : (pPrimeCore 2 (gsFixedLayer L e)).index = (pPrimeCore 2 M).index := by
      rw [index_eq_card, index_eq_card, Nat.card_congr φTe.toEquiv, hdL]
    have hidxTa : (pPrimeCore 2 (gsFixedLayer (conjugate L a) e)).index =
        (pPrimeCore 2 M).index := by
      rw [index_eq_card, index_eq_card, Nat.card_congr φTa.toEquiv, hLaL, hdL]
    obtain ⟨-, hse⟩ := OrbitFixedComponent.stable_case M _ hVM _ hTeV hTepcV
    obtain ⟨-, hsa⟩ := OrbitFixedComponent.stable_case M _ hVM _ hTaV hTapcV
    have hTeq : gsFixedLayer L e = gsFixedLayer (conjugate L a) e :=
      (hse hidxTe).1.symm.trans (hsa hidxTa).1
    have hLq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Hb hLb).mp hL).2.2
    have hLaq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ Hb hLaHb).mp hLa).2.2
    have hq1 := UGSChain.map_mk_eq_of_sup_pPrimeCore hLb hL
      (gsFixedLayer_sup_map_pPrimeCore he hLq heL hLe)
    have hq2 := UGSChain.map_mk_eq_of_sup_pPrimeCore hLaHb hLa
      (gsFixedLayer_sup_map_pPrimeCore he hLaq heLa hLae)
    rw [hTeq] at hq1
    exact hne (UGSChain.eq_of_subgroupOf_eq hLaHb hLb
      (pComponent_eq_of_map_eq hLa hL (hq2.trans hq1.symm)))
  refine ⟨hMne, fun hiso => hMne ?_⟩
  have hMaM : conjugate M a ≤ M := le_sup_right.trans hiso.2.1.le
  have hcard : Nat.card M ≤ Nat.card (conjugate M a) := by
    rw [conjugate, card_map_of_injective (MulAut.conj a⁻¹).injective]
  exact eq_of_le_of_card_ge hMaM hcard

theorem fixed_source_rank_increase_of_index_eq {a b : G} {J L S : Subgroup G}
    (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hJ2 : 2 ≤ pRank 2 J)
    (hfixed : ∀ (e : G) (K : Subgroup G), GSWeakCorr a J e K →
      (pPrimeCore 2 J).index = (pPrimeCore 2 K).index)
    (hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf
        (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hbP : b ∈ S ⊓ coreActionKernel J) (hC : GSWeakCorr a J b L)
    (hnot : ¬ GSIsoCorr a J b L) :
    ∃ (e : G) (K : Subgroup G), orderOf e = 2 ∧
      e ∈ S ⊓ coreActionKernel J ∧ GSWeakCorr a J e K ∧ conjugate K a ≠ K ∧
      pRank 2 ↥(centralizer ({a} : Set G) ⊓ coreActionKernel J) <
        pRank 2 ↥(centralizer ({e} : Set G) ⊓ coreActionKernel K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let A : Set (G × Subgroup G) := {p | orderOf p.1 = 2 ∧
    p.1 ∈ S ⊓ coreActionKernel J ∧ GSWeakCorr a J p.1 p.2 ∧ ¬ GSIsoCorr a J p.1 p.2}
  obtain ⟨⟨e, K⟩, ⟨he, heP, hCK, hnotK⟩, hmax⟩ := Set.exists_max_image A
    (fun p : G × Subgroup G => Nat.card ↥(S ⊓ centralizer ({p.1} : Set G)))
    (Set.toFinite A) ⟨(b, L), hC.2.1, hbP, hC, hnot⟩
  have hdK := hfixed e K hCK
  have hstrong := hCK.to_gsCorr_of_index_eq hdK
  have hne : conjugate K a ≠ K := by
    intro hKa
    apply hnotK
    exact (UnbalancingLocal.correspondence_quotient_order_comparison hstrong).2.1 hKa |>.mp
      (by rw [← index_eq_card, ← index_eq_card]; exact hdK)
  by_cases hr : pRank 2 ↥(centralizer ({a} : Set G) ⊓ coreActionKernel J) <
      pRank 2 ↥(centralizer ({e} : Set G) ⊓ coreActionKernel K)
  · exact ⟨e, K, he, heP, hCK, hne, hr⟩
  have heq : ∀ (c : G) (X : Subgroup G),
      centralizer ({c} : Set G) ⊓ normalizer (X : Set G) ⊓ coreActionKernel X =
        centralizer ({c} : Set G) ⊓ coreActionKernel X := by
    intro c X
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · intro x hx
      exact ⟨⟨hx.1, (mem_coreActionKernel.mp hx.2).1⟩, hx.2⟩
  set P := S ⊓ coreActionKernel J
  have hP : P = S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓
      coreActionKernel J) := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1, hSH hx.1, hx.2⟩
    · exact fun x hx => ⟨hx.1, hx.2.2⟩
  obtain ⟨-, -, hTP, hT8⟩ := GSThmB.CorC.rank_gap_of_bound ha hJa hJ hstrong hnotK
    hdK.symm.le (fun _ => by
      rw [heq e K, heq a J]
      exact Nat.le_of_not_gt hr)
    hSH hSsyl heP.1 hP (T := P ⊓ centralizer ({e} : Set G)) rfl hJ2
  obtain ⟨-, -, R, -, -, -, -, -, -, w, -, -, -, -, z, hz, -, -, hQlt,
      hzP, hzJ, hJz, hKz, hza, hze, -⟩ :=
    swapped_correspondence_large_kernel_centralizer_replacement hstrong hne hdK hSH hSsyl
      heP.1 hP (Q := S ⊓ centralizer ({e} : Set G)) rfl rfl hTP hT8
  obtain ⟨M, hCM⟩ := exists_gsWeakCorr ha hJa hJ hz hza.symm hzP.2
  have hdM := hfixed z M hCM
  have hbad := swapped_fixed_source_replacement hstrong hne hdK hz hza.symm hze.symm
    hzJ hJz hKz hCM hdM
  have hle := hmax (z, M) ⟨hz, hzP, hCM, hbad.2⟩
  exact False.elim ((not_le.mpr (card_lt_of_lt hQlt)) hle)

end CFSG.ComponentClassification.GrSLit
