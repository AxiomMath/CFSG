module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscDefs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMcLLy
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Setup

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] noncomputable def footeK (L : Subgroup G) (t : G) : Subgroup G :=
  (pLayer ↥(footeB L t) 2).map (footeB L t).subtype

noncomputable def quotientPPrimeCoreCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ pPrimeCore 2 X ≃* Y ⧸ pPrimeCore 2 Y :=
  QuotientGroup.congr (pPrimeCore 2 X) (pPrimeCore 2 Y) e (CFSG.pPrimeCore_map_iso 2 e)

theorem foote_lemma_4_9 (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ coreActionKernel M)
    (hCt : ¬ centralizer ({t} : Set G) ≤ normalizer (M : Set G)) :
    footeK L t ≤ footeB L t ∧ IsPComponent 2 ((footeK L t).subgroupOf (footeB L t)) ∧
      (∀ K : Subgroup G, K ≤ footeB L t → IsPComponent 2 (K.subgroupOf (footeB L t)) →
        K = footeK L t) ∧
      IsPComponent 2 ((footeK L t).subgroupOf (centralizer ({t} : Set G))) ∧
      ((Open.fusionIsBenderGroup (footeK L t ⧸ pPrimeCore 2 (footeK L t)) ∧ t ∉ footeK L t) ∨
        (IsCoverOverTwo (footeK L t ⧸ pPrimeCore 2 (footeK L t)) (Open.Sz 1) ∧
          t ∈ footeK L t)) ∧
      ∀ x ∈ footeB L t, orderOf x = 2 → x ∈ footeK L t ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨t₀, hce⟩ := h.ce
  obtain ⟨hBN, htB, hBt, -, -⟩ := foote_lemma_4_9_core h h47 hST hM ht htC hCt
  set B := footeB L t with hBdef
  set t' : ↥B := ⟨t, htB⟩ with ht'def
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have htZ : t' ∈ center ↥B := mem_center_iff.mpr fun b => Subtype.ext
    (mem_centralizer_singleton_iff.mp (hBt b.2))
  have hBn : (B.subgroupOf (centralizer ({t} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBt).mpr hBN
  have hpc : ∀ X : Subgroup ↥B, IsPComponent 2 X →
      IsPComponent 2 ((X.map B.subtype).subgroupOf (centralizer ({t} : Set G))) := by
    intro X hX
    have h1 : IsPComponent 2 ((X.map B.subtype).subgroupOf B) := by
      rw [show (X.map B.subtype).subgroupOf B = X from
        Subgroup.comap_map_eq_self_of_injective B.subtype_injective X]
      exact hX
    exact isPComponent_subgroupOf_of_isSubnormal (map_subtype_le X) hBt hBn.isSubnormal h1
  have hmemt : ∀ X : Subgroup ↥B, t' ∈ X → t ∈ X.map B.subtype := fun X htX =>
    ⟨t', htX, rfl⟩
  have hcl : ∀ X : Subgroup ↥B, IsPComponent 2 X → t' ∈ X → CFSG.pRank 2 ↥X ≤ 1 → False := by
    intro X hX htX hr
    have eX : ↥X ≃* ↥(X.map B.subtype) := X.equivMapOfInjective B.subtype B.subtype_injective
    refine not_classical_of_counterexample h.hCI hce t (X.map B.subtype)
      ⟨ht, (map_subtype_le X).trans hBt, hpc X hX⟩ (hmemt X htX) ?_
    rw [← UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two eX]
    exact hr
  have hA9 : ∀ X : Subgroup ↥B, IsPComponent 2 X → t' ∈ X →
      IsCoverOverTwo (X ⧸ pPrimeCore 2 X) (alternatingGroup (Fin 9)) → False := by
    intro X hX htX hcov
    set X' := X.map B.subtype with hX'
    have eX : ↥X ≃* ↥X' := X.equivMapOfInjective B.subtype B.subtype_injective
    have hcov' : IsCoverOverTwo (X' ⧸ pPrimeCore 2 X') (alternatingGroup (Fin 9)) :=
      IsCoverOverTwo.of_mulEquiv (quotientPPrimeCoreCongr eX).symm hcov
    obtain ⟨hA9s, hna9⟩ := alternatingGroup_nine_simple_nonabelian
    obtain ⟨π₉, hπ₉s, hK₉Z, hK₉C, hK₉2⟩ := hcov'
    obtain ⟨hq, hker⟩ := isQuasisimple_of_isCoverOverTwo hna9 hπ₉s hK₉Z hK₉C
    have e9 : (X' ⧸ pPrimeCore 2 X') ⧸ center (X' ⧸ pPrimeCore 2 X') ≃*
        alternatingGroup (Fin 9) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective π₉ hπ₉s)
    rcases h2An G t ht X' 9 (by norm_num) ((map_subtype_le X).trans hBt) (hpc X hX)
        (hmemt X htX) hq.1 (by rw [← hker]; exact hK₉2) ⟨e9⟩ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact not_mulEquiv_McL h hM e
    · exact not_mulEquiv_Ly h hM e
  obtain ⟨S, hcore, hrank⟩ := foote_lemma_4_9_gamma h h47 hST hM ht htC hCt
  have hdich : FooteAschbacherDichotomy (↥B ⧸ pPrimeCore 2 ↥B) :=
    hAsc ↥B S hcore t' ht' htZ hrank hcl hA9
  obtain ⟨K, hK, huniq, htype, hinv⟩ := foote_lemma_4_9_abstract ht' htZ hdich hcl hA9
  have hlayer : pLayer ↥B 2 = K := by
    have hset : {X : Subgroup ↥B | IsPComponent 2 X} = {K} := by
      ext X
      exact ⟨fun hX => huniq X hX, fun hX => hX ▸ hK⟩
    rw [pLayer, hset, sSup_singleton]
  have hKt : footeK L t = K.map B.subtype := by
    rw [footeK, ← hBdef, hlayer]
  have hKB : footeK L t ≤ B := hKt ▸ map_subtype_le K
  have hKsub : (footeK L t).subgroupOf B = K := by
    rw [hKt]
    exact Subgroup.comap_map_eq_self_of_injective B.subtype_injective K
  have eK : ↥K ≃* ↥(footeK L t) :=
    (K.equivMapOfInjective B.subtype B.subtype_injective).trans
      (MulEquiv.subgroupCongr hKt.symm)
  have htK : t ∈ footeK L t ↔ t' ∈ K := by
    rw [hKt]
    constructor
    · rintro ⟨y, hy, hyt⟩
      have : y = t' := Subtype.ext hyt
      rw [← this]
      exact hy
    · intro h1
      exact ⟨t', h1, rfl⟩
  refine ⟨hKB, hKsub ▸ hK, fun K₁ hK₁B hK₁ => ?_, hKt ▸ hpc K hK, ?_, fun x hx hx2 => ?_⟩
  · have h1 := huniq _ hK₁
    rw [← map_subgroupOf_eq_of_le hK₁B, h1, hKt]
  · rcases htype with ⟨hBen, htK'⟩ | ⟨hSz, htK'⟩
    · exact Or.inl ⟨QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
        (quotientPPrimeCoreCongr eK) hBen, fun h1 => htK' (htK.mp h1)⟩
    · exact Or.inr ⟨IsCoverOverTwo.of_mulEquiv (quotientPPrimeCoreCongr eK).symm hSz,
        htK.mpr htK'⟩
  · have h1 := hinv ⟨x, hx⟩ (by rw [Subgroup.orderOf_mk]; exact hx2)
    have h2 : x ∈ (K ⊔ zpowers t').map B.subtype := ⟨⟨x, hx⟩, h1, rfl⟩
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hKt] at h2
    exact h2

end CFSG.ComponentClassification.FooteLit
