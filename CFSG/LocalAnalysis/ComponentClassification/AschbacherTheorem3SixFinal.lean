module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixGoldFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem one_le_pRank {T : Subgroup X} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    1 ≤ CFSG.Open.pRank 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card T := by
    rcases hT2.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hT
    · exact h1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hto : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hel : IsElemAbelian 2 (Subgroup.zpowers (t : X)) := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hto, pow_orderOf_eq_one,
      one_zpow]
  refine CFSG.SectionRank.le_pRank one_lt_two (Subgroup.zpowers_le.mpr t.2) hel ?_
  rw [Nat.card_zpowers, hto, pow_one]

theorem concl46_of_top (hG : CFSG.Goldschmidt.TopStatement) (hK : Theorem3KnownGroupFacts)
    {G T S Q H : Subgroup X} {g : X} (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X))) (hS : SylowFrame G T S) (h43 : Hyp43 G T Q H)
    (hT : T ≠ ⊥) (hO : CFSG.oddCore G = ⊥) (hg : g ∈ G)
    (hW : relativeWeakClosure G T S = T ⊔ rightConjugate T g)
    (hgN : rightConjugate T g ≤ Subgroup.normalizer (T : Set X)) : Concl46 G T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Concl46
  by_cases hne : rightConjugate T g = T
  ·
    right; left
    have hWT : relativeWeakClosure G T S = T := by rw [hW, hne, sup_idem]
    have h := lemma_4_2_oddCore ⟨hS.toFrame, hS.sylow, hS.le, fun x hx hle =>
      Subgroup.eq_of_le_of_card_ge
        ((rightConjugate_le_relativeWeakClosure hx hle).trans hWT.le)
        (by rw [rightConjugate_card])⟩
    rw [hO, Subgroup.map_bot, le_bot_iff] at h
    rw [hWT]
    refine sup_le ?_ Subgroup.le_normalizer
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le_normalizer _)
  by_cases hm : CFSG.Open.pRank 2 T ≤ 1
  · left
    have := one_le_pRank hS.isPGroup hT
    omega
  push Not at hm
  have c : Conf46 G T S Q H g := ⟨hS, h43, hg, hne, hgN, hW, hm⟩
  right
  by_cases hD : ∃ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D ∧
      D ≤ S ⊓ G ∧ G ≤ Subgroup.normalizer (D : Set X)
  ·
    left
    obtain ⟨D, hZD, hDS, hDN⟩ := hD
    rw [hW]
    exact c.caseOne htop hO IH hZD hDS hDN
  ·
    right
    have hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
        G ≤ Subgroup.normalizer (D : Set X) → False :=
      fun D h1 h2 h3 => hD ⟨D, h1, h2, h3⟩
    have hGn : G.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
    have hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) ≤ G :=
      Subgroup.normalClosure_le_normal
        (SetLike.coe_subset_coe.mpr ((omegaOne_le _).trans inf_le_right))
    rcases eq_or_lt_of_le hMG with heq | hlt
    · exact c.bender_of_eq htop hO IH hnn hG hK heq
    · exact c.bender_of_lt htop hO IH hnn hlt

omit [Finite X] in
theorem map_pCoreOf_subtype (L : Subgroup X) (K : Subgroup L) :
    (pCoreOf 2 K).map L.subtype = pCoreOf 2 (K.map L.subtype) := by
  set e : K ≃* K.map L.subtype := K.equivMapOfInjective L.subtype L.subtype_injective with he
  rw [pCoreOf, pCoreOf, Subgroup.map_map, ← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e,
    Subgroup.map_map]
  rfl

omit [Finite X] in
theorem IsBenderType.of_mulEquiv {Y : Type} [Group Y] {B : Subgroup X} {B' : Subgroup Y} {n : ℕ}
    (e : B ≃* B') (h : IsBenderType B' n) : IsBenderType B n := by
  rcases h with ⟨hn, ⟨e'⟩⟩ | ⟨m, hm, hmn, ⟨e'⟩⟩ | ⟨hn, ⟨e'⟩⟩
  · exact Or.inl ⟨hn, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨m, hm, hmn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨hn, ⟨e.trans e'⟩⟩)

omit [Finite X] in
theorem Bender46.of_subgroupOf {L G T S : Subgroup X} (hGL : G ≤ L) (hTL : T ≤ L)
    (hSL : S ≤ L) (h : Bender46 (G.subgroupOf L) (T.subgroupOf L) (S.subgroupOf L)) :
    Bender46 G T S := by
  obtain ⟨n, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  set f := L.subtype with hf
  have hfi : Function.Injective f := L.subtype_injective
  have hGm : (G.subgroupOf L).map f = G := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hGL]
  have hTm : (T.subgroupOf L).map f = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
  have hBm : ⁅T.subgroupOf L, G.subgroupOf L⁆.map f = ⁅T, G⁆ := by
    rw [Subgroup.map_commutator, hTm, hGm]
  have hcc : (conjugateClosure (G.subgroupOf L) (T.subgroupOf L)).map f =
      conjugateClosure G T := by
    rw [FourEight.conjugateClosure_eq, FourEight.conjugateClosure_eq, Subgroup.map_sup, hTm, hBm]
  have hAm : (pCoreOf 2 (conjugateClosure (G.subgroupOf L) (T.subgroupOf L))).map f =
      pCoreOf 2 (conjugateClosure G T) := by
    rw [hf, map_pCoreOf_subtype, ← hf, hcc]
  have hWm : (relativeWeakClosure (G.subgroupOf L) (T.subgroupOf L) (S.subgroupOf L)).map f =
      relativeWeakClosure G T S := relativeWeakClosure_subgroupOf hGL hTL hSL
  refine ⟨n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (Subgroup.map f) h1
    rwa [hcc, Subgroup.map_sup, hAm, hBm] at this
  · have := congrArg (Subgroup.map f) h2
    rwa [Subgroup.map_inf_eq _ _ _ hfi, hAm, hBm, Subgroup.map_bot] at this
  · have := congrArg (Subgroup.map f) h3
    rwa [Subgroup.map_commutator, hAm, hBm, Subgroup.map_bot] at this
  · rw [← hAm]
    exact CFSG.SectionRank.isElemAbelian_map h4 f
  · rw [← hAm, Subgroup.card_map_of_injective hfi, h5]
  · exact IsBenderType.of_mulEquiv ((MulEquiv.subgroupCongr hBm.symm).trans
      (⁅T.subgroupOf L, G.subgroupOf L⁆.equivMapOfInjective f hfi).symm) h6
  · rw [← hTm]
    exact CFSG.SectionRank.isElemAbelian_map h7 f
  · rw [← hTm, Subgroup.card_map_of_injective hfi, h8]
  · have := Subgroup.map_mono (f := f) h9
    rwa [Subgroup.map_inf_eq _ _ _ hfi, hWm, hGm, hBm] at this
  · have := congrArg (Subgroup.map f) h10
    rwa [Subgroup.map_inf_eq _ _ _ hfi, hTm, hAm, Subgroup.map_bot] at this

theorem concl46_of_subgroupOf {L G T S : Subgroup X} (hGL : G ≤ L) (hTL : T ≤ L)
    (hSL : S ≤ L) (h : Concl46 (G.subgroupOf L) (T.subgroupOf L) (S.subgroupOf L)) :
    Concl46 G T S := by
  have hTm : (T.subgroupOf L).map L.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
  have hGm : (G.subgroupOf L).map L.subtype = G := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hGL]
  rcases h with hm | hN | hB
  · left
    rw [← pRank_map_eq L.subtype L.subtype_injective, hTm] at hm
    exact hm
  · right; left
    intro x hx
    rw [← hGm, ← hTm, ← Subgroup.map_sup] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 := Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype (hN hy))
    rwa [relativeWeakClosure_subgroupOf hGL hTL hSL] at h1
  · right; right
    exact Bender46.of_subgroupOf hGL hTL hSL hB

theorem concl46_step (hG : CFSG.Goldschmidt.TopStatement) (hK : Theorem3KnownGroupFacts)
    {G T S Q H : Subgroup X} {g : X} (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hS : SylowFrame G T S) (h43 : Hyp43 G T Q H) (hT : T ≠ ⊥) (hO : CFSG.oddCore G = ⊥)
    (hg : g ∈ G) (hW : relativeWeakClosure G T S = T ⊔ rightConjugate T g)
    (hgN : rightConjugate T g ≤ Subgroup.normalizer (T : Set X)) : Concl46 G T S := by
  set L := G ⊔ T with hL
  have hGL : G ≤ L := le_sup_left
  have hTL : T ≤ L := le_sup_right
  have hSL : S ≤ L := hS.sylow.le
  set G' := G.subgroupOf L with hG'
  set T' := T.subgroupOf L with hT'def
  set S' := S.subgroupOf L with hS'def
  have hS' : SylowFrame G' T' S' := hS.subgroupOf
  have h43' := h43.subgroupOf
  have htop : G' ⊔ T' = ⊤ := sup_subgroupOf_eq_top G T
  have hTm : T'.map L.subtype = T := by
    rw [hT'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
  have hT'ne : T' ≠ ⊥ := fun h => hT (by rw [← hTm, h, Subgroup.map_bot])
  have hO' : CFSG.oddCore G' = ⊥ := by
    have h1 := map_subtype_oddCore_subgroupOf hGL
    rw [hO, Subgroup.map_bot] at h1
    have h2 := (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ G'.subtype_injective).mp h2
  set g' : L := ⟨g, hGL hg⟩
  have hg' : g' ∈ G' := hg
  have hconjm : ∀ x : L, (rightConjugate T' x).map L.subtype = rightConjugate T x :=
    fun x => by rw [map_rightConjugate, hTm]; rfl
  have hW'm : (relativeWeakClosure G' T' S').map L.subtype = relativeWeakClosure G T S :=
    relativeWeakClosure_subgroupOf hGL hTL hSL
  have hW' : relativeWeakClosure G' T' S' = T' ⊔ rightConjugate T' g' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hW'm, Subgroup.map_sup, hTm, hconjm, hW]
  have hgN' : rightConjugate T' g' ≤ Subgroup.normalizer (T' : Set L) := by
    intro y hy
    rw [hT'def, ← Subgroup.subgroupOf_normalizer_eq hTL]
    have h1 := Subgroup.mem_map_of_mem L.subtype hy
    rw [hconjm] at h1
    exact hgN h1
  have hcard : Nat.card (G' ⊔ T' : Subgroup L) = Nat.card (G ⊔ T : Subgroup X) := by
    rw [htop, Subgroup.card_top]
  have IH' : IH46 (Nat.card (G' ⊔ T' : Subgroup L)) := by rw [hcard]; exact IH
  exact concl46_of_subgroupOf hGL hTL hSL
    (concl46_of_top hG hK htop IH' hS' h43' hT'ne hO' hg' hW' hgN')

theorem ih46 (hG : CFSG.Goldschmidt.TopStatement) (hK : Theorem3KnownGroupFacts) (n : ℕ) :
    IH46 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ G T S Q H g hcard hS h43 hT hO hg hW hgN
    exact concl46_step hG hK (ih _ hcard) hS h43 hT hO hg hW hgN

theorem concl46 (hG : CFSG.Goldschmidt.TopStatement) (hK : Theorem3KnownGroupFacts)
    {G T S Q H : Subgroup X} {g : X} (hS : SylowFrame G T S) (h43 : Hyp43 G T Q H) (hT : T ≠ ⊥)
    (hO : CFSG.oddCore G = ⊥) (hg : g ∈ G)
    (hW : relativeWeakClosure G T S = T ⊔ rightConjugate T g)
    (hgN : rightConjugate T g ≤ Subgroup.normalizer (T : Set X)) : Concl46 G T S :=
  concl46_step hG hK (ih46 hG hK _) hS h43 hT hO hg hW hgN

theorem lemma_4_6 (hG : CFSG.Goldschmidt.TopStatement) (hK : Theorem3KnownGroupFacts) :
    Lemma46Statement := by
  intro Y _ _ G T S Q H g hS h43 hT hO hg hW hgN
  rcases concl46 hG hK hS h43 hT hO hg hW hgN with hm | hN | hB
  · exact Or.inl hm
  · exact Or.inr (Or.inl hN)
  · exact Or.inr (Or.inr hB.lemma46)

end CFSG.ComponentClassification.AschbacherTheorem3
