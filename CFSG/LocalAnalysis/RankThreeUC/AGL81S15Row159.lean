module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.ABGLocalTools

theorem exists_yComponent_dvd_aux_isComponentOf_conj {Y : Type} [Group Y] {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (g : Y) :
    CFSG.Open.IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL

theorem exists_yComponent_dvd_aux_not_dvd_card_iSup {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (S : Set (Subgroup Y)) (hS : ∀ K ∈ S, ¬ p ∣ Nat.card K)
    (hc : ∀ K ∈ S, ∀ K' ∈ S, K ≠ K' → ∀ x ∈ K, ∀ y ∈ K', Commute x y) :
    ¬ p ∣ Nat.card (⨆ K ∈ S, K : Subgroup Y) := by
  haveI : Fintype ↥S := Fintype.ofFinite _
  let H : ↥S → Subgroup Y := fun i => i.1
  have hcomm : Pairwise fun i j : ↥S => ∀ x y : Y, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact hc i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx y hy
  have hrange : (Subgroup.noncommPiCoprod hcomm).range = ⨆ K ∈ S, K := by
    rw [Subgroup.noncommPiCoprod_range]
    exact (iSup_subtype' (p := fun K => K ∈ S) (f := fun K _ => K)).symm
  intro hdvd
  rw [← hrange] at hdvd
  have h1 := hdvd.trans (Subgroup.card_range_dvd _)
  rw [Nat.card_pi] at h1
  rw [(Nat.prime_iff.mp hp).dvd_finset_prod_iff] at h1
  obtain ⟨i, -, hi⟩ := h1
  exact hS i.1 i.2 hi

theorem exists_yComponent_dvd_aux_normal_sup {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) :
    ∃ J : Subgroup Y, J.Normal ∧ ¬ p ∣ Nat.card J ∧
      ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ → ¬ p ∣ Nat.card K → K ≤ J := by
  set S : Set (Subgroup Y) := {K | CFSG.Open.IsComponentOf K ⊤ ∧ ¬ p ∣ Nat.card K} with hSdef
  set J : Subgroup Y := ⨆ K ∈ S, K with hJ
  have hcard : ¬ p ∣ Nat.card J := by
    refine exists_yComponent_dvd_aux_not_dvd_card_iSup hp S (fun K hK => hK.2) ?_
    intro K hK K' hK' hne x hx y hy
    have h := kComp_holds.1 Y K K' hK.1 hK'.1 hne
    have hle : K ≤ Subgroup.centralizer (K' : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  have hle : ∀ K ∈ S, K ≤ J := fun K hK => le_iSup₂ (f := fun K (_ : K ∈ S) => K) K hK
  have hconj : ∀ g : Y, J.map (MulAut.conj g).toMonoidHom ≤ J := by
    intro g
    rw [hJ, Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    refine hle _ ⟨exists_yComponent_dvd_aux_isComponentOf_conj hK.1 g, ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hK.2
  refine ⟨J, ⟨fun n hn g => ?_⟩, hcard, fun K hK hpK => hle K ⟨hK, hpK⟩⟩
  have := hconj g ⟨n, hn, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem exists_yComponent_dvd_aux_isSylowOf_sup {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {A N C P : Subgroup X} [N.Normal] (hCA : C ≤ A)
    (hidx : ¬ p ∣ C.relIndex N) (hP : IsSylowOf p P A) : IsSylowOf p P (A ⊔ N) := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hle, hpg, hdvd⟩ := hP
  refine ⟨hle.trans le_sup_left, hpg, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P A (A ⊔ N) hle le_sup_left]
  have h1 : A.relIndex (A ⊔ N) = A.relIndex N := by
    rw [sup_comm]
    exact relIndex_sup_eq_relIndex_of_normal N A
  have h2 : A.relIndex N ∣ C.relIndex N := Subgroup.relIndex_dvd_of_le_left N hCA
  intro h
  rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
  · exact hdvd h
  · rw [h1] at h
    exact hidx (h.trans h2)

theorem exists_yComponent_dvd_aux_map_subtype_smul {X : Type} [Group X] {q : ℕ} [Fact q.Prime]
    (M : Subgroup X) (g : M) (T : Sylow q M) :
    ((g • T : Sylow q M) : Subgroup M).map M.subtype =
      ((T : Subgroup M).map M.subtype).map (MulAut.conj (g : X)).toMonoidHom := by
  ext x
  simp only [Sylow.coe_subgroup_smul, Subgroup.mem_map,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · refine ⟨g⁻¹ * y * g, ?_, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using hy
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hz
    · simp [MulAut.conj_apply]

theorem exists_yComponent_dvd_aux_sylow_conj {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {K P P' : Subgroup X} (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ g : X, P' = P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  exact ⟨(g : X), by rw [← hg, exists_yComponent_dvd_aux_map_subtype_smul]⟩

theorem exists_yComponent_dvd_aux_pRank_map_conj {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : 1 < p) (P : Subgroup X) (g : X) :
    CFSG.Open.pRank p (P.map (MulAut.conj g).toMonoidHom) = CFSG.Open.pRank p P := by
  refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map hp _ (MulAut.conj g).injective P)
  have h := CFSG.SectionRank.pRank_le_map hp (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective (P.map (MulAut.conj g).toMonoidHom)
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h

theorem exists_yComponent_dvd_aux_pRank_eq_of_sylow {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {K P P' : Subgroup X} (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    CFSG.Open.pRank p P' = CFSG.Open.pRank p P := by
  obtain ⟨g, rfl⟩ := exists_yComponent_dvd_aux_sylow_conj h h'
  exact exists_yComponent_dvd_aux_pRank_map_conj (Fact.out : p.Prime).one_lt P g

theorem exists_yComponent_dvd_aux_pRank_sylow {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p X) :
    CFSG.Open.pRank p (Q : Subgroup X) = CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  refine le_antisymm (CFSG.SectionRank.pRank_mono hp le_top) ?_
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup X)
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨Q', hEQ'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q Q'
  have hQ' : (Q' : Subgroup X) = (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ CFSG.Open.pRank p (Q' : Subgroup X) :=
    CFSG.SectionRank.le_pRank hp hEQ' hE hEcard
  rw [hQ', exists_yComponent_dvd_aux_pRank_map_conj hp] at h1
  exact h1

theorem exists_yComponent_dvd_aux_isCyclic {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p P) (h : CFSG.Open.pRank p P ≤ 1) :
    IsCyclic P := by
  by_contra hnc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian p (S.map P.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hcard : Nat.card (S.map P.subtype) = p ^ 2 := by
    rw [← hScard]
    exact (Nat.card_congr (S.equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le S)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hSm) hcard
  omega

section Main

open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem exists_yComponent_dvd {p : ℕ} (hW : KWiel) (hH : KHupAt p) {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    (h₁ : CFSG.Open.pRank p (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank p (Subgroup.normalizer (T₂ : Set X)) ≤ 1) :
    ∃ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls ∧ p ∣ Nat.card Ls := by
  by_contra hcon
  push Not at hcon
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨J, hJn, hJc, hJle⟩ := exists_yComponent_dvd_aux_normal_sup (Y := X ⧸ gnC T) hp
  have hYJ : Ystar T T₁ T₂ ≤ J := iSup₂_le fun L hL => hJle L hL.1 (hcon L hL)
  set N : Subgroup X := J.comap (toStar T) with hN
  haveI : N.Normal := hJn.comap _
  have hY0N : Y0 T T₁ T₂ ≤ N := Subgroup.comap_mono hYJ
  have hCN : gnC T ≤ N := by
    intro x hx
    show toStar T x ∈ J
    rw [show toStar T x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact J.one_mem
  have hNcard : Nat.card N = Nat.card (gnC T) * Nat.card J :=
    QuotientGroup.card_preimage_mk (gnC T) (J : Set (X ⧸ gnC T))
  have hrel : (gnC T).relIndex N = Nat.card J := by
    have h1 := Subgroup.relIndex_mul_card (gnC T) N
    rw [inf_eq_left.mpr hCN, hNcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))
  have hidx : ¬ p ∣ (gnC T).relIndex N := by
    rw [hrel]
    exact hJc
  set A : Subgroup X := Subgroup.centralizer (T₁ : Set X) with hA
  set B : Subgroup X := Subgroup.normalizer (T₂ : Set X) with hB
  have hCA : gnC T ≤ A := by
    apply Subgroup.centralizer_le
    intro x hx
    exact Subgroup.le_normalClosure (hg.pair.le_center hx)
  have hAB : ∀ x : X, ∃ a ∈ A ⊔ N, ∃ b ∈ B, x = a * b := by
    intro x
    obtain ⟨a, ha, y, hy, b, hb, rfl⟩ := hg.factor x
    exact ⟨a * y, Subgroup.mul_mem_sup ha (hY0N hy), b, hb, rfl⟩
  obtain ⟨P₁, P₂, hP₁, hP₂, ⟨Q, hQ⟩, hset⟩ := hW X (A ⊔ N) B p hp hAB
  obtain ⟨PA, hPA⟩ := exists_isSylowOf p A
  have hPA' : IsSylowOf p PA (A ⊔ N) := exists_yComponent_dvd_aux_isSylowOf_sup hCA hidx hPA
  have hr₁ : CFSG.Open.pRank p P₁ ≤ 1 := by
    rw [exists_yComponent_dvd_aux_pRank_eq_of_sylow hPA' hP₁]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hPA.le).trans
      ((CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.centralizer_le_normalizer _)).trans h₁)
  have hr₂ : CFSG.Open.pRank p P₂ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hP₂.le).trans h₂
  have hc₁ := exists_yComponent_dvd_aux_isCyclic hp hp2 hP₁.isPGroup hr₁
  have hc₂ := exists_yComponent_dvd_aux_isCyclic hp hp2 hP₂.isPGroup hr₂
  have hWp : IsPGroup p (P₁ ⊔ P₂ : Subgroup X) := by
    rw [← hQ]
    exact Q.isPGroup'
  have hprod : ∀ w ∈ (P₁ ⊔ P₂ : Subgroup X), ∃ a ∈ P₁, ∃ b ∈ P₂, w = a * b := by
    intro w hw
    have hw' : w ∈ (P₁ : Set X) * (P₂ : Set X) := hset ▸ hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw'
    exact ⟨a, ha, b, hb, rfl⟩
  have h2 := hH X (P₁ ⊔ P₂) P₁ P₂ hWp le_sup_left le_sup_right hc₁ hc₂ hprod
  rw [← hQ, exists_yComponent_dvd_aux_pRank_sylow] at h2
  omega

end Main

theorem exists_yComponent_dvd_ctx_gen {p : ℕ} (hW : KWiel) (hH : KHupAt p) {G : Type} [Group G]
    [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hp : p ∈ sigmaM G M) :
    ∃ Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M)),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls ∧ p ∣ Nat.card Ls :=
  exists_yComponent_dvd hW hH ctx.gn
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.good ctx)
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1)
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1) (ctx.three_le p hp)
    (ctx.rank_N₁ p hp) (ctx.rank_N₂ p hp)

end CFSG.LocalAnalysis.RankThreeUC.S15
