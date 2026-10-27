module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NormalizerClosure
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP.Fus

section Aut

variable {K : Type*} [Group K]

theorem mem_inner_of_pow_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime)
    (hOut : ¬ p ∣ Nat.card (Outer K)) {f : MulAut K} (hf : f ^ p = 1) : f ∈ inner K := by
  have h1 : orderOf (QuotientGroup.mk' (inner K) f) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hf, map_one])
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  · exact absurd (h ▸ orderOf_dvd_natCard _) hOut

theorem isElemAbelian_comap_of_injective {H : Type*} [Group H] {p : ℕ} {f : K →* H}
    (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  have := hE.1
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨f a, a.2⟩ : E) ⟨f b, b.2⟩)
  · rw [map_pow, map_one]
    exact hE.2 _ hx

end Aut

theorem pRank_top_mulAut_le_of_not_dvd {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center K = ⊥) (hOut : ¬ p ∣ Nat.card (Outer K)) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MulAut K))
  have hinj := mulAut_conj_injective hZ
  have hEc : E ≤ (MulAut.conj : K →* MulAut K).range := fun f hf =>
    mem_inner_of_pow_eq_one_of_not_dvd hp hOut (hE.2 f hf)
  refine SectionRank.le_pRank hp.one_lt le_top (isElemAbelian_comap_of_injective hinj hE) ?_
  rw [← hcard, ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hEc]

section Fusion

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem one_le_pRank_of_isPGroup_of_ne_bot (hp : p.Prime) {H : Subgroup G} (hH : IsPGroup p H)
    (hne : H ≠ ⊥) : 1 ≤ Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card H :=
    hH.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx' : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  refine SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.mpr x.2)
    (isElemAbelian_zpowers (hx' ▸ pow_orderOf_eq_one (x : G))) ?_
  rw [Nat.card_zpowers, hx', pow_one]

theorem le_glbCore_one_of_ne_bot (hp : p.Prime) (T : Sylow p G) (hT : (T : Subgroup G) ≠ ⊥) :
    (T : Subgroup G) ≤ GLBCore p 1 (T : Subgroup G) := by
  have h1 : 1 ≤ Open.pRank p (T : Subgroup G) :=
    one_le_pRank_of_isPGroup_of_ne_bot hp T.isPGroup' hT
  have h := RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 p (T : Subgroup G)
    (T : Subgroup G) le_rfl h1
  exact Subgroup.le_normalizer.trans h

theorem mem_glbCore_one_of_conj_mem (hp : p.Prime) (T : Sylow p G) {t g : G}
    (ht : t ∈ (T : Subgroup G)) (ht1 : t ≠ 1) (hg : g * t * g⁻¹ ∈ (T : Subgroup G)) :
    g ∈ GLBCore p 1 (T : Subgroup G) := by
  have hT : (T : Subgroup G) ≠ ⊥ := fun h => ht1 (Subgroup.mem_bot.mp (h ▸ ht))
  have hTΓ := le_glbCore_one_of_ne_bot hp T hT
  have hpt : IsPGroup p (Subgroup.zpowers t) := T.isPGroup'.to_le (Subgroup.zpowers_le.mpr ht)
  refine RankThreeCoreUniqueness.Helpers.normalizer_closure_transporter_mem 1 p hp _
    (RankThreeCoreUniqueness.Helpers.gamma_rank_normalizer_le_overgroup 1 p hp T _ hTΓ le_rfl)
    (Subgroup.zpowers t) hpt (Subgroup.zpowers_le.mpr (hTΓ ht))
    (one_le_pRank_of_isPGroup_of_ne_bot hp hpt (by rwa [Ne, Subgroup.zpowers_eq_bot])) g ?_
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
  exact hTΓ hg

end Fusion

theorem glbCore_one_eq_top_of_fusionGenerationOf {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h : FusionGenerationOf K p) (T : Sylow p K) :
    GLBCore p 1 (T : Subgroup K) = ⊤ := by
  obtain ⟨E, Γ, hEp, -, hΓ, hfus⟩ := h
  obtain ⟨x, hx⟩ := RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup
    p hp T ⊤ le_top E hEp le_top
  have hgen : Γ ⊆ (GLBCore p 1 (T : Subgroup K)).comap (MulAut.conj (x : K)).toMonoidHom := by
    intro g hg
    obtain ⟨e, he, he1, hge⟩ := hfus g hg
    refine mem_glbCore_one_of_conj_mem hp T (t := MulAut.conj (x : K) e) (hx ⟨e, he, rfl⟩) ?_ ?_
    · rwa [Ne, map_eq_one_iff _ (MulAut.conj (x : K)).injective]
    · convert hx ⟨g * e * g⁻¹, hge, rfl⟩ using 1
      simp [MulAut.conj_apply, mul_assoc]
  have hle := (Subgroup.closure_le _).mpr hgen
  rw [hΓ] at hle
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨z, rfl⟩ := (MulAut.conj (x : K)).surjective y
  exact hle (Subgroup.mem_top z)

section Conclusion

variable {X : Type} [Group X] [Finite X] {p : ℕ}

omit [Finite X] in
theorem center_eq_bot_of_isSimpleGroup_of_nonabelian (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases hX.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab

theorem pRank_le_one_of_isCyclic_sylow (hp : p.Prime) (T : Sylow p X)
    (hT : IsCyclic (T : Subgroup X)) : Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine SectionRank.pRank_le hp.one_lt fun A _ hA => ?_
  rw [pow_one]
  exact card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA

omit [Finite X] in
theorem commute_of_card_eq_pow_le_two (hp : p.Prime) {n : ℕ} (hn : Nat.card X = p ^ n)
    (hn2 : n ≤ 2) (a b : X) : a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  interval_cases n
  · have : Subsingleton X := (Nat.card_eq_one_iff_unique.mp (by rw [hn, pow_zero])).1
    exact Subsingleton.elim _ _
  · have : IsCyclic X := isCyclic_of_prime_card (by rw [hn, pow_one])
    exact mul_comm' a b
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
    exact mul_comm' a b

theorem pRank_le_two_of_hasNoncommPair (hp : p.Prime) (h4 : ¬ p ^ 4 ∣ Nat.card X)
    (h : HasNoncommPair p X) : Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, -, -, hxy, hS⟩ := h
  have hxS : x ∈ Subgroup.closure ({x, y} : Set X) := Subgroup.subset_closure (by simp)
  have hyS : y ∈ Subgroup.closure ({x, y} : Set X) := Subgroup.subset_closure (by simp)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
  have hle : n ≤ 3 := by
    by_contra hlt
    exact h4 ((pow_dvd_pow p (by omega)).trans
      (hn ▸ Subgroup.card_subgroup_dvd_card (Subgroup.closure ({x, y} : Set X))))
  have hge : 3 ≤ n := by
    by_contra hlt
    exact hxy (congrArg Subtype.val
      (commute_of_card_eq_pow_le_two hp hn (by omega) ⟨x, hxS⟩ ⟨y, hyS⟩))
  exact RankThree.PartTwo.Census.pRank_le_two_of_nonabelian hp h4
    (hn.trans (by rw [le_antisymm hle hge])) ⟨x, hxS, y, hyS, hxy⟩

end Conclusion

theorem kFactBetaConclusion_of_data (K : Type) [Group K] [Finite K] (hK : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : SporadicBetaData K) : KFactBetaConclusion K := by
  intro p hp hp2 T _ hT
  left
  obtain ⟨hOut, hdata⟩ := h
  have hOutp : ¬ p ∣ Nat.card (Outer K) := fun hd => by
    have := Nat.le_of_dvd Nat.card_pos hd
    have := hp.two_le
    omega
  refine (pRank_top_mulAut_le_of_not_dvd hp
    (center_eq_bot_of_isSimpleGroup_of_nonabelian hK hnab) hOutp).trans ?_
  rcases hdata p hp hp2 with h3 | ⟨h4, hpair⟩ | hfus
  · exact RankThree.PartTwo.Census.pRank_le_two_of_not_dvd hp h3
  · exact pRank_le_two_of_hasNoncommPair hp h4 hpair
  · have hcyc := hT.resolve_right (not_not.mpr (glbCore_one_eq_top_of_fusionGenerationOf hp hfus T))
    exact (pRank_le_one_of_isCyclic_sylow hp T hcyc).trans (by norm_num)

theorem fusionGenerationOf_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : FusionGenerationOf X p) : FusionGenerationOf Y p := by
  obtain ⟨E, Γ, hEp, hE1, hΓ, hfus⟩ := h
  refine ⟨E.map e.toMonoidHom, e.toMonoidHom '' Γ, hEp.map _, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha, ha1, hga⟩ := hfus g hg
    refine ⟨e a, ⟨a, ha, rfl⟩, ?_, ⟨g * a * g⁻¹, hga, by simp⟩⟩
    rwa [Ne, map_eq_one_iff _ e.injective]

theorem SporadicBetaData.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    SporadicBetaData X → SporadicBetaData Y := by
  rintro ⟨hOut, h⟩
  refine ⟨(Nat.card_congr (equivalence e).symm.toEquiv).trans_le hOut, fun p hp hp2 => ?_⟩
  rw [Nat.card_congr e.symm.toEquiv]
  rcases h p hp hp2 with h3 | ⟨h4, hpair⟩ | hfus
  · exact Or.inl h3
  · exact Or.inr (Or.inl ⟨h4, hpair.map e.toMonoidHom e.injective⟩)
  · exact Or.inr (Or.inr (fusionGenerationOf_of_mulEquiv e hfus))

theorem kFactBetaSpor_of_data
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h : ∀ s, s ≠ .M → SporadicBetaData (Blueprint.NativeSporadic.Carrier s))
    (hM : MonsterBetaData) : KFactBetaSpor := by
  intro K _ _ hK hnab s ⟨e⟩
  obtain ⟨b⟩ := hbr s
  refine kFactBetaConclusion_of_data K hK hnab ?_
  by_cases hs : s = .M
  · subst hs
    exact hM K hnab ⟨e.trans b.symm⟩
  · exact (h s hs).of_mulEquiv (e.trans b.symm).symm

end CFSG.AGLEmbedding
