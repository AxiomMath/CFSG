module

public import CFSG.LieType.SeitzGeneration.Regimes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPOne
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporOneLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveFinal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Tits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharCyc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharU42
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporB7

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding

theorem isElemAbelian_comap_inj {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  obtain ⟨⟨hc⟩, hx⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx' => ?_⟩
  · apply Subtype.ext
    apply hf
    have := hc.comm ⟨f (a : G), a.2⟩ ⟨f (b : G), b.2⟩
    have h := congrArg Subtype.val this
    change f ((a : G) * b) = f ((b : G) * a)
    rw [map_mul, map_mul]
    exact h
  · apply hf
    rw [map_pow, map_one]
    exact hx _ hx'

theorem glbCore_eq_top_of_seitzEx (hS : KFactSeitzRankTwoInnerEx) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* CatGroup d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) (T : Sylow p K) (hT : ¬ IsCyclic (T : Subgroup K)) :
    GLBCore p 1 (T : Subgroup K) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p (T : Subgroup K)) := ⟨T.isPGroup'⟩
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hT
  set E₀ : Subgroup K := E.map (T : Subgroup K).subtype with hE₀
  have hEel' : IsElemAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEel
  have hE₀el : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEel' _
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hEcard]
  have hinj := conj_injective_of_simple hs hnab
  let ψ : K →* MulAut (CatGroup d) := (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hinj
  have hψel : IsElemAbelian p (E₀.map ψ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el ψ
  obtain ⟨E', hE'el, hE'card, hE'inner, hE'gen⟩ := hS d p hp hp2 hpd hex
    ⟨E₀.map ψ, hψel, by rw [Subgroup.card_map_of_injective hψ, hE₀card],
      InnerPlane.map_congr_conj e E₀ p⟩
  have hrange : E' ≤ ψ.range := by
    intro ε hε
    obtain ⟨c, hc⟩ := hE'inner hε
    refine ⟨e.symm c, ?_⟩
    rw [← hc]
    change (MulAut.congr e).toMonoidHom (MulAut.conj (e.symm c)) = MulAut.conj c
    rw [mulAut_congr_conj e, MulEquiv.apply_symm_apply]
  set E₁ : Subgroup K := E'.comap ψ with hE₁
  have hmap : E₁.map ψ = E' := Subgroup.map_comap_eq_self hrange
  have hE₁el : IsElemAbelian p E₁ := isElemAbelian_comap_inj ψ hψ hE'el
  have hclos : Subgroup.closure {c : CatGroup d | ∃ ε ∈ E₁.map ψ, ε ≠ 1 ∧ ε c = c} = ⊤ := by
    rw [hmap]
    exact hE'gen
  have hle : (⊤ : Subgroup (CatGroup d)) ≤ (GLBCore p 1 E₁).map e.toMonoidHom := by
    rw [← hclos, Subgroup.closure_le]
    rintro c ⟨ε, hε, hε1, hεc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hε
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    refine ⟨e.symm c, mem_glbCore_of_commute hp hE₁el hx hx1 ?_, by simp⟩
    have h1 : ψ x c = e (x * e.symm c * x⁻¹) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1] at hεc
    have h2 : x * e.symm c * x⁻¹ = e.symm c := by
      apply e.injective
      rw [hεc]
      simp
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hcore : GLBCore p 1 E₁ = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e k)))
    exact e.injective hk'e ▸ hk'
  exact glbCore_eq_top_of_mulEquiv hp (MulEquiv.refl K) (isPGroup_of_isElemAbelian hE₁el) hcore T

section OffCharGen

theorem offCharGen_of_seitzEx (hS : KFactSeitzRankTwoInnerEx) : OffCharGen := by
  intro K _ _ hs hnab d ⟨e⟩ p hp hp2 hpd T hT hL34 hTits
  by_cases hex : IsD2SeitzException p d.1
  swap
  · exact glbCore_eq_top_of_seitzEx hS hs hnab d e hp hp2 hpd hex T hT
  obtain ⟨d, hv⟩ := d
  change IsD2SeitzException p d at hex
  rcases hex with ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩
  · rcases hcase with ⟨q, hq2, hqe, hd⟩ | ⟨q, hq2, hqe, hd⟩ | ⟨q, hq2, hqe, hd⟩ |
      ⟨q, hq2, hqe, hd | hd⟩ | hd
    · subst hd
      exact absurd (isCyclic_sylow_three_linTwoEight q hq2 hqe hv e T) hT
    · exact absurd ⟨rfl, q, hq2, hqe, hd⟩ hL34
    · subst hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hq2, hqe] at h
      exact OffCharU42.glbCore_eq_top_of_stated_u42 h T
    · subst hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2
        le_rfl e
      rw [hq2, hqe] at h
      exact OffCharSp.glbCore_eq_top_of_stated_sp 3 le_rfl h T
    · subst hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hq2
        (by norm_num) e
      rw [hq2, hqe] at h
      exact OffCharSp.glbCore_eq_top_of_stated_sp 4 (by norm_num) h T
    · subst hd
      have h2 := kFactTitsThreeCore K ⟨.tits, hv⟩ rfl ⟨e⟩ T
      exact top_le_iff.mp (h2 ▸ glbCore_anti 3 (by norm_num : 1 ≤ 2) (T : Subgroup K))
  · rcases hcase with hd | hd
    · exact absurd ⟨rfl, hd⟩ hTits
    · subst hd
      exact absurd (isCyclic_sylow_five_suzuki 2 hv e T) hT
end OffCharGen

section SmallIdent

theorem kFactSmallIdent_of_seitzEx_of_rows (hS : KFactSeitzRankTwoInnerEx)
    (hHS5 : SporGammaOneAt .HS 5) (hB7 : SporGammaOneAt .B 7) (hM : SmallIdentSporAt .M) :
    KFactSmallIdent :=
  kFactSmallIdent_of_families smallIdentAlt smallIdentLieCharP
    (smallIdentLieOffChar_of_gen (offCharGen_of_seitzEx hS)) fun s => by
      by_cases hs : s = .M
      · subst hs
        exact hM
      · exact smallIdentSporAt_of_ne s hs hHS5 hB7

theorem kFactSmallIdent_of_seitzEx (hS : KFactSeitzRankTwoInnerEx)
    (hB7 : SporGammaOneAt .B 7) (hM : SmallIdentSporAt .M) : KFactSmallIdent :=
  kFactSmallIdent_of_seitzEx_of_rows hS sporGammaOneAt_HS_five hB7 hM

end SmallIdent

section OneLieIdent

theorem kFactOneLieIdent_of_seitzEx
    (hS : KFactSeitzRankTwoInnerEx)
    (hM : OneLieIdentSporAt .M) : KFactOneLieIdent :=
  kFactOneLieIdent_of_families oneLieIdentAlt (oneLieIdentLieCharP charPGen)
    (oneLieIdentLieOffChar_of_gen (offCharGen_of_seitzEx hS) offCharAut) fun s => by
      by_cases hs : s = .M
      · subst hs
        exact hM
      · exact oneLieIdentSporAt_of_ne s hs

end OneLieIdent

section SmallInvolve

theorem kFactSmallInvolve_of_seitzEx
    (hS : KFactSeitzRankTwoInnerEx)
    (hMS : SmallIdentSporAt .M) (hMO : OneLieIdentSporAt .M) : KFactSmallInvolve :=
  kFactSmallInvolve_of_bad (kFactOneLieIdent_of_seitzEx hS hMO)
    (kFactSmallIdent_of_seitzEx hS sporGammaOneAt_B_seven hMS) smallBadNonComm

end SmallInvolve

end CFSG.LieType.SeitzGeneration
