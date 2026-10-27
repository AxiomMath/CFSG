module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineShared
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open CFSG.QuasiDihedralFusion

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem involves_refl (A : Type*) [Group A] : Involves A A :=
  involves_of_surjective (MonoidHom.id A) Function.surjective_id

theorem involves_trans {A B C : Type*} [Group A] [Group B] [Group C] (hAB : Involves A B)
    (hBC : Involves B C) : Involves A C := by
  obtain ⟨U, φ, hφ⟩ := hAB
  obtain ⟨V, ψ, hψ⟩ := hBC
  refine ⟨(V.comap φ).map U.subtype, ψ.comp ((φ.subgroupComap V).comp
    ((V.comap φ).equivMapOfInjective U.subtype U.subtype_injective).symm.toMonoidHom), ?_⟩
  exact hψ.comp ((φ.subgroupComap_surjective V hφ).comp (MulEquiv.surjective _))

theorem involves_of_witness {M H N W : Subgroup G} (hn : (d1KBar p M H).Normal)
    (hW : W ≤ H ⊓ N)
    (hWH : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      d1KBar p M H)
    (hWN : (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
      d1KBar p M N) :
    Involves (d1KBar p M N) (d1KBar p M H) := by
  classical
  have hWHle : W ≤ H := hW.trans inf_le_left
  have hWNle : W ≤ N := hW.trans inf_le_right
  set fH : W →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hWHle)
  set fN : W →* N ⧸ primeComplementCore (G := N) p :=
    (QuotientGroup.mk' (primeComplementCore (G := N) p)).comp (Subgroup.inclusion hWNle)
  have hrH : fH.range = d1KBar p M H := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hWH]
  have hrN : fN.range ≤ d1KBar p M N := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hWN
  have hmemH : ∀ w, fH w ∈ d1KBar p M H := fun w => hrH ▸ ⟨w, rfl⟩
  set gH : W →* d1KBar p M H := fH.codRestrict _ hmemH
  have hgH : Function.Surjective gH := by
    rintro ⟨y, hy⟩
    rw [← hrH] at hy
    obtain ⟨w, rfl⟩ := hy
    exact ⟨w, rfl⟩
  set V : Subgroup (d1KBar p M H) := fN.ker.map gH
  have hV : V.Normal := Subgroup.Normal.map inferInstance gH hgH
  have hcop : p.Coprime (Nat.card V) := by
    have hker : fN.ker = (primeComplementCore (G := N) p).comap (Subgroup.inclusion hWNle) := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    refine ((primeComplementCore_coprime (G := N) p).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hWNle))).coprime_dvd_right
      ?_
    rw [← hker]
    exact Subgroup.card_map_dvd _ _
  have hVbot : V = ⊥ := noPPrime_of_normal _ V hV hcop
  have hle : fN.rangeRestrict.ker ≤ gH.ker := by
    intro w hw
    rw [MonoidHom.ker_rangeRestrict] at hw
    have : gH w ∈ V := ⟨w, hw, rfl⟩
    rw [hVbot] at this
    exact this
  set φ : fN.range →* d1KBar p M H :=
    (QuotientGroup.lift _ gH hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective _ fN.rangeRestrict_surjective).symm.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨w, rfl⟩ := hgH y
    refine ⟨fN.rangeRestrict w, ?_⟩
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show (QuotientGroup.quotientKerEquivOfSurjective _ fN.rangeRestrict_surjective).symm
      (fN.rangeRestrict w) = (w : W ⧸ fN.rangeRestrict.ker) from
      (MulEquiv.symm_apply_eq _).mpr rfl]
    rfl
  exact (involves_of_surjective φ hφ).of_injective (Subgroup.inclusion hrN)
    (Subgroup.inclusion_injective hrN)

structure AGLMuAt (p : ℕ) (P : Sylow p G) (M : Subgroup G) : Prop where
  escape : ∃ H₁ R₁ : Subgroup G, D1Escape p P M H₁ R₁

theorem AGLMuAt.maxTwoLocal_M {P : Sylow p G} {M : Subgroup G} (h : AGLMuAt p P M) :
    GLBIsMaxTwoLocal M := by
  obtain ⟨_, _, he⟩ := h.escape
  exact he.maxTwoLocal_M

theorem muAt_of_escape {P : Sylow p G} {M H R : Subgroup G} (he : D1Escape p P M H R) :
    AGLMuAt p P M :=
  ⟨⟨H, R, he⟩⟩

variable (G) in
@[expose] def AGL81NineCompetitorQ : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H : Subgroup G), AGLMuAt p P M →
    GLBIsMaxTwoLocal H → ¬ H ≤ M →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N →
      AGLCovers p H N (d1KBar p M H) →
      AGL81NineAt p M H N ∧
        ((∃ W : Subgroup G, ∃ _ : W ≤ H ⊓ N,
          (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
            d1KBar p M H ∧
          (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
            d1KBar p M N) ∨
        (∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) ∨
        Involves (d1KBar p M N) (d1KBar p M H))

theorem factor_or_involves (h9 : AGL81NineCompetitorQ G) (hg : AGLGlobal G) {P : Sylow p G}
    {M H B N : Subgroup G} (hσ : AGLMuAt p P M) (hH : GLBIsMaxTwoLocal H) (hHM : ¬ H ≤ M)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) (hB : IsAGLQ p M B) (hBH : B ≤ H) (hN : GLBIsMaxTwoLocal N)
    (hNM : ¬ N ≤ M) (hBN : B ≤ N) (hcov : AGLCovers p H N (d1KBar p M H)) :
    (∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) ∨
      Involves (d1KBar p M N) (d1KBar p M H) := by
  have hn : (d1KBar p M H).Normal :=
    (h9 hg p P M H hσ hH hHM hK B H hB hBH hH hHM hBH (aglCovers_self H _)).1.nineThree.normal
  rcases (h9 hg p P M H hσ hH hHM hK B N hB hBH hN hNM hBN hcov).2 with
    ⟨W, hW, hWH, hWN⟩ | hfac | hinv
  · exact Or.inr (involves_of_witness hn hW hWH hWN)
  · exact Or.inl hfac
  · exact Or.inr hinv

@[expose] def AGLAscentStep (p : ℕ) (M H₁ N : Subgroup G) : Prop :=
  ∃ B : Subgroup G, IsAGLQ p M B ∧ B ≤ H₁ ∧ GLBIsMaxTwoLocal N ∧ ¬ N ≤ M ∧ B ≤ N ∧
    AGLCovers p H₁ N (d1KBar p M H₁) ∧ d1Kappa p M H₁ < d1Kappa p M N ∧
    Involves (d1KBar p M N) (d1KBar p M H₁)

omit [Finite G] in
theorem exists_component_of_d1KBar_ne_bot {N M : Subgroup G} (h : d1KBar p M N ≠ ⊥) :
    ∃ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M N := by
  by_contra hno
  push Not at hno
  apply h
  refine iSup₂_eq_bot.mpr fun L hL => ?_
  exact absurd (hno L hL.1) hL.2

theorem exists_component_of_kappa_lt {M H₁ N : Subgroup G} (h : d1Kappa p M H₁ < d1Kappa p M N) :
    ∃ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M N := by
  refine exists_component_of_d1KBar_ne_bot fun hbot => ?_
  have h1 : d1Kappa p M N = 1 := by
    unfold d1Kappa
    rw [hbot]
    exact Subgroup.card_bot
  have h0 : 0 < d1Kappa p M H₁ := Nat.card_pos
  omega

theorem ascent_invariants {M H H₀ : Subgroup G} (hH : GLBIsMaxTwoLocal H) (hHM : ¬ H ≤ M)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) (hB : ∃ B : Subgroup G, IsAGLQ p M B ∧ B ≤ H)
    (hc : H₀ = H ∨ Relation.TransGen (AGLAscentStep p M) H H₀) :
    GLBIsMaxTwoLocal H₀ ∧ ¬ H₀ ≤ M ∧
      (∃ L : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) p), IsComponentOf L ⊤ ∧
        ¬ L ≤ d1X0 p M H₀) ∧ (∃ B : Subgroup G, IsAGLQ p M B ∧ B ≤ H₀) ∧
      d1Kappa p M H ≤ d1Kappa p M H₀ ∧ Involves (d1KBar p M H₀) (d1KBar p M H) := by
  rcases hc with rfl | hc
  · exact ⟨hH, hHM, hK, hB, le_rfl, involves_refl _⟩
  induction hc with
  | single hs =>
    obtain ⟨B, hB, -, hN, hNM, hBN, -, hlt, hinv⟩ := hs
    exact ⟨hN, hNM, exists_component_of_kappa_lt hlt, ⟨B, hB, hBN⟩, hlt.le, hinv⟩
  | tail _ hs ih =>
    obtain ⟨-, -, -, -, hle, hinv₀⟩ := ih
    obtain ⟨B, hB, -, hN, hNM, hBN, -, hlt, hinv⟩ := hs
    exact ⟨hN, hNM, exists_component_of_kappa_lt hlt, ⟨B, hB, hBN⟩, hle.trans hlt.le,
      involves_trans hinv hinv₀⟩

theorem kappa_lt_of_transGen {M H H₀ : Subgroup G}
    (hc : Relation.TransGen (AGLAscentStep p M) H H₀) : d1Kappa p M H < d1Kappa p M H₀ := by
  induction hc with
  | single hs => exact hs.choose_spec.2.2.2.2.2.2.1
  | tail _ hs ih => exact ih.trans hs.choose_spec.2.2.2.2.2.2.1

theorem eq_of_ascent_of_kappa_le {M H H₀ : Subgroup G}
    (hc : H₀ = H ∨ Relation.TransGen (AGLAscentStep p M) H H₀)
    (hle : d1Kappa p M H₀ ≤ d1Kappa p M H) : H₀ = H :=
  hc.resolve_right fun h => absurd hle (not_le.mpr (kappa_lt_of_transGen h))

theorem exists_first_step_of_ascent {M H H₀ : Subgroup G}
    (hc : Relation.TransGen (AGLAscentStep p M) H H₀) :
    ∃ H₁ : Subgroup G, AGLAscentStep p M H H₁ ∧ d1Kappa p M H₁ ≤ d1Kappa p M H₀ ∧
      Involves (d1KBar p M H₀) (d1KBar p M H₁) := by
  obtain ⟨H₁, hs, hr⟩ := Relation.TransGen.head'_iff.mp hc
  obtain ⟨B, hB, -, hN, hNM, hBN, -, hlt, -⟩ := id hs
  obtain ⟨-, -, -, -, hle, hinv⟩ := ascent_invariants hN hNM (exists_component_of_kappa_lt hlt)
    ⟨B, hB, hBN⟩ (Relation.reflTransGen_iff_eq_or_transGen.mp hr)
  exact ⟨H₁, hs, hle, hinv⟩

theorem exists_sizeMax_of_ascent (h9 : AGL81NineCompetitorQ G) (hg : AGLGlobal G)
    {P : Sylow p G} {M H : Subgroup G} (hσ : AGLMuAt p P M) (hH : GLBIsMaxTwoLocal H)
    (hHM : ¬ H ≤ M)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) (hB : ∃ B : Subgroup G, IsAGLQ p M B ∧ B ≤ H) :
    ∃ H₀ : Subgroup G, (H₀ = H ∨ Relation.TransGen (AGLAscentStep p M) H H₀) ∧
      GLBIsMaxTwoLocal H₀ ∧ ¬ H₀ ≤ M ∧
      (∃ L : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) p), IsComponentOf L ⊤ ∧
        ¬ L ≤ d1X0 p M H₀) ∧ (∃ B : Subgroup G, IsAGLQ p M B ∧ B ≤ H₀) ∧
      d1Kappa p M H ≤ d1Kappa p M H₀ ∧ Involves (d1KBar p M H₀) (d1KBar p M H) ∧
      AGLCompetitorFactor p M H₀ (d1KBar p M H₀) := by
  set S : Set (Subgroup G) := {H' | H' = H ∨ Relation.TransGen (AGLAscentStep p M) H H'}
  obtain ⟨H₀, hS₀, hmax⟩ := Set.exists_max_image S (d1Kappa p M) (Set.toFinite S)
    ⟨H, Or.inl rfl⟩
  obtain ⟨hH₀, hH₀M, hK₀, hB₀, hle, hinv⟩ := ascent_invariants hH hHM hK hB hS₀
  refine ⟨H₀, hS₀, hH₀, hH₀M, hK₀, hB₀, hle, hinv, ?_⟩
  intro Q N hQ hQH hN hNM hQN hcov
  have hat := (h9 hg p P M H₀ hσ hH₀ hH₀M hK₀ Q N hQ hQH hN hNM hQN hcov).1
  have hfi := factor_or_involves h9 hg hσ hH₀ hH₀M hK₀ hQ hQH hN hNM hQN hcov
  have hn : (d1KBar p M H₀).Normal :=
    (h9 hg p P M H₀ hσ hH₀ hH₀M hK₀ Q H₀ hQ hQH hH₀ hH₀M hQH
      (aglCovers_self H₀ _)).1.nineThree.normal
  by_cases hNH : d1Kappa p M N ≤ d1Kappa p M H₀
  · obtain ⟨W, hW, -, heq | hfac⟩ := hat.nineSeventeen.toEq
      (fun V hV hc => noPPrime_of_normal _ V hV hc) le_rfl hNH
    · exact factor_of_map_eq hat.hyp93At hW heq.ge
    · exact hfac
  · rcases hfi with hfac | hinvN
    · exact hfac
    · have hstep : AGLAscentStep p M H₀ N :=
        ⟨Q, hQ, hQH, hN, hNM, hQN, hcov, not_le.mp hNH, hinvN⟩
      have hNS : N ∈ S := by
        rcases hS₀ with rfl | hc
        · exact Or.inr (Relation.TransGen.single hstep)
        · exact Or.inr (hc.tail hstep)
      exact absurd (hmax N hNS) hNH

theorem hyp111Pair_of_competitorFactor (h9 : AGL81NineCompetitorQ G) (hg : AGLGlobal G)
    {P : Sylow p G} {M H₀ Q₀ : Subgroup G} (hσ : AGLMuAt p P M) (hH₀ : GLBIsMaxTwoLocal H₀)
    (hH₀M : ¬ H₀ ≤ M)
    (hK₀ : ∃ L : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H₀) (hQ₀ : IsAGLQ p M Q₀) (hQ₀H : Q₀ ≤ H₀)
    (hfac : AGLCompetitorFactor p M H₀ (d1KBar p M H₀))
    (hOH : pCoreOf 2 M ≤ pCoreOf 2 H₀) (hHM : pCoreOf 2 H₀ ≤ M) :
    AGLHyp111Pair p M H₀ Q₀ (d1KBar p M H₀) := by
  have hat := (h9 hg p P M H₀ hσ hH₀ hH₀M hK₀ Q₀ H₀ hQ₀ hQ₀H hH₀ hH₀M hQ₀H
    (aglCovers_self H₀ _)).1
  obtain ⟨L, hL, hLX⟩ := hK₀
  refine ⟨hQ₀, hQ₀H, hH₀M, fun hle => hLX ((le_d1KBar hL hLX).trans hle), hat.core_le,
    absorbs_of_factor hσ.maxTwoLocal_M.1 hH₀ hOH hHM hat.core_le hat.nineThree.factor hfac⟩

@[expose] def KFactNineThreeInvolvedA6L34 : Prop :=
  ∀ (A K : Type) [Group A] [Finite A] [Group K], (IsAltTwoP 3 A ∨ IsLinThreeFour A) →
    NineThreeListGroup 3 K → Involves A K → IsAltTwoP 3 K ∨ IsLinThreeFour K

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
