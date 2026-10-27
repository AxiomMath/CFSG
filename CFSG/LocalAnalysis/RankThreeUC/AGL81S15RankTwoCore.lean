module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CardOne
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.RankTwoCore

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal.Unitary
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

section Model

variable {Y : Type} [Group Y] [Finite Y]

theorem isMinOverBorel_top_of_borelQuotient {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y}
    {M : ℕ} (h : BorelQuotient D n H π M) (hr : D.rank = 1) (S : Sylow 2 Y) :
    IsMinOverBorel ⊤ (S : Subgroup Y) ⊤ := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hlt := (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.isMinOverBorel_map_parJ hQ
    ⟨0, by omega⟩).2.1
  rw [← hT] at hlt
  refine ⟨le_top, lt_of_lt_of_le hlt le_top, fun Q hQ1 _ => ?_⟩
  by_cases hQt : Q = ⊤
  · exact Or.inr hQt
  · rw [top_inf_eq] at hQ1 ⊢
    exact Or.inl (borelMaximal_of_borelQuotient h hr S Q hQ1 hQt)

theorem isMinOverBorel_top_of_psl_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Y) (S : Sylow 2 Y) :
    IsMinOverBorel ⊤ (S : Subgroup Y) ⊤ :=
  isMinOverBorel_top_of_borelQuotient (borelQuotient_sl (m := 1) e) rfl S

theorem isMinOverBorel_top_of_model_psu_three {f : ℕ} (h : StatedClassicalModel Y .PSU 3 2 f)
    (S : Sylow 2 Y) : IsMinOverBorel ⊤ (S : Subgroup Y) ⊤ := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  exact isMinOverBorel_top_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e) rfl S

theorem isMinOverBorel_top_of_rankOneChevTwo
    (hY : RankOneChevTwo Y) (S : Sylow 2 Y) : IsMinOverBorel ⊤ (S : Subgroup Y) ⊤ := by
  rcases hY with ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ | he
  · rcases hd with ⟨Q, hQ, hdQ⟩ | ⟨Q, hQ, hdQ⟩
    · obtain rfl : d = .A 1 Q := hdQ
      have : Fact Q.p.Prime := ⟨Q.prime_p⟩
      have : CharP (GaloisField Q.p Q.exponent) 2 := CharP.congr Q.p hQ
      exact isMinOverBorel_top_of_psl_two
        ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv).symm.trans e.symm) S
    · obtain rfl : d = .twistedA 2 Q := hdQ
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 Q hv e
      rw [hQ] at h
      exact isMinOverBorel_top_of_model_psu_three h S
  · obtain ⟨e⟩ := he
    have hK : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 2 2) (.inl hK)
    exact isMinOverBorel_top_of_psl_two
      ((projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)).trans (e₅.trans e.symm)) S

end Model

theorem not_rankOneChevTwo_of_gnParabolic {X : Type} [Group X]
    [Finite X] {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hpar : GNParabolic T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ Ls)
    (hChev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls)) :
    ¬ RankOneChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) := by
  intro hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hY.1.2.1
  have hbar :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.isSylowTwoOf_top_map_center hSyl
  have hidx : ¬ 2 ∣ (((gnImg T T ⊓ Ls).subgroupOf Ls).map
      (QuotientGroup.mk' (Subgroup.center ↥Ls))).index := by
    rw [← Subgroup.relIndex_top_right]
    exact hbar.2.2
  have hP := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.isMinOverBorel_preimage hSyl
    (isMinOverBorel_top_of_rankOneChevTwo hR (hbar.2.1.toSylow hidx))
  rw [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hP
  have hTp : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hW : pElementSubgroup 2 Ls = Ls :=
    CFSG.AGLEmbeddingD2.Tits.GN516.pElementSubgroup_eq_of_isMinOverBorel_self hY.1.2.2
      inf_le_right (hTp.to_le inf_le_left) hP
  rcases hpar Ls hY.1 hChev Ls hP with h | h
  · exact hY.2.1 (hW ▸ h)
  · exact hY.2.2 (hW ▸ h)

end CFSG.LocalAnalysis.RankThreeUC.S15.RankTwoCore
