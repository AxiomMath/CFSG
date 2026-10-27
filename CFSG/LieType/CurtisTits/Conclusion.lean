module

public import CFSG.LieType.Steinberg.Presentation
public import CFSG.LieType.CurtisTits.Amalgam
public import CFSG.LieType.CurtisTits.AmalgamPresentation
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LieType.CurtisTits

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.Blueprint

universe w

theorem statedClassicalModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel G' t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem lieModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel G t n p f) : LieModel G' t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

noncomputable def centerQuotientEquivOfSurjective {K G : Type*} [Group K] [Group G]
    (ψ : K →* G) (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K)
    (hZ : Subgroup.center G = (Subgroup.center K).map ψ) :
    K ⧸ Subgroup.center K ≃* G ⧸ Subgroup.center G := by
  have hcomp : Function.Surjective ((QuotientGroup.mk' (Subgroup.center G)).comp ψ) :=
    (QuotientGroup.mk'_surjective _).comp hsurj
  have hkerc : ((QuotientGroup.mk' (Subgroup.center G)).comp ψ).ker = Subgroup.center K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ,
      Subgroup.comap_map_eq_self (by simpa using hker)]
  exact (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hcomp)

@[expose] def CurtisTitsConclusion {K : Type} [Group K] (D : UniversalRootDatum K)
    (t : StatedLieTag) (n p f : ℕ) : Prop :=
  ((⨆ J, D.leviAmalgam J = ⊤) ∧ IsQuasisimple K ∧
    LieModel (K ⧸ Subgroup.center K) t n p f) ∧
  (IsUniversalCompletion.{0, 0, w} D.leviAmalgam ∧ IsPresentedByAmalgam D.leviAmalgam) ∧
  (∀ (G : Type) [Group G] (φ : ∀ J, D.leviAmalgam J →* G), IsCompatible D.leviAmalgam φ →
    (⨆ J, (φ J).range = ⊤) → (∃ J, ∃ x, φ J x ≠ 1) →
    ∃ ψ : K →* G, (∀ J (x : D.leviAmalgam J), ψ x = φ J x) ∧ Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple G ∧
      Subgroup.center G = (Subgroup.center K).map ψ ∧ Nonempty (K ⧸ ψ.ker ≃* G) ∧
      LieModel (G ⧸ Subgroup.center G) t n p f) ∧
  (∀ (G : Type) [Group G] (M : {J : Finset (Fin D.rank) // J.card ≤ 2} → Subgroup G),
    (⨆ J, M J = ⊤) → ∀ ψ : ∀ J, D.leviAmalgam J ≃* M J,
    (∀ I J, I ≤ J → ∀ (x : D.leviAmalgam I) (y : D.leviAmalgam J), (x : K) = y →
      (ψ I x : G) = ψ J y) →
    ∃ θ : K →* G, (∀ J (x : D.leviAmalgam J), θ x = ψ J x) ∧ Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center K)

theorem exists_leviAmalgam_ne_bot {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} (hext : Steinberg.SteinbergExtras D n H)
    (hrank : 0 < D.rank) : ∃ J, D.leviAmalgam J ≠ ⊥ := by
  refine ⟨⟨{⟨0, hrank⟩}, by simp⟩, fun hbot => ?_⟩
  have hle : D.rootGroup (Pi.single ⟨0, hrank⟩ 1) ≤ levi D.rootGroup {⟨0, hrank⟩} :=
    le_trans le_sup_left (rankOne_le_levi D.rootGroup (Finset.mem_singleton_self _))
  have hbot' : levi D.rootGroup {⟨0, hrank⟩} = ⊥ := hbot
  have hroot : (Pi.single ⟨0, hrank⟩ 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (isCTRootSystem D.isFiniteType D.divisible).single_mem _
  rw [hbot', le_bot_iff] at hle
  exact hext.ne_bot _ hroot hle

theorem curtisTitsConclusion_of {K : Type} [Group K] {D : UniversalRootDatum K}
    {nw : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    (hext : Steinberg.SteinbergExtras D nw H) (hrank : 0 < D.rank) (hK : IsQuasisimple K)
    {t : StatedLieTag} {n p f : ℕ} (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f) :
    CurtisTitsConclusion.{w} D t n p f := by
  have hgen : ⨆ J, D.leviAmalgam J = ⊤ :=
    iSup_leviAmalgam_eq_top (isCTRootSystem D.isFiniteType D.divisible) hct
  have hU1 : IsUniversalCompletion.{0, 0, 0} D.leviAmalgam :=
    D.isUniversalCompletion_of_steinbergPresentation hct
      (Steinberg.steinbergPresentation_of_extras hct hext)
  refine ⟨⟨hgen, hK, hmodel⟩, ⟨D.isUniversalCompletion_of_steinbergPresentation hct
    (Steinberg.steinbergPresentation_of_extras hct hext), isPresentedByAmalgam_of hgen hU1⟩,
    ?_, ?_⟩
  · intro G _ φ hφ hGgen hnt
    obtain ⟨ψ, hψ, hsurj, hker, hGq, hZ, hiso⟩ :=
      recognition_of_isUniversalCompletion hgen hK hU1 φ hφ hGgen hnt
    exact ⟨ψ, hψ, hsurj, hker, hGq, hZ, hiso,
      lieModel_of_mulEquiv (centerQuotientEquivOfSurjective ψ hsurj hker hZ) hmodel⟩
  · intro G _ M hMgen ψ hψ
    exact exists_surjective_ker_le_center_of_isUniversalCompletion hgen hK hU1
      (exists_leviAmalgam_ne_bot hext hrank) M hMgen ψ hψ

end CFSG.LieType.CurtisTits
