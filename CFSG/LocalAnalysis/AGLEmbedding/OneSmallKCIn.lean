module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCInKFact
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKC
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPL34

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactL34InvolveIso : Prop :=
  ∀ (KC : Type) [Group KC] [Finite KC], IsSimpleGroup KC → (∃ a b : KC, a * b ≠ b * a) →
    IsCatalogGroup KC → ∀ T : Sylow 3 KC, ¬ IsCyclic (T : Subgroup KC) →
    GLBCore 3 1 (T : Subgroup KC) ≠ ⊤ → Open.pRank 3 (⊤ : Subgroup (MulAut KC)) ≤ 2 →
    ∀ (L : Type) [Group L], IsLinThreeFour L → ∀ (A : Subgroup KC) (f : A →* L),
      Function.Surjective f → Nonempty (KC ≃* L)

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_czIn_three (hKF : KFactCoverThreeFix)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnSP : ¬ D1CzSP p z) (hp3 : p = 3) (hin : ¬ D1CzOutside p z) : False := by
  subst hp3
  obtain ⟨-, T, Pbar, KC, -, -, -, hc⟩ := hd.exists_czReduced hz
  simp only [D1CzOutside, not_forall, not_not] at hin
  obtain ⟨KC', hKC', hzKC'⟩ := hin
  rw [hc.unique KC' hKC'] at hzKC'
  exact hc.red.false_of_smallCoverThree_of_mem (hc.pRank_eq_three hnSP).le hc.catalog hc.center
    hc.order hc.comp hc.normal hzKC' hKF

theorem D1OneSmallData.czIso_of_l34_of_outside (hSch : KFactCatalogSchreier)
    (hRk : KFactSmallOfRankTwo) (hInvC : KFactSmallInvolveCard) (hI : KFactL34InvolveIso)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnSP : ¬ D1CzSP p z) (hp3 : p = 3) (hL : IsLinThreeFour K) (hout : D1CzOutside p z) :
    D1CzIso p z K := by
  subst hp3
  obtain ⟨-, T, Pbar, KC, -, -, -, hc⟩ := hd.exists_czReduced hz
  obtain ⟨-, hsimple, hnonab, hcat, TC, -, hTCnc, hΓ, hAut, -⟩ :=
    hd.czComponent_facts_of_not_mem hSch hRk hInvC hz hc hnSP (hout KC hc.comp)
  obtain ⟨A₀, f₀, hf₀⟩ := hd.exists_surjective_czQuot hz
  obtain ⟨A, f, hf⟩ := hc.exists_surjective_of_surjective hSch ⟨hd.comp.2.2.1⟩ f₀ hf₀
  obtain ⟨e⟩ := hI KC hsimple hnonab hcat TC hTCnc hΓ hAut K hL A f hf
  intro KC' hKC'
  obtain rfl := hc.unique KC' hKC'
  exact ⟨e⟩

end Config

@[expose] def D1SmallKCLeftOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1CzSP p z → ¬ D1CzIso p z K → D1SmallOpenPosIf p M H Rbar K → D1SmallLa p M H Rbar K →
    D1CzOutside p z → D1CzB0 p R z → D1CzEven p z →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    False

theorem d1SmallKCLeft_of (hKF : KFactCoverThreeFix) (hOut : D1SmallKCLeftOut) :
    D1SmallKCLeft := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hnSP hnIso hOP hLa h
  rcases h with ⟨hp3, hin⟩ | ⟨hout, hB0, hE, hcomm, hnle⟩
  · exact hd.false_of_czIn_three hKF hz hnSP hp3 hin
  · exact hOut G p P M H R Rbar K hd huniq z hz hnSP hnIso hOP hLa hout hB0 hE hcomm hnle

@[expose] def D1SmallL34LeftIso : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 3 → IsLinThreeFour K → ¬ D1CzSP p z → ¬ D1SmallOuterR p H Rbar K →
    (D1SmallU2Fails p M H K ∨ D1SmallOpenPos p M H Rbar K) → D1CzIso p z K →
    D1CzB0 p R z → D1CzEven p z → False

theorem d1SmallL34Left_of (hSch : KFactCatalogSchreier) (hRk : KFactSmallOfRankTwo)
    (hInvC : KFactSmallInvolveCard) (hKF : KFactCoverThreeFix) (hI : KFactL34InvolveIso)
    (hIso : D1SmallL34LeftIso) : D1SmallL34Left := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hp3 hL hnSP h
  rcases h with ⟨-, hnIso⟩ | ⟨hOR, hpos, hIso', hB0, hE⟩
  · by_cases hout : D1CzOutside p z
    · exact hnIso (hd.czIso_of_l34_of_outside hSch hRk hInvC hI hz hnSP hp3 hL hout)
    · exact hd.false_of_czIn_three hKF hz hnSP hp3 hout
  · exact hIso G p P M H R Rbar K hd huniq z hz hp3 hL hnSP hOR hpos hIso' hB0 hE

end CFSG.AGLEmbedding
