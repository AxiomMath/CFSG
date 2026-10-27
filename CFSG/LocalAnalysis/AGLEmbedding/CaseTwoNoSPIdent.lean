module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Cz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
  {K : Subgroup (D1CzQuot p z)}

theorem D1CzReduced.le_of_isPerfect (hc : D1CzReduced p M z T Pbar K) (hSch : KFactCatalogSchreier)
    {A : Subgroup (D1CzQuot p z)} (hA : Group.IsPerfect A) : A ≤ K := by
  have := hc.normal
  have hE := hc.red.le_layer_of_isPerfect hc.catalog hSch hc.comp hA fun L hL => by
    rw [hc.unique L hL, Subgroup.normalizer_eq_top]
    exact le_top
  refine hE.trans (sSup_le fun L hL => ?_)
  rw [hc.unique L ((CFSG.isComponent_iff_open L).mp hL)]

theorem D1CzReduced.exists_surjective_of_surjective (hc : D1CzReduced p M z T Pbar K)
    (hSch : KFactCatalogSchreier) {A₀ : Subgroup (D1CzQuot p z)} {Λ : Type} [Group Λ]
    [Finite Λ] (hΛ : Group.IsPerfect Λ) (φ : A₀ →* Λ) (hφ : Function.Surjective φ) :
    ∃ (A : Subgroup K) (f : A →* Λ), Function.Surjective f := by
  set D : Subgroup A₀ := perfectCore (⊤ : Subgroup A₀)
  have hDperf : ⁅D, D⁆ = D := perfectCore_perfect _
  have hDφ : D.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hΛ.commutator_eq_top)
  have hDK : D.map A₀.subtype ≤ K := hc.le_of_isPerfect hSch
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDperf]))
  set ρK : D →* K := (A₀.subtype.comp D.subtype).codRestrict K fun d => hDK ⟨d, d.2, rfl⟩
  have hφD : Function.Surjective (φ.comp D.subtype) := by
    intro l
    obtain ⟨d, hd, hdl⟩ : l ∈ D.map φ := hDφ ▸ Subgroup.mem_top l
    exact ⟨⟨d, hd⟩, hdl⟩
  obtain ⟨f, -, hf, -⟩ := exists_surjective_comp_eq ρK.rangeRestrict ρK.rangeRestrict_surjective
    (φ.comp D.subtype) hφD (by
      rw [MonoidHom.ker_rangeRestrict]
      intro d hd
      have h1 : ((d : A₀) : D1CzQuot p z) = 1 := congrArg Subtype.val hd
      have h2 : d = 1 := Subtype.ext (Subtype.ext h1)
      rw [h2]
      exact Subgroup.one_mem _)
  exact ⟨ρK.range, f, hf⟩

theorem D1CzReduced.pRank_eq_three (hc : D1CzReduced p M z T Pbar K) (hnSP : ¬ D1CzSP p z) :
    Open.pRank p (Pbar : Subgroup (D1CzQuot p z)) = 3 := by
  have hp := hc.red.prime
  have h3 := hc.red.three_le_pRank
  have hle : Open.pRank p (Pbar : Subgroup (D1CzQuot p z)) ≤
      Open.pRank p (Subgroup.centralizer ({z} : Set G)) := by
    rw [hc.sylow_eq, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p)]
    exact pRank_mono p hp (Subgroup.map_subtype_le _)
  have h4 : ¬ 4 ≤ Open.pRank p (Subgroup.centralizer ({z} : Set G)) := hnSP
  omega

theorem D1CzReduced.isCyclic_and_isCaseTwoGroup_at (hc : D1CzReduced p M z T Pbar K)
    (hAut : KFactCycAut) (hS : KFactSeitzCyc) (hSch : KFactCatalogSchreier)
    (hInv : KFactCaseTwoInvIn G)
    (hnSP : ¬ D1CzSP p z) (hzK : d1CzElt p z ∉ K) {Λ : Type} [Group Λ] [Finite Λ]
    (hΛ : IsCaseTwoGroup p Λ) (hΛp : Group.IsPerfect Λ) {A₀ : Subgroup (D1CzQuot p z)}
    (φ : A₀ →* Λ) (hφ : Function.Surjective φ) :
    IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)) ∧
      IsCaseTwoGroup p K := by
  have hp := hc.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hc.pRank_eq_three hnSP
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd' | hd', -⟩ := hΛ
    · exact Or.inl hd'.1
    · exact Or.inr hd'.1
  have hKn := hc.normal
  obtain ⟨hZ, hrk⟩ := hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK
  have hcyc : IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)) := by
    by_contra hnc
    obtain ⟨hN, hKX₀⟩ := hrk hnc
    obtain ⟨hsimple, hnonab, hcat⟩ := hc.catalog.isSimpleGroup_of_center_eq_bot hc.comp hZ
    obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKn.isSubnormal
    have hTKnc : ¬ IsCyclic (TK : Subgroup K) := fun hTc => hnc (by
      rw [← hTK]
      exact isCyclic_of_surjective
        ((TK : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective)
        (MulEquiv.surjective _))
    have hΓ := hc.red.glbCore_ne_top_of_rankOne hN hKX₀ hTK
    have hrank : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
      rw [← (SectionRank.pRank_sylow TK).1,
        ← pRank_map_of_injective p hp K.subtype K.subtype_injective, hTK]
      obtain ⟨E, hE, hEel, hEcard⟩ :=
        pRank_attained p hp ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K)
      have hzE : d1CzElt p z ∉ E := fun h => hzK (hE h).2
      have hzC : d1CzElt p z ∈ Subgroup.centralizer (E : Set (D1CzQuot p z)) :=
        Subgroup.center_le_centralizer _ hc.center
      have hzP : d1CzElt p z ∈ (Pbar : Subgroup (D1CzQuot p z)) :=
        mem_sylow_of_mem_center hc.center hc.order Pbar
      have hzp1 : d1CzElt p z ^ p = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hc.order)
      have := succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hEel hEcard hzp1 hzE hzC
        (hE.trans inf_le_left) hzP
      omega
    obtain ⟨A, f, hf⟩ := hc.exists_surjective_of_surjective hSch hΛp φ hφ
    exact hInv _ _ K hc.comp.2.2 hZ hsimple hnonab hcat p hp35 TK hTKnc hΓ hrank A Λ hΛ f hf
  refine ⟨hcyc, hc.red.isCaseTwoGroup_of_not_le_of_aut hc.catalog (hAut _ _ _ _ hc.red hc.catalog)
      hS (fun L hL => ?_) h3 hc.comp
    (hc.red.not_le_of_not_mem_of_center hc.center hc.order hc.comp hKn hzK)⟩
  rw [hc.unique L hL]
  exact hcyc

end Cz

end CFSG.AGLEmbedding
