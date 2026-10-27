module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneSetup
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem isCyclic_sylow_of_surjective {X L : Type*} [Group X] [Finite X] [Group L] [Finite L]
    {p : ℕ} [Fact p.Prime] (hcyc : ∀ S : Sylow p X, IsCyclic (S : Subgroup X)) {A : Subgroup X}
    (f : A →* L) (hf : Function.Surjective f) (TL : Sylow p L) : IsCyclic (TL : Subgroup L) := by
  obtain ⟨T⟩ : Nonempty (Sylow p A) := inferInstance
  have hT'p : IsPGroup p ((T : Subgroup A).map A.subtype) := T.isPGroup'.map _
  obtain ⟨S, hS⟩ := hT'p.exists_le_sylow
  have : IsCyclic (S : Subgroup X) := hcyc S
  have hT'c : IsCyclic ((T : Subgroup A).map A.subtype) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom (MulEquiv.surjective _)
  have hTc : IsCyclic (T : Subgroup A) :=
    isCyclic_of_surjective
      ((T : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hTf : IsCyclic ((T.mapSurjective hf : Sylow p L) : Subgroup L) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (f.subgroupMap (T : Subgroup A))
      (f.subgroupMap_surjective (T : Subgroup A))
  exact isCyclic_of_surjective (Sylow.equiv (T.mapSurjective hf) TL).toMonoidHom
    (MulEquiv.surjective _)

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_czReduced (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    ∃ (m : G) (T : Sylow p (Subgroup.centralizer ({z} : Set G))) (Pbar : Sylow p (D1CzQuot p z))
      (KC : Subgroup (D1CzQuot p z)), m ∈ M ∧
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ∧
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom ∧ D1CzReduced p M z T Pbar KC := by
  have hp := hd.cfg.red.prime
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.exists_sylow_centralizer hz
  obtain ⟨Pbar, hPbar, hred⟩ := hd.exists_reducedNongeneration_three hz hm hRT hTP
  obtain ⟨KC, hKC, hKCn, huniq, hzZ, hzp⟩ := hd.exists_component_czQuot hz hred
  have hz1 : z ≠ 1 := fun h1 => hp.one_lt.ne (by rw [← hz.2.1, h1, orderOf_one])
  refine ⟨m, T, Pbar, KC, hm, hRT, hTP, hPbar, hred, ?_, hzZ, hzp, hKC, hKCn, huniq⟩
  exact (catalogSimpleSections_of_isKProper hd.cfg.glob.kProper _
    (centralizer_singleton_ne_top hd.cfg.glob.simple hd.cfg.glob.nonab hz1)).quotient _

theorem D1OneSmallData.czComponent_facts_of_not_mem (hSch : KFactCatalogSchreier)
    (hRk : KFactSmallOfRankTwo) (hInvC : KFactSmallInvolveCard)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hc : D1CzReduced p M z T Pbar KC) (hnSP : ¬ D1CzSP p z) (hzK : d1CzElt p z ∉ KC) :
    Subgroup.center KC = ⊥ ∧ IsSimpleGroup KC ∧ (∃ a b : KC, a * b ≠ b * a) ∧
      IsCatalogGroup KC ∧ ∃ TC : Sylow p KC,
        (TC : Subgroup KC).map KC.subtype = (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ∧
        ¬ IsCyclic (TC : Subgroup KC) ∧ GLBCore p 1 (TC : Subgroup KC) ≠ ⊤ ∧
        Open.pRank p (⊤ : Subgroup (MulAut KC)) ≤ 2 ∧
        Nat.card TC = Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup _) := by
  have hp := hc.red.prime
  have hp2 := hc.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hc.pRank_eq_three hnSP
  have hKn := hc.normal
  obtain ⟨hZ, hrk⟩ := hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK
  let e : KC ≃* KC ⧸ Subgroup.center KC :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (KC ⧸ Subgroup.center KC) := hc.comp.2.2.2
  have hsimple : IsSimpleGroup KC := e.isSimpleGroup
  have hnonab : ∃ a b : KC, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian KC hc.comp.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup KC :=
    IsCatalogGroup.of_mulEquiv e (hc.catalog.isCatalogGroup_center_quotient hc.comp)
  obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKn.isSubnormal
  obtain ⟨A₀, f₀, hf₀⟩ := hd.exists_surjective_czQuot hz
  obtain ⟨A, f, hf⟩ := hc.exists_surjective_of_surjective hSch ⟨hd.comp.2.2.1⟩ f₀ hf₀
  obtain ⟨T₁, hT₁, hs, hnab, hcK, hT₁nc, hΓ₁, -⟩ := hd.exists_sylow
  have hTKnc : ¬ IsCyclic (TK : Subgroup KC) := by
    intro hTc
    have hall : ∀ S : Sylow p KC, IsCyclic (S : Subgroup KC) := fun S =>
      isCyclic_of_surjective (Sylow.equiv TK S).toMonoidHom (MulEquiv.surjective _)
    exact hT₁nc (isCyclic_sylow_of_surjective hall f hf T₁)
  have hnc : ¬ IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup (D1CzQuot p z)) :=
    fun hcy => hTKnc (by
      rw [← hTK] at hcy
      exact isCyclic_of_surjective
        ((TK : Subgroup KC).equivMapOfInjective KC.subtype KC.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _))
  obtain ⟨hN, hKX₀⟩ := hrk hnc
  have hΓ := hc.red.glbCore_ne_top_of_rankOne hN hKX₀ hTK
  have hrank : Open.pRank p (⊤ : Subgroup KC) ≤ 2 := by
    rw [← (SectionRank.pRank_sylow TK).1,
      ← pRank_map_of_injective p hp KC.subtype KC.subtype_injective, hTK]
    obtain ⟨E, hE, hEel, hEcard⟩ :=
      pRank_attained p hp ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
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
  have hAut := hRk KC hsimple hnonab hcat p hp hp2 TK hTKnc hΓ hrank
  have hcard := hInvC KC hsimple hnonab hcat p hp hp2 TK hTKnc hΓ hAut K hs hnab hcK T₁ hT₁nc
    hΓ₁ hd.small A f hf
  refine ⟨hZ, hsimple, hnonab, hcat, TK, hTK, hTKnc, hΓ, hAut, ?_⟩
  rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, hcard]

theorem D1OneSmallData.czComponent_facts_of_iso
    (hNoTwo : ∀ (S : Sylow p K) (W : Subgroup K), IsPGroup 2 W →
      (S : Subgroup K) ≤ Subgroup.normalizer (W : Set K) → W = ⊥)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hc : D1CzReduced p M z T Pbar KC) (hIso : D1CzIso p z K) :
    Subgroup.center KC = ⊥ ∧
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
        Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) ∧
      ∀ (S : Sylow p KC) (W : Subgroup KC), IsPGroup 2 W →
        (S : Subgroup KC) ≤ Subgroup.normalizer (W : Set KC) → W = ⊥ := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  obtain ⟨e⟩ := hIso KC hc.comp
  obtain ⟨T₁, hT₁, -, -, -, -, -, -⟩ := hd.exists_sylow
  obtain ⟨TC, hTC⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hc.normal.isSubnormal
  refine ⟨?_, ?_, fun S W hW hSW => ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => e.injective ?_
    have hey : e y ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k => by
      obtain ⟨k', rfl⟩ := e.surjective k
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy k']
    rw [hd.center, Subgroup.mem_bot] at hey
    rw [hey, map_one]
  · rw [← hTC, Subgroup.card_map_of_injective KC.subtype_injective, ← hT₁,
      Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]
  · have hW' := hNoTwo (S.mapSurjective (f := e.toMonoidHom) e.surjective)
      (W.map e.toMonoidHom) (hW.map _) (by
        show (S : Subgroup KC).map e.toMonoidHom ≤ _
        exact (Subgroup.map_mono hSW).trans (Subgroup.le_normalizer_map _))
    exact (Subgroup.map_eq_bot_iff_of_injective W e.injective).mp hW'

end Config

end CFSG.AGLEmbedding
