module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Generic

variable {X : Type} [Group X] [Finite X] {p : ℕ} {T : Sylow p X} {X₀ : Subgroup X}

theorem Sp48NCent.le_of_isPerfect_unique (h : ReducedNongeneration p X T X₀)
    (hX : CatalogSimpleSections X) (hSch : KFactCatalogSchreier) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K) {A : Subgroup X}
    (hA : Group.IsPerfect A) : A ≤ K := by
  have hE := h.le_layer_of_isPerfect hX hSch hK hA fun L hL => by
    rw [huniq L hL, Subgroup.normalizer_eq_top]
    exact le_top
  refine hE.trans (sSup_le fun L hL => ?_)
  rw [huniq L ((CFSG.isComponent_iff_open L).mp hL)]

end Generic

section Involve

variable {G : Type} [Group G] [Finite G] {e : G}
  {Tb : Sylow 3 (Subgroup.centralizer ({e} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)}
  {X₀ : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)}
  {K : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)}

theorem Sp48NCent.exists_surjective_unique
    (h : ReducedNongeneration 3 (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) Tb X₀)
    (hX : CatalogSimpleSections (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3))
    (hSch : KFactCatalogSchreier) (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (huniq : ∀ L : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3), IsComponentOf L ⊤ → L = K)
    {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({e} : Set G)) {Λ : Type} [Group Λ]
    [Finite Λ] [IsSimpleGroup Λ] (hΛ : Group.IsPerfect Λ) (φ : W →* Λ)
    (hφ : Function.Surjective φ) {x : Λ} (hx : x ≠ 1) (hx3 : x ^ 3 ^ 1 = 1) :
    ∃ (A : Subgroup K) (f : A →* Λ), Function.Surjective f := by
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({e} : Set G)) 3
  have hN : ∀ n ∈ (primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3).comap
      (Subgroup.inclusion hW), (3 : ℕ).Coprime (orderOf n) := by
    intro n hn
    have h1 : orderOf (Subgroup.inclusion hW n) ∣ Nat.card
        (primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) :=
      Subgroup.orderOf_dvd_natCard _ hn
    rw [orderOf_injective _ (Subgroup.inclusion_injective hW)] at h1
    exact hO.coprime_dvd_right h1
  have hker := le_ker_of_isSimpleGroup φ hφ _ hN hx hx3
  set ρ : W →* Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3 :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hW) with hρ
  set D : Subgroup W := perfectCore (⊤ : Subgroup W)
  have hDperf : ⁅D, D⁆ = D := perfectCore_perfect _
  have hDφ : D.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hΛ.commutator_eq_top)
  have hDK : D.map ρ ≤ K := Sp48NCent.le_of_isPerfect_unique h hX hSch hK hKn huniq
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDperf]))
  set ρK : D →* K := (ρ.comp D.subtype).codRestrict K fun d => hDK ⟨d, d.2, rfl⟩
  have hφD : Function.Surjective (φ.comp D.subtype) := by
    intro l
    obtain ⟨d, hd, hdl⟩ : l ∈ D.map φ := hDφ ▸ Subgroup.mem_top l
    exact ⟨⟨d, hd⟩, hdl⟩
  obtain ⟨f, -, hf, -⟩ := exists_surjective_comp_eq ρK.rangeRestrict ρK.rangeRestrict_surjective
    (φ.comp D.subtype) hφD (by
      rw [MonoidHom.ker_rangeRestrict]
      intro d hd
      have h1 : ρ (d : W) = 1 := congrArg Subtype.val hd
      rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hker h1)
  exact ⟨ρK.range, f, hf⟩

end Involve

section CM

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G}

theorem Sp48NCent.cm_beta (hloc : D1Local 3 P M) (hPM : (P : Subgroup G) ≤ M) (hglob : D1Global G)
    {e : G} (he3 : orderOf e = 3)
    (hCM : ¬ Subgroup.centralizer ({e} : Set G) ≤ M)
    (hrank : 3 ≤ Open.pRank 3 (Subgroup.centralizer ({e} : Set G) ⊓ M))
    (T : Sylow 3 (Subgroup.centralizer ({e} : Set G)))
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({e} : Set G)).subtype ≤ P)
    (h4 : 4 ≤ Open.pRank 3 ((T : Subgroup _).map (Subgroup.centralizer ({e} : Set G)).subtype))
    {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({e} : Set G)) {Λ : Type} [Group Λ]
    [Finite Λ] [IsSimpleGroup Λ] (hΛ : Group.IsPerfect Λ) (hiso : IsCaseTwoGroup 3 Λ)
    (φ : W →* Λ) (hφ : Function.Surjective φ) {x : Λ} (hx : x ≠ 1) (hx3 : x ^ 3 ^ 1 = 1)
    (hSch : KFactCatalogSchreier) (hAE : KFactCaseTwoAlphaElimW) :
    ∃ (Tb : Sylow 3 (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3))
      (K : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)),
      ReducedNongeneration 3 (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) Tb
        (((Subgroup.centralizer ({e} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({e} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3))) ∧
      4 ≤ Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)) ∧
      CatalogSimpleSections (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) ∧
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)
        ⟨e, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _ ∧
      IsComponentOf K ⊤ ∧ K.Normal ∧
      (∀ L : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3),
          IsComponentOf L ⊤ → L = K) ∧
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)
        ⟨e, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∉ K ∧
      ∃ (A : Subgroup K) (f : A →* Λ), Function.Surjective f := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({e} : Set G)) 3
  have hcore : GLBPrimeCore 3 (Subgroup.centralizer ({e} : Set G)) ≤ M :=
    intersecting_local_primeCore_le 3 hp P hPM hloc.core hrank
  have h3 : 3 ≤ Open.pRank 3 ((T : Subgroup _).map (Subgroup.centralizer ({e} : Set G)).subtype) :=
    (by norm_num : 3 ≤ 4).trans h4
  obtain ⟨Tb, hTb, hred⟩ := reducedNongeneration_of_not_le hp hp2 P hPM hloc.core hCM T hTP h3
    hcore
  set eC : Subgroup.centralizer ({e} : Set G) := ⟨e, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzZ := mk_mem_center_centralizer (primeComplementCore (G := Subgroup.centralizer
    ({e} : Set G)) 3) (zC := eC) rfl
  have hzp : orderOf (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer
      ({e} : Set G)) 3) eC) = 3 :=
    orderOf_mk_of_coprime hp _ hO (by rw [← Subgroup.orderOf_coe]; exact he3)
  have hlayer := layer_ne_bot_of_four_le_pRank hp hp2 P hPM hloc.core hCM T hTP h4 hcore
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  have hKn := hred.normal_of_isComponentOf_of_center hzZ hzp hK
  have huniq : ∀ L : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3),
      IsComponentOf L ⊤ → L = K := fun L hL => hred.eq_of_isComponentOf_of_center hzZ hzp hL hK
  have he1 : e ≠ 1 := fun h1 => hp.one_lt.ne (by rw [← he3, h1, orderOf_one])
  have hcat : CatalogSimpleSections (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) :=
    (catalogSimpleSections_of_isKProper hglob.kProper _
      (centralizer_singleton_ne_top hglob.simple hglob.nonab he1)).quotient _
  have hR4 : 4 ≤ Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)) := by
    rw [hTb, pRank_map_mk_eq_pRank_map_subtype hp _ hO]
    exact h4
  obtain ⟨A, f, hf⟩ :=
    Sp48NCent.exists_surjective_unique hred hcat hSch hK hKn huniq hW hΛ φ hφ hx hx3
  refine ⟨Tb, K, hred, hR4, hcat, hzZ, hK, hKn, huniq, fun hzK => ?_, A, f, hf⟩
  exact hred.false_of_caseTwo_of_mem hR4 hcat hzZ hzp hK hKn hzK hAE (Or.inl rfl) hiso f hf

end CM

end CFSG.AGLEmbedding
