module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentApply
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem isSolvable_of_layer_eq_bot {X : Type} [Group X] [Finite X] {Tb : Sylow 3 X}
    {X₀ : Subgroup X} (h : ReducedNongeneration 3 X Tb X₀) (hlayer : CFSG.layer X = ⊥) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzc : z ∈ Subgroup.centralizer ((Tb : Subgroup X) : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hz g
  obtain ⟨-, E, C, hEn, -, -, -, -, hEZ, -, -, -, -, -, -, -, -, -, hker, e, -⟩ :=
    h.structure_of_layer_eq_bot3 hlayer hzc hzp
  have : E.Normal := hEn
  set ρ := CFSG.LocalAnalysis.RankThreeTheoremC.centerQuotientActionNormal E e
  have hle : ρ.ker ≤ (CFSG.pCore 3 X).subtype.range := fun x hx =>
    ⟨⟨x, (hker x).mpr
      ((CFSG.LocalAnalysis.RankThreeTheoremC.mem_ker_centerQuotientActionNormal hEZ e).mp hx)⟩,
      rfl⟩
  have : Group.IsNilpotent (CFSG.pCore 3 X) := (CFSG.pCore_isPGroup (p := 3)).isNilpotent
  have : Group.IsSolvable (GL (Fin 2) (ZMod 3)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
      (ZMod 3) (Or.inr (by simp))
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 3 X).subtype ρ hle

theorem false_of_isSolvable_of_surjective {G : Type} [Group G] [Finite G] {e : G}
    (hsolv : Group.IsSolvable (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3))
    {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({e} : Set G)) {Λ : Type} [Group Λ]
    [Finite Λ] [IsSimpleGroup Λ] (hΛ : Group.IsPerfect Λ) (φ : W →* Λ)
    (hφ : Function.Surjective φ) {x : Λ} (hx : x ≠ 1) (hx3 : x ^ 3 ^ 1 = 1) : False := by
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
  have hDρ : D.map ρ = ⊥ := by
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [← Subgroup.map_commutator, hDperf] at hlt
    exact hlt.ne rfl
  have hDk : D ≤ φ.ker := fun d hd => by
    have h1 : ρ d = 1 := by
      have : ρ d ∈ D.map ρ := ⟨d, hd, rfl⟩
      rwa [hDρ, Subgroup.mem_bot] at this
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hker h1
  have htop : (⊤ : Subgroup Λ) = ⊥ := by
    rw [← hDφ, eq_bot_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact hDk hd
  exact hx (by
    have : x ∈ (⊤ : Subgroup Λ) := Subgroup.mem_top x
    rwa [htop, Subgroup.mem_bot] at this)

@[expose] def D1Sp48NCentRankCompResidue : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A V : Subgroup G} {d : G},
    D1Local 3 P M → D1Extremal 3 P M H R → D1Sp48NData P M H R X U A V →
    CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ → d ∈ centerOf R → d ≠ 1 →
    ¬ Subgroup.centralizer ({d} : Set G) ⊓ H ≤ M →
    (∃ Y : Subgroup G, IsPGroup 3 Y ∧ R < Y ∧ Y ≤ M ⊓ Subgroup.centralizer ({d} : Set G)) →
    D1Sp48NInvolves H d → pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥ →
    ∀ (Tb : Sylow 3 (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3))
      (K : Subgroup (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)),
      ReducedNongeneration 3 (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3) Tb
        (((Subgroup.centralizer ({d} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({d} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3))) →
      CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)) = 3 →
      CatalogSimpleSections (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3) →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)
        ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _ →
      IsComponentOf K ⊤ → K.Normal →
      (∀ L : Subgroup (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3),
          IsComponentOf L ⊤ → L = K) →
      (∃ (B : Subgroup K) (L : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (f : B →* L),
        Function.Surjective f ∧ IsCaseTwoGroup 3 L) → False

theorem d1Sp48NCentRankResidue_of_comp (hSch : KFactCatalogSchreier)
    (hres : D1Sp48NCentRankCompResidue) : D1Sp48NCentRankResidue := by
  intro G _ _ P M H R X U A V d Y hloc hext hd hO3 hdZ hd1 hCH hY3 hRY hYC hinv hO
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set C := Subgroup.centralizer ({d} : Set G)
  intro T hYT hT3
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hd.elem_X.2 d (hd.center_le hdZ)) hd1
  have hT3' : IsPGroup 3 ((T : Subgroup C).map C.subtype) := T.isPGroup'.map _
  have hR3 : 3 ≤ CFSG.Open.pRank 3 R := hext.three_le_pRank
  have hYr : 3 ≤ CFSG.Open.pRank 3 Y := hR3.trans (pRank_mono 3 hp hRY.le)
  have hPM : (P : Subgroup G) ≤ M := hext.sylow_le
  have hT'M : (T : Subgroup C).map C.subtype ≤ M :=
    intersecting_pSubgroup_le 3 hp P hPM hloc.core hT3'
      (hYr.trans (pRank_mono 3 hp (le_inf hYT (hYC.trans inf_le_left))))
  obtain ⟨P', hloc', hP'M, hTP'⟩ := Sp48NCent.exists_sylow_conj hloc hPM hT'M hT3'
  have hCM : ¬ C ≤ M := fun h => hCH (inf_le_left.trans h)
  have hRC : R ≤ C := fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hdZ.2 r hr)
  have hrank : 3 ≤ CFSG.Open.pRank 3 (C ⊓ M) :=
    hR3.trans (pRank_mono 3 hp (le_inf hRC hext.le_M))
  have hcore : GLBPrimeCore 3 C ≤ M :=
    intersecting_local_primeCore_le 3 hp P' hP'M hloc'.core hrank
  have h3 : 3 ≤ CFSG.Open.pRank 3 ((T : Subgroup C).map C.subtype) :=
    hYr.trans (pRank_mono 3 hp hYT)
  have hO' := primeComplementCore_coprime (G := C) 3
  obtain ⟨Tb, hTb, hred⟩ := reducedNongeneration_of_not_le hp (by norm_num) P' hP'M hloc'.core
    hCM T hTP' h3 hcore
  have hzZ := mk_mem_center_centralizer (primeComplementCore (G := C) 3)
    (zC := ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) rfl
  have hzp : orderOf (QuotientGroup.mk' (primeComplementCore (G := C) 3)
      ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 3 :=
    orderOf_mk_of_coprime hp _ hO' (by rw [← Subgroup.orderOf_coe]; exact hd3)
  have hTb3 : CFSG.Open.pRank 3 (Tb : Subgroup (C ⧸ primeComplementCore (G := C) 3)) = 3 := by
    rw [hTb, pRank_map_mk_eq_pRank_map_subtype hp _ hO']
    omega
  have hglob := hd.surv.ph3.glob
  have hcat : CatalogSimpleSections (C ⧸ primeComplementCore (G := C) 3) :=
    (catalogSimpleSections_of_isKProper hglob.kProper _
      (centralizer_singleton_ne_top hglob.simple hglob.nonab hd1)).quotient _
  obtain ⟨W, L, φ, hWC, hφ, hLs, hLp, hLiso, x, hxL, hx1, hx3⟩ := hinv
  have : IsSimpleGroup L := hLs
  have hx1' : (⟨x, hxL⟩ : L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx3' : (⟨x, hxL⟩ : L) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hx3)
  by_cases hlayer : CFSG.layer (C ⧸ primeComplementCore (G := C) 3) = ⊥
  · exact false_of_isSolvable_of_surjective (isSolvable_of_layer_eq_bot hred hlayer hzZ hzp) hWC
      (Subgroup.isPerfect_iff.mpr hLp) φ hφ hx1' hx3'
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  have hKn := hred.normal_of_isComponentOf_of_center hzZ hzp hK
  have huniq : ∀ L' : Subgroup (C ⧸ primeComplementCore (G := C) 3), IsComponentOf L' ⊤ →
      L' = K := fun L' hL' => hred.eq_of_isComponentOf_of_center hzZ hzp hL' hK
  obtain ⟨B, f, hf⟩ := Sp48NCent.exists_surjective_unique hred hcat hSch hK hKn huniq hWC
    (Subgroup.isPerfect_iff.mpr hLp) φ hφ hx1' hx3'
  exact hres hloc hext hd hO3 hdZ hd1 hCH ⟨Y, hY3, hRY, hYC⟩
    ⟨W, L, φ, hWC, hφ, hLs, hLp, hLiso, x, hxL, hx1, hx3⟩ hO Tb K hred hTb3 hcat hzZ hK hKn
    huniq ⟨B, L, f, hf, hLiso⟩

end CFSG.AGLEmbedding
