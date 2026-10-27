module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentMethod
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszOut
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentData

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1Sp48NCentRankResidue : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A V : Subgroup G} {d : G}
    {Y : Subgroup G}, D1Local 3 P M → D1Extremal 3 P M H R → D1Sp48NData P M H R X U A V →
    CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ → d ∈ centerOf R → d ≠ 1 →
    ¬ Subgroup.centralizer ({d} : Set G) ⊓ H ≤ M → IsPGroup 3 Y → R < Y →
    Y ≤ M ⊓ Subgroup.centralizer ({d} : Set G) → D1Sp48NInvolves H d →
    pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥ →
    ∀ T : Sylow 3 (Subgroup.centralizer ({d} : Set G)),
      Y ≤ (T : Subgroup _).map (Subgroup.centralizer ({d} : Set G)).subtype →
      Open.pRank 3 ((T : Subgroup _).map (Subgroup.centralizer ({d} : Set G)).subtype) ≤ 3 →
      False

@[expose] def D1Sp48NCentBetaResidue : Prop :=
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
      4 ≤ Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)) →
      CatalogSimpleSections (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3) →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)
        ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _ →
      IsComponentOf K ⊤ → K.Normal →
      (∀ L : Subgroup (Subgroup.centralizer ({d} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3),
          IsComponentOf L ⊤ → L = K) →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)
        ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∉ K →
      Group.IsSolvable ((((Subgroup.centralizer ({d} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({d} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore 3))).subgroupOf K) →
      (∃ (B : Subgroup K) (L : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (f : B →* L),
        Function.Surjective f ∧ IsCaseTwoGroup 3 L) → False

section Apply

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G}

theorem Sp48NCent.exists_sylow_conj (hloc : D1Local 3 P M) (hPM : (P : Subgroup G) ≤ M)
    {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 3 T) :
    ∃ P' : Sylow 3 G, D1Local 3 P' M ∧ (P' : Subgroup G) ≤ M ∧ T ≤ P' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcM, hc⟩ := CFSG.LyonsUnitaryFour.exists_conj_le_sylow_of_le P hPM hTM hT
  have hcoe : ((c⁻¹ • P : Sylow 3 G) : Subgroup G) =
      (P : Subgroup G).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    rfl
  refine ⟨c⁻¹ • P, ⟨hloc.beta, hloc.maxLocal, ?_⟩, ?_, ?_⟩
  · rw [hcoe]
    exact weakCore_conj_le Nat.prime_three hloc.core (M.inv_mem hcM)
  · rw [hcoe]
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) (hPM hq)) hcM
  · rw [hcoe]
    intro q hq
    refine ⟨c * q * c⁻¹, hc q hq, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem d1Sp48NCentResidue_of_cm (hSch : KFactCatalogSchreier) (hAE : KFactCaseTwoAlphaElimW)
    (hβ : KFactBeta) (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable)
    (hRk : D1Sp48NCentRankResidue) (hBe : D1Sp48NCentBetaResidue) : D1Sp48NCentResidue := by
  intro G _ _ P M H R X U A V d hloc hext hd hO3 hdZ hd1 hCH hY hinv hO
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Y, hY3, hRY, hYC⟩ := hY
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hd.elem_X.2 d (hd.center_le hdZ)) hd1
  have hYC' : Y ≤ C := hYC.trans inf_le_right
  obtain ⟨T, hT⟩ := (hY3.comap_subtype (K := C)).exists_le_sylow
  have hYT : Y ≤ (T : Subgroup C).map C.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hYC']
    exact Subgroup.map_mono hT
  have hT3 : IsPGroup 3 ((T : Subgroup C).map C.subtype) := T.isPGroup'.map _
  have hR3 : 3 ≤ Open.pRank 3 R := hext.three_le_pRank
  have hYr : 3 ≤ Open.pRank 3 Y := hR3.trans (pRank_mono 3 Nat.prime_three hRY.le)
  have hPM : (P : Subgroup G) ≤ M := hext.sylow_le
  have hT'M : (T : Subgroup C).map C.subtype ≤ M :=
    intersecting_pSubgroup_le 3 Nat.prime_three P hPM hloc.core hT3
      (hYr.trans (pRank_mono 3 Nat.prime_three (le_inf hYT (hYC.trans inf_le_left))))
  by_cases h4 : 4 ≤ Open.pRank 3 ((T : Subgroup C).map C.subtype)
  swap
  · exact hRk hloc hext hd hO3 hdZ hd1 hCH hY3 hRY hYC hinv hO T hYT
      (Nat.le_of_lt_succ (not_le.mp h4))
  obtain ⟨P', hloc', hP'M, hTP'⟩ := Sp48NCent.exists_sylow_conj hloc hPM hT'M hT3
  have hCM : ¬ C ≤ M := fun h => hCH (inf_le_left.trans h)
  have hRC : R ≤ C := fun r hr => by
    have hc : r * d = d * r := Subgroup.mem_centralizer_iff.mp hdZ.2 r hr
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc
  have hrank : 3 ≤ Open.pRank 3 (C ⊓ M) :=
    hR3.trans (pRank_mono 3 Nat.prime_three (le_inf hRC hext.le_M))
  obtain ⟨W, L, φ, hWC, hφ, hLs, hLp, hLiso, x, hxL, hx1, hx3⟩ := hinv
  have : IsSimpleGroup L := hLs
  have hx1' : (⟨x, hxL⟩ : L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx3' : (⟨x, hxL⟩ : L) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hx3)
  obtain ⟨Tb, K, hred, hR4, hcat, hzZ, hK, hKn, huniq, hzK, B, f, hf⟩ :=
    Sp48NCent.cm_beta hloc' hP'M
      (hd.surv.ph3.glob.toD1Global (four_le_evenRank_of_mem_betaFour hloc'.beta)) hd3 hCM hrank T
      hTP' h4 hWC
      (Subgroup.isPerfect_iff.mpr hLp) hLiso φ hφ hx1' hx3' hSch hAE
  have hzp : orderOf (QuotientGroup.mk' (primeComplementCore (G := C) 3)
      ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 3 :=
    orderOf_mk_of_coprime Nat.prime_three _ (primeComplementCore_coprime 3)
      (by rw [← Subgroup.orderOf_coe]; exact hd3)
  have hsolv := hred.isSolvable_inf_of_not_mem hR4 hcat hzZ hzp hK hKn hzK hβ hKO hΓ
  exact hBe hloc hext hd hO3 hdZ hd1 hCH ⟨Y, hY3, hRY, hYC⟩
    ⟨W, L, φ, hWC, hφ, hLs, hLp, hLiso, x, hxL, hx1, hx3⟩ hO Tb K hred hR4 hcat hzZ hK hKn
    huniq hzK hsolv ⟨B, L, f, hf, hLiso⟩

theorem d1Sp48NonsolvResidue_closed_cm (hSchur : KFactChevTwoSurvivorSchur)
    (hK48 : KFactSp48Local) (hKN : KFactSp48NonsolvLocal) (hKC : KFactSp48NonsolvCent)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hSch : KFactCatalogSchreier)
    (hAE : KFactCaseTwoAlphaElimW) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hRk : D1Sp48NCentRankResidue)
    (hBe : D1Sp48NCentBetaResidue) : D1Sp48NonsolvResidue :=
  d1Sp48NonsolvResidue_closed_cent hSchur hK48 hKN hKC h84 hD2
    (d1Sp48NCentResidue_of_cm hSch hAE hβ hKO hΓ hRk hBe)

end Apply

end CFSG.AGLEmbedding
