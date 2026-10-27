module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockEscRed
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentApply
public import CFSG.Quasithin.EmptyFaithful.ModHA6

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section CM

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G}

theorem Sp62Block.cm_data (hloc : D1Local 3 P M) (hPM : (P : Subgroup G) ≤ M)
    (hglob : D1Global G) {e : G} (he3 : orderOf e = 3)
    (hCM : ¬ Subgroup.centralizer ({e} : Set G) ≤ M)
    (hrank : 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({e} : Set G) ⊓ M))
    (T : Sylow 3 (Subgroup.centralizer ({e} : Set G)))
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({e} : Set G)).subtype ≤ P)
    (h4 : 4 ≤ CFSG.Open.pRank 3
      ((T : Subgroup _).map (Subgroup.centralizer ({e} : Set G)).subtype))
    {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({e} : Set G)) {Λ : Type} [Group Λ]
    [Finite Λ] [IsSimpleGroup Λ] (hΛ : Group.IsPerfect Λ)
    (φ : W →* Λ) (hφ : Function.Surjective φ) {x : Λ} (hx : x ≠ 1) (hx3 : x ^ 3 ^ 1 = 1)
    (hSch : KFactCatalogSchreier) :
    ∃ (Tb : Sylow 3 (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3))
      (K : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)),
      ReducedNongeneration 3 (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) Tb
        (((Subgroup.centralizer ({e} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({e} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3))) ∧
      4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)) ∧
      CatalogSimpleSections (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3) ∧
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)
        ⟨e, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _ ∧
      IsComponentOf K ⊤ ∧ K.Normal ∧
      (∀ L : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3),
          IsComponentOf L ⊤ → L = K) ∧
      ∃ (A : Subgroup K) (f : A →* Λ), Function.Surjective f := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({e} : Set G)) 3
  have hcore : GLBPrimeCore 3 (Subgroup.centralizer ({e} : Set G)) ≤ M :=
    intersecting_local_primeCore_le 3 hp P hPM hloc.core hrank
  have h3 : 3 ≤ CFSG.Open.pRank 3
      ((T : Subgroup _).map (Subgroup.centralizer ({e} : Set G)).subtype) :=
    (by norm_num : 3 ≤ 4).trans h4
  obtain ⟨Tb, hTb, hred⟩ := reducedNongeneration_of_not_le hp hp2 P hPM hloc.core hCM T hTP h3
    hcore
  set eC : Subgroup.centralizer ({e} : Set G) :=
    ⟨e, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
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
  have hR4 : 4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({e} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({e} : Set G)) 3)) := by
    rw [hTb, pRank_map_mk_eq_pRank_map_subtype hp _ hO]
    exact h4
  obtain ⟨A, f, hf⟩ :=
    Sp48NCent.exists_surjective_unique hred hcat hSch hK hKn huniq hW hΛ φ hφ hx hx3
  exact ⟨Tb, K, hred, hR4, hcat, hzZ, hK, hKn, huniq, A, f, hf⟩

end CM

@[expose] def D1Sp62CMResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, p = 3 → IsSpSixTwoIndex d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ L : Subgroup G, Sp62BlockShape M H R L →
          blockCentralizer M L ≤ GLBPrimeCore p H →
          (∀ d' : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d' →
            IsEmpty (barM M L ≃* CatGroup d')) →
          ∀ x ∈ R, orderOf x = p → ¬ Subgroup.centralizer ({x} : Set G) ⊓ H ≤ M →
            pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ →
            (∃ A : Subgroup G, A ≤ R ⊓ Subgroup.centralizer ({x} : Set G) ∧
              IsElemAbelian p A ∧ Nat.card A = p ^ 3) →
            (∃ E : Subgroup G, E ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧
              IsElemAbelian p E ∧ Nat.card E = p ^ 4) →
            (∃ Y : Subgroup G, Y ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup p Y ∧
              p ^ 5 ≤ Nat.card Y ∧ 4 ≤ CFSG.Open.pRank p Y) →
            (∃ (W : Subgroup G) (φ : W →* alternatingGroup (Fin 6)),
              W ≤ Subgroup.centralizer ({x} : Set G) ⊓ H ∧ Function.Surjective φ) →
            ∀ (Tb : Sylow 3 (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3))
              (KC : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)),
              ReducedNongeneration 3 (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) Tb
                (((Subgroup.centralizer ({x} : Set G) ⊓ M).subgroupOf
                  (Subgroup.centralizer ({x} : Set G))).map
                    (QuotientGroup.mk' (primeComplementCore 3))) →
              4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)) →
              CatalogSimpleSections (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) →
              QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
                ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _ →
              IsComponentOf KC ⊤ → KC.Normal →
              (∀ L' : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
                primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3),
                  IsComponentOf L' ⊤ → L' = KC) →
              (∃ (B : Subgroup KC) (f : B →* alternatingGroup (Fin 6)), Function.Surjective f) →
              False

theorem d1Sp62EscResidue_of_cm (hSch : KFactCatalogSchreier) (hres : D1Sp62CMResidue) :
    D1Sp62EscResidue := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL hCL h4 x hxR hx3
    hxH hO hA hE hY hW
  subst hp3
  have := CFSG.Quasithin.ModH.a6_simple
  obtain ⟨E, hEC, hEe, hEc⟩ := hE
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  have hEC' : E ≤ C := hEC.trans inf_le_right
  obtain ⟨T, hT⟩ := (hE3.comap_subtype (K := C)).exists_le_sylow
  have hET : E ≤ (T : Subgroup C).map C.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEC']
    exact Subgroup.map_mono hT
  have hT3 : IsPGroup 3 ((T : Subgroup C).map C.subtype) := T.isPGroup'.map _
  have h4T : 4 ≤ CFSG.Open.pRank 3 ((T : Subgroup C).map C.subtype) :=
    CFSG.SectionRank.le_pRank (by norm_num) hET hEe hEc
  have hPM : (P : Subgroup G) ≤ M := hcfg.ext.sylow_le
  have hTM : (T : Subgroup C).map C.subtype ≤ M :=
    intersecting_pSubgroup_le 3 Nat.prime_three P hPM hcfg.loc.core hT3
      ((by norm_num : 3 ≤ 4).trans (CFSG.SectionRank.le_pRank (by norm_num)
        (le_inf hET (hEC.trans inf_le_left)) hEe hEc))
  obtain ⟨P', hloc', hP'M, hTP'⟩ := Sp48NCent.exists_sylow_conj hcfg.loc hPM hTM hT3
  have hCM : ¬ C ≤ M := fun h => hxH (inf_le_left.trans h)
  have hrank : 3 ≤ CFSG.Open.pRank 3 (C ⊓ M) :=
    (by norm_num : 3 ≤ 4).trans (CFSG.SectionRank.le_pRank (by norm_num)
      (le_inf hEC' (hEC.trans inf_le_left)) hEe hEc)
  obtain ⟨W, φ, hWC, hφ⟩ := hW
  have hperf : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 6)) 3
    (by rw [CFSG.Quasithin.ModH.a6_card]; norm_num)
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha; norm_num at ha
  have ha3 : a ^ 3 ^ 1 = 1 := by rw [pow_one, ← ha]; exact pow_orderOf_eq_one a
  obtain ⟨Tb, KC, hred, hR4, hcat, hzZ, hKC, hKCn, huniqC, B, f, hf⟩ :=
    Sp62Block.cm_data hloc' hP'M hcfg.glob hx3 hCM hrank T hTP' h4T (hWC.trans inf_le_left)
      hperf φ hφ ha1 ha3 hSch
  exact hres G 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD d rfl hd e L hL hCL h4 x hxR hx3
    hxH hO hA ⟨E, hEC, hEe, hEc⟩ hY ⟨W, φ, hWC, hφ⟩ Tb KC hred hR4 hcat hzZ hKC hKCn huniqC
    ⟨B, f, hf⟩

end CFSG.AGLEmbedding
