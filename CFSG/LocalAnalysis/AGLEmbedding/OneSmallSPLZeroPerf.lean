module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszOut
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.FeitThompson.OddOrderTheorem

public section


namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Perf

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem exists_surjective_of_le_centralizer (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M)
    (hzp : orderOf z = p) {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hDz : D ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ φ : (Subgroup.centralizer ({z} : Set G) ⊓
        (D.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype : Subgroup G) →* D,
      Function.Surjective φ := by
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set W : Subgroup G :=
    Subgroup.centralizer ({z} : Set G) ⊓ (D.comap πM).map M.subtype
  have hWM : W ≤ M := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hφ₀ : ∀ w : W, πM (Subgroup.inclusion hWM w) ∈ D := by
    rintro ⟨w, -, m, hm, rfl⟩
    exact hm
  refine ⟨(πM.comp (Subgroup.inclusion hWM)).codRestrict _ hφ₀, ?_⟩
  have hzMp : orderOf (⟨z, hzM⟩ : M) = p := by rw [← Subgroup.orderOf_coe]; exact hzp
  intro x
  have hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq hp _ hcop
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzMp, pow_one])) (hDz x.2)
  have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  have hgD : g ∈ D.comap πM := by
    rw [Subgroup.mem_comap, hgx]
    exact x.2
  exact ⟨⟨g, hgC, g, hgD, rfl⟩, Subtype.ext hgx⟩

theorem D1OneSmallData.odd_card_primeCore_cz (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hSP : D1CzSP p z) :
    ∃ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC ∧
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  refine ⟨P', Pbar, KC, hRC, ?_⟩
  set C := Subgroup.centralizer ({z} : Set G)
  have hRC' : R ≤ C := hd.le_centralizer_czElt hz
  have hCM : ¬ C ≤ M := hd.centralizer_not_le hz
  set T : Subgroup G := (P' : Subgroup G) ⊓ C
  have hTp : IsPGroup p T := P'.isPGroup'.to_le inf_le_left
  have hTM : T ≤ M := inf_le_left.trans hP'M
  have hT4 : 4 ≤ Open.pRank p T := by
    have h4 := hRC.four_le_pRank
    rw [hRC.sylow_eq, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.subgroupOf_map_subtype] at h4
    exact h4
  have hRT : R ≤ T := le_inf hRP' hRC'
  have hRT' : R < T := lt_of_le_of_ne hRT fun h => by
    have h3 := hd.pRank_R
    rw [h] at h3
    omega
  have hcoreM : GLBPrimeCore p C ≤ M :=
    intersecting_local_primeCore_le p hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      (hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRC' hd.cfg.ext.le_M)))
  exact odd_card_of_twoLocals_le hp hTp inf_le_right hCM (glbPrimeCore_le p _)
    (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) hcoreM
    fun U hU hU1 hTU => hd.cfg.ext.le_of_card_lt hTM hTp (by omega)
      (Subgroup.card_lt_of_lt hRT') ⟨U, hU1, hU, rfl⟩ hTU

theorem D1OneSmallData.eq_bot_of_perfect_le_centralizer (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hSP : D1CzSP p z) (hout : D1CzOutside p z) (hzM : z ∈ M)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D)
    (hDz : D ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    D = ⊥ := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P', Pbar, KC, hRC, hodd⟩ := hd.odd_card_primeCore_cz hz hSP
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzpbar⟩ := hRC.center ⟨z, hzC⟩ rfl
  have := hRC.normal
  have hsolv := hRC.red.isSolvable_inf_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzpbar
    hRC.comp hRC.normal (hout KC hRC.comp) hβ hKO hΓ
  set W : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ ((D.comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)
  obtain ⟨φ, hφ⟩ := exists_surjective_of_le_centralizer hp hp2 hzM hz.2.1 hDz
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hWM : W ≤ M := inf_le_right.trans (Subgroup.map_subtype_le _)
  set E : Subgroup W := perfectCore (⊤ : Subgroup W)
  have hEperf : ⁅E, E⁆ = E := perfectCore_perfect _
  have hDper : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDp
  have hEφ : E.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect
      (by rw [← commutator_def]; exact hDper.commutator_eq_top)
  set ρ : W →* D1CzQuot p z := (QuotientGroup.mk' _).comp (Subgroup.inclusion hWC)
  have hEK : E.map ρ ≤ KC := hRC.le_of_isPerfect hSch
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hEperf]))
  have hEX : E.map ρ ≤ ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _) := by
    rintro _ ⟨w, -, rfl⟩
    exact ⟨Subgroup.inclusion hWC w, ⟨(w : W).2.1, hWM (w : W).2⟩, rfl⟩
  have hEbot : E.map ρ = ⊥ := by
    by_contra hne
    have : Nontrivial (E.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect (E.map ρ) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hEperf])
    have hsE : Group.IsSolvable (E.map ρ) := by
      have hle : (E.map ρ).subgroupOf KC ≤
          (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
            (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _)).subgroupOf KC :=
        fun x hx => hEX hx
      have h1 : Group.IsSolvable (((E.map ρ).subgroupOf KC).subgroupOf
          ((((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
            (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _)).subgroupOf KC)) :=
        inferInstance
      have h2 : Group.IsSolvable ((E.map ρ).subgroupOf KC) :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hEK).toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.not_isSolvable (E.map ρ) hsE
  have hEker : ∀ e ∈ E, Subgroup.inclusion hWC e ∈
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p := by
    intro e he
    have h1 : ρ e ∈ E.map ρ := Subgroup.mem_map_of_mem _ he
    rw [hEbot, Subgroup.mem_bot] at h1
    rw [← QuotientGroup.ker_mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
      MonoidHom.mem_ker]
    exact h1
  let ψ : E →* primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p :=
    { toFun := fun e => ⟨Subgroup.inclusion hWC e, hEker e e.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b hab => by
    have h1 := congrArg (fun x : primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p =>
      ((x : Subgroup.centralizer ({z} : Set G)) : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hEO := Subgroup.card_dvd_of_injective ψ hψ
  have hOcard : Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) =
      Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) := by
    rw [← glbPrimeCore_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le p _)).toEquiv
  have hDE : Nat.card D ∣ Nat.card E := by
    have h1 := Subgroup.card_map_dvd E φ
    rw [hEφ, Subgroup.card_top] at h1
    exact h1
  have hEodd : Odd (Nat.card E) := Odd.of_dvd_nat (by rw [hOcard]; exact hodd) hEO
  have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat hEodd hDE
  by_contra hne
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable D (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hDodd)

end Perf

end CFSG.AGLEmbedding
