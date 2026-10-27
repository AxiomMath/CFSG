module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbLinTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.exists_cover_cz (hSch : KFactCatalogSchreier)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    {P' : Sylow 3 G} {Pbar : Sylow 3 (D1CzQuot 3 z)} {KC : Subgroup (D1CzQuot 3 z)}
    (hRC : D1ReducedCentralizer 3 P' M z Pbar KC) {Xt : Subgroup (D1CzQuot 3 z)}
    (hXt : Xt = ((d1LiftX 3 H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3))) :
    Xt ≤ KC ∧ ∃ (W : Subgroup KC) (f : W →* K), Function.Surjective f ∧
      (∀ w : W, f w = 1 → Nat.Coprime 3 (orderOf w)) ∧ Xt.subgroupOf KC ≤ W ∧
      ∃ TL : Sylow 3 K, ((Xt.subgroupOf KC).subgroupOf W).map f = (TL : Subgroup K) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  subst hXt
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  set Oz : Subgroup C := primeComplementCore (G := C) 3 with hOz
  have hOzc : Nat.Coprime 3 (Nat.card Oz) := primeComplementCore_coprime 3
  set ρ : C →* C ⧸ Oz := QuotientGroup.mk' Oz with hρ
  set X := d1LiftX 3 H R K with hXdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  obtain ⟨-, hzp', hzH, hzc⟩ := id hz
  set W₀ : Subgroup G := C ⊓ (K.comap π).map H.subtype with hW₀
  have hW₀H : W₀ ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hW₀C : W₀ ≤ C := inf_le_left
  have hφ₀ : ∀ w : W₀, π (Subgroup.inclusion hW₀H w) ∈ K := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W₀ →* K := (π.comp (Subgroup.inclusion hW₀H)).codRestrict K hφ₀ with hφdef
  have hzH' : orderOf (⟨z, hzH⟩ : H) = 3 := (Subgroup.orderOf_coe _).symm.trans hzp'
  have hO := primeComplementCore_coprime (G := H) 3
  have hφ : Function.Surjective φ := by
    intro l
    obtain ⟨g, hg, hgl⟩ := exists_mem_centralizer_mk_eq hp _ hO
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc l l.2))
    have hgC : (g : G) ∈ C :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have hgL : g ∈ K.comap π := by
      rw [Subgroup.mem_comap, hgl]
      exact l.2
    exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgl⟩
  have hφker : ∀ w : W₀, φ w = 1 → Nat.Coprime 3 (orderOf w) := by
    intro w hw
    have h1 : π (Subgroup.inclusion hW₀H w) = 1 := congrArg Subtype.val hw
    have h2 : Subgroup.inclusion hW₀H w ∈ primeComplementCore (G := H) 3 :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hW₀H w)).mp h1
    have h3 := Subgroup.orderOf_dvd_natCard _ h2
    rw [orderOf_injective _ (Subgroup.inclusion_injective hW₀H)] at h3
    exact hO.coprime_dvd_right h3
  obtain ⟨hKsimple, -⟩ := hd.isSimpleGroup
  have hKperf : Group.IsPerfect K := ⟨hd.comp.2.2.1⟩
  obtain ⟨T₁, hT₁, -, -, -, hT₁nc, -⟩ := hd.exists_sylow
  obtain ⟨x₁, hx₁⟩ : ∃ x : (T₁ : Subgroup K), x ≠ 1 :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp fun h => hT₁nc (h ▸ inferInstance)
  obtain ⟨k₁, hk₁⟩ := T₁.isPGroup' x₁
  have hx₁' : (x₁ : K) ≠ 1 := fun h1 => hx₁ (Subtype.ext h1)
  have hx₁k : (x₁ : K) ^ 3 ^ k₁ = 1 := by rw [← Subgroup.coe_pow, hk₁, Subgroup.coe_one]
  set D₀ : Subgroup W₀ := perfectCore (⊤ : Subgroup W₀) with hD₀
  have hD₀perf : ⁅D₀, D₀⁆ = D₀ := perfectCore_perfect _
  set ρW : W₀ →* C ⧸ Oz := ρ.comp (Subgroup.inclusion hW₀C) with hρW
  have hDK : D₀.map ρW ≤ KC := hRC.le_of_isPerfect hSch
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hD₀perf]))
  set ρK : D₀ →* KC := (ρW.comp D₀.subtype).codRestrict KC fun d => hDK ⟨d, d.2, rfl⟩
    with hρK
  have hDφ : D₀.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hKperf.commutator_eq_top)
  have hφD : Function.Surjective (φ.comp D₀.subtype) := by
    intro l
    obtain ⟨d, hd', hdl⟩ : l ∈ D₀.map φ := hDφ ▸ Subgroup.mem_top l
    exact ⟨⟨d, hd'⟩, hdl⟩
  have hkerρK : ρK.rangeRestrict.ker ≤ (φ.comp D₀.subtype).ker := by
    rw [MonoidHom.ker_rangeRestrict]
    refine le_trans ?_ (Subgroup.comap_mono (f := D₀.subtype)
      (le_ker_of_isSimpleGroup (p := 3) φ hφ (Oz.comap (Subgroup.inclusion hW₀C)) ?_ hx₁' hx₁k))
    · intro d hd'
      have h1 : ρ (Subgroup.inclusion hW₀C (d : W₀)) = 1 := congrArg Subtype.val hd'
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hW₀C (d : W₀))).mp h1
    · intro n hn
      have h1 : orderOf (Subgroup.inclusion hW₀C n) ∣ Nat.card Oz :=
        Subgroup.orderOf_dvd_natCard _ hn
      rw [orderOf_injective _ (Subgroup.inclusion_injective hW₀C)] at h1
      exact hOzc.coprime_dvd_right h1
  obtain ⟨f, hfρ, hf, hfker⟩ := exists_surjective_comp_eq ρK.rangeRestrict
    ρK.rangeRestrict_surjective (φ.comp D₀.subtype) hφD hkerρK
  have hfker' : ∀ w : ρK.range, f w = 1 → Nat.Coprime 3 (orderOf w) := by
    intro w hw
    have hw' : w ∈ f.ker := hw
    rw [hfker] at hw'
    obtain ⟨d, hd', rfl⟩ := hw'
    have h1 : orderOf (ρK.rangeRestrict d) ∣ orderOf d := orderOf_map_dvd _ d
    have h2 : orderOf (d : W₀) = orderOf d := Subgroup.orderOf_coe d
    exact Nat.Coprime.coprime_dvd_right h1 (h2 ▸ hφker (d : W₀) hd')
  have hXp : IsPGroup 3 X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le 3 H R K)
  have hXC : X ≤ C := hd.d1LiftX_le_centralizer hz
  have hXW₀ : X ≤ W₀ := le_inf hXC (Subgroup.map_mono inf_le_right)
  have hXD : ∀ x (hx : x ∈ X), (⟨x, hXW₀ hx⟩ : W₀) ∈ D₀ := by
    intro x hx
    obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
    refine mem_perfectCore_of_pow_eq_one φ hφ hKperf hφker (k := k) (Subtype.ext ?_)
    simpa using congrArg Subtype.val hk
  have hEtK : (X.subgroupOf C).map ρ ≤ KC := by
    rintro _ ⟨⟨x, hxC⟩, hxX, rfl⟩
    exact hDK ⟨⟨x, hXW₀ hxX⟩, hXD x hxX, rfl⟩
  refine ⟨hEtK, ρK.range, f, hf, hfker', fun e he => ?_, T₁, ?_⟩
  · obtain ⟨⟨x, hxC⟩, hxX, hex⟩ := Subgroup.mem_subgroupOf.mp he
    exact ⟨⟨⟨x, hXW₀ hxX⟩, hXD x hxX⟩, Subtype.ext hex⟩
  have hEp : IsPGroup 3 (((X.subgroupOf C).map ρ).subgroupOf KC) :=
    ((hXp.comap_subtype (K := C)).map ρ).comap_subtype
  have hLp : IsPGroup 3 (((((X.subgroupOf C).map ρ).subgroupOf KC).subgroupOf ρK.range).map f) :=
    hEp.comap_subtype.map f
  refine T₁.is_maximal' hLp fun t ht => ?_
  have h1 : (t : H ⧸ primeComplementCore (G := H) 3) ∈
      ((d1LiftX 3 H R K).subgroupOf H).map π := by
    rw [hd.cfg.map_d1LiftX_eq_inf, ← hT₁]
    exact ⟨t, ht, rfl⟩
  obtain ⟨⟨x, hxH⟩, hxX, hxt⟩ := h1
  have hxX' : x ∈ X := hxX
  refine ⟨ρK.rangeRestrict ⟨⟨x, hXW₀ hxX'⟩, hXD x hxX'⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
      ⟨⟨x, hXC hxX'⟩, hxX', rfl⟩)
  · rw [hfρ]
    exact Subtype.ext hxt

theorem D1OneSmallData.mem_of_mk_mem_cz (hd : D1OneSmallData 3 P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) (y : Subgroup.centralizer ({z} : Set G))
    (hy : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3) y ∈
      ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3))) :
    (y : G) ∈ M := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set ρ := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)
    with hρ
  have hRC' : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hcoreM : GLBPrimeCore 3 (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le 3 hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      (hd.cfg.ext.three_le_pRank.trans (pRank_mono 3 hp (le_inf hRC' hd.cfg.ext.le_M)))
  obtain ⟨v, hvM, hvy⟩ := hy
  have h1 : v⁻¹ * y ∈ primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3 := by
    refine (QuotientGroup.eq_one_iff (v⁻¹ * y)).mp ?_
    change ρ (v⁻¹ * y) = 1
    rw [map_mul, map_inv, hvy, inv_mul_cancel]
  have h2 : v⁻¹ * y ∈ (GLBPrimeCore 3 (Subgroup.centralizer ({z} : Set G))).subgroupOf
      (Subgroup.centralizer ({z} : Set G)) := by
    rw [glbPrimeCore_subgroupOf]
    exact h1
  have h3 : (y : G) = (v : G) * ((v⁻¹ * y : Subgroup.centralizer ({z} : Set G)) : G) := by simp
  rw [h3]
  exact M.mul_mem (Subgroup.mem_subgroupOf.mp hvM).2 (hcoreM h2)

theorem D1OneSmallData.exists_scalar_cz (hβ : KFactBeta) (hSch : KFactCatalogSchreier)
    (hKS : KFactSPLInvolveScalar) (hd : D1OneSmallData 3 P M H R Rbar K)
    (hspl : IsSPLFamily 3 K) {z : G} (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z)
    (hout : D1CzOutside 3 z) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian 3 A ∧
      d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G) ≤ A ∧
      ∃ c ∈ M, c ∈ Subgroup.normalizer (A : Set G) ∧ ∃ m lam : ℕ, 5 ≤ 2 * m ∧
        ¬ 3 ∣ lam - 1 ∧ (∀ a ∈ A, c ^ m * a * (c ^ m)⁻¹ = a ^ lam) ∧
        ∀ k, 0 < k → k < m → ∀ F : Subgroup G, F ≤ A → F.relIndex A = 3 →
          c ^ k ∉ Subgroup.normalizer (F : Set G) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  set Oz : Subgroup C := primeComplementCore (G := C) 3 with hOz
  have hOzc : Nat.Coprime 3 (Nat.card Oz) := primeComplementCore_coprime 3
  set ρ : C →* C ⧸ Oz := QuotientGroup.mk' Oz with hρ
  set X := d1LiftX 3 H R K with hXdef
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : ρ ⟨z, hzC⟩ ∉ KC := hout KC hRC.comp
  obtain ⟨hKCs, hKCna, hKCc, hAut, T, hTnc, hΓ⟩ := hRC.red.exists_sylow_of_not_mem
    hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp hRC.normal hzK hβ
  obtain ⟨hzR, -, -, -⟩ := id hz
  have hXp : IsPGroup 3 X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le 3 H R K)
  have hXC : X ≤ C := hd.d1LiftX_le_centralizer hz
  set Et : Subgroup (C ⧸ Oz) := (X.subgroupOf C).map ρ with hEt
  obtain ⟨hEtK, W, f, hf, hfker, hEW, TL, hETL⟩ := hd.exists_cover_cz hSch hz hRC hEt
  set E : Subgroup KC := Et.subgroupOf KC with hE
  have hEtp : IsPGroup 3 Et := (hXp.comap_subtype (K := C)).map ρ
  have hEp : IsPGroup 3 E := hEtp.comap_subtype
  obtain ⟨T', hT'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar
    hRC.normal.isSubnormal
  have hEtP : Et ≤ Pbar := by
    rw [hRC.sylow_eq]
    exact Subgroup.map_mono fun x hx => hRP' (d1LiftX_le 3 H R K hx)
  have hET' : E ≤ T' := by
    intro e he
    have h1 : (e : C ⧸ Oz) ∈ (Pbar : Subgroup (C ⧸ Oz)) ⊓ KC :=
      ⟨hEtP (Subgroup.mem_subgroupOf.mp he), e.2⟩
    rw [← hT'] at h1
    obtain ⟨t, ht, hte⟩ := h1
    rwa [← KC.subtype_injective hte]
  obtain ⟨A, hAT', hAel, hZA, c, hcN, m, lam, hm, hlam, hscal, horb⟩ :=
    hKS KC hKCs hKCna hKCc T hTnc hΓ hAut W K hspl f hf hfker E hEW hEp ⟨TL, hETL⟩ T' hET'
  set U : Subgroup (C ⧸ Oz) := A.map KC.subtype with hU
  have hUPK : U ≤ (Pbar : Subgroup (C ⧸ Oz)) ⊓ KC := by
    rw [← hT']
    exact Subgroup.map_mono hAT'
  have hUel : IsElemAbelian 3 U := isElemAbelian_map_of_isElemAbelian KC.subtype hAel
  set ZX : Subgroup G := X ⊓ Subgroup.centralizer (X : Set G) with hZX
  have hZXU : ∀ x (hx : x ∈ ZX), ρ ⟨x, hXC hx.1⟩ ∈ U := by
    intro x hx
    have hxE : (⟨ρ ⟨x, hXC hx.1⟩, hEtK ⟨⟨x, hXC hx.1⟩, hx.1, rfl⟩⟩ : KC) ∈
        E ⊓ Subgroup.centralizer (E : Set KC) := by
      refine ⟨Subgroup.mem_subgroupOf.mpr ⟨⟨x, hXC hx.1⟩, hx.1, rfl⟩,
        Subgroup.mem_centralizer_iff.mpr fun h hh => Subtype.ext ?_⟩
      obtain ⟨⟨y, hyC⟩, hyX, hyh⟩ := Subgroup.mem_subgroupOf.mp hh
      have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.mp hx.2 y hyX
      change (h : C ⧸ Oz) * ρ ⟨x, hXC hx.1⟩ = ρ ⟨x, hXC hx.1⟩ * (h : C ⧸ Oz)
      rw [← hyh, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxy
    exact ⟨_, hZA hxE, rfl⟩
  have hU1 : U ≠ ⊥ := by
    have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hd.d1LiftX_ne_bot
    have := hXp.center_nontrivial
    obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center X)
    have hwZX : ((w : X) : G) ∈ ZX := ⟨(w : X).2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨y, hy⟩)⟩
    intro hbot
    have h1 := hZXU _ hwZX
    rw [hbot, Subgroup.mem_bot] at h1
    obtain ⟨k, hk⟩ := hXp (w : X)
    have h2 := eq_one_of_mk_eq_one_of_coprime Oz hOzc (k := k)
      (a := ⟨((w : X) : G), hXC hwZX.1⟩) (Subtype.ext (by simpa using congrArg Subtype.val hk)) h1
    exact hw (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h2)))
  have hcU : (c : C ⧸ Oz) ∈ Subgroup.normalizer (U : Set (C ⧸ Oz)) :=
    Subgroup.le_normalizer_map KC.subtype ⟨c, hcN, rfl⟩
  obtain ⟨hscalU, horbU⟩ := scalar_push (KC.subtype) (A₂ := U) rfl
    (fun a _ h => KC.subtype_injective (h.trans (map_one _).symm)) hcN
    (t₂ := (c : C ⧸ Oz)) (fun k a _ => by simp) hscal horb
  have hzPbar : ρ ⟨z, hzC⟩ ∈ (Pbar : Subgroup (C ⧸ Oz)) := by
    rw [hRC.sylow_eq]
    exact ⟨⟨z, hzC⟩, hRP' hzR, rfl⟩
  have hzcen : ρ ⟨z, hzC⟩ ∈ Subgroup.centralizer (KC : Set (C ⧸ Oz)) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hzZ g
  have hnc : ¬ IsCyclic ((Pbar : Subgroup (C ⧸ Oz)) ⊓ KC : Subgroup (C ⧸ Oz)) := fun hcyc =>
    hd.not_isCyclic_map hXC (Subgroup.isCyclic_of_le (le_inf hEtP hEtK))
  obtain ⟨c₀, hc₀M, hc₀c⟩ := (hRC.red.rankOne_principle hRC.comp hnc hzPbar hzK hzp hzcen).1
    U hUPK hU1 ⟨c.2, hcU⟩
  have hUX₀ : U ≤ ((C ⊓ M).subgroupOf C).map ρ := by
    refine hUPK.trans (inf_le_left.trans ?_)
    rw [hRC.sylow_eq]
    exact Subgroup.map_mono fun y hy => ⟨y.2, hP'M hy⟩
  have hZp : IsPGroup 3 (ZX.subgroupOf C) := (hXp.to_le inf_le_left).comap_subtype
  obtain ⟨Ah, hAhU, hAhel, hZAh, u, huU, hucN, hscalC, horbC⟩ :=
    exists_lift_scalar Oz hOzc hUel hZp (fun y hy => hZXU (y : G) hy) (c := c₀)
      (by rw [hc₀c]; exact hcU) (by rw [hc₀c]; exact hscalU) (by rw [hc₀c]; exact horbU)
  obtain ⟨hscalG, horbG⟩ := scalar_push C.subtype (A₂ := Ah.map C.subtype) rfl
    (fun a _ h => C.subtype_injective (h.trans (map_one _).symm)) hucN
    (t₂ := ((u * c₀ : C) : G)) (fun k a _ => by simp) hscalC horbC
  refine ⟨Ah.map C.subtype, ?_, isElemAbelian_map_of_isElemAbelian C.subtype hAhel, ?_,
    ((u * c₀ : C) : G), ?_, Subgroup.le_normalizer_map C.subtype ⟨_, hucN, rfl⟩, m, lam, hm,
    hlam, hscalG, horbG⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hd.mem_of_mk_mem_cz hz a (hUX₀ (hAhU ha))
  · intro x hx
    exact ⟨⟨x, hXC hx.1⟩, hZAh (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · exact M.mul_mem (hd.mem_of_mk_mem_cz hz u (hUX₀ huU)) (Subgroup.mem_subgroupOf.mp hc₀M).2

end CFSG.AGLEmbedding
