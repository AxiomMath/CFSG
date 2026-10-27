module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedNotConstrained
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_surjective_czQuot (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    ∃ (A : Subgroup (D1CzQuot p z)) (f : A →* K), Function.Surjective f := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  obtain ⟨-, hzp, hzH, hzC⟩ := hz
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set W : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ (K.comap π).map H.subtype
  have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ K := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W →* K := (π.comp (Subgroup.inclusion hWH)).codRestrict K hφ₀
  have hzH' : orderOf (⟨z, hzH⟩ : H) = p := (Subgroup.orderOf_coe _).symm.trans hzp
  have hφ : Function.Surjective φ := by
    intro k
    obtain ⟨g, hg, hgk⟩ := exists_mem_centralizer_mk_eq hp _ hO
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzC k k.2))
    have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have hgK : g ∈ K.comap π := by
      rw [Subgroup.mem_comap, hgk]
      exact k.2
    exact ⟨⟨g, hgC, g, hgK, rfl⟩, Subtype.ext hgk⟩
  have : IsSimpleGroup K := hd.isSimpleGroup.1
  obtain ⟨T₁, -, -, -, -, hT₁nc, -⟩ := hd.exists_sylow
  obtain ⟨x, hx⟩ : ∃ x : (T₁ : Subgroup K), x ≠ 1 :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp fun h => hT₁nc (h ▸ inferInstance)
  obtain ⟨k, hk⟩ := T₁.isPGroup' x
  have hOC := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hN : ∀ n ∈ (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p).comap
      (Subgroup.inclusion hWC), p.Coprime (orderOf n) := by
    intro n hn
    have h1 : orderOf (Subgroup.inclusion hWC n) ∣ Nat.card
        (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) :=
      Subgroup.orderOf_dvd_natCard _ hn
    rw [orderOf_injective _ (Subgroup.inclusion_injective hWC)] at h1
    exact hOC.coprime_dvd_right h1
  have hker := le_ker_of_isSimpleGroup φ hφ _ hN (x := (x : K)) (fun h1 => hx (Subtype.ext h1))
    (k := k) (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
  set ρ : W →* D1CzQuot p z := (QuotientGroup.mk' _).comp (Subgroup.inclusion hWC) with hρ
  obtain ⟨f, -, hf, -⟩ := exists_surjective_comp_eq ρ.rangeRestrict ρ.rangeRestrict_surjective
    φ hφ (by
      rw [MonoidHom.ker_rangeRestrict]
      intro w hw
      have h1 : ρ w = 1 := hw
      rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hker h1)
  exact ⟨ρ.range, f, hf⟩

theorem D1OneSmallData.exists_reducedNongeneration_three (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) {m : G} (hm : m ∈ M)
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom) :
    ∃ Pbar : Sylow p (D1CzQuot p z),
      (Pbar : Subgroup (D1CzQuot p z)) =
        (T : Subgroup _).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (D1CzQuot p z) Pbar
        (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore p))) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set P' : Sylow p G := m • P with hP'def
  have hP'eq : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
    rw [hP'def, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hP'M : (P' : Subgroup G) ≤ M := by
    rw [hP'eq]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hd.cfg.ext.sylow_le hx)) (M.inv_mem hm)
  have hW' : GLBWeakCore p (P' : Subgroup G) ≤ M := by
    rw [hP'eq]
    exact weakCore_conj_le hp hd.cfg.ext.weakCore_le hm
  have hTP' : (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤ P' := by
    rw [hP'eq]
    exact hTP
  have hCM : ¬ (Subgroup.centralizer ({z} : Set G)) ≤ M := hd.centralizer_not_le hz
  have hRC : R ≤ (Subgroup.centralizer ({z} : Set G)) := hd.le_centralizer_czElt hz
  have hcore : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      (hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRC hd.cfg.ext.le_M)))
  have hT3 : 3 ≤ Open.pRank p ((T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype) :=
    hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp hRT)
  obtain ⟨Pbar, hPbar, hred⟩ :=
    reducedNongeneration_of_not_le hp hp2 P' hP'M hW' hCM T hTP' hT3 hcore
  exact ⟨Pbar, hPbar, hred⟩

theorem D1OneSmallData.exists_component_czQuot (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) {Pbar : Sylow p (D1CzQuot p z)} {X₀ : Subgroup (D1CzQuot p z)}
    (hred : ReducedNongeneration p (D1CzQuot p z) Pbar X₀) :
    ∃ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ ∧ KC.Normal ∧
      (∀ L : Subgroup (D1CzQuot p z), IsComponentOf L ⊤ → L = KC) ∧
      d1CzElt p z ∈ Subgroup.center (D1CzQuot p z) ∧ orderOf (d1CzElt p z) = p := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, f, hf⟩ := hd.exists_surjective_czQuot hz
  obtain ⟨T₁, -, hs, hn, -, hT₁nc, -⟩ := hd.exists_sylow
  have : IsSimpleGroup K := hs
  obtain ⟨KC, hKC⟩ :=
    exists_isComponentOf_of_layer_ne_bot (hred.layer_ne_bot_of_surjective hn T₁ hT₁nc f hf)
  have hzZ : d1CzElt p z ∈ Subgroup.center (D1CzQuot p z) := mk_mem_center_centralizer _ rfl
  have hzp : orderOf (d1CzElt p z) = p := orderOf_mk_of_coprime hp _
    (primeComplementCore_coprime p) (by rw [← Subgroup.orderOf_coe]; exact hz.2.1)
  exact ⟨KC, hKC, hred.normal_of_isComponentOf_of_center hzZ hzp hKC,
    fun L hL => hred.eq_of_isComponentOf_of_center hzZ hzp hL hKC, hzZ, hzp⟩

end Config

end CFSG.AGLEmbedding
