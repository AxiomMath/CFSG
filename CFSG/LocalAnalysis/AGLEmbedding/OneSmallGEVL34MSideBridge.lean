module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideSocle
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSidePerfect
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Esc

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]
variable {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem L34MSide.hasPrimeConstraint_of_l34 (hKZ : KFactMSideAlmostSimpleE27)
    (hKβ1 : KFactCompFixedThreeEltN) (hKZ9 : KFactCompCenterNine)
    (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits) (hExp : KFactSmallSylowExp)
    (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) (hB0 : D1CzB0 3 R z) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR 3 H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) :
    HasPrimeConstraint (G := M) 3 := by
  by_contra hcon
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdec, -, hcard, hfus⟩ :=
    L34MSide.fusion_data hUE hOrb hExp hOut hSh3 hO hd hz hB0 rfl hL hOR
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  set T := d1LiftX 3 H R K with hTdef
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.le_P
  have hPM : (P : Subgroup G) ≤ M := hd.cfg.ext.sylow_le
  have hzR : z ∈ R := hz.1
  have hzM : z ∈ M := hPM (hRP hzR)
  have hz3 : orderOf z = 3 := hz.2.1
  obtain ⟨hzT, hTc⟩ := hd.d1LiftX_facts hz
  have hT9 : Nat.card T = 9 := by rw [hTc, hcard]; norm_num
  have hPR := L34MSide.card_lt_card_sylow hd hz hB0
  obtain ⟨E, hER, hEel, hEcard⟩ := pRank_attained 3 Nat.prime_three R
  rw [hd.pRank_R] at hEcard
  have hR27 : Nat.card R = 27 := by
    obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
      (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
    rw [hcard] at hR
    have h1 := Subgroup.card_le_of_le hER
    rw [hEcard] at h1
    norm_num at hR h1 ⊢
    omega
  have hER' : E = R := Subgroup.eq_of_le_of_card_ge hER (by rw [hEcard, hR27]; norm_num)
  have hRel : IsElemAbelian 3 R := hER' ▸ hEel
  set π := QuotientGroup.mk' (primeComplementCore (G := M) 3) with hπ
  have hP'p : IsPGroup 3 ((P : Subgroup G).subgroupOf M) := P.isPGroup'.comap_subtype
  have hR'P' : R.subgroupOf M ≤ (P : Subgroup G).subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRP (Subgroup.mem_subgroupOf.mp hx))
  have hT'R' : T.subgroupOf M ≤ R.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hTR (Subgroup.mem_subgroupOf.mp hx))
  have hR'p : IsPGroup 3 (R.subgroupOf M) := hP'p.to_le hR'P'
  have hT'p : IsPGroup 3 (T.subgroupOf M) := hR'p.to_le hT'R'
  have hinjP : ∀ a ∈ (P : Subgroup G).subgroupOf M, ∀ b ∈ (P : Subgroup G).subgroupOf M,
      π a = π b → a = b := fun a ha b hb h => L34MSide.mk_eq_of_pGroup hP'p ha hb h
  have hmemT : ∀ x : M, (x : G) ∈ (P : Subgroup G) →
      π x ∈ (T.subgroupOf M).map π → (x : G) ∈ T := by
    intro x hxP hx
    obtain ⟨t, ht, hteq⟩ := hx
    have := hinjP t (hR'P' (hT'R' ht)) x (Subgroup.mem_subgroupOf.mpr hxP) hteq
    rw [← this]; exact Subgroup.mem_subgroupOf.mp ht
  have hcardR' : Nat.card (R.subgroupOf M) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hRP.trans hPM)).toEquiv
  have hcardT' : Nat.card (T.subgroupOf M) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((hTR.trans hRP).trans hPM)).toEquiv
  have hnormR : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ hg : g ∈ M,
      π ⟨g, hg⟩ ∈ Subgroup.normalizer (((R.subgroupOf M).map π : Subgroup _) : Set _) := by
    intro g hgN hg
    refine Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hgN x
  have hNRM : Subgroup.normalizer (R : Set G) ≤ M := hd.cfg.ext.normalizer_le
  have hzt3 : (π ⟨z, hzM⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hz3]; exact pow_orderOf_eq_one z
    rw [this, map_one]
  have hzt1 : π ⟨z, hzM⟩ ≠ 1 := by
    intro h
    have h' : π ⟨z, hzM⟩ = π 1 := by rw [h, map_one]
    have := hinjP _ (Subgroup.mem_subgroupOf.mpr (hRP hzR)) 1 (Subgroup.one_mem _) h'
    have hz1 : z = 1 := congrArg Subtype.val this
    rw [hz1, orderOf_one] at hz3
    omega
  have hcore := primeComplementCore_quotient_eq_bot (G := M) 3
  have hRelt : IsElemAbelian 3 ((R.subgroupOf M).map π) := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
    · obtain ⟨a', ha', hae⟩ := a.2
      obtain ⟨b', hb', hbe⟩ := b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hae, ← hbe, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have h := (isMulCommutative_iff.mp hRel.1) ⟨a', Subgroup.mem_subgroupOf.mp ha'⟩
        ⟨b', Subgroup.mem_subgroupOf.mp hb'⟩
      have h' := congrArg Subtype.val h
      simpa using h'
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext (by
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        exact hRel.2 _ (Subgroup.mem_subgroupOf.mp hx'))
      rw [this, map_one]
  have hR27t : Nat.card ((R.subgroupOf M).map π) = 27 := by
    rw [L34MSide.card_map_mk_of_pGroup hR'p, hcardR', hR27]
  have hTRt : (T.subgroupOf M).map π ≤ (R.subgroupOf M).map π := Subgroup.map_mono hT'R'
  have hT9t : Nat.card ((T.subgroupOf M).map π) = 9 := by
    rw [L34MSide.card_map_mk_of_pGroup hT'p, hcardT', hT9]
  have hzRt : π ⟨z, hzM⟩ ∈ (R.subgroupOf M).map π :=
    ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzR, rfl⟩
  have hzTt : π ⟨z, hzM⟩ ∉ (T.subgroupOf M).map π := fun h =>
    hzT (hmemT ⟨z, hzM⟩ (hRP hzR) h)
  have hRgent : ∀ r ∈ (R.subgroupOf M).map π, ∃ t ∈ (T.subgroupOf M).map π, ∃ i : ℕ,
      r = t * (π ⟨z, hzM⟩) ^ i := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨t, ht, i, hri⟩ := hdec r (Subgroup.mem_subgroupOf.mp hr)
    have htM : t ∈ M := hPM (hRP (hTR ht))
    refine ⟨π ⟨t, htM⟩, ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, i, ?_⟩
    rw [← map_pow, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hri
  have hfusNt : ∀ r ∈ (R.subgroupOf M).map π, r ∉ (T.subgroupOf M).map π →
      ∃ n ∈ Subgroup.normalizer (((R.subgroupOf M).map π : Subgroup _) : Set _),
        n * r * n⁻¹ ∈ Subgroup.zpowers (π ⟨z, hzM⟩) := by
    rintro _ ⟨r, hr, rfl⟩ hrT
    have hrT' : (r : G) ∉ T := fun h => hrT ⟨r, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    obtain ⟨-, n, hn, hmem⟩ := hfus r (Subgroup.mem_subgroupOf.mp hr) hrT'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hn' : n⁻¹ ∈ Subgroup.normalizer (R : Set G) := Subgroup.inv_mem _ hn
    have hnM : n⁻¹ ∈ M := hNRM hn'
    refine ⟨π ⟨n⁻¹, hnM⟩, hnormR _ hn' hnM, Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩⟩
    rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [conj_zpow] at hk
    calc z ^ k = n⁻¹ * (n * z ^ k * n⁻¹) * n := by group
      _ = n⁻¹ * (r : G) * n⁻¹⁻¹ := by rw [hk]; group
  have htrNt : ∀ t ∈ (T.subgroupOf M).map π, t ≠ 1 → ∀ s ∈ (T.subgroupOf M).map π, s ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (((R.subgroupOf M).map π : Subgroup _) : Set _),
        n * π ⟨z, hzM⟩ * n⁻¹ = π ⟨z, hzM⟩ ∧
        (∀ x ∈ (T.subgroupOf M).map π, n * x * n⁻¹ ∈ (T.subgroupOf M).map π) ∧
        n * t * n⁻¹ = s := by
    rintro _ ⟨t, ht, rfl⟩ ht1 _ ⟨s, hs, rfl⟩ hs1
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (by rw [show t = 1 from Subtype.ext h, map_one])
    have hs1' : (s : G) ≠ 1 := fun h => hs1 (by rw [show s = 1 from Subtype.ext h, map_one])
    obtain ⟨n, hn, hnz, hnT, hnt⟩ := hd.exists_conj_eq_of_l34 hOrb hz hdec rfl hA6 hcard
      t (Subgroup.mem_subgroupOf.mp ht) ht1' s (Subgroup.mem_subgroupOf.mp hs) hs1'
    have hnM : n ∈ M := hNRM hn
    refine ⟨π ⟨n, hnM⟩, hnormR n hn hnM, ?_, ?_, ?_⟩
    · rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simpa using hnz
    · rintro _ ⟨x, hx, rfl⟩
      have hxT := hnT x (Subgroup.mem_subgroupOf.mp hx)
      refine ⟨⟨n, hnM⟩ * x * ⟨n, hnM⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      simpa using hxT
    · rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simpa using hnt
  have hRCt : (R.subgroupOf M).map π ≤ Subgroup.centralizer ({π ⟨z, hzM⟩} : Set _) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (isMulCommutative_iff.mp hRelt.1) ⟨r, hr⟩ ⟨_, hzRt⟩ |> congrArg Subtype.val
  have hm : ∀ Q : Subgroup M, Q ≤ Subgroup.centralizer ({(⟨z, hzM⟩ : M)} : Set M) →
      IsPGroup 3 Q → Nat.card Q ≤ Nat.card R := by
    intro Q hQC hQp
    obtain ⟨SZ, hSZ⟩ := hB0
    have hQG : Q.map M.subtype ≤ Subgroup.centralizer ({z} : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)
      exact congrArg Subtype.val this
    have := card_le_card_map_sylow SZ (hQp.map M.subtype) hQG
    rw [hSZ, Subgroup.card_map_of_injective M.subtype_injective] at this
    exact this
  have hRsylt : ∀ Q : Subgroup (M ⧸ primeComplementCore (G := M) 3),
      Q ≤ Subgroup.centralizer ({π ⟨z, hzM⟩} : Set _) → IsPGroup 3 Q →
      Nat.card Q ≤ Nat.card ((R.subgroupOf M).map π) := by
    intro Q hQC hQp
    rw [hR27t, ← hR27]
    exact L34MSide.card_le_of_pGroup_le_centralizer_mk
      (L34MSide.isPGroup_zpowers_of_orderOf hzM hz3) hm hQC hQp
  have hperft : ∀ D : Subgroup (M ⧸ primeComplementCore (G := M) 3),
      D ≤ Subgroup.centralizer ({π ⟨z, hzM⟩} : Set _) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D := by
    intro D hDC hDp h3
    exact L34MSide.perfect_mtilde hUE hSch hΓ3 hExp hOut hd hz hB0 hL hOR hCz D hDp hDC h3
  set SP : Sylow 3 M := P.subtype hPM with hSP
  have hSPc : (SP : Subgroup M) = (P : Subgroup G).subgroupOf M := Sylow.coe_subtype P hPM
  have hcenter0 : ∀ x ∈ (P : Subgroup G), (∀ y ∈ (P : Subgroup G), x * y = y * x) → x ∈ T :=
    fun x hxP hxc => L34MSide.mem_d1LiftX_of_mem_center hd hz hB0 hfus hPR hxP hxc
  have hT3c : ∀ t ∈ (T.subgroupOf M).map π, t ≠ 1 → ∃ S : Sylow 3 (M ⧸ primeComplementCore
      (G := M) 3), (S : Subgroup _) ≤ Subgroup.centralizer ({t} : Set _) := by
    rintro _ ⟨t, ht, rfl⟩ ht1
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (by rw [show t = 1 from Subtype.ext h, map_one])
    obtain ⟨x₀, hx₀P, hx₀1, hx₀c⟩ := L34MSide.exists_center_ne_one hd hz hB0
    have hx₀T := hcenter0 x₀ hx₀P hx₀c
    obtain ⟨γ, hγN, -, -, hγt⟩ := hd.exists_conj_eq_of_l34 hOrb hz hdec rfl hA6 hcard
      x₀ hx₀T hx₀1 t (Subgroup.mem_subgroupOf.mp ht) ht1'
    have hγM : γ ∈ M := hNRM hγN
    refine ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective _) ((⟨γ, hγM⟩ : M) • SP), ?_⟩
    rw [Sylow.coe_mapSurjective, Sylow.coe_subgroup_smul, hSPc]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hyP : (y : G) ∈ (P : Subgroup G) := Subgroup.mem_subgroupOf.mp hy
    have e := hx₀c y hyP
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hγt]
    calc γ * (y : G) * γ⁻¹ * (γ * x₀ * γ⁻¹) = γ * ((y : G) * x₀) * γ⁻¹ := by group
      _ = γ * (x₀ * (y : G)) * γ⁻¹ := by rw [e]
      _ = γ * x₀ * γ⁻¹ * (γ * (y : G) * γ⁻¹) := by group
  have h81 : 81 ∣ Nat.card (M ⧸ primeComplementCore (G := M) 3) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hk4 : 4 ≤ k := by
      by_contra hk4
      push Not at hk4
      have : Nat.card (P : Subgroup G) ≤ 27 := by
        rw [hk]
        calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 27 := by norm_num
      omega
    have hPt : Nat.card (((P : Subgroup G).subgroupOf M).map π) = 3 ^ k := by
      rw [L34MSide.card_map_mk_of_pGroup hP'p, ← hk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
    have h1 : 81 ∣ 3 ^ k := by
      have : (81 : ℕ) = 3 ^ 4 := by norm_num
      rw [this]
      exact pow_dvd_pow 3 hk4
    exact h1.trans (hPt ▸ Subgroup.card_subgroup_dvd_card _)
  have hcenterP : ∃ S : Sylow 3 (M ⧸ primeComplementCore (G := M) 3),
      ∀ x ∈ (S : Subgroup _), (∀ y ∈ (S : Subgroup _), x * y = y * x) →
        x ∈ (T.subgroupOf M).map π := by
    refine ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective _) SP, ?_⟩
    rw [Sylow.coe_mapSurjective, hSPc]
    rintro _ ⟨y, hy, rfl⟩ hyc
    have hyP : (y : G) ∈ (P : Subgroup G) := Subgroup.mem_subgroupOf.mp hy
    have hyc' : ∀ y' ∈ (P : Subgroup G), (y : G) * y' = y' * y := by
      intro y' hy'
      have hy'M : y' ∈ M := hPM hy'
      have hmem : (⟨y', hy'M⟩ : M) ∈ (P : Subgroup G).subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr hy'
      have h1 := hyc (π ⟨y', hy'M⟩) ⟨⟨y', hy'M⟩, hmem, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      have h2 := hinjP _ (Subgroup.mul_mem _ hy hmem) _ (Subgroup.mul_mem _ hmem hy) h1
      exact congrArg Subtype.val h2
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (hcenter0 _ hyP hyc'), rfl⟩
  have hMne : M ≠ ⊤ := fun h => hd.cfg.ext.not_le (h ▸ le_top)
  have hzcomp : ∀ L : Subgroup (M ⧸ primeComplementCore (G := M) 3), IsComponentOf L ⊤ →
      π ⟨z, hzM⟩ ∈ Subgroup.normalizer (L : Set _) ∧
        π ⟨z, hzM⟩ ∉ Subgroup.centralizer (L : Set _) := fun L hLc =>
    L34MSide.mtilde_component hUE hSch hΓ3 hExp hOut hd hz hB0 hL hOR hCz hLc
  have hX : CatalogSimpleSections (M ⧸ primeComplementCore (G := M) 3) :=
    (catalogSimpleSections_of_isKProper hd.cfg.glob.kProper M hMne).quotient _
  have hcat : ∀ L : Subgroup (M ⧸ primeComplementCore (G := M) 3), IsComponentOf L ⊤ →
      IsCatalogGroup (L ⧸ Subgroup.center L) := fun L hLc =>
    hX.isCatalogGroup_center_quotient hLc
  obtain ⟨L₁, hL₁, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component
    hd.cfg.glob.kProper M hMne 3 Nat.prime_three hcon
  exact L34MSide.false_of_mtilde' hKZ hKβ1 hKZ9 hcore hzt3 hzt1 hRelt hR27t hTRt hT9t hzRt
    hzTt hRgent hfusNt htrNt hRCt hRsylt hperft hT3c h81 hcenterP hzcomp hcat ⟨L₁, hL₁⟩

end CFSG.AGLEmbedding
