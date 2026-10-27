module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5S136ab5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd pRank_subgroupOf_eq)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem inner_all_of_case2_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF3 : FactLieZCentPGL3) (hF6 : FactL3SylowCenterCyclic) (hEven : Ch1.EvenLieAutInner)
    (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))
    (hr : 1 < CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hSQ : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K))
    {X Q : Subgroup G} {y : G} (hyLv : y ∈ S.Lv) (hconf : Conf1366 K X Q S.a S.z y)
    (h2 : A318Case2 (starImage 3 (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G)))))
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    ∀ y' ∈ S.Lv, Odd (orderOf y') → ∀ hy'N : y' ∈ Subgroup.normalizer (K : Set G),
      ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K, ConfAB.indHom K (MulEquiv.refl _) ⟨y', hy'N⟩ = MulAut.conj k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have hGvS : SQTKGroup ↥Gv :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian S.pCoreOf_Gv_ne_bot'
  have hSQ' := SQTKHyp.of_sqtkGroup ↥Gv hGvS
  have hLc := subgroupOf_mem_cComp hKc

  set K' : Subgroup ↥Gv := K.subgroupOf Gv with hK'
  let e₁ : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKG
  have hmap : (CFSG.pCore 2 ↥K').map (e₁ : ↥K' →* ↥K) = CFSG.pCore 2 ↥K := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e₁
    rw [← CFSG.pCore_eq_open, ← CFSG.pCore_eq_open] at this
    exact this
  let e₀ : (↥K' ⧸ CFSG.pCore 2 ↥K') ≃* (↥K ⧸ CFSG.pCore 2 ↥K) := QuotientGroup.congr _ _ e₁ hmap
  have hQ' : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hZ' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥ := by
    have h1 := Subgroup.map_center_eq e₀
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).mp h1
  have h3' : 3 ∣ Nat.card (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    rw [Nat.card_congr e₀.toEquiv]
    exact h3
  have hr1 : 1 < CFSG.Open.pRank 3 K' := by
    rw [pRank_subgroupOf_eq hKG Nat.prime_three (by norm_num)]
    exact hr
  have hK'n : K'.Normal :=
    A318.normal_of_pRank_gt_one hGvS ((a38ForSQTK_of_cat h38) _ hSQ') hLc Nat.prime_three
      (by norm_num) hr1

  obtain ⟨θ, hθ⟩ := ConfAB.exists_starEquiv hK'n hQ' hZ' h3'
  let π₃ : ↥Gv →* PStar 3 ↥Gv := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Gv)
  let Ks : Subgroup (PStar 3 ↥Gv) := starImage 3 K'
  let Θ : ↥Ks ≃* (↥K ⧸ CFSG.pCore 2 ↥K) := θ.trans e₀
  have hmemKs : ∀ (k : G) (hk : k ∈ K), π₃ ⟨k, hKG hk⟩ ∈ Ks := fun k hk =>
    Subgroup.mem_map_of_mem _ (show (⟨k, hKG hk⟩ : ↥Gv) ∈ K' from hk)
  have hΘ : ∀ (k : G) (hk : k ∈ K), Θ ⟨π₃ ⟨k, hKG hk⟩, hmemKs k hk⟩ =
      ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro k hk
    exact (congrArg e₀ (hθ ⟨⟨k, hKG hk⟩, hk⟩)).trans rfl

  have hKsn : Ks.Normal := hK'n.map π₃ (QuotientGroup.mk'_surjective _)
  have hΘc : ∀ (g : G) (hg : g ∈ Gv) (hgN : g ∈ Subgroup.normalizer (K : Set G)) (κ : ↥Ks),
      Θ ⟨π₃ ⟨g, hg⟩ * κ * (π₃ ⟨g, hg⟩)⁻¹, hKsn.conj_mem _ κ.2 _⟩ =
        ConfAB.indHom K (MulEquiv.refl _) ⟨g, hgN⟩ (Θ κ) := by
    intro g hg hgN κ
    obtain ⟨⟨k, hkGv⟩, hk, hκ⟩ := κ.2
    have hk' : k ∈ K := hk
    have hκ' : κ = ⟨π₃ ⟨k, hKG hk'⟩, hmemKs k hk'⟩ := Subtype.ext hκ.symm
    have hgk : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgN k).mp hk'
    have e2 : π₃ ⟨g, hg⟩ * κ * (π₃ ⟨g, hg⟩)⁻¹ = π₃ ⟨g * k * g⁻¹, hKG hgk⟩ := by
      rw [hκ']
      show π₃ ⟨g, hg⟩ * π₃ ⟨k, hKG hk'⟩ * (π₃ ⟨g, hg⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e3 : (⟨π₃ ⟨g, hg⟩ * κ * (π₃ ⟨g, hg⟩)⁻¹, hKsn.conj_mem _ κ.2 _⟩ : ↥Ks) =
        ⟨π₃ ⟨g * k * g⁻¹, hKG hgk⟩, hmemKs _ hgk⟩ := Subtype.ext e2
    rw [e3, hΘ _ hgk, hκ', hΘ _ hk']
    exact (ConfAB.indHom_apply K (MulEquiv.refl (↥K ⧸ CFSG.pCore 2 ↥K)) ⟨g, hgN⟩ ⟨k, hk'⟩).symm

  have hinn : ∀ β : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K), (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 (↥K ⧸ CFSG.pCore 2 ↥K), ∀ t ∈ (P : Subgroup _), β t = t) →
        Ch1.IsInnerAut β := fun β hβ hP => hEven _ hSQ β hβ hP
  obtain ⟨P, u, w, haN, hzN, hu, hw, hu1, hw1, huw, hγa, hγz⟩ :=
    ConfAB.exists_conj_of_conf hqs (MulEquiv.refl _) hinn hconf
  have hnc : ¬ IsCyclic (Subgroup.center ↥(P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) := by
    intro hc
    have h1mem : (1 : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ KG68.omegaZ (P : Subgroup _) :=
      KG68.mem_omegaZ_of_commute P (fun t _ => by rw [one_mul, mul_one]) (one_mul 1)
    exact ConfSpor.false_of_three_le (KG68.card_omegaZ_le_two (P : Subgroup _) hc) h1mem hu hw
      (Ne.symm hu1) (Ne.symm hw1) huw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hyodd, hya, hyz⟩ := hconf

  obtain ⟨s, q, hmod, ⟨p, e, hp, he, hqe, hPSL⟩, hX⟩ := h2
  have hpe : p = 2 ∧ 2 ≤ e := by
    by_contra hcon
    have hor : p ≠ 2 ∨ e = 1 := by
      by_cases hp2 : p = 2
      · right
        have : ¬ 2 ≤ e := fun h => hcon ⟨hp2, h⟩
        omega
      · exact Or.inl hp2
    have hcyc := hF6 s p e hp he hor ↥Ks hPSL
    apply hnc
    have hc := hcyc (P.mapSurjective (f := Θ.symm.toMonoidHom) Θ.symm.surjective)
    let E : ↥(P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
        ↥((P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)).map Θ.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ Θ.symm.injective
    have hc' : IsCyclic (Subgroup.center ↥((P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)).map
        Θ.symm.toMonoidHom)) := hc
    exact isCyclic_of_surjective (Subgroup.centerCongr E).symm.toMonoidHom
      (Subgroup.centerCongr E).symm.surjective
  obtain ⟨rfl, he2⟩ := hpe
  subst hqe

  set Xb := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 ↥Gv)) with hXb
  have hXbn : Xb.Normal := ConfAB.oPrimeResidualOf_three_top_normal
  have hgen := ConfAB.oPrimeResidualOf_three_top_eq_top hq hZ h3
  have hKsX : Ks ≤ Xb := by
    intro κ hκ
    set Y : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := (Xb.comap Ks.subtype).map Θ.toMonoidHom with hY
    have hle : oPrimeResidualOf 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ Y := by
      rw [oPrimeResidualOf, Subgroup.closure_le]
      rintro x ⟨-, k, hk⟩
      refine ⟨Θ.symm x, ?_, by simp⟩
      show ((Θ.symm x : ↥Ks) : PStar 3 ↥Gv) ∈ Xb
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, k, ?_⟩
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hk]
    rw [hgen] at hle
    obtain ⟨κ', hκ', he⟩ := hle (Subgroup.mem_top (Θ ⟨κ, hκ⟩))
    have h1 : (κ' : PStar 3 ↥Gv) = κ := congrArg Subtype.val (Θ.injective he)
    rw [← h1]
    exact hκ'

  have hGvN : Gv ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hK'n
  have hyGv : y ∈ Gv := (oTwoRes_le _ hyLv).2
  have hy3 : y ^ 3 = 1 := S.pow_three_eq_one_of_mem_Lv hyLv hyodd
  have hvC : ∀ k : ℤ, S.v12 ^ k ∈ Subgroup.centralizer (K : Set G) := by
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hKG hx)) k).eq
  set yb := π₃ ⟨y, hyGv⟩ with hyb
  have hyb3 : yb ^ 3 = 1 := by
    have h1 : (⟨y, hyGv⟩ : ↥Gv) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [hyb, ← map_pow, h1, map_one]
  have hybX : yb ∈ Xb := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hyb3) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩

  have hβu : ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ u = u := by
    refine ConfAB.apply_eq_of_commute_conj hZ ?_
    rw [← hγa]
    exact ConfAB.indHom_commute_of_mem_centralizer _ hyN haN hya

  have hfix : ∀ (g : G) (hg : g ∈ Gv) (x : ↥K ⧸ CFSG.pCore 2 ↥K),
      ConfAB.indHom K (MulEquiv.refl _) ⟨g, hGvN hg⟩ x = x →
        π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv) = (Θ.symm x : PStar 3 ↥Gv) * π₃ ⟨g, hg⟩ := by
    intro g hg x hx
    have h1 := hΘc g hg (hGvN hg) (Θ.symm x)
    rw [MulEquiv.apply_symm_apply, hx] at h1
    have h1' := congrArg Θ.symm h1
    rw [MulEquiv.symm_apply_apply] at h1'
    have h2 : π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv) * (π₃ ⟨g, hg⟩)⁻¹ =
        (Θ.symm x : PStar 3 ↥Gv) := congrArg Subtype.val h1'
    calc π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv)
        = (π₃ ⟨g, hg⟩ * (Θ.symm x : PStar 3 ↥Gv) * (π₃ ⟨g, hg⟩)⁻¹) * π₃ ⟨g, hg⟩ := by group
      _ = (Θ.symm x : PStar 3 ↥Gv) * π₃ ⟨g, hg⟩ := by rw [h2]
  rcases hX with hPGL | ⟨m, -, hcirc⟩
  ·
    exfalso
    have hTv : IsSylowTwoOf S.Tv Gv :=
      S.isSylowTwoOf_centralizer_F4 h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
    set Tb : Subgroup (PStar 3 ↥Gv) := (S.Tv.subgroupOf Gv).map π₃ with hTb
    have hTbS : IsSylowTwoOf Tb ⊤ := by
      refine ⟨le_top, (hTv.2.1.comap_subtype).map _, fun h2 => hTv.2.2 ?_⟩
      have h1 : (Tb.subgroupOf ⊤).index = Tb.index := Subgroup.relIndex_top_right Tb
      have h4 : Tb.index ∣ (S.Tv.subgroupOf Gv).index :=
        Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
      rw [h1] at h2
      exact dvd_trans h2 h4
    have hXbN : (⊤ : Subgroup (PStar 3 ↥Gv)) ≤ Subgroup.normalizer (Xb : Set (PStar 3 ↥Gv)) :=
      fun g _ => Subgroup.mem_normalizer_iff.mpr fun x =>
        ⟨fun hx => hXbn.conj_mem x hx g, fun hx => by
          simpa [mul_assoc] using hXbn.conj_mem _ hx g⁻¹⟩
    obtain ⟨Pb, hPb⟩ := KGL33.exists_sylow_le le_top hXbN hTbS

    have hPbT : ∀ t ∈ (Pb : Subgroup ↥Xb), ∃ (t₀ : G) (ht₀ : t₀ ∈ Gv), t₀ ∈ S.Tv ∧
        (t : PStar 3 ↥Gv) = π₃ ⟨t₀, ht₀⟩ := by
      intro t ht
      obtain ⟨⟨t₀, ht₀⟩, ht₀T, he⟩ := hPb t ht
      exact ⟨t₀, ht₀, ht₀T, he.symm⟩
    set ub : ↥Xb := ⟨(Θ.symm u : PStar 3 ↥Gv), hKsX (Θ.symm u).2⟩ with hub
    set wb : ↥Xb := ⟨(Θ.symm w : PStar 3 ↥Gv), hKsX (Θ.symm w).2⟩ with hwb
    set kb : ↥Xb := ⟨yb, hybX⟩ with hkb

    have hubC : ∀ t ∈ (Pb : Subgroup ↥Xb), ub * t = t * ub := by
      intro t ht
      obtain ⟨t₀, ht₀, ht₀T, he⟩ := hPbT t ht
      have hc : ConfAB.indHom K (MulEquiv.refl _) ⟨t₀, hGvN ht₀⟩ u = u := by
        refine ConfAB.apply_eq_of_commute_conj hZ ?_
        rw [← hγa]
        have hC : S.a * t₀ * S.a⁻¹ * t₀⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv ht₀T)
          rw [← hk]
          exact hvC k
        exact (ConfAB.indHom_commute_of_mem_centralizer _ haN (hGvN ht₀) hC).symm
      have h1 := hfix t₀ ht₀ u hc
      apply Subtype.ext
      show (Θ.symm u : PStar 3 ↥Gv) * t = t * (Θ.symm u : PStar 3 ↥Gv)
      rw [he]
      exact h1.symm
    have hwbC : ∀ t ∈ (Pb : Subgroup ↥Xb), wb * t = t * wb := by
      intro t ht
      obtain ⟨t₀, ht₀, ht₀T, he⟩ := hPbT t ht
      have hc : ConfAB.indHom K (MulEquiv.refl _) ⟨t₀, hGvN ht₀⟩ w = w := by
        refine ConfAB.apply_eq_of_commute_conj hZ ?_
        rw [← hγz]
        have hC : S.z * t₀ * S.z⁻¹ * t₀⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
          have h1 := S.conj_z_of_mem_T ht₀T.1
          have h2 : S.z * t₀ * S.z⁻¹ * t₀⁻¹ = 1 := by
            calc S.z * t₀ * S.z⁻¹ * t₀⁻¹ = S.z * (t₀ * S.z * t₀⁻¹)⁻¹ := by group
              _ = 1 := by rw [h1]; group
          rw [h2]
          exact Subgroup.one_mem _
        exact (ConfAB.indHom_commute_of_mem_centralizer _ hzN (hGvN ht₀) hC).symm
      have h1 := hfix t₀ ht₀ w hc
      apply Subtype.ext
      show (Θ.symm w : PStar 3 ↥Gv) * t = t * (Θ.symm w : PStar 3 ↥Gv)
      rw [he]
      exact h1.symm
    have hsq : ∀ x : ↥K ⧸ CFSG.pCore 2 ↥K, x * x = 1 →
        (⟨(Θ.symm x : PStar 3 ↥Gv), hKsX (Θ.symm x).2⟩ : ↥Xb) *
          ⟨(Θ.symm x : PStar 3 ↥Gv), hKsX (Θ.symm x).2⟩ = 1 := by
      intro x hx
      apply Subtype.ext
      show ((Θ.symm x * Θ.symm x : ↥Ks) : PStar 3 ↥Gv) = 1
      rw [← map_mul, hx, map_one]
      rfl
    have hubP := ConfAB.mem_sylow_of_commute Pb (hsq u hu.2.2) hubC
    have hwbP := ConfAB.mem_sylow_of_commute Pb (hsq w hw.2.2) hwbC
    have hub1 : ub ≠ 1 := by
      intro h
      apply hu1
      have h1 : (Θ.symm u : PStar 3 ↥Gv) = 1 := congrArg Subtype.val h
      have h2 : Θ.symm u = 1 := Subtype.ext h1
      simpa using congrArg Θ h2
    have hkb3 : kb ^ 3 = 1 := Subtype.ext (by simpa [hkb] using hyb3)
    have hkbodd : Odd (orderOf kb) :=
      Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hkb3)
    have hkbub : kb * ub = ub * kb := Subtype.ext (hfix y hyGv u hβu)
    have hkw := hF3 s e he2 ↥Xb hPGL Pb ub wb kb hubP hubC hub1 hwbP hwbC hkbodd hkbub

    have h1 : yb * (Θ.symm w : PStar 3 ↥Gv) * yb⁻¹ = (Θ.symm w : PStar 3 ↥Gv) := by
      have := congrArg Subtype.val hkw
      simp only [hkb, hwb, Subgroup.coe_mul] at this
      rw [this]
      group
    have h2 := hΘc y hyGv hyN (Θ.symm w)
    have h3 : (⟨yb * (Θ.symm w : PStar 3 ↥Gv) * yb⁻¹, hKsn.conj_mem _ (Θ.symm w).2 _⟩ : ↥Ks) =
        Θ.symm w := Subtype.ext h1
    rw [h3, MulEquiv.apply_symm_apply] at h2
    have hβw : ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ w = w := h2.symm
    apply hyz
    refine ConfAB.comm_mem_centralizer_of_indHom_commute hqs (MulEquiv.refl _) hyN hzN ?_
    rw [hγz]
    exact ConfAB.commute_conj_of_apply_eq hβw
  ·
    obtain ⟨e', L₀, hL₀n, hq', hPSL₀, hcard3, -, h3L₀⟩ := hcirc
    have hee : e = e' := Nat.pow_right_injective (le_refl 2) hq'
    subst hee

    set KsX : Subgroup ↥Xb := Ks.subgroupOf Xb with hKsXdef
    let eK : ↥KsX ≃* ↥Ks := Subgroup.subgroupOfEquivOfLe hKsX
    have hcomm : ∀ x y : ↥Xb ⧸ L₀, x * y = y * x := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic (↥Xb ⧸ L₀) := isCyclic_of_prime_card (p := 3) hcard3
      exact fun x y => (IsCyclic.isMulCommutative (α := ↥Xb ⧸ L₀)).is_comm.comm x y
    let f : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥Xb ⧸ L₀ :=
      (QuotientGroup.mk' L₀).comp (KsX.subtype.comp (eK.symm.toMonoidHom.comp Θ.symm.toMonoidHom))
    have hfker : f.ker = ⊤ := by
      have hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := Group.isPerfect_def.mp hq.1
      rw [eq_top_iff, ← hperf, commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have hKsL : KsX ≤ L₀ := by
      intro κ hκ
      have h1 : f (Θ (eK ⟨κ, hκ⟩)) = 1 := by
        rw [← MonoidHom.mem_ker, hfker]
        exact Subgroup.mem_top _
      have h2 : f (Θ (eK ⟨κ, hκ⟩)) = QuotientGroup.mk' L₀ κ := by
        show QuotientGroup.mk' L₀ ((eK.symm (Θ.symm (Θ (eK ⟨κ, hκ⟩))) : ↥KsX) : ↥Xb) = _
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hcardKs : Nat.card ↥L₀ ≤ Nat.card ↥KsX := by
      rw [Nat.card_congr eK.toEquiv, ConfAB.card_eq_of_isPSLEps3 hPSL hPSL₀]
    have heq : KsX = L₀ := Subgroup.eq_of_le_of_card_ge hKsL hcardKs

    intro y' hy' hy'odd hy'N
    have hy'Gv : y' ∈ Gv := (oTwoRes_le _ hy').2
    have hy'3 : y' ^ 3 = 1 := S.pow_three_eq_one_of_mem_Lv hy' hy'odd
    set yb' := π₃ ⟨y', hy'Gv⟩ with hyb'
    have hyb'3 : yb' ^ 3 = 1 := by
      have h1 : (⟨y', hy'Gv⟩ : ↥Gv) ^ 3 = 1 := Subtype.ext (by simpa using hy'3)
      rw [hyb', ← map_pow, h1, map_one]
    have hyb'X : yb' ∈ Xb := by
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hyb'3) with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    by_cases hb1 : yb' = 1
    ·
      have h1 : yb' = 1 := hb1
      rw [hyb', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hd1 : orderOf (⟨y', hy'Gv⟩ : ↥Gv) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy'3))
      have hd2 : orderOf (⟨⟨y', hy'Gv⟩, h1⟩ : ↥(CFSG.pPrimeCore 3 ↥Gv)) ∣
          Nat.card ↥(CFSG.pPrimeCore 3 ↥Gv) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hd2
      have hcop := Nat.Coprime.coprime_dvd_right hd2 (CFSG.pPrimeCore_coprime_card (p := 3))
      have h1' : orderOf (⟨y', hy'Gv⟩ : ↥Gv) = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hd1
      have hy1 : y' = 1 := by
        have := congrArg Subtype.val (orderOf_eq_one_iff.mp h1')
        simpa using this
      subst hy1
      refine ⟨1, ?_⟩
      rw [map_one]
      exact map_one _
    · set kb' : ↥Xb := ⟨yb', hyb'X⟩ with hkb'
      have hkb'3 : orderOf kb' = 3 :=
        orderOf_eq_prime (Subtype.ext (by simpa [hkb'] using hyb'3))
          (fun h => hb1 (congrArg Subtype.val h))
      have hkb'L : kb' ∈ L₀ := h3L₀ kb' hkb'3
      have hyb'Ks : yb' ∈ Ks := by
        have : kb' ∈ KsX := heq ▸ hkb'L
        exact this
      refine ⟨Θ ⟨yb', hyb'Ks⟩, ?_⟩
      ext x
      obtain ⟨κ, rfl⟩ := Θ.surjective x
      rw [← hΘc y' hy'Gv hy'N κ, MulAut.conj_apply]
      have e : (⟨π₃ ⟨y', hy'Gv⟩ * κ * (π₃ ⟨y', hy'Gv⟩)⁻¹, hKsn.conj_mem _ κ.2 _⟩ : ↥Ks) =
          ⟨yb', hyb'Ks⟩ * κ * (⟨yb', hyb'Ks⟩ : ↥Ks)⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_inv]

end Setting

end CFSG.Quasithin.H13.A5
