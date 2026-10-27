module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Abs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_conj_eq_of_l34 (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) (hp3 : p = 3)
    (hA6 : ¬ IsAltTwoP 3 K)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) :
    ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∀ s ∈ d1LiftX p H R K, s ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
        (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧ n * t * n⁻¹ = s := by
  intro t ht ht1 s hs hs1
  set T := d1LiftX p H R K with hT
  set Orb : Set G := {s | s ∈ T ∧ s ≠ 1 ∧ ∃ n ∈ Subgroup.normalizer (R : Set G),
    n * z * n⁻¹ = z ∧ (∀ x ∈ T, n * x * n⁻¹ ∈ T) ∧ n * t * n⁻¹ = s} with hOrbDef
  have hinv : D1InvSubset p H R K z Orb := by
    refine ⟨fun s hs => ⟨hs.1, hs.2.1⟩, fun m hm hmz hmT s hs => ?_⟩
    obtain ⟨hsT, hs1, n, hn, hnz, hnT, hnt⟩ := hs
    refine ⟨hmT s hsT, fun h1 => hs1 ?_, m * n, Subgroup.mul_mem _ hm hn, ?_, ?_, ?_⟩
    · calc s = m⁻¹ * (m * s * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    · calc m * n * z * (m * n)⁻¹ = m * (n * z * n⁻¹) * m⁻¹ := by group
        _ = z := by rw [hnz, hmz]
    · intro x hx
      have := hmT _ (hnT x hx)
      have e : m * n * x * (m * n)⁻¹ = m * (n * x * n⁻¹) * m⁻¹ := by group
      rw [e]
      exact this
    · rw [← hnt]; group
  have htOrb : t ∈ Orb := ⟨ht, ht1, 1, Subgroup.one_mem _, by group, fun x hx => by simpa using hx,
    by group⟩
  have hT1 : ((T : Set G) \ {1}).ncard = p ^ 2 - 1 := by
    obtain ⟨-, hTc⟩ := hd.d1LiftX_facts hz
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hTc.trans hcard)
  have hsize : Orb.ncard = p ^ 2 - 1 := by
    rcases hd.orbit_sizes hOrb hz hdec (fun h => by omega) hcard with h | ⟨-, h5, -⟩ | ⟨hA, -⟩
    · rcases h Orb hinv with h0 | h8
      · exact absurd ((Set.ncard_eq_zero (Set.toFinite _)).mp h0 ▸ htOrb) (Set.notMem_empty t)
      · exact h8
    · omega
    · exact absurd (hp3 ▸ hA) hA6
  have heq := Set.eq_of_subset_of_ncard_le hinv.1 (by rw [hsize, hT1])
  have hsO : s ∈ Orb := heq ▸ ⟨hs, hs1⟩
  obtain ⟨-, -, n, hn, hnz, hnT, hnt⟩ := hsO
  exact ⟨n, hn, hnz, hnT, hnt⟩

open CFSG.ComponentClassification in
theorem D1OneSmallData.exists_l34_escape_component (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hH₁M : ¬ H₁ ≤ M) (hRH₁ : R ≤ H₁)
    (htr : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∀ s ∈ d1LiftX p H R K, s ≠ 1 →
      ∃ n ∈ H₁ ⊓ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
        (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧ n * t * n⁻¹ = s) :
    ∃ (Rbar₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p))
      (K₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)),
      D1ComponentConfig p P M H₁ R Rbar₁ ∧ IsComponentOf K₁ ⊤ ∧
      ¬ IsCyclic ((Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ K₁ :
        Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ∧
      Nat.card (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) = 27 ∧
      Subgroup.normalizer (((Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ K₁ :
        Subgroup _) : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤
        ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      (Subgroup.centralizer ({⟨z, hRH₁ hz.1⟩} : Set H₁) ⊓
        K₁.comap (QuotientGroup.mk' (primeComplementCore (G := H₁) p))).map
          (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = K₁ := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hcardR, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).1 hL
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨hzT, hTc⟩ := hd.d1LiftX_facts hz
  set T := d1LiftX 3 H R K with hTdef
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hTc9 : Nat.card T = 9 := by rw [hTc, hcard]; norm_num
  have hzR : z ∈ R := hz.1
  have hzo : orderOf z = 3 := hz.2.1
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzt : ∀ x ∈ R, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hx)
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    have hTc' : Nat.card T = 3 ^ 2 := by rw [hTc9]; norm_num
    have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hTc').is_comm.comm
    intro a ha b hb
    exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    obtain ⟨t, ht, i, rfl⟩ := hdec a ha
    obtain ⟨s, hs', j, rfl⟩ := hdec b hb
    have c1 : Commute t s := hTab t ht s hs'
    have c2 : Commute t (z ^ j) := Commute.pow_right (hzt t (hTR ht)) j
    have c3 : Commute (z ^ i) s := Commute.pow_left (hzt s (hTR hs')).symm i
    have c4 : Commute (z ^ i) (z ^ j) := Commute.pow_pow_self z i j
    exact (Commute.mul_left (c1.mul_right c2) (c3.mul_right c4)).eq
  have hTz : T ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxz⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hzT ((Subgroup.zpowers_le.mpr hxT)
      (mem_zpowers_of_mem_zpowers_of_prime hp hzo hxz hx1))
  have hRc : Nat.card R = 27 := by
    refine le_antisymm (by rw [hcard] at hcardR; norm_num at hcardR; exact hcardR) ?_
    have h := mul_card_le_of_inf_eq_bot hTR (Subgroup.zpowers_le.mpr hzR) hTz
    rw [hTc9, Nat.card_zpowers, hzo] at h
    norm_num at h ⊢
    exact h
  have hext₁ : D1Extremal 3 P M H₁ R := hd.cfg.ext.of_le hH₁ hRH₁ hH₁M
  by_cases hcon : HasPrimeConstraint (G := H₁) 3
  · exact (d1ConstrainedCase_of_kFactsW hβ hα G hd.cfg.glob 3 P M hd.cfg.loc H₁ R hext₁ hcon).elim
  obtain ⟨Rbar₁, hcfg₁⟩ := hext₁.exists_componentConfig hd.cfg.glob hd.cfg.loc hcon hd.cfg.ind
  by_cases hallc : ∀ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3), IsComponentOf L ⊤ →
      IsCyclic ((Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) ⊓ L :
        Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3))
  · exact (h2 G 3 P M H₁ R Rbar₁ hcfg₁ hallc).elim
  push Not at hallc
  obtain ⟨K₁, hK₁, hnc⟩ := hallc
  rcases hcfg₁.red.rankOne_or_center hK₁ hnc with
    ⟨z₁, hz₁R, hz₁K, hz₁o, hz₁c, -, -, hN₁, hZ⟩ | hcent
  swap
  · exact (h3 _ 3 P M H₁ R Rbar₁ hcfg₁ K₁ hK₁
      (fun L hL => hcfg₁.red.eq_of_forall_mem_center hK₁ hL hcent) hnc hcent).elim
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) 3) with hπ₁
  have hO₁ := primeComplementCore_coprime (G := H₁) 3
  have hzH₁ : z ∈ H₁ := hRH₁ hzR
  set ζ : (H₁ ⧸ primeComplementCore (G := H₁) 3) := π₁ ⟨z, hzH₁⟩ with hζ
  set Tb : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3) := (T.subgroupOf H₁).map π₁ with hTb
  have hRb : (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) = (R.subgroupOf H₁).map π₁ :=
    hcfg₁.rbar
  have hmemR : ∀ r ∈ R, ∀ hr : r ∈ H₁,
      π₁ ⟨r, hr⟩ ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) := fun r hr hrH =>
    hRb ▸ ⟨⟨r, hrH⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hmemT : ∀ t ∈ T, ∀ ht : t ∈ H₁, π₁ ⟨t, ht⟩ ∈ Tb := fun t ht htH =>
    ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hRbel : ∀ x ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)),
      ∃ r ∈ R, ∃ hr : r ∈ H₁, x = π₁ ⟨r, hr⟩ := by
    intro x hx
    rw [hRb] at hx
    obtain ⟨⟨r, hrH⟩, hr, rfl⟩ := hx
    exact ⟨r, Subgroup.mem_subgroupOf.mp hr, hrH, rfl⟩
  have hTbel : ∀ x ∈ Tb, ∃ t ∈ T, ∃ ht : t ∈ H₁, x = π₁ ⟨t, ht⟩ := by
    intro x hx
    obtain ⟨⟨t, htH⟩, ht, rfl⟩ := hx
    exact ⟨t, Subgroup.mem_subgroupOf.mp ht, htH, rfl⟩
  have hconjπ : ∀ a b : H₁, π₁ a * π₁ b * (π₁ a)⁻¹ = π₁ (a * b * a⁻¹) := fun a b => by
    rw [map_mul, map_mul, map_inv]
  have hab : ∀ a ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)),
      ∀ b ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)), a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, haH, rfl⟩ := hRbel a ha
    obtain ⟨b₀, hb₀, hbH, rfl⟩ := hRbel b hb
    rw [← map_mul, ← map_mul]
    exact congrArg π₁ (Subtype.ext (hRab a₀ ha₀ b₀ hb₀))
  have hexp : ∀ r ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)), r ^ 3 = 1 := by
    intro r hr
    obtain ⟨r₀, hr₀, hrH, rfl⟩ := hRbel r hr
    rw [← map_pow]
    have h1 : (⟨r₀, hrH⟩ : H₁) ^ 3 = 1 := Subtype.ext (by simpa using hexpR r₀ hr₀)
    rw [h1, map_one]
  have hRp : IsPGroup 3 (R.subgroupOf H₁) := hd.cfg.ext.isPGroup.comap_subtype
  have hRc' : Nat.card (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) = 27 := by
    rw [hRb, card_map_mk_of_isPGroup hp _ hO₁ hRp, ← hRc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH₁).toEquiv
  have hTp : IsPGroup 3 (T.subgroupOf H₁) := (hd.cfg.ext.isPGroup.to_le hTR).comap_subtype
  have hTc' : Nat.card Tb = 9 := by
    rw [hTb, card_map_mk_of_isPGroup hp _ hO₁ hTp, ← hTc9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hTR.trans hRH₁)).toEquiv
  have hTR' : Tb ≤ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) := by
    rw [hRb]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hTR (Subgroup.mem_subgroupOf.mp hx))
  have hζR : ζ ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) := hmemR z hzR hzH₁
  have hdec' : ∀ r ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)),
      ∃ t ∈ Tb, ∃ i : ℕ, r = t * ζ ^ i := by
    intro r hr
    obtain ⟨r₀, hr₀, hrH, rfl⟩ := hRbel r hr
    obtain ⟨t, ht, i, hti⟩ := hdec r₀ hr₀
    refine ⟨π₁ ⟨t, hTR.trans hRH₁ ht⟩, hmemT t ht _, i, ?_⟩
    rw [hζ, ← map_pow, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hti)
  have htr' : ∀ t ∈ Tb, t ≠ 1 → ∀ s ∈ Tb, s ≠ 1 → ∃ ν : (H₁ ⧸ primeComplementCore (G := H₁) 3),
      ν * ζ * ν⁻¹ = ζ ∧ (∀ x ∈ Tb, ν * x * ν⁻¹ ∈ Tb) ∧
      (∀ r ∈ (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)), ν * r * ν⁻¹ ∈ Rbar₁) ∧
        ν * t * ν⁻¹ = s := by
    intro t ht ht1 s hs hs1
    obtain ⟨t₀, ht₀, ht₀H, rfl⟩ := hTbel t ht
    obtain ⟨s₀, hs₀, hs₀H, rfl⟩ := hTbel s hs
    have ht₀1 : t₀ ≠ 1 := fun h => ht1 (by
      have : (⟨t₀, ht₀H⟩ : H₁) = 1 := Subtype.ext h
      rw [this, map_one])
    have hs₀1 : s₀ ≠ 1 := fun h => hs1 (by
      have : (⟨s₀, hs₀H⟩ : H₁) = 1 := Subtype.ext h
      rw [this, map_one])
    obtain ⟨n, ⟨hnH₁, hnN⟩, hnz, hnT, hnt⟩ := htr t₀ ht₀ ht₀1 s₀ hs₀ hs₀1
    refine ⟨π₁ ⟨n, hnH₁⟩, ?_, ?_, ?_, ?_⟩
    · rw [hζ, hconjπ]
      congr 1
      exact Subtype.ext (by simpa using hnz)
    · intro x hx
      obtain ⟨x₀, hx₀, hxH, rfl⟩ := hTbel x hx
      rw [hconjπ]
      have hm : n * x₀ * n⁻¹ ∈ T := hnT x₀ hx₀
      have e : (⟨n, hnH₁⟩ : H₁) * ⟨x₀, hxH⟩ * (⟨n, hnH₁⟩ : H₁)⁻¹ =
          ⟨n * x₀ * n⁻¹, (hTR.trans hRH₁) hm⟩ := Subtype.ext (by simp)
      rw [e]
      exact hmemT _ hm _
    · intro r hr
      obtain ⟨r₀, hr₀, hrH, rfl⟩ := hRbel r hr
      rw [hconjπ]
      have hm : n * r₀ * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hnN r₀).mp hr₀
      have e : (⟨n, hnH₁⟩ : H₁) * ⟨r₀, hrH⟩ * (⟨n, hnH₁⟩ : H₁)⁻¹ =
          ⟨n * r₀ * n⁻¹, hRH₁ hm⟩ := Subtype.ext (by simp)
      rw [e]
      exact hmemR _ hm _
    · rw [hconjπ]
      congr 1
      exact Subtype.ext (by simpa using hnt)
  have hcomp : ∀ ν : (H₁ ⧸ primeComplementCore (G := H₁) 3),
      K₁.map (MulAut.conj ν).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj ν).toMonoidHom ≤
        Subgroup.centralizer (K₁ : Set (H₁ ⧸ primeComplementCore (G := H₁) 3)) := by
    intro ν
    have hK' : IsComponentOf (K₁.map (MulAut.conj ν).toMonoidHom) ⊤ :=
      (LocalComponents.equiv_iff (MulAut.conj ν) K₁).mpr hK₁
    by_cases he : K₁.map (MulAut.conj ν).toMonoidHom = K₁
    · exact Or.inl he
    · exact Or.inr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne _ _ hK' hK₁ he))
  have hKC := inf_centralizer_eq_bot_of_center hZ
  have hz₁ζ := mem_zpowers_of_isCompL34 hab hexp hRc' hTc' hTR' hζR hdec' htr' hcomp hKC hnc
    hz₁R hz₁K hz₁c
  have hζo : orderOf ζ = 3 := orderOf_mk_of_coprime hp _ hO₁
    (by rw [← Subgroup.orderOf_coe]; exact hzo)
  have hz₁1 : z₁ ≠ 1 := fun h => hz₁K (h ▸ K₁.one_mem)
  have hζz₁ : ζ ∈ Subgroup.zpowers z₁ := mem_zpowers_of_mem_zpowers_of_prime hp hζo hz₁ζ hz₁1
  have hζC : ζ ∈ Subgroup.centralizer (K₁ : Set (H₁ ⧸ primeComplementCore (G := H₁) 3)) :=
    (Subgroup.zpowers_le.mpr hz₁c) hζz₁
  set zH : H₁ := ⟨z, hzH₁⟩ with hzHdef
  set Y₁ : Subgroup H₁ := Subgroup.centralizer ({zH} : Set H₁) ⊓ K₁.comap π₁ with hY₁def
  have hzHp : IsPGroup 3 (Subgroup.zpowers zH) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hzo
  have hY₁ : Y₁.map π₁ = K₁ := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro k hk
      have hkC : k ∈ Subgroup.centralizer
          ({π₁ zH} : Set (H₁ ⧸ primeComplementCore (G := H₁) 3)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hζC k hk
      obtain ⟨g, hg, hgk⟩ := exists_mem_centralizer_mk_eq hp _ hO₁ hzHp hkC
      exact ⟨g, ⟨hg, show π₁ g ∈ K₁ from hgk ▸ hk⟩, hgk⟩
  exact ⟨Rbar₁, K₁, hcfg₁, hK₁, hnc, hRc', hN₁, hY₁⟩

open CFSG.ComponentClassification in
theorem D1OneSmallData.false_of_l34_escape_nine (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hH₁M : ¬ H₁ ≤ M) (hRH₁ : R ≤ H₁)
    (hNH₁ : ∀ n ∈ Subgroup.normalizer (R : Set G), n ∈ Subgroup.centralizer ({z} : Set G) →
      n ∈ H₁)
    (hperf9 : ∀ U : Subgroup G, U ≤ H₁ ⊓ Subgroup.centralizer ({z} : Set G) → ⁅U, U⁆ = U →
      ¬ 9 ∣ Nat.card U) : False := by
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).1 hL
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  have htrG := hd.exists_conj_eq_of_l34 hOrb hz hdec rfl hA6 hcard
  obtain ⟨Rbar₁, K₁, -, hK₁, hnc, hRc', -, hY₁⟩ := hd.exists_l34_escape_component hβ hα h2 h3
    hOut hExp hSh3 hO hz hB0 rfl hL hOR hH₁ hH₁M hRH₁ fun t ht ht1 s hs hs1 => by
      obtain ⟨n, hnN, hnz, hnT, hnt⟩ := htrG t ht ht1 s hs hs1
      have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc n * z = n * z * n⁻¹ * n := by group
          _ = z * n := by rw [hnz]
      exact ⟨n, ⟨hNH₁ n hnN hnC, hnN⟩, hnz, hnT, hnt⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) 3) with hπ₁
  set zH : H₁ := ⟨z, hRH₁ hz.1⟩ with hzHdef
  set Y₁ : Subgroup H₁ := Subgroup.centralizer ({zH} : Set H₁) ⊓ K₁.comap π₁ with hY₁def
  set U₀ := CFSG.Quasithin.perfectCore Y₁ with hU₀def
  have hK₁p : ⁅K₁, K₁⁆ = K₁ := Subgroup.isPerfect_iff.mp (⟨hK₁.2.2.1⟩ : Group.IsPerfect K₁)
  have hU₀map : U₀.map π₁ = K₁ := by
    rw [hU₀def, CFSG.Quasithin.map_perfectCore, hY₁]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hK₁p
  have h9K : 9 ∣ Nat.card K₁ := by
    have h1 := card_eq_nine_or_of_not_isCyclic
      (inf_le_left : (Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) ⊓ K₁ ≤ Rbar₁)
      hRc' hnc
    have h2 : 9 ∣ Nat.card ((Rbar₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) ⊓ K₁ :
        Subgroup (H₁ ⧸ primeComplementCore (G := H₁) 3)) := by
      rcases h1 with h | h
      · rw [h]
      · rw [h]; norm_num
    exact h2.trans (Subgroup.card_dvd_of_le inf_le_right)
  have h9U : 9 ∣ Nat.card U₀ := h9K.trans (hU₀map ▸ Subgroup.card_map_dvd U₀ π₁)
  set U := U₀.map H₁.subtype with hUdef
  have hUle : U ≤ H₁ ⊓ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    have huY : u ∈ Y₁ := CFSG.Quasithin.perfectCore_le Y₁ hu
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp huY.1
    show (u : G) ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hc'
  have hUp : ⁅U, U⁆ = U := by
    rw [hUdef, ← Subgroup.map_commutator, CFSG.Quasithin.perfectCore_perfect]
  have hUc : Nat.card U = Nat.card U₀ := Subgroup.card_map_of_injective H₁.subtype_injective
  exact hperf9 U hUle hUp (hUc ▸ h9U)

open CFSG.ComponentClassification in
theorem D1OneSmallData.false_of_l34_escape (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hH₁M : ¬ H₁ ≤ M) (hHM : H ⊓ M ≤ H₁)
    (hperf : ∀ U : Subgroup G, U ≤ H₁ ⊓ Subgroup.centralizer ({z} : Set G) → ⁅U, U⁆ = U →
      Nat.Coprime 3 (Nat.card U)) : False := by
  have hRH₁ : R ≤ H₁ := (le_inf hd.cfg.ext.le_H hd.cfg.ext.le_M).trans hHM
  refine hd.false_of_l34_escape_nine hβ hα h2 h3 hOut hExp hOrb hSh3 hO hz hB0 hp3 hL hOR hH₁
    hH₁M hRH₁ (fun n hnN hnC => hHM ⟨hCz hnC, hd.cfg.ext.normalizer_le hnN⟩)
    fun U hU hUp h9 => ?_
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hperf U hU hUp)
    ((by norm_num : 3 ∣ 9).trans h9)

end CFSG.AGLEmbedding
