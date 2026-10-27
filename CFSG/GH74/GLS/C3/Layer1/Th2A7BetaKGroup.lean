module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Glue
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Side
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Tables
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Loc2
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32LocA7
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32M12Out
public import CFSG.GH74.GLS.C3.Layer1.Ivk79Pump
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Layer
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Y

public section

namespace CFSG.GH74.GLS.Th2A7Beta

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc

theorem mem_of_normal_of_center {G : Type} [Group G] [Finite G] {R N : Subgroup G} {e : G}
    (hR : IsPGroup 2 ↥R) (hNR : N ≤ R) (hN : N ≠ ⊥)
    (hnorm : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N)
    (hZ : ∀ r ∈ R, (∀ t ∈ R, r * t = t * r) → r = 1 ∨ r = e) : e ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥R) := ⟨hR⟩
  have hNn : (N.subgroupOf R).Normal := by
    refine ⟨fun n hn r => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm r r.2 n hn
  have hNt : Nontrivial ↥(N.subgroupOf R) := by
    obtain ⟨⟨n, hn⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hN
    refine ⟨⟨⟨⟨n, hNR hn⟩, by simpa [Subgroup.mem_subgroupOf] using hn⟩, 1, ?_⟩⟩
    intro h
    apply hn1
    have := congrArg (fun y : ↥(N.subgroupOf R) => ((y : ↥R) : G)) h
    exact Subtype.ext this
  obtain ⟨y, hy1, hyc⟩ := CFSG.exists_nontrivial_center_mem_normal (N.subgroupOf R) (p := 2)
  have hyR : ((y : ↥R) : G) ∈ R := (y : ↥R).2
  have hcomm : ∀ t ∈ R, ((y : ↥R) : G) * t = t * ((y : ↥R) : G) := by
    intro t ht
    have := (Subgroup.mem_center_iff.1 hyc) ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm
  rcases hZ _ hyR hcomm with h | h
  · exfalso
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · have hyN : ((y : ↥R) : G) ∈ N := Subgroup.mem_subgroupOf.1 y.2
    rw [h] at hyN
    exact hyN

theorem two_dvd_card_of_hasL2Model {X : Type} [Group X] {q : ℕ} (hq : Odd q)
    (h : HasL2Model X (fun r => r = q)) : 2 ∣ Nat.card X := by
  have h2 := Bk.two_mul_card_of_hasL2Model_eq hq h
  obtain ⟨m, rfl⟩ := hq
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [e1] at h2
  have h3 : Nat.card X = 2 * ((2 * m + 1) * (m * (m + 1))) := by
    have : (2 * m + 1) * (4 * (m * (m + 1))) = 2 * (2 * ((2 * m + 1) * (m * (m + 1)))) := by ring
    omega
  exact ⟨_, h3⟩

theorem false_of_transposition_central
    (hGKF : GenericKnownFacts) (hE2 : E2ComponentFacts)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x e : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hx2 : orderOf x = 2) (he2 : orderOf e = 2)
    (heC : e ∈ centralizer ({x} : Set G))
    (hct : (psiEquiv e7 (Back.actHom hKN ⟨e, heC⟩)).cycleType = {2})
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer ({e} : Set G)))
    (hZ : ∀ r ∈ R, (∀ t ∈ R, r * t = t * r) → r = 1 ∨ r = e) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTab : Thm1L32.StableTables := Thm1L32.stableTables_proved hGKF hE2
  have hC2 : C2Facts := Ivk79.c2Facts_of_facts hGKF hE2
  have hLoc2 : Thm1L32.LocL2 := fun Z _ _ F _ _ hF L eL s hs2 hsL hmove P hPL hP hP1 hPs hsub =>
    Thm1L32.l2_fixed_classification hF L eL s hs2 hsL hmove P hPL hP hP1 hPs hsub
  have hLocA7 : Thm1L32.LocA7 := fun Z _ _ L eL s hs2 hsL hmove P hPL hP hP1 hPs hsub =>
    Thm1L32.a7_fixed_classification L eL s hs2 hsL hmove P hPL hP hP1 hPs hsub
  have hO1 : Thm1L32.M12OuterProp :=
    fun Z _ _ L h s hs2 hsL hout P hPL hP hP1 hPs g hgs hgL hgP =>
      Thm1L32.m12_outer_centralizer_inner L h s hs2 hsL hout P hPL hP hP1 hPs g hgs hgL hgP
  have hαα : Back.actHom hKN ⟨e, heC⟩ * Back.actHom hKN ⟨e, heC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨e, heC⟩ * ⟨e, heC⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one e
      rwa [he2, sq] at this
    rw [this, map_one]
  obtain ⟨hA, hB, hC⟩ := Thm1L32.kside_A7 e7 _ hαα hct
  have hlayer : pLayerOf 2 (K ⊓ centralizer ({e} : Set G)) ≠ ⊥ :=
    layer_ne_bot_of_good hKN heC he2 (goodC_A7 e7 _ hct)
  obtain ⟨Λ, hΛ, hΛK, hlay, hΛmod, -, -, himg, hΛW, hΛc⟩ :=
    Thm1L32.layer_A7 hKC hKN heC he2 e7 hB hlayer
  have hKS : Thm1L32.KSide K x e Λ :=
    Thm1L32.kside_of_data hKC hKN heC he2 hΛK himg hΛc hA hB hC
  have hxe : x * e = e * x := (mem_centralizer_singleton_iff.1 heC).symm
  have hΛU : HasL2Model (kBar Λ) Odd := by
    obtain ⟨p, f', hp, hf', hq, hl⟩ := hΛmod
    exact ⟨p, f', hp, hf', hq ▸ (by decide : Odd 5), hl⟩
  let E : Thm1L32.YEnv G x e Λ := ⟨hx2, he2, hxe, hΛ, hΛU⟩
  have hKcen : Subgroup.center (kBar K) = ⊥ := Stage1.Thm6.Glue.center_eq_bot_of_isA7Model ⟨e7⟩
  have hM12 : ∀ L : Subgroup (barQ ↥(centralizer ({e} : Set G))),
      ∀ S : Thm1L32.Stable32 E L, S.sigma ≠ 1 → Shape2M12 ↥L → False :=
    fun L S hσ h2M =>
      S.false_of_2M12 hO1 hG hσ h2M hKC hKcen hΛW hΛK (by decide) hΛmod (fun _ => hKS)
  obtain ⟨hJc, hJn, hJmod⟩ :=
    Thm1L32.ylevel hTab hE2 hC2 hG hLoc2 hLocA7 E hlay (by decide) hΛmod hM12
  set J : Subgroup G := pumpUp 2 K e with hJ
  have hJe : J ≤ centralizer ({e} : Set G) := (isPCompIn_two_iff.1 hJc).1
  have hJcen : Subgroup.center (kBar J) = ⊥ := by
    rcases hJmod with h | h | ⟨-, ⟨eJ⟩⟩
    · exact Thm1L32.center_eq_bot_of_hasL2Model_eq (by decide) h
    · exact Thm1L32.center_eq_bot_of_hasL2Model_eq (by decide) h
    · exact Stage1.Thm6.Glue.center_eq_bot_of_isA7Model ⟨eJ⟩
  have h2J : 2 ∣ Nat.card (kBar J) := by
    rcases hJmod with h | h | ⟨-, ⟨eJ⟩⟩
    · exact two_dvd_card_of_hasL2Model (by decide) h
    · exact two_dvd_card_of_hasL2Model (by decide) h
    · rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
  have h2J' : 2 ∣ Nat.card ↥J :=
    h2J.trans (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥J))
  have hCN : centralizer ({e} : Set G) ≤ normalizer (J : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      exact hJn c hc j hj
    · intro hj
      have := hJn c⁻¹ ((centralizer ({e} : Set G)).inv_mem hc) _ hj
      simpa [mul_assoc] using this
  have hRJ : IsSylowOf 2 (R ⊓ J) J := hR.inf_of_le_normalizer hJe hCN
  have hRJne : R ⊓ J ≠ ⊥ := by
    intro hbot
    have hcard := hRJ.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have h1 : (Nat.card ↥J).factorization 2 = 0 := by
      have := hcard.symm
      exact (Nat.pow_eq_one.1 this).resolve_left (by norm_num)
    have : ¬ 2 ∣ Nat.card ↥J := by
      rw [Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne']
      omega
    exact this h2J'
  have heJ : e ∈ J := by
    have hmem := mem_of_normal_of_center (hR.isPGroup) inf_le_left hRJne
      (fun r hr n hn => ⟨R.mul_mem (R.mul_mem hr hn.1) (R.inv_mem hr), hJn r (hR.le hr) n hn.2⟩) hZ
    exact hmem.2
  have hecen : (QuotientGroup.mk (⟨e, heJ⟩ : ↥J) : kBar J) ∈ Subgroup.center (kBar J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective g
    have hye : y * e = e * y := mem_centralizer_singleton_iff.1 (hJe hy)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hye
  rw [hJcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hecen
  have hodd := pPrimeCore_coprime_card (G := ↥J) (p := 2)
  have hdvd : orderOf (⟨⟨e, heJ⟩, hecen⟩ : ↥(pPrimeCore 2 ↥J)) ∣ Nat.card ↥(pPrimeCore 2 ↥J) :=
    orderOf_dvd_natCard _
  have hord : orderOf (⟨⟨e, heJ⟩, hecen⟩ : ↥(pPrimeCore 2 ↥J)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact he2
  rw [hord] at hdvd
  exact absurd hdvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hodd)

end CFSG.GH74.GLS.Th2A7Beta
