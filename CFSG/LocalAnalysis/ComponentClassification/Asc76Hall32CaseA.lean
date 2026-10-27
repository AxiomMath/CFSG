module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Basic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X CFSG.LocalCores
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

section Abstract

variable {E : Type} [Group E]

theorem eq_of_card_two {Q : Subgroup E} (hQ2 : Nat.card Q = 2) {x y : E} (hx : x ∈ Q)
    (hy : y ∈ Q) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  by_contra hxy
  have hsub : ({1, x, y} : Set E) ⊆ Q := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact one_mem Q
    · exact hx
    · exact hy
  have h1 : (1 : E) ∉ ({x, y} : Set E) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hy1.symm⟩
  have h3 : ({1, x, y} : Set E).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_pair hxy]
  have h7 : (Q : Set E).ncard = 2 := hQ2
  have h6 := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero (by rw [h7]; norm_num))
  omega

theorem le_center_of_card_two {Q : Subgroup E} [hQ : Q.Normal] (hQ2 : Nat.card Q = 2) :
    Q ≤ center E := by
  intro q hq
  rw [mem_center_iff]
  intro g
  by_cases hq1 : q = 1
  · rw [hq1, one_mul, mul_one]
  · have h1 : g * q * g⁻¹ ∈ Q := hQ.conj_mem q hq g
    have h2 : g * q * g⁻¹ ≠ 1 := fun h => hq1 (conj_eq_one_iff.mp h)
    have h3 := eq_of_card_two hQ2 h1 hq h2 hq1
    calc g * q = g * q * g⁻¹ * g := by group
      _ = q * g := by rw [h3]

theorem openPCore_normal (p : ℕ) : (CFSG.Open.pCore p E).Normal :=
  ⟨fun x hx g => by
    rw [← openPCore_map_eq p (MulAut.conj g)]
    exact ⟨x, hx, rfl⟩⟩

theorem card_center_eq_card_sylowCenter (P : Subgroup E) :
    Nat.card (center P) = Nat.card (sylowCenter P) := by
  have e : (center P).map P.subtype = sylowCenter P := by
    ext x
    rw [mem_sylowCenter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun t ht => congrArg Subtype.val (mem_center_iff.mp hy ⟨t, ht⟩)⟩
    · rintro ⟨hxP, hxC⟩
      exact ⟨⟨x, hxP⟩, mem_center_iff.mpr fun h => Subtype.ext (hxC h h.2), rfl⟩
  rw [← e, card_map_of_injective P.subtype_injective]

variable [Finite E]

theorem eq_bot_of_normal_odd_quotient {Q : Subgroup E} [Q.Normal] (hQc : Q ≤ center E)
    (hQ2 : Nat.card Q = 2) (hO : ∀ N : Subgroup E, N.Normal → Odd (Nat.card N) → N = ⊥)
    (N : Subgroup (E ⧸ Q)) (hN : N.Normal) (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.comap (QuotientGroup.mk' Q) with hN'def
  have hN'n : N'.Normal := hN.comap _
  have hQN' : Q ≤ N' := fun q hq => by
    have h1 : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    show QuotientGroup.mk' Q q ∈ N
    rw [h1]
    exact one_mem N
  have hcard : Nat.card N * 2 = Nat.card N' := by
    have h := card_map_mul_card_inf_ker (QuotientGroup.mk' Q) N'
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q), QuotientGroup.ker_mk',
      inf_eq_left.mpr hQN', hQ2] at h
  have hQcard : Nat.card (Q.subgroupOf N') = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQN').toEquiv, hQ2]
  have hP₀ : Nat.card (Q.subgroupOf N') = 2 ^ (Nat.card N').factorization 2 := by
    rw [hQcard, ← hcard, Nat.factorization_mul hNodd.pos.ne' two_ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hNodd.not_two_dvd_nat, zero_add,
      Nat.Prime.factorization_self Nat.prime_two, pow_one]
  set PS := Sylow.ofCard (Q.subgroupOf N') hP₀ with hPS
  have hPS' : (PS : Subgroup N') = Q.subgroupOf N' := Sylow.coe_ofCard _ _
  have hPScard : Nat.card (PS : Subgroup N') = 2 := by rw [hPS', hQcard]
  have hP : normalizer (PS : Set N') ≤ centralizer (PS : Set N') := fun x _ => by
    rw [mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ (PS : Subgroup N') := hh
    rw [hPS'] at hh'
    exact Subtype.ext (mem_center_iff.mp (hQc hh') x).symm
  have hKodd : ¬ 2 ∣ Nat.card (MonoidHom.transferSylow PS hP).ker :=
    MonoidHom.not_dvd_card_ker_transferSylow PS hP
  have hKodd' : Odd (Nat.card (MonoidHom.transferSylow PS hP).ker) := Nat.odd_iff.mpr (by omega)
  have hK'n : ((MonoidHom.transferSylow PS hP).ker.map N'.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, hk, rfl⟩ := hx
    have hgk : g * (k : E) * g⁻¹ ∈ N' := hN'n.conj_mem k k.2 g
    refine ⟨⟨_, hgk⟩, ?_, rfl⟩
    have hkn : (k : E) ^ Nat.card (MonoidHom.transferSylow PS hP).ker = 1 := by
      have h1 := pow_card_eq_one' (G := (MonoidHom.transferSylow PS hP).ker) (x := ⟨k, hk⟩)
      have h2 := congrArg (fun y : (MonoidHom.transferSylow PS hP).ker => ((y : N') : E)) h1
      simpa using h2
    have hyn : (⟨g * k * g⁻¹, hgk⟩ : N') ^ Nat.card (MonoidHom.transferSylow PS hP).ker = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [conj_pow, hkn, mul_one, mul_inv_cancel]
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine (pow_eq_one_iff_of_coprime (Nat.coprime_two_right.mpr hKodd')).mp ⟨?_, ?_⟩
    · rw [← map_pow, hyn, map_one]
    · have h1 := pow_card_eq_one' (x := MonoidHom.transferSylow PS hP ⟨g * k * g⁻¹, hgk⟩)
      rwa [hPScard] at h1
  have hKbot := hO _ hK'n (by rw [card_map_of_injective N'.subtype_injective]; exact hKodd')
  rw [map_eq_bot_iff_of_injective _ N'.subtype_injective] at hKbot
  have h1 := (MonoidHom.ker_transferSylow_isComplement' PS hP).card_mul_card
  rw [hKbot, card_bot, one_mul, hPScard, ← hcard] at h1
  exact eq_bot_of_card_eq N (by omega)

theorem false_of_card_pCore_eq_two {Sb Tb : Subgroup E} (hSb : IsSylowOf 2 Sb ⊤)
    (hTS : Tb ≤ Sb) (hT4 : Nat.card Tb = 4) (hTsq : ∀ x ∈ Tb, x ^ 2 = 1)
    (hSN : Sb ≤ normalizer (Tb : Set E))
    (hsc : ∀ x ∈ Tb, ∀ g : E, g⁻¹ * x * g ∈ Sb → g⁻¹ * x * g ∈ Tb)
    (hO : ∀ N : Subgroup E, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hQT : CFSG.Open.pCore 2 E ≤ Tb) (hQ2 : Nat.card (CFSG.Open.pCore 2 E) = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCore 2 E with hQdef
  have hQn : Q.Normal := openPCore_normal 2
  have hQc : Q ≤ center E := le_center_of_card_two hQ2
  set ψ := QuotientGroup.mk' Q with hψdef
  have hψker : ∀ x, ψ x = 1 ↔ x ∈ Q := fun x => QuotientGroup.eq_one_iff x
  obtain ⟨t, htT, htQ⟩ : ∃ t ∈ Tb, t ∉ Q := by
    by_contra h
    push Not at h
    have h1 := card_le_of_le (show Tb ≤ Q from h)
    omega
  have hcardTψ : Nat.card (Tb.map ψ) = 2 := by
    have h := card_map_mul_card_inf_ker ψ Tb
    rw [show ψ.ker = Q from QuotientGroup.ker_mk' Q, inf_eq_left.mpr hQT, hQ2, hT4] at h
    omega
  have hsame : ∀ x ∈ Tb, x ∉ Q → ψ x = ψ t := fun x hx hxQ =>
    eq_of_card_two hcardTψ ⟨x, hx, rfl⟩ ⟨t, htT, rfl⟩ (fun h => hxQ ((hψker x).mp h))
      (fun h => htQ ((hψker t).mp h))
  have hconj : ∀ x g : E, x ∉ Q → g⁻¹ * x * g ∉ Q := fun x g hx h => hx (by
    have h1 := hQn.conj_mem _ h g
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1)
  obtain ⟨SbS, hSbS⟩ := exists_sylow_eq_of_isSylowOf_top hSb
  set St := SbS.mapSurjective (QuotientGroup.mk'_surjective Q) with hStdef
  have hSt : (St : Subgroup (E ⧸ Q)) = Sb.map ψ := by
    rw [hStdef, Sylow.coe_mapSurjective, hSbS]
  have htSt : ψ t ∈ (St : Subgroup (E ⧸ Q)) := by
    rw [hSt]
    exact ⟨t, hTS htT, rfl⟩
  have hord : orderOf (⟨ψ t, htSt⟩ : (St : Subgroup (E ⧸ Q))) = 2 := by
    rw [← Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ (fun h => htQ ((hψker t).mp h))
    rw [← map_pow, hTsq t htT, map_one]
  have hcent : (⟨ψ t, htSt⟩ : (St : Subgroup (E ⧸ Q))) ∈ center (St : Subgroup (E ⧸ Q)) := by
    rw [mem_center_iff]
    rintro ⟨y, hy⟩
    rw [hSt] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    apply Subtype.ext
    change ψ s * ψ t = ψ t * ψ s
    have h1 : s * t * s⁻¹ ∈ Tb := (mem_normalizer_iff.mp (hSN hs) t).mp htT
    have h2 : s * t * s⁻¹ ∉ Q := by
      have h3 := hconj t s⁻¹ htQ
      rwa [inv_inv] at h3
    have h3 := hsame _ h1 h2
    rw [map_mul, map_mul, map_inv] at h3
    calc ψ s * ψ t = ψ s * ψ t * (ψ s)⁻¹ * ψ s := by group
      _ = ψ t * ψ s := by rw [h3]
  have hiso : ∀ g : E ⧸ Q, g⁻¹ * ψ t * g ∈ (St : Subgroup (E ⧸ Q)) → g⁻¹ * ψ t * g = ψ t := by
    intro g hg
    obtain ⟨x, rfl⟩ : ∃ x, ψ x = g := QuotientGroup.mk'_surjective Q g
    have e : (ψ x)⁻¹ * ψ t * ψ x = ψ (x⁻¹ * t * x) := by rw [map_mul, map_mul, map_inv]
    rw [e] at hg ⊢
    rw [hSt] at hg
    obtain ⟨s, hs, hsx⟩ := hg
    have h1 : x⁻¹ * t * x ∈ Sb := by
      have hq : s⁻¹ * (x⁻¹ * t * x) ∈ Q := by
        rw [← hψker, map_mul, map_inv, hsx, inv_mul_cancel]
      have h2 := mul_mem hs (hTS (hQT hq))
      rwa [mul_inv_cancel_left] at h2
    exact hsame _ (hsc t htT x h1) (hconj t x htQ)
  obtain ⟨hZ1, -⟩ := CFSG.Adapters.glauberman_zStar St ⟨ψ t, htSt⟩ hcent hord hiso
  have hOt : CFSG.oddCore (E ⧸ Q) = ⊥ :=
    eq_bot_iff.mpr (sSup_le fun N hN => (eq_bot_of_normal_odd_quotient hQc hQ2 hO N hN.1 hN.2).le)
  have htc : ∀ g : E ⧸ Q, g * ψ t = ψ t * g := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hZ1 g
    rw [hOt, mem_bot] at hk
    rw [hk, mul_one]
    exact (mem_centralizer_iff.mp hc (ψ t) (Set.mem_singleton _)).symm
  have hTbn : Tb.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h1 : ψ (g * x * g⁻¹) = ψ x := by
      by_cases hxQ : x ∈ Q
      · rw [map_mul, map_mul, map_inv, (hψker x).mpr hxQ, mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv, hsame x hx hxQ, htc, mul_inv_cancel_right]
    have h2 : (g * x * g⁻¹) * x⁻¹ ∈ Q := by
      rw [← hψker, map_mul, h1, map_inv, mul_inv_cancel]
    have h3 := mul_mem (hQT h2) hx
    rwa [inv_mul_cancel_right] at h3
  have h1 := card_le_of_le (le_openPCore hTbn (hSb.isPGroup.to_le hTS))
  rw [← hQdef] at h1
  omega

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_bar {M T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (h : IsSylowOf 2 (bar M T) ⊤) : IsSylowOf 2 T M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff_card] at h ⊢
  refine ⟨hTM, ?_⟩
  rw [← card_bar_of_pGroup hTM hT, h.2, ← bar_self M, factorization_card_bar le_rfl]

theorem caseA (hgold : GoldschmidtTheoremA) {S T : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hTS : T ≤ S) (hT4 : Nat.card T = 4) (hTel : IsElemAbelian 2 T)
    (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T)
    (hsc : ∀ t ∈ T, ∀ g : G, g⁻¹ * t * g ∈ S → g⁻¹ * t * g ∈ T) :
    IsSylowOf 2 T (normalClosure (T : Set G)) ∨
      Nonempty (↥(normalClosure (T : Set G)) ⧸
        CFSG.Assembly.oddCore ↥(normalClosure (T : Set G)) ≃* PSU3 2 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq_of_isSylowOf_top hS
  have hTP₀ : T ≤ (P₀ : Subgroup G) := by rw [hP₀]; exact hTS
  obtain ⟨hGa, hGb, hGc⟩ := hgold G P₀ T hTP₀ hTel.1 (by rw [hP₀]; exact hsc)
  set M := normalClosure (T : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hTM : T ≤ M := subset_normalClosure
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  have hTb4 : Nat.card (bar M T) = 4 := by rw [card_bar_of_pGroup hTM hT2, hT4]
  have hTbel : IsElemAbelian 2 (bar M T) := isElemAbelian_of_mulEquiv (barEquiv hTM hT2) hTel
  have hSb : IsSylowOf 2 (bar M S) ⊤ := isSylowOf_bar hMn hS
  have hTSb : bar M T ≤ bar M S := bar_mono hTS
  have hcl : normalClosure ((bar M T : Subgroup (BarGroup M)) : Set (BarGroup M)) = ⊤ :=
    normalClosure_bar_eq_top (normalClosure_subgroupOf_eq_top hS hTS hwc)
  have hOE : ∀ N : Subgroup (BarGroup M), N.Normal → Odd (Nat.card N) → N = ⊥ :=
    eq_bot_of_normal_of_odd_bar M
  have hGb' : bar M T = CFSG.Open.pCore 2 (BarGroup M) ⊔
      closure {t | t ∈ bar M S ⊓ CFSG.Open.goldschmidtLayer (BarGroup M) ∧ t ^ 2 = 1} := by
    rw [← hP₀]
    exact hGb
  set Q := CFSG.Open.pCore 2 (BarGroup M) with hQdef
  have hQT : Q ≤ bar M T := by
    rw [hGb']
    exact le_sup_left
  have hQn : Q.Normal := openPCore_normal 2
  have hQdvd : Nat.card Q ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hTb4]
    exact card_dvd_of_le hQT
  obtain ⟨k, hk2, hQk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hQdvd
  interval_cases k
  ·
    have hQbot : Q = ⊥ := eq_bot_of_card_eq Q (by rw [hQk]; rfl)
    have hlayer : CFSG.Open.goldschmidtLayer (BarGroup M) = CFSG.layer (BarGroup M) :=
      CFSG.Adapters.goldschmidtLayer_eq_foundations _
    have hLE : CFSG.layer (BarGroup M) = ⊤ := by
      have hGa' : Q ⊔ CFSG.Open.goldschmidtLayer (BarGroup M) = ⊤ := hGa
      rw [hQbot, bot_sup_eq, hlayer] at hGa'
      exact hGa'
    have hO2E : ∀ N : Subgroup (BarGroup M), N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hN2 =>
      le_bot_iff.mp ((le_openPCore hN hN2).trans hQbot.le)
    have hZE := center_eq_bot_of hOE hO2E
    have hCE : ∀ L : Subgroup (BarGroup M), IsComponent L →
        CFSG.Open.goldschmidtSimpleType (↥L ⧸ center ↥L) := fun L hL =>
      hGc L ((CFSG.isComponent_iff_open L).mp hL)
    have hTbΩ : bar M T = omega1 (bar M S) := by
      rw [hGb', hQbot, bot_sup_eq, hlayer, hLE, inf_top_eq]
      rfl
    have hab : IsMulCommutative (omega1 (bar M S)) := by
      rw [← hTbΩ]
      exact hTbel.1
    have hΩ4 : Nat.card (omega1 (bar M S)) = 4 := by rw [← hTbΩ, hTb4]
    obtain ⟨K, hK⟩ : ∃ K : Subgroup (BarGroup M), IsComponent K := by
      by_contra h
      push Not at h
      have h1 : CFSG.layer (BarGroup M) = ⊥ := by
        simp only [CFSG.layer.eq_sSup]
        rw [sSup_eq_bot]
        intro K hK
        exact absurd hK (h K)
      rw [hLE] at h1
      have h2 : bar M T = ⊥ := le_bot_iff.mp (h1 ▸ le_top)
      rw [h2, card_bot] at hTb4
      norm_num at hTb4
    have hcard4 := (card_inf_ge_and_exists_conj hLE hZE hCE hSb hab hK).1
    have hΩK : omega1 (bar M S) ≤ K := by
      have h1 : omega1 (bar M S) ⊓ K = omega1 (bar M S) :=
        eq_of_le_of_card_ge inf_le_left (by rw [hΩ4]; exact hcard4)
      rw [← h1]
      exact inf_le_right
    have hKn : K.Normal := component_normal_of_layer_eq_top hLE hK
    have hKtop : K = ⊤ := by
      rw [eq_top_iff, ← hcl]
      exact normalClosure_le_normal (by rw [hTbΩ]; exact hΩK)
    subst hKtop
    have hsimple : IsSimpleGroup (BarGroup M) :=
      (MulEquiv.isSimpleGroup_congr Subgroup.topEquiv).mp (isSimpleGroup_component hLE hZE hK)
    have hgst : CFSG.Open.goldschmidtSimpleType (BarGroup M) := by
      have hZK := center_component_eq_bot hLE hZE hK
      exact goldschmidtSimpleType_of_mulEquiv (Subgroup.topEquiv.symm.trans
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)))
        (hCE ⊤ hK)
    obtain ⟨SbS, hSbS⟩ := exists_sylow_eq_of_isSylowOf_top hSb
    have hΩab : IsMulCommutative (CFSG.Goldschmidt.Omega1 (SbS : Subgroup (BarGroup M))) := by
      rw [hSbS]
      exact hab
    obtain ⟨hN11a1, hN11a2⟩ := CFSG.Goldschmidt.N11a (BarGroup M) hgst SbS hΩab
    by_cases hSab : IsMulCommutative (SbS : Subgroup (BarGroup M))
    ·
      left
      have h1 := hN11a1 hSab
      rw [hSbS] at h1
      have h2 : omega1 (bar M S) = bar M S :=
        le_antisymm (omega1_le _) fun x hx => mem_omega1_of_sq hx (h1 x hx)
      exact isSylowOf_of_bar hTM hT2 (by rw [hTbΩ, h2]; exact hSb)
    ·
      have hZcard : ∀ q k : ℕ, fusionBenderBorel (BarGroup M) q k → q = 4 := by
        intro q k hB
        have h1 := (hB SbS).2.2.2.1
        rw [card_center_eq_card_sylowCenter,
          ← (CFSG.Goldschmidt.N11c (BarGroup M) (hN11a2 hSab) SbS).1, hSbS] at h1
        rw [← h1]
        exact hΩ4
      rcases hN11a2 hSab with ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
      · exfalso
        have h1 := hZcard _ _ (fusionBenderBorel_of_mulEquiv_sz hn e)
        have h2 : 2 * n + 1 = 2 :=
          Nat.pow_right_injective le_rfl (h1.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
        omega
      · right
        have h1 := hZcard _ _ (fusionBenderBorel_of_mulEquiv_psu3 hf e)
        have h2 : f = 2 :=
          Nat.pow_right_injective le_rfl (h1.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
        subst h2
        exact ⟨e⟩
  ·
    exact (false_of_card_pCore_eq_two hSb hTSb hTb4 hTbel.2
      (le_normalizer_of_weaklyClosed hTSb (bar_weaklyClosed hS2 hMn hTM hT2 hwc))
      (bar_stronglyClosed hS2 hTS hsc) hOE hQT (by rw [hQk]; norm_num)).elim
  ·
    have hQeq : Q = bar M T := eq_of_le_of_card_ge hQT (by rw [hTb4, hQk]; norm_num)
    have hTbtop : bar M T = ⊤ := by
      have : (bar M T).Normal := hQeq ▸ hQn
      rw [eq_top_iff, ← hcl]
      exact normalClosure_le_normal subset_rfl
    left
    refine isSylowOf_of_bar hTM hT2 ?_
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same]
    rw [isSylowOf_iff_card]
    refine ⟨le_top, ?_⟩
    rw [← hTbtop, hTb4, h4]
    norm_num

end CFSG.ComponentClassification.Asc76X.Hall32
