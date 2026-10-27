module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsModel
public import CFSG.LocalAnalysis.ABGTheoremB.IV4

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.OddFieldTorus
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
open scoped Pointwise

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_map_of_characteristic [Finite G] {Y : Subgroup G}
    (A : Subgroup Y) [hA : A.Characteristic] :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((A.map Y.subtype : Subgroup G) : Set G) := by
  intro g hg
  set B : Subgroup G := A.map Y.subtype with hB
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hfix := hA.fixed (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩)
    have hmem : a ∈ Subgroup.comap (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩).toMonoidHom A := by
      rw [hfix]
      exact ha
    refine ⟨_, hmem, ?_⟩
    change (((Subgroup.normalizerMonoidHom Y ⟨g, hg⟩) a : Y) : G) = g * a * g⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm

theorem normalizer_le_normalizer_centralizer (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have key : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ c ∈ Subgroup.centralizer (T : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro t ht
    have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem hg) t).mp ht
    rw [inv_inv] at ht'
    have h := hc _ ht'
    calc t * (g * c * g⁻¹) = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * t := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key g hg c
  · intro h
    have h1 := key g⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem hg) _ h
    simpa [mul_assoc] using h1

theorem automizerIndex_subgroupOf_eq {T H : Subgroup G} (hTH : T ≤ H)
    (hN : Subgroup.normalizer (T : Set G) ≤ H) :
    automizerIndex (T.subgroupOf H) = automizerIndex T := by
  have hC : Subgroup.centralizer ((T.subgroupOf H : Subgroup H) : Set H) =
      (Subgroup.centralizer (T : Set G)).subgroupOf H := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh t ht
      exact congrArg Subtype.val (hh ⟨t, hTH ht⟩ (Subgroup.mem_subgroupOf.mpr ht))
    · intro hh t ht
      exact Subtype.ext (hh t (Subgroup.mem_subgroupOf.mp ht))
  rw [automizerIndex, automizerIndex, hC, ← Subgroup.subgroupOf_normalizer_eq hTH,
    Subgroup.relIndex_subgroupOf hN]

theorem sq_conj_eq_of_card_three [Finite G] {K : Subgroup G} (hK : Nat.card K = 3) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    g ^ 2 * k * (g ^ 2)⁻¹ = k := by
  classical
  by_cases hk1 : k = 1
  · rw [hk1, mul_one, mul_inv_cancel]
  have hord : orderOf k = 3 := by
    have h1 : orderOf (⟨k, hk⟩ : K) ∣ 3 := hK ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk1
    · exact h
  have hzK : Subgroup.zpowers k = K := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk)
    rw [hK, Nat.card_zpowers, hord]
  have hgk : g * k * g⁻¹ ∈ Subgroup.zpowers k := by
    rw [hzK]
    exact (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hgk
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hgk
  have hk3 : k ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one k
  have hconj : g ^ 2 * k * (g ^ 2)⁻¹ = (g * k * g⁻¹) ^ i := by
    calc g ^ 2 * k * (g ^ 2)⁻¹ = g * (g * k * g⁻¹) * g⁻¹ := by rw [sq]; group
      _ = g * k ^ i * g⁻¹ := by rw [hik]
      _ = (g * k * g⁻¹) ^ i := by rw [conj_pow]
  rw [hconj, ← hik, ← pow_mul]
  rw [Finset.mem_range] at hi
  interval_cases i
  · exfalso
    apply hk1
    have h0 : g * k * g⁻¹ = 1 := by rw [← hik, pow_zero]
    have := congrArg (fun x => g⁻¹ * x * g) h0
    simpa [mul_assoc] using this
  · rw [pow_one]
  · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hk3, one_mul, pow_one]

namespace IsWModel

variable {σ : Setting G} {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ}
  {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
  {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
  {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}

theorem padicValInt_nine : padicValInt 2 ((9 : ℕ) - (if 9 % 4 = 1 then (1 : ℤ) else -1)) = 3 := by
  have h : ((9 : ℕ) : ℤ) - (if 9 % 4 = 1 then (1 : ℤ) else -1) = ((2 ^ 3 : ℕ) : ℤ) := by
    norm_num
  rw [h, padicValInt.of_nat]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat.prime_pow 3

theorem m_eq_eight (hW : IsWModel σ φ) (h9 : σ.p ^ σ.f = 9) : m = 8 := by
  have h := hW.two_part
  rw [h9, padicValInt_nine] at h
  exact h

theorem card_sigma_eq_one (hW : IsWModel σ φ) (h9 : σ.p ^ σ.f = 9) : Nat.card Sigma = 1 := by
  have hp := hW.p_prime
  have hf2 : σ.f = 2 := by
    have h3 : 3 ≤ σ.p := by
      have := hp.two_le
      rcases hW.p_odd with ⟨k, hk⟩
      omega
    rcases Nat.lt_or_ge σ.f 2 with h | h
    · interval_cases hf : σ.f
      · exact absurd hW.one_le_f (by omega)
      · rw [pow_one] at h9
        rw [h9] at hp
        exact absurd hp (by norm_num)
    · rcases Nat.lt_or_ge σ.f 3 with h' | h'
      · omega
      · exfalso
        have : 3 ^ 3 ≤ σ.p ^ σ.f :=
          (Nat.pow_le_pow_left h3 3).trans (Nat.pow_le_pow_right (by omega) h')
        omega
  have hdvd := hW.sigma_dvd
  rw [hf2] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact h
  · exact absurd (h ▸ hW.sigma_odd) (by decide)

theorem eq_one_of_mem_torus_of_odd (hW : IsWModel σ φ) (h9 : σ.p ^ σ.f = 9)
    {w : Matrix.SpecialLinearGroup (Fin 2) F} (hw : w ∈ torus F) (hodd : Odd (orderOf w)) :
    w = 1 := by
  have hc := card_oddTorus (L := F) hW.two_ne_zero
  rw [hW.card, h9, padicValInt_nine] at hc
  norm_num at hc
  have hsub : Subsingleton {g : torus F // Odd (orderOf g)} :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  have h1 : (⟨⟨w, hw⟩, by rw [Subgroup.orderOf_mk]; exact hodd⟩ :
      {g : torus F // Odd (orderOf g)}) = ⟨1, by rw [orderOf_one]; exact odd_one⟩ :=
    Subsingleton.elim _ _
  exact congrArg (fun g : {g : torus F // Odd (orderOf g)} => ((g.1 : torus F) :
    Matrix.SpecialLinearGroup (Fin 2) F)) h1

theorem oddCore_C_le_ON (hW : IsWModel σ φ) [Finite G] (h9 : σ.p ^ σ.f = 9) :
    oddCoreIn σ.C ≤ σ.ON := by
  intro c hc
  have hcC : c ∈ σ.C := oddCoreIn_le σ.C hc
  have hcN : c ∈ σ.N := TIFacts.C_le_N σ hcC
  have hodd : Odd (orderOf (φ ⟨c, hcN⟩)) := by
    have h1 : orderOf (φ ⟨c, hcN⟩) ∣ orderOf (⟨c, hcN⟩ : σ.N) := orderOf_map_dvd φ _
    have h2 : orderOf (⟨c, hc⟩ : oddCoreIn σ.C) ∣ Nat.card (oddCoreIn σ.C) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1 h2
    exact ((odd_card_oddCoreIn σ.C).of_dvd_nat h2).of_dvd_nat h1
  obtain ⟨W, hW'⟩ := exists_oddTorus F
  obtain ⟨w, hwW, τ, hτ⟩ := exists_eq_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hW' (hW.map_mem_modelC ⟨c, hcN⟩ hcC) hodd
  have hw1 : w = 1 := hW.eq_one_of_mem_torus_of_odd h9 ((hW' w).mp hwW).1 ((hW' w).mp hwW).2
  have hτ1 : τ = 1 := by
    have : Subsingleton Sigma := (Nat.card_eq_one_iff_unique.mp (hW.card_sigma_eq_one h9)).1
    exact Subsingleton.elim _ _
  exact (hW.mem_ON_iff ⟨c, hcN⟩).mpr (by rw [hτ, hw1, hτ1, map_one, map_one, one_mul])

end IsWModel

theorem x2_eight_eq :
    Original.x2 (2 ^ 3) = Original.a (2 ^ 3) ^ 2 * Original.r (2 ^ 3) ^ 2 := by
  rw [Original.x2_eq, Original.a_eq, Original.r_eq, element_base_pow, element_base_pow,
    element_base_mul]
  congr 1

variable [Finite G] [IsSimpleGroup G]

theorem wreath_propIV51
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hII : (wreathedSetting n S e p f).ChapterIIFacts) :
    (wreathedSetting n S e p f).PropIV51 := by
  intro J hJL₀ hL₀ hJC hNJ hq9 hJON
  exfalso
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  set σ := wreathedSetting n S e p f with hσ
  have h9 : σ.p ^ σ.f = 9 := hq9
  have hn3 : n = 3 := by
    have h8 := hW.m_eq_eight h9
    have : 2 ^ n = 2 ^ 3 := h8
    exact Nat.pow_right_injective (le_refl 2) this
  subst hn3
  set K : Subgroup G := J ⊓ σ.ON with hKdef
  have hNK : σ.N ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNJ hg, σ.N_le_normalizer_ON hg⟩
  have hL₀K : σ.L₀ ≤ Subgroup.centralizer (K : Set G) := by
    rw [hL₀]
    refine sup_le ?_ ?_
    · exact hJC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))
    · exact Subgroup.le_centralizer_iff.mp ((inf_le_left : K ≤ J).trans hJC)
  have hKN : K ≤ σ.N := inf_le_right.trans (TIFacts.ON_le_N σ)
  have hx₂ : σ.x₂ = wreathModelHom S e (Original.a (2 ^ 3)) ^ 2 *
      wreathModelHom S e (Original.r (2 ^ 3)) ^ 2 := by
    change wreathModelHom S e (Original.x2 (2 ^ 3)) = _
    rw [x2_eight_eq, map_mul, map_pow, map_pow]
  have hSN : (S : Subgroup G) ≤ σ.N := sylow_le_involutionCentralizer 3 hn S e
  have haN : wreathModelHom S e (Original.a (2 ^ 3)) ∈ σ.N := hSN (e.symm _).property
  have hrL₀ : wreathModelHom S e (Original.r (2 ^ 3)) ∈ σ.L₀ := by
    apply modelY_le_wreathedSetting_L₀ hnonab 3 hn S e hfour p f
    exact ⟨Original.r (2 ^ 3), Subgroup.subset_closure (by simp), rfl⟩
  have hx₂K : ∀ k ∈ K, σ.x₂ * k = k * σ.x₂ := by
    intro k hk
    set α := wreathModelHom S e (Original.a (2 ^ 3)) with hα
    set ρr := wreathModelHom S e (Original.r (2 ^ 3)) with hρr
    have hr2 : ρr ^ 2 * k = k * ρr ^ 2 :=
      (Subgroup.mem_centralizer_iff.mp (hL₀K (σ.L₀.pow_mem hrL₀ 2)) k hk).symm
    have ha2 := sq_conj_eq_of_card_three hJON (hNK haN) hk
    rw [hx₂]
    calc α ^ 2 * ρr ^ 2 * k = α ^ 2 * k * ρr ^ 2 := by rw [mul_assoc, hr2, ← mul_assoc]
      _ = (α ^ 2 * k * (α ^ 2)⁻¹) * α ^ 2 * ρr ^ 2 := by group
      _ = _ := by rw [ha2, mul_assoc]
  have hKC : K ≤ σ.C := fun k hk =>
    (TIFacts.mem_C_iff σ (hKN hk)).mpr (hx₂K k hk).symm
  set R : Subgroup G := pCoreIn 3 σ.C with hRdef
  have hRC : R ≤ σ.C := pCoreIn_le 3 σ.C
  have hRp : IsPGroup 3 R := by
    rw [hRdef, pCoreIn]
    exact (CFSG.pCore_isPGroup).map _
  have hCR : σ.C ≤ Subgroup.normalizer (R : Set G) := by
    have : (CFSG.pCore 3 σ.C).Normal := CFSG.pCore_normal
    exact CFSG.ABGTheoremB.le_normalizer_map_subtype σ.C (CFSG.pCore 3 σ.C)
  have hRodd : Odd (Nat.card R) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    rw [hk]
    exact (by decide : Odd 3).pow
  have hRON : R ≤ σ.ON :=
    (le_oddCoreIn hRC hCR hRodd).trans (hW.oddCore_C_le_ON h9)
  have hKR : K ≤ R := by
    have hKp : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by rw [hJON, pow_one])
    have hnormal : (K.subgroupOf σ.C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr
        (fun c hc => hNK (TIFacts.C_le_N σ hc))
    have hle : K.subgroupOf σ.C ≤ CFSG.pCore 3 σ.C :=
      le_sSup ⟨hnormal, hKp.comap_subtype⟩
    intro k hk
    exact ⟨⟨k, hKC hk⟩, hle (Subgroup.mem_subgroupOf.mpr hk), rfl⟩
  have hRne : R ≠ ⊥ := by
    intro hR
    have hK : K = ⊥ := le_bot_iff.mp (hR ▸ hKR)
    rw [hK, Subgroup.card_bot] at hJON
    omega
  set H : Subgroup G := Subgroup.normalizer (R : Set G) with hHdef
  have hTH : σ.T ≤ H := by
    intro t ht
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRC hr) t ht).symm
  have hOH : oddCoreIn H ≠ ⊥ := by
    intro hO
    apply hRne
    exact le_bot_iff.mp (hO ▸ le_oddCoreIn Subgroup.le_normalizer le_rfl hRodd)
  have hJH : J ≤ H := fun j hj => Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRON) (hJC hj))
  have hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON := by
    have hJON' : J ≤ Subgroup.normalizer (σ.ON : Set G) :=
      fun j hj => σ.N_le_normalizer_ON (hW.model.L₀_le (hJL₀ hj))
    rw [hL₀, Subgroup.coe_mul_of_left_le_normalizer_right J σ.ON hJON']
    exact Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr hJH)
  have hQ : IsQGroup H := (hII.cover_qgroup H hTH hOH hcov).1.1
  have hMH : Subgroup.normalizer (σ.C : Set G) ≤ H := by
    have h := normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 3 σ.C)
    exact h
  have hNTH : Subgroup.normalizer (σ.T : Set G) ≤ H :=
    (normalizer_le_normalizer_centralizer σ.T).trans hMH
  have hDH : σ.D ≤ H := inf_le_right.trans hNTH
  have h3 : 3 ∣ automizerIndex (σ.T.subgroupOf H) := by
    rw [automizerIndex_subgroupOf_eq hTH hNTH, hII.automizer_T]
    norm_num
  obtain ⟨hQD, -, -, hQD', -, -⟩ := hII.fusion_disjoint H
  rcases hII.qd_or_d_of_three H hTH (Or.inl hDH) h3 with h | h
  · exact hQD h hQ
  · exact hQD' hQ h.1

end CFSG.Wreathed.OriginalAllPrime.IVFacts
