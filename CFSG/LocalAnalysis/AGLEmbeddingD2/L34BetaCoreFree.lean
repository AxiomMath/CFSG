module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaAmalgam
public import CFSG.LocalAnalysis.AGLEmbeddingD2.EscapeMaxTools
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

section OrderThree

variable {G : Type} [Group G] [Finite G]

theorem exists_eq_zpowers_of_card_three {Y : Subgroup G} (hY : Nat.card Y = 3) :
    ∃ y ∈ Y, y ≠ 1 ∧ Y = Subgroup.zpowers y := by
  have hne : Y ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hY; norm_num at hY
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨y, y.2, fun h => hy1 (Subtype.ext h), ?_⟩
  have hle : Subgroup.zpowers (y : G) ≤ Y := Subgroup.zpowers_le.mpr y.2
  have hdvd : orderOf (y : G) ∣ 3 := hY ▸ Subgroup.orderOf_dvd_natCard Y y.2
  have hord : orderOf (y : G) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h)) hy1
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hY])).symm

omit [Finite G] in
theorem map_conj_mul (g₁ g₂ : G) (S : Subgroup G) :
    S.map (MulAut.conj (g₁ * g₂)).toMonoidHom =
      (S.map (MulAut.conj g₂).toMonoidHom).map (MulAut.conj g₁).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem le_of_isPGroup_of_not_dvd_index {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K T : Subgroup X} [K.Normal] (hK : ¬ p ∣ K.index) (hT : IsPGroup p T) : T ≤ K := by
  have : Fact p.Prime := ⟨hp⟩
  have hmap : T.map (QuotientGroup.mk' K) = ⊥ := by
    have h1 : Nat.card (T.map (QuotientGroup.mk' K)) ∣ K.index := by
      rw [Subgroup.index]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨n, hn⟩ := (hT.map (QuotientGroup.mk' K)).exists_card_eq
    rw [hn] at h1
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq _ hn
    · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans h1) hK
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  exact hmap

end OrderThree

section CardNine

open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem card_le_nine_of_stronglyEmbedded {K A R : Subgroup X} [K.Normal]
    (hL : IsLinThreeFour K) (hAK : A ≤ K) (hA : Nat.card A = 9) (hR : IsPGroup 3 R)
    (hRN : R ≤ Subgroup.normalizer (A : Set X))
    (hstr : ∀ x : X, x ∉ Subgroup.normalizer (A : Set X) →
      ¬ 3 ∣ Nat.card (Subgroup.normalizer (A : Set X) ⊓
        GLBConj x (Subgroup.normalizer (A : Set X)) : Subgroup X)) :
    Nat.card R ≤ 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardK : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hL
  have hAc : Nat.card (A.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA, hcardK,
      factorization_20160_three]
    norm_num
  let T₀ : Sylow 3 K := Sylow.ofCard (A.subgroupOf K) hAc
  have hT₀ : (T₀ : Subgroup K) = A.subgroupOf K := rfl
  have hloc := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T₀
  have hRK : R ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  let : MulDistribMulAction R K := CFSG.SignalizerFunctor.Helpers.conjugationAction R K hRK
  have hsmul : ∀ (r : R) (k : K), ((r • k : K) : X) = (r : X) * k * (r : X)⁻¹ := fun _ _ => rfl
  have hmem : ∀ (r : R) (T : Sylow 3 K) (x : X),
      x ∈ ((r • T : Sylow 3 K) : Subgroup K).map K.subtype ↔
        (r : X)⁻¹ * x * (r : X) ∈ (T : Subgroup K).map K.subtype := by
    intro r T x
    constructor
    · rintro ⟨k, hk, rfl⟩
      change k ∈ r • (T : Subgroup K) at hk
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hk
      refine ⟨r⁻¹ • k, hk, ?_⟩
      rw [Subgroup.coe_subtype, hsmul]
      simp
    · rintro ⟨k, hk, hkx⟩
      have hxK : x ∈ K := by
        have : (r : X) * k * (r : X)⁻¹ ∈ K :=
          (inferInstance : K.Normal).conj_mem (k : X) k.2 (r : X)
        rw [Subgroup.coe_subtype] at hkx
        rw [show x = (r : X) * k * (r : X)⁻¹ by rw [hkx]; group]
        exact this
      refine ⟨⟨x, hxK⟩, ?_, rfl⟩
      change ⟨x, hxK⟩ ∈ r • (T : Subgroup K)
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have heq : r⁻¹ • (⟨x, hxK⟩ : K) = k := by
        apply Subtype.ext
        rw [hsmul, Subgroup.coe_inv, inv_inv]
        rw [Subgroup.coe_subtype] at hkx
        exact hkx.symm
      rw [heq]
      exact hk
  have hA' : (T₀ : Subgroup K).map K.subtype = A := by
    rw [hT₀]
    exact Subgroup.map_subgroupOf_eq_of_le hAK
  have hfixiff : ∀ (r : R) (T : Sylow 3 K), r • T = T →
      (r : X) ∈ Subgroup.normalizer (((T : Subgroup K).map K.subtype : Subgroup X) : Set X) := by
    intro r T hrT
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := hmem r T ((r : X) * x * (r : X)⁻¹)
    rw [hrT] at h1
    rw [h1]
    simp [mul_assoc]
  have hfix₀ : ∀ r : R, r • T₀ = T₀ := by
    intro r
    apply Sylow.ext
    apply Subgroup.map_injective K.subtype_injective
    ext x
    rw [hmem r T₀ x, hA']
    have hrN := hRN r.2
    constructor
    · intro h
      have := (Subgroup.mem_normalizer_iff.mp hrN ((r : X)⁻¹ * x * (r : X))).mp h
      simpa [mul_assoc] using this
    · intro h
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) x).mp h
      simpa using this
  have hfix : ∀ r : R, r ≠ 1 → ∀ T : Sylow 3 K, r • T = T → T = T₀ := by
    intro r hr1 T hT
    by_contra hne
    obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq K T₀ T
    have hkT : ((k • T₀ : Sylow 3 K) : Subgroup K).map K.subtype =
        A.map (MulAut.conj (k : X)).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, ← hA']
      ext x
      simp only [Subgroup.mem_map, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, ⟨z, hz, rfl⟩, by simp [MulAut.conj_apply]⟩
      · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨MulAut.conj k z, ⟨z, hz, rfl⟩, by simp [MulAut.conj_apply]⟩
    have hrk := hfixiff r _ hT
    rw [hkT] at hrk
    have hkN : (k : X) ∉ Subgroup.normalizer (A : Set X) := by
      intro hkN
      apply hne
      rw [Sylow.smul_eq_iff_mem_normalizer]
      show k ∈ Subgroup.normalizer (((T₀ : Subgroup K)) : Set K)
      rw [hT₀, ← Subgroup.subgroupOf_normalizer_eq hAK]
      exact Subgroup.mem_subgroupOf.mpr hkN
    apply hstr (k : X)⁻¹ (fun h => hkN (by simpa using Subgroup.inv_mem _ h))
    have hr : (r : X) ∈ Subgroup.normalizer (A : Set X) ⊓
        GLBConj (k : X)⁻¹ (Subgroup.normalizer (A : Set X)) := by
      refine ⟨hRN r.2, ?_⟩
      rw [GLBConj, inv_inv, ← normalizer_map_conj]
      exact hrk
    have hr1' : (r : X) ≠ 1 := fun h => hr1 (Subtype.ext h)
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    have hord : orderOf (r : X) ∣ 3 ^ n := by
      rw [← hn, Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard r
    obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hmeq
      exact hr1' hmeq
    have h3 : 3 ∣ orderOf (r : X) := by
      rw [hmeq]
      exact dvd_pow_self 3 hm0
    exact h3.trans (Subgroup.orderOf_dvd_natCard _ hr)
  have : Fintype R := Fintype.ofFinite R
  have : Fintype (Sylow 3 K) := Fintype.ofFinite _
  have : Fintype (MulAction.orbitRel.Quotient R (Sylow 3 K)) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group R (Sylow 3 K)
  have hfixed : ∀ r : R, Fintype.card (MulAction.fixedBy (Sylow 3 K) r) =
      if r = 1 then Fintype.card (Sylow 3 K) else 1 := by
    intro r
    split_ifs with hr
    · subst hr
      rw [Fintype.card_congr (Equiv.subtypeUnivEquiv fun T => by simp)]
    · rw [Fintype.card_eq_one_iff]
      refine ⟨⟨T₀, hfix₀ r⟩, ?_⟩
      rintro ⟨T, hT⟩
      exact Subtype.ext (hfix r hr T hT)
  simp only [hfixed] at hburn
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_eq' Finset.univ (1 : R),
    ite_eq_left (Finset.mem_univ _), Finset.card_singleton, one_smul, smul_eq_mul, mul_one,
    Finset.filter_ne' Finset.univ (1 : R), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ] at hburn
  have h280 : Fintype.card (Sylow 3 K) = 280 := by
    rw [Fintype.card_eq_nat_card, Sylow.card_eq_index_normalizer T₀]
    have h1 : (Subgroup.normalizer ((T₀ : Subgroup K) : Set K)).index * 72 = 20160 := by
      have := Subgroup.index_mul_card (Subgroup.normalizer ((T₀ : Subgroup K) : Set K))
      rwa [hloc.card_normalizer, hcardK] at this
    show (Subgroup.normalizer ((T₀ : Subgroup K) : Set K)).index = 280
    omega
  rw [h280] at hburn
  have hRpos : 0 < Fintype.card R := Fintype.card_pos
  have hdvd : Fintype.card R ∣ 279 := by
    have h1 : Fintype.card R ∣ 280 + (Fintype.card R - 1) := by
      rw [hburn]
      exact dvd_mul_left _ _
    have h2 : 280 + (Fintype.card R - 1) = 279 + Fintype.card R := by omega
    rw [h2] at h1
    exact (Nat.dvd_add_left (dvd_refl _)).mp h1
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [← Nat.card_eq_fintype_card, hn] at hdvd
  rw [hn]
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have h27 : 3 ^ 3 ∣ 3 ^ n := Nat.pow_dvd_pow 3 (by omega)
    have := h27.trans hdvd
    norm_num at this
  calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 9 := by norm_num

end CardNine

end CFSG.AGLEmbeddingD2

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaConf3.card_R_eq_nine
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) : Nat.card R = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX₀ := hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  have hAb : Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) = 9 := by
    rw [hc.almostSimple.card_A]
    norm_num
  have hstrX : ∀ x, x ∉ Subgroup.normalizer
      (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)) →
      ¬ 3 ∣ Nat.card (Subgroup.normalizer
        (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) ⊓
        GLBConj x (Subgroup.normalizer
          (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
            Set (H ⧸ primeComplementCore (G := H) 3))) : Subgroup _) := by
    rw [← hX₀]
    intro x hx
    exact not_dvd_card_inf_glbConj_map hstr.2.2 _ hc.esc.primeComplementCore_le_inf x hx
  have hRbN : (Rbar : Subgroup _) ≤ Subgroup.normalizer
      (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)) :=
    hX₀ ▸ hc.almostSimple.sylow_le
  have := hc.almostSimple.normal
  have h9 := card_le_nine_of_stronglyEmbedded hL hc.le_K hAb Rbar.isPGroup' hRbN hstrX
  obtain ⟨T, hT⟩ := hc.esc.isSylow
  have hRp : IsPGroup 3 (R.subgroupOf H) := by
    have hTR : (T : Subgroup H) = R.subgroupOf H := by
      rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [← hTR]
    exact T.isPGroup'
  have hRcard : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) =
      Nat.card R := by
    rw [hc.rbar, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hRp]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.esc.le_H).toEquiv
  have hAR : Nat.card A ≤ Nat.card R := Subgroup.card_le_of_le hc.esc.A_le
  rw [hc.esc.card_A] at hAR
  omega

theorem d2L34BetaCoreFree3
    (hglob : AGLGlobal G) (hD1 : D1At G 3) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) (hX : D2OnlyL34At P M) {U Y Q : Subgroup G} (hYH : Y ≤ H)
    (hYM : ¬ Y ≤ M) (hY3 : Nat.card Y = 3) (hQM : Q ≤ M) (hQ3 : Nat.card Q = 3)
    (hQconj : ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H) :
    pCoreOf 2 ((U ⊔ Y) ⊔ (U ⊔ Q)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hD
  have hloc : IsTwoLocal (Subgroup.normalizer
      ((pCoreOf 2 ((U ⊔ Y) ⊔ (U ⊔ Q)) : Subgroup G) : Set G)) :=
    ⟨_, hD, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨H₀, hNH₀, hH₀⟩ := exists_maximal_twoLocal hloc
  have hNle : (U ⊔ Y) ⊔ (U ⊔ Q) ≤ H₀ := (le_normalizer_twoCore _).trans hNH₀
  have hYH₀ : Y ≤ H₀ := le_sup_right.trans (le_sup_left.trans hNle)
  have hQH₀ : Q ≤ H₀ := le_sup_right.trans (le_sup_right.trans hNle)
  have hH₀M : ¬ H₀ ≤ M := fun h => hYM (hYH₀.trans h)
  suffices hconj : ∃ g : G, Q.map (MulAut.conj g).toMonoidHom = Y by
    obtain ⟨g, hg⟩ := hconj
    exact hQconj g (hg ▸ hYH)
  have hQp : IsPGroup 3 (Q.subgroupOf H₀) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH₀).toEquiv, hQ3, pow_one])
  have hYp : IsPGroup 3 (Y.subgroupOf H₀) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH₀).toEquiv, hY3, pow_one])
  obtain ⟨T, hQT⟩ := hQp.exists_le_sylow
  obtain ⟨T', hYT'⟩ := hYp.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq H₀ T T'
  set Y' : Subgroup G := Y.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom with hY'
  have hY'3 : Nat.card Y' = 3 := by
    rw [hY', Subgroup.card_map_of_injective (MulAut.conj _).injective, hY3]
  set E₀ : Subgroup G := (T : Subgroup H₀).map H₀.subtype with hE₀
  have hQE₀ : Q ≤ E₀ := by
    intro q hq
    exact ⟨⟨q, hQH₀ hq⟩, hQT (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hY'E₀ : Y' ≤ E₀ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyT : (⟨y, hYH₀ hy⟩ : H₀) ∈ ((h • T : Sylow 3 H₀) : Subgroup H₀) :=
      hYT' (Subgroup.mem_subgroupOf.mpr hy)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyT
    refine ⟨_, hyT, ?_⟩
    simp [MulAut.inv_def]
  have hdone : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom = Y' →
      ∃ g : G, Q.map (MulAut.conj g).toMonoidHom = Y := by
    intro g hg
    refine ⟨(h : G) * g, ?_⟩
    rw [map_conj_mul, hg, hY', ← map_conj_mul, mul_inv_cancel]
    ext x
    simp
  have hE₀p : IsPGroup 3 E₀ := T.isPGroup'.map H₀.subtype
  by_cases hcyc : IsCyclic (T : Subgroup H₀)
  ·
    have : IsCyclic E₀ :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ H₀.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective _ _ H₀.subtype_injective).surjective
    have hsub : Q.subgroupOf E₀ = Y'.subgroupOf E₀ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE₀).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY'E₀).toEquiv, hQ3, hY'3]
    have hQY : Q = Y' := by
      rw [Subgroup.subgroupOf_inj, inf_of_le_left hQE₀, inf_of_le_left hY'E₀] at hsub
      exact hsub
    refine hdone 1 ?_
    rw [← hQY]
    ext x
    simp
  ·
    have : Fact (IsPGroup 3 (T : Subgroup H₀)) := ⟨T.isPGroup'⟩
    obtain ⟨E, -, hEc, hEel⟩ :=
      CFSG.lemma_4_5_a (R := (T : Subgroup H₀)) (p := 3) (by norm_num) hcyc
    set E' : Subgroup G := (E.map (T : Subgroup H₀).subtype).map H₀.subtype with hE'
    have hE'el : IsElemAbelian 3 E' :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
          ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hEel) _) _
    have hE'c : Nat.card E' = 3 ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective H₀.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hEc]
    have hE'E₀ : E' ≤ E₀ := Subgroup.map_mono (Subgroup.map_subtype_le E)
    have hQne : Q ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hQ3; norm_num at hQ3
    have hE₀M : E₀ ≤ M := by
      refine le_of_stronglyEmbedded_of_inf_ne_bot Nat.prime_three hstr hE₀p fun h => hQne ?_
      exact le_bot_iff.mp (h ▸ le_inf hQE₀ hQM)
    have hE'M : GLBCore 3 1 E' ≤ M :=
      glbCore_one_le_of_stronglyEmbedded Nat.prime_three hstr (hE₀p.to_le hE'E₀) (hE'E₀.trans hE₀M)
    have hE₀H₀ : E₀ ≤ H₀ := Subgroup.map_subtype_le _
    have hrank₀ : Open.pRank 3 (H₀ ⊓ M) ≤ 2 := by
      by_contra hlt
      exact hH₀M (hD1 P M hc.esc.maxTwoLocal_M
        ((weakCore_le_fullCore 3 (P : Subgroup G)).trans hc.esc.core_le) H₀ hH₀.1 (by omega))
    have hE'rank : 2 ≤ Open.pRank 3 E' := le_pRank_of_isElemAbelian Nat.prime_three hE'el hE'c
    have hesc₀ : D2Escape 3 P M E' H₀ E₀ :=
      { prime := Nat.prime_three
        ne_two := by norm_num
        sylow_le := hc.esc.sylow_le
        core_le := hc.esc.core_le
        maxTwoLocal_M := hc.esc.maxTwoLocal_M
        maxTwoLocal_H := hH₀
        elem := hE'el
        card_A := hE'c
        core_A := hE'M
        A_le := hE'E₀
        le_H := hE₀H₀
        le_M := hE₀M
        isSylow := ⟨T, rfl⟩
        pRank_eq := le_antisymm
          ((pRank_mono 3 Nat.prime_three (le_inf hE₀H₀ hE₀M)).trans hrank₀)
          (hE'rank.trans (pRank_mono 3 Nat.prime_three hE'E₀))
        not_le := hH₀M }
    have hR9 := hc.card_R_eq_nine hstr
    have hE₀9 : Nat.card E₀ = 9 := by
      refine le_antisymm (hR9 ▸ hc.max E' H₀ E₀ hesc₀) ?_
      have := Subgroup.card_le_of_le hE'E₀
      rw [hE'c] at this
      omega
    have hE'eq : E' = E₀ := Subgroup.eq_of_le_of_card_ge hE'E₀ (by rw [hE₀9, hE'c]; norm_num)
    have hmax₀ : D2EscapeMax 3 P M E₀ := fun A' H' R' h' =>
      (hc.max A' H' R' h').trans (by rw [hR9, hE₀9])
    obtain ⟨Rbar₀, K₀, hRbar₀, hK₀⟩ := hesc₀.almostSimple hglob
    obtain ⟨d₀, hd₀, hi⟩ := hX E' H₀ E₀ hesc₀ hmax₀ Rbar₀ K₀ hRbar₀ hK₀
    have := hK₀.normal
    have hE'H₀ : E' ≤ H₀ := hE'E₀.trans hE₀H₀
    have hE'p : IsPGroup 3 (E'.subgroupOf H₀) := IsPGroup.of_card (n := 2)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'H₀).toEquiv, hE'c])
    have hE₀p' : IsPGroup 3 (E₀.subgroupOf H₀) := IsPGroup.of_card (n := 2)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀H₀).toEquiv, hE₀9]; norm_num)
    have hAK₀ : (E'.subgroupOf H₀).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K₀ := by
      refine le_of_isPGroup_of_not_dvd_index Nat.prime_three ?_ (hE'p.map _)
      intro h3
      have hL₀ : IsLinThreeFour K₀ := isLinThreeFour_of_l34Index hd₀ hi
      have hK₀c : Nat.card K₀ = 20160 := (kFactSmallThreeOrders K₀).2.1 hL₀
      have hRb : Nat.card (Rbar₀ : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) 3)) = 3 ^ 2 := by
        rw [hRbar₀, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3)
          hE₀p', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀H₀).toEquiv, hE₀9]
        norm_num
      have hfac : (Nat.card (H₀ ⧸ primeComplementCore (G := H₀) 3)).factorization 3 = 2 := by
        have h1 := Rbar₀.card_eq_multiplicity
        rw [hRb] at h1
        exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
      have hmul := K₀.index_mul_card
      rw [hK₀c] at hmul
      have hidx0 : K₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : (K₀.index * 20160).factorization 3 = 2 := by rw [hmul, hfac]
      rw [Nat.factorization_mul hidx0 (by norm_num), Finsupp.add_apply,
        factorization_20160_three] at h2
      have h1 := (Nat.prime_three.dvd_iff_one_le_factorization hidx0).mp h3
      omega
    have htr := hesc₀.exists_conj_eq_of_l34 hd₀ hi hAK₀
    obtain ⟨q, hqQ, hq1, hQq⟩ := exists_eq_zpowers_of_card_three hQ3
    obtain ⟨y, hyY, hy1, hYy⟩ := exists_eq_zpowers_of_card_three hY'3
    have hqE : q ∈ E' := hE'eq ▸ hQE₀ hqQ
    have hyE : y ∈ E' := hE'eq ▸ hY'E₀ hyY
    obtain ⟨g, -, hg⟩ := htr q hqE hq1 y hyE hy1
    refine hdone g ?_
    rw [hQq, MonoidHom.map_zpowers, hYy]
    congr 1

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaCoreFree :
    D2L34BetaCoreFree := by
  intro d G _ _ P M A H R Rbar K hc hstr hX U Y Q _ hYH hYM hY3 _ hQM hQ3 _ hQconj
  exact CFSG.LocalAnalysis.RankThreeTheoremC.d2L34BetaCoreFree3 hc.glob.toAGLGlobal
    (hc.d1 3 hc.beta) hc.toConf3 hstr hX hYH hYM hY3 hQM hQ3 hQconj

end CFSG.AGLEmbeddingD2
