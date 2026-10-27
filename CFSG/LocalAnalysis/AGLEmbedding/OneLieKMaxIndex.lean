module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_index_stabilizer_eq_of_not_sq_dvd {R Ω : Type*} [Group R] [Finite R]
    [MulAction R Ω] [Finite Ω] {p : ℕ} [Fact p.Prime] (hR : IsPGroup p R)
    (hfix : ∀ ω : Ω, ∃ r : R, r • ω ≠ ω) (hsq : ¬ p ^ 2 ∣ Nat.card Ω) :
    ∃ ω : Ω, (MulAction.stabilizer R ω).index = p := by
  have hp : p.Prime := Fact.out
  by_contra hno
  push Not at hno
  apply hsq
  have key : ∀ ω : Ω, p ^ 2 ∣ Nat.card (MulAction.orbit R ω) := by
    intro ω
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp
      (hn ▸ (MulAction.stabilizer R ω).index_dvd_card)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.index_eq_one] at hk
      obtain ⟨r, hr⟩ := hfix ω
      exact hr (MulAction.mem_stabilizer_iff.mp (hk ▸ Subgroup.mem_top r))
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hno ω (by rw [hk, pow_one])
    rw [hk]
    exact pow_dvd_pow p (by omega)
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient R Ω)
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits R Ω), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => key _

section Index

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.map_sylowTwo_d1PlusCore (hd : D1OneLieData p P M H R Rbar K)
    {T : Subgroup G} (hTN : T ≤ d1PlusCore p H K) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index) :
    (T.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      IsPGroup 2 ((T.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) ∧
      ¬ 2 ∣ (((T.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))).subgroupOf
        (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))).index := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hC
  have hNH : d1PlusCore p H K ≤ H := hd.d1PlusCore_facts.1.trans inf_le_left
  have hTH : T ≤ H := hTN.trans hNH
  have hNsub : (d1PlusCore p H K).subgroupOf H = C.comap π :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hTC : (T.subgroupOf H).map π ≤ C := by
    rw [Subgroup.map_le_iff_le_comap, ← hNsub]
    exact Subgroup.comap_mono hTN
  refine ⟨hTC, hT2.comap_subtype.map _, ?_⟩
  change ¬ 2 ∣ ((T.subgroupOf H).map π).relIndex C
  have h1 : ((T.subgroupOf H).map π).relIndex C =
      (((T.subgroupOf H).map π).comap π).relIndex (C.comap π) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
  have h2 : (T.subgroupOf H).relIndex ((d1PlusCore p H K).subgroupOf H) =
      T.relIndex (d1PlusCore p H K) := by
    rw [Subgroup.subgroupOf, Subgroup.relIndex_comap, Subgroup.subgroupOf,
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hNH)]
  have h3 : (((T.subgroupOf H).map π).comap π).relIndex (C.comap π) ∣
      (T.subgroupOf H).relIndex (C.comap π) :=
    Subgroup.relIndex_dvd_of_le_left _ (Subgroup.le_comap_map _ _)
  rw [h1]
  intro h
  apply hTidx
  change 2 ∣ T.relIndex (d1PlusCore p H K)
  rw [← h2, hNsub]
  exact h.trans h3

theorem D1OneLieData.exists_indexP (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hno : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)))
    (hc : Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) = p) :
    ∃ T : Subgroup G, T ≤ d1PlusCore p H K ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index ∧ pCoreOf 2 H ≤ T ∧
      d1LiftX p H R K ≤ R ⊓ Subgroup.normalizer (T : Set G) ∧
      Nat.card R = p * Nat.card (R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) ∧
      R ⊓ Subgroup.normalizer (T : Set G) ⊓ d1PlusCore p H K = ⊥ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := d1PlusCore p H K with hNdef
  obtain ⟨hNHM, hHN, hON⟩ := hd.d1PlusCore_facts
  have hNH : N ≤ H := hNHM.trans inf_le_left
  have hRH : R ≤ H := hd.cfg.ext.le_H
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := hRH.trans hHN
  have hRp : IsPGroup p R := hd.cfg.ext.isPGroup
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (R ⊓ N) N :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hd.cfg.ext.isSylow hNH hHN
  obtain ⟨-, -, hndvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hsyl
  have hcardN : Nat.card N = (R ⊓ N).relIndex N * p := by
    have h := Subgroup.relIndex_mul_card (H := R ⊓ N) (K := N)
    rw [inf_eq_left.mpr (inf_le_right : R ⊓ N ≤ N), hc] at h
    exact h.symm
  have hsqN : ¬ p ^ 2 ∣ Nat.card N := by
    rw [hcardN, pow_two]
    intro h
    exact hndvd (Nat.dvd_of_mul_dvd_mul_right hp.pos h)
  set R' : Subgroup (Subgroup.normalizer (N : Set G)) :=
    R.subgroupOf (Subgroup.normalizer (N : Set G)) with hR'
  have hR'p : IsPGroup p R' := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  have hfixN : ∀ (g : Subgroup.normalizer (N : Set G)) (T₀ : Sylow 2 N), g • T₀ = T₀ →
      (g : G) ∈ Subgroup.normalizer (((T₀ : Subgroup N).map N.subtype : Subgroup G) : Set G) := by
    intro g T₀ hg
    refine mem_normalizer_of_conj_map_le ?_
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have hmem : g • t ∈ ((g • T₀ : Sylow 2 N) : Subgroup N) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ ht
    rw [hg] at hmem
    exact ⟨_, hmem, rfl⟩
  have hnoT : ∀ T₀ : Sylow 2 N,
      ¬ R ≤ Subgroup.normalizer (((T₀ : Subgroup N).map N.subtype : Subgroup G) : Set G) := by
    intro T₀ hRT
    obtain ⟨hWC, hW2, hWidx⟩ := hd.map_sylowTwo_d1PlusCore (Subgroup.map_subtype_le _)
      (T₀.isPGroup'.map _) (by
        rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
        exact T₀.not_dvd_index)
    apply hno _ hWC hW2 hWidx
    rw [hd.cfg.rbar]
    exact map_le_normalizer_map _ ((Subgroup.map_subtype_le _).trans hNH) hRT
  have hfree : ∀ T₀ : Sylow 2 N, ∃ r : R', r • T₀ ≠ T₀ := by
    intro T₀
    by_contra h
    push Not at h
    apply hnoT T₀
    intro r hr
    exact hfixN ⟨r, hRN hr⟩ T₀ (h ⟨⟨r, hRN hr⟩, hr⟩)
  have hpΩ : p ∣ Nat.card (Sylow 2 N) := by
    have h := hR'p.card_modEq_card_fixedPoints (Sylow 2 N)
    have hempty : Nat.card (MulAction.fixedPoints R' (Sylow 2 N)) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨T₀, hT₀⟩
      obtain ⟨r, hr⟩ := hfree T₀
      exact hr (hT₀ r)
    rw [hempty] at h
    exact Nat.modEq_zero_iff_dvd.mp h
  have hΩN : ∀ T₀ : Sylow 2 N,
      Nat.card N = Nat.card (Sylow 2 N) * Nat.card (Subgroup.normalizer ((T₀ : Subgroup N) :
        Set N)) := fun T₀ => by
    rw [Sylow.card_eq_index_normalizer T₀]
    exact (Subgroup.index_mul_card _).symm
  have hsqΩ : ¬ p ^ 2 ∣ Nat.card (Sylow 2 N) := by
    intro h
    apply hsqN
    obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 N))
    rw [hΩN T₀]
    exact Dvd.dvd.mul_right h _
  obtain ⟨T₀, hT₀⟩ := exists_index_stabilizer_eq_of_not_sq_dvd hR'p hfree hsqΩ
  set T : Subgroup G := (T₀ : Subgroup N).map N.subtype with hT
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map _
  have hTidx : ¬ 2 ∣ (T.subgroupOf N).index := by
    rw [hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact T₀.not_dvd_index
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hd.cfg.red.ne_two
  have hST : pCoreOf 2 H ≤ T := by
    have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := pCoreOf_le_glbPrimeCore Nat.prime_two hp2 H
    have hTS : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      (hTN.trans hNH).trans (localGroup_le_normalizer_pCoreOf 2 H)
    have hST2 : IsPGroup 2 (pCoreOf 2 H ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
        hT2 hTS
    exact le_sup_left.trans
      (le_of_le_of_isPGroup_of_not_dvd_index le_sup_right (sup_le (hSN.trans hON) hTN) hST2 hTidx)
  set R₁ := R ⊓ Subgroup.normalizer (T : Set G) with hR₁
  have hstab : p * Nat.card (MulAction.stabilizer R' T₀) = Nat.card R := by
    rw [← hT₀, Subgroup.index_mul_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv]
  have hstabR₁ : Nat.card (MulAction.stabilizer R' T₀) ≤ Nat.card R₁ := by
    let ι : MulAction.stabilizer R' T₀ →* G := (Subgroup.normalizer (N : Set G)).subtype.comp
      (R'.subtype.comp (MulAction.stabilizer R' T₀).subtype)
    have hι : Function.Injective ι := (Subgroup.subtype_injective _).comp
      ((Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _))
    have hle : ι.range ≤ R₁ := by
      rintro _ ⟨s, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.mp (s : R').2, hfixN _ T₀ s.2⟩
    calc Nat.card (MulAction.stabilizer R' T₀) = Nat.card ι.range :=
          Nat.card_congr (MonoidHom.ofInjective hι).toEquiv
      _ ≤ Nat.card R₁ := Subgroup.card_le_of_le hle
  have hR₁R : ¬ R ≤ R₁ := fun h => hnoT T₀ (h.trans inf_le_right)
  have hcardR₁ : Nat.card R = p * Nat.card R₁ := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (inf_le_left : R₁ ≤ R)
    have hmdvd : m ∣ p ^ n := hn ▸ Dvd.intro_left _ hm.symm
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hmdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hm
      exact hR₁R (Subgroup.eq_of_le_of_card_ge inf_le_left hm.le).ge
    have hpos : 0 < Nat.card R₁ := Nat.card_pos
    have hj1 : j = 1 := by
      by_contra hj1
      have h2 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
      have h3 : p * p ≤ p ^ j := by rwa [pow_two] at h2
      have h4 : p * Nat.card R₁ < Nat.card R₁ * p ^ j := by
        have : p * Nat.card R₁ < p * p * Nat.card R₁ := by
          have := hp.two_le
          nlinarith
        nlinarith
      have h5 : Nat.card R₁ * p ^ j ≤ p * Nat.card R₁ := by
        rw [← hm, ← hstab]
        exact Nat.mul_le_mul_left p hstabR₁
      exact absurd h5 (not_le.mpr h4)
    rw [hm, hj1, pow_one, mul_comm]
  have hR₁N : R₁ ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨haR, haT⟩, haN⟩
    by_contra ha1
    have hap : p ∣ orderOf a := by
      obtain ⟨k, hk⟩ := hRp ⟨a, haR⟩
      have hk' : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hi
        exact ha1 (Subgroup.mem_bot.mpr hi)
      rw [hi]
      exact dvd_pow_self p hi0
    have ha' : (⟨a, haN⟩ : N) ∈ Subgroup.normalizer ((T₀ : Subgroup N) : Set N) := by
      have h1 := Subgroup.le_normalizer_comap N.subtype (H := T) (show (⟨a, haN⟩ : N) ∈
        (Subgroup.normalizer (T : Set G)).comap N.subtype from haT)
      rwa [hT, Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at h1
    have hpn : p ∣ Nat.card (Subgroup.normalizer ((T₀ : Subgroup N) : Set N)) := by
      refine hap.trans ?_
      rw [← Subgroup.orderOf_mk a haN, ← Subgroup.orderOf_mk (⟨a, haN⟩ : N) ha']
      exact orderOf_dvd_natCard _
    apply hsqN
    rw [hΩN T₀, pow_two]
    exact Nat.mul_dvd_mul hpΩ hpn
  have hNJ := (hd.d1PlusCore_le_and_commutator hK h84 hD2 hY hWK).2
  have hJT : nclIn H (d1LiftX p H R K) ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
    have hc' := hNJ (Subgroup.commutator_mem_commutator (N.inv_mem (hTN ht)) hj)
    rw [commutatorElement_def, inv_inv] at hc'
    have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
    rw [e]
    exact T.mul_mem ht (hST hc')
  exact ⟨T, hTN, hT2, hTidx, hST,
    le_inf (d1LiftX_le p H R K) ((le_nclIn (d1LiftX_le_H p H R K)).trans hJT), hcardR₁, hR₁N⟩

end Index

end CFSG.AGLEmbedding
