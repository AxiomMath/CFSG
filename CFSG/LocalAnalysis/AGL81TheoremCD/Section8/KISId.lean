module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AltTwoPGammaSylow
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableKID
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.AGLEmbedding
open CFSG.AGLEmbedding.KFactProofs.SmallIdent
open CFSG.AGLEmbedding.AltTwoPGammaSylow
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

private theorem three_dvd_card_altOn {p : ℕ} (hp5 : 5 ≤ p) {s : Finset (Fin (2 * p))}
    (hs : s.card = p) : 3 ∣ Nat.card (altOn s) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).toEquiv]
  have hc : Nat.card s = p := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hs]
  have : Nontrivial s := by
    rw [← Finite.one_lt_card_iff_nontrivial, hc]
    omega
  have h := two_mul_nat_card_alternatingGroup (α := s)
  rw [Nat.card_perm, hc] at h
  have h1 : 3 ∣ 2 * Nat.card (alternatingGroup s) :=
    h ▸ Nat.dvd_factorial (by norm_num) (by omega)
  exact (Nat.Coprime.dvd_mul_left
    ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))).mp h1

private theorem exists_altOn_map {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type*} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin (2 * p)))
    (T : Sylow p K) (a b : alternatingGroup (Fin (2 * p)))
    (hT0p : IsPGroup p
      (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup (alternatingGroup (Fin (2 * p)))))
    (hT0c : p * p ≤ Nat.card
      (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup (alternatingGroup (Fin (2 * p))))) :
    ∃ φ : alternatingGroup (Fin (2 * p)) →* K, Function.Injective φ ∧
      (T : Subgroup K) = Subgroup.zpowers (φ a) ⊔ Subgroup.zpowers (φ b) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set T₀ := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hT₀p : IsPGroup p T₀ := by simpa [T₀] using hT0p
  have hT₀c : p * p ≤ Nat.card T₀ := by simpa [T₀] using hT0c
  set φ₀ : alternatingGroup (Fin (2 * p)) →* K := e.symm.toMonoidHom
  have hφ₀ : Function.Injective φ₀ := e.symm.injective
  have hT₀Kp : IsPGroup p (T₀.map φ₀) := hT₀p.map φ₀
  obtain ⟨T', hT'⟩ := hT₀Kp.exists_le_sylow
  have hT'c : Nat.card (T' : Subgroup K) ≤ p * p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T'.isPGroup'
    have hdvd : p ^ k ∣ Nat.card K := hk ▸ Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr e.toEquiv] at hdvd
    have h2 := two_mul_card_alternatingGroup_fin (n := 2 * p) (by omega)
    have hk2 : k ≤ 2 := by
      by_contra h3
      exact CFSG.AGLEmbedding.AltTwoPGammaSylow.not_cube_dvd_factorial_two_mul hp hp5
        (h2 ▸ ((pow_dvd_pow p (by omega : 3 ≤ k)).trans hdvd).trans (dvd_mul_left _ _))
    rw [hk, ← pow_two]
    exact Nat.pow_le_pow_right hp.pos hk2
  have hT'eq : T₀.map φ₀ = T' := Subgroup.eq_of_le_of_card_ge hT' (by
    rw [Subgroup.card_map_of_injective hφ₀]
    omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T' T
  set φ : alternatingGroup (Fin (2 * p)) →* K := (MulAut.conj g).toMonoidHom.comp φ₀
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp hφ₀
  have hTφ : (T : Subgroup K) = T₀.map φ := by
    ext k
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv, ← hT'eq]
    constructor
    · rintro ⟨t, ht, htk⟩
      refine ⟨t, ht, ?_⟩
      change g * φ₀ t * g⁻¹ = k
      rw [htk]
      group
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      change φ₀ t = g⁻¹ * (g * φ₀ t * g⁻¹) * g
      group
  refine ⟨φ, hφ, ?_⟩
  rw [hTφ, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]

private theorem exists_altOn_transport {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type*} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin (2 * p)))
    (T : Sylow p K) :
    ∃ (φ : alternatingGroup (Fin (2 * p)) →* K) (a b : alternatingGroup (Fin (2 * p))),
      Function.Injective φ ∧ a ∈ altOn (half p) ∧ b ∈ altOn (half p)ᶜ ∧
        orderOf a = p ∧ orderOf b = p ∧
          (T : Subgroup K) = Subgroup.zpowers (φ a) ⊔ Subgroup.zpowers (φ b) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (dvd_card_altOn hp hp2 (card_half (p := p)))
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p
    (dvd_card_altOn hp hp2 (card_half_compl (p := p)))
  set a' : alternatingGroup (Fin (2 * p)) := a.1
  set b' : alternatingGroup (Fin (2 * p)) := b.1
  have ha' : orderOf a' = p := (Subgroup.orderOf_coe a).trans ha
  have hb' : orderOf b' = p := (Subgroup.orderOf_coe b).trans hb
  have hab : a' * b' = b' * a' := commute_altOn (s := half p) a.2 b.2
  have hzp : ∀ {x : alternatingGroup (Fin (2 * p))}, orderOf x = p →
      IsPGroup p (Subgroup.zpowers x) := fun hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  set T₀ := Subgroup.zpowers a' ⊔ Subgroup.zpowers b'
  have hnorm : Subgroup.zpowers b' ≤ Subgroup.normalizer (Subgroup.zpowers a' : Set _) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun n hn => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : b' * a' ^ k * b'⁻¹ = a' ^ k := by
      rw [((Commute.zpow_left (show Commute a' b' from hab) k).symm).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers a' k
  have hT₀p : IsPGroup p T₀ := (hzp ha').to_sup_of_normal_left' (hzp hb') hnorm
  have hinf : Subgroup.zpowers a' ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff, ← altOn_inf_compl (half p)]
    exact inf_le_inf (Subgroup.zpowers_le.mpr a.2) (Subgroup.zpowers_le.mpr b.2)
  have hT₀c : p * p ≤ Nat.card T₀ := by
    have := mul_card_le_of_inf_eq_bot (le_sup_left : Subgroup.zpowers a' ≤ T₀) le_sup_right hinf
    rwa [Nat.card_zpowers, Nat.card_zpowers, ha', hb'] at this
  obtain ⟨φ, hφ, hTφ⟩ := exists_altOn_map hp hp5 e T a' b' hT₀p hT₀c
  exact ⟨φ, a', b', hφ, a.2, b.2, ha', hb', hTφ⟩

private theorem exists_three_rank_witness {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type*} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin (2 * p)))
    (T : Sylow p K) :
    ∃ x y u v : K, x ∈ (T : Subgroup K) ∧ y ∈ (T : Subgroup K) ∧
      orderOf x = p ∧ orderOf y = p ∧ orderOf u = 3 ∧ orderOf v = 3 ∧
        Commute u y ∧ Commute v x ∧ Commute u v ∧ v ∉ Subgroup.zpowers u := by
  classical
  obtain ⟨φ, a, b, hφ, ha, hb, hao, hbo, hT⟩ := exists_altOn_transport hp hp5 e T
  obtain ⟨c₁, hc₁⟩ := exists_prime_orderOf_dvd_card' 3
    (three_dvd_card_altOn (p := p) hp5 (card_half (p := p)))
  obtain ⟨c₂, hc₂⟩ := exists_prime_orderOf_dvd_card' 3
    (three_dvd_card_altOn (p := p) hp5 (card_half_compl (p := p)))
  set c₁' : alternatingGroup (Fin (2 * p)) := c₁.1
  set c₂' : alternatingGroup (Fin (2 * p)) := c₂.1
  have hc₁' : orderOf c₁' = 3 := (Subgroup.orderOf_coe c₁).trans hc₁
  have hc₂' : orderOf c₂' = 3 := (Subgroup.orderOf_coe c₂).trans hc₂
  set x := φ a
  set y := φ b
  set u := φ c₁'
  set v := φ c₂'
  have hcyc₁ : c₁' ∈ altOn (half p) := c₁.2
  have hcyc₂ : c₂' ∈ altOn (half p)ᶜ := c₂.2
  have hxT : x ∈ (T : Subgroup K) :=
    hT ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers (φ a))
  have hyT : y ∈ (T : Subgroup K) :=
    hT ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (φ b))
  have hxo : orderOf x = p := by rw [orderOf_injective φ hφ, hao]
  have hyo : orderOf y = p := by rw [orderOf_injective φ hφ, hbo]
  have huo : orderOf u = 3 := by rw [orderOf_injective φ hφ, hc₁']
  have hvo : orderOf v = 3 := by rw [orderOf_injective φ hφ, hc₂']
  have huy : Commute u y := (show Commute c₁' b from commute_altOn (s := half p) hcyc₁ hb).map φ
  have hvx : Commute v x :=
    (show Commute a c₂' from commute_altOn (s := half p) ha hcyc₂).symm.map φ
  have huv : Commute u v :=
    (show Commute c₁' c₂' from commute_altOn (s := half p) hcyc₁ hcyc₂).map φ
  have hnot : v ∉ Subgroup.zpowers u := by
    intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hc : c₁' ^ k = c₂' := hφ (by
      calc φ (c₁' ^ k) = (φ c₁') ^ k := map_zpow φ c₁' k
        _ = u ^ k := rfl
        _ = v := hk
        _ = φ c₂' := rfl)
    have hc₂ne : c₂' ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hc₂'
      omega
    have hnot' : c₂' ∉ Subgroup.zpowers c₁' := by
      intro hmem
      have hle : Subgroup.zpowers c₁' ⊓ Subgroup.zpowers c₂' ≤ (⊥ : Subgroup _) := by
        rw [← altOn_inf_compl (half p)]
        exact inf_le_inf (Subgroup.zpowers_le.mpr hcyc₁) (Subgroup.zpowers_le.mpr hcyc₂)
      have hmem' : c₂' ∈ Subgroup.zpowers c₁' ⊓ Subgroup.zpowers c₂' :=
        ⟨hmem, Subgroup.mem_zpowers c₂'⟩
      exact hc₂ne (Subgroup.mem_bot.mp (hle hmem'))
    exact hnot' (Subgroup.mem_zpowers_iff.mpr ⟨k, hc⟩)
  exact ⟨x, y, u, v, hxT, hyT, hxo, hyo, huo, hvo, huy, hvx, huv, hnot⟩

theorem two_le_pRank_three_of_mulEquiv_alternatingGroup {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Type*} [Group X] [Finite X] {K N : Subgroup X}
    (e : ↥K ≃* alternatingGroup (Fin (2 * p))) (hN : IsStronglyPEmbedded p N)
    (T : Sylow p ↥K) (hT : (T : Subgroup ↥K) ≤ N.subgroupOf K) :
    2 ≤ CFSG.Open.pRank 3 N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, u, v, hxT, hyT, hxo, hyo, huo, hvo, huy, hvx, huv, hnot⟩ :=
    exists_three_rank_witness hp hp5 e T
  have hxN : (x : X) ∈ N := Subgroup.mem_subgroupOf.mp (hT hxT)
  have hyN : (y : X) ∈ N := Subgroup.mem_subgroupOf.mp (hT hyT)
  have hy_ne : (y : X) ≠ 1 := by
    intro h1
    have h2 : y = 1 := Subtype.ext (by simpa using h1)
    rw [h2, orderOf_one] at hyo
    omega
  have hx_ne : (x : X) ≠ 1 := by
    intro h1
    have h2 : x = 1 := Subtype.ext (by simpa using h1)
    rw [h2, orderOf_one] at hxo
    omega
  have hy_pow : (y : X) ^ p = 1 := by
    have h2 : y ^ p = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    simpa using congrArg (fun z : ↥K => (z : X)) h2
  have hx_pow : (x : X) ^ p = 1 := by
    have h2 : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    simpa using congrArg (fun z : ↥K => (z : X)) h2
  have huN : (u : X) ∈ N := by
    refine hN.centralizer_le hy_ne hy_pow hyN ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (huy.map K.subtype).eq
  have hvN : (v : X) ∈ N := by
    refine hN.centralizer_le hx_ne hx_pow hxN ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hvx.map K.subtype).eq
  have hv_not : (v : X) ∉ Subgroup.zpowers (u : X) := by
    intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hkK : u ^ k = v := Subtype.ext (by simpa using hk)
    exact hnot (Subgroup.mem_zpowers_iff.mpr ⟨k, hkK⟩)
  have huoX : orderOf (u : X) = 3 := (Subgroup.orderOf_coe u).trans huo
  have hvoX : orderOf (v : X) = 3 := (Subgroup.orderOf_coe v).trans hvo
  exact CFSG.GroupTheory.two_le_pRank_of_commute (p := 3) (H := N) huN hvN huoX hvoX
    (huv.map K.subtype) hv_not

private theorem solvable_or_id_of_smallAut
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {N K : Subgroup X} [K.Normal]
    (hO : CFSG.pPrimeCore p X = ⊥) (hKs : IsSimpleGroup ↥K)
    (hKnab : ∃ a b : ↥K, a * b ≠ b * a) (hK : K = CFSG.generalizedFitting X)
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) (hcat : CFSG.Open.IsCatalogGroup ↥K)
    (T : Sylow p ↥K) (hcyc : ¬ IsCyclic (T : Subgroup ↥K))
    (hΓT : CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) ≠ ⊤)
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2)
    (hId : CFSG.AGLEmbedding.KFactSmallIdent) (hFi : KFactFi22SPEThreeRank)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11)
    (hN : IsStronglyPEmbedded p N)
    (hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K)
    (hne : N.subgroupOf K ≠ ⊤) (hout : Group.IsSolvable (Outer ↥K)) :
    IsSolvable ↥N ∨
      (2 ≤ CFSG.Open.pRank 3 N ∧
        (CoverHasLargeTwoLocal ↥K ∨
          (p = 5 ∧ Nonempty (↥K ≃* alternatingGroup (Fin 10))))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hTN : (T : Subgroup ↥K) ≤ N.subgroupOf K := le_trans Subgroup.le_normalizer hle
  have hK2 : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2 :=
    (CFSG.AGLEmbedding.pRank_le_pRank_mulAut_of_nonabelian hKnab hp.one_lt
      (le_refl (CFSG.Open.pRank p (⊤ : Subgroup ↥K)))).trans hAut
  have hrank : CFSG.pRank p ↥(⊤ : Subgroup ↥K) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥K) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup ↥K)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup ↥K)).symm
  have hsmall : CFSG.AGLEmbedding.IsSmallStrongP p ↥K := by
    refine hId ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT ?_
    rw [hrank]
    exact hK2
  rcases hsmall with hlin | huni | halt | h34 | h5spor | h11J4
  · have hD := CFSG.AGLEmbedding.smallRankOneData_of_small hp hp5 (Or.inl hlin) T
    exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
  · have hD := CFSG.AGLEmbedding.smallRankOneData_of_small hp hp5 (Or.inr huni) T
    exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
  · obtain ⟨e⟩ := halt
    by_cases hp5' : p = 5
    · subst p
      have h3 := two_le_pRank_three_of_mulEquiv_alternatingGroup (p := 5) (by norm_num)
        (le_rfl) e hN T hTN
      exact Or.inr ⟨h3, Or.inr ⟨rfl, ⟨e⟩⟩⟩
    · have hp7 : 7 ≤ p := by
        by_contra h7
        have hp6 : p ≤ 6 := by omega
        interval_cases p
        · exact hp5' rfl
        · norm_num at hp
      have h3 := two_le_pRank_three_of_mulEquiv_alternatingGroup hp hp5 e hN T hTN
      exact Or.inr ⟨h3, Or.inl <|
        coverHasLargeTwoLocal_of_mulEquiv_alternatingGroup (n := 2 * p) (by omega) e⟩
  · omega
  · rcases h5spor with ⟨rfl, hTits | hMcL | hFi22⟩
    · have hD := sporCore_of_isTitsGroup hKs hKnab hTits T
      exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
    · have hD := sporCore_of_isMcL hKs hKnab hMcL T
      exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
    · have hKs' : IsSimpleGroup ↥(CFSG.generalizedFitting X) := by
        rw [← hK]; exact hKs
      have hFi22' : CFSG.AGLEmbedding.IsFi22 ↥(CFSG.generalizedFitting X) := by
        rw [← hK]; exact hFi22
      have hcov : CoverHasLargeTwoLocal ↥K := by
        rw [hK]
        exact coverHasLargeTwoLocal_of_isFi22 hKs' hFi22'
      exact Or.inr ⟨hFi X hO hFi22' N hN, Or.inl hcov⟩
  · rcases h11J4 with ⟨rfl, hJ4K⟩
    have hD := sporCore_of_d2HeisLocalAt hp (by norm_num) hJ4 hKs hKnab hJ4K T
    exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)

private theorem solvable_or_id_of_largeAut
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {N K : Subgroup X} [K.Normal]
    (hKs : IsSimpleGroup ↥K) (hKnab : ∃ a b : ↥K, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup ↥K)
    (T : Sylow p ↥K) (hcyc : ¬ IsCyclic (T : Subgroup ↥K))
    (hΓT : CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) ≠ ⊤)
    (hAut : ¬ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2)
    (hTor : CFSG.AGLEmbedding.KFactOneLieTorus)
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) (hout : Group.IsSolvable (Outer ↥K))
    (hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K)
    (hne : N.subgroupOf K ≠ ⊤) :
    IsSolvable ↥N ∨
      (2 ≤ CFSG.Open.pRank 3 N ∧
        (CoverHasLargeTwoLocal ↥K ∨
          (p = 5 ∧ Nonempty (↥K ≃* alternatingGroup (Fin 10))))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, e, hF⟩ := hTor ↥K hKs hKnab hcat p hp2 T hcyc hΓT hAut
  have hTbot : (T : Subgroup ↥K) ≠ ⊥ := by
    intro h
    exact hcyc (h ▸ inferInstance)
  have hdvd : p ∣ Nat.card (T : Subgroup ↥K) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      refine hTbot (Subgroup.card_eq_one.1 ?_)
      simpa using hk
    rw [hk]
    exact dvd_pow_self p hk0
  have hleΓ : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤
      CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) :=
    le_sSup ⟨T, le_rfl,
      CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd hp hdvd, rfl⟩
  have heq : CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) =
      Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    (hF.borel_coatom.le_iff.1 hleΓ).resolve_left hΓT
  have hsol : Group.IsSolvable
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    heq ▸ (CFSG.AGLEmbedding.kFactOneLieBorelSolvable_of_torus hTor
      ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT hAut)
  exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hF.borel_coatom hsol hle hne)

theorem stronglyEmbeddedSolvableId_of_kFacts
    (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hTor : CFSG.AGLEmbedding.KFactOneLieTorus)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11)
    (hFi : KFactFi22SPEThreeRank) :
    StronglyEmbeddedSolvableId := by
  classical
  intro p hp hp5 X _ _ hX hO h2 N hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  set K := CFSG.generalizedFitting X with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hcat : CFSG.Open.IsCatalogGroup ↥K :=
    hX.isCatalogGroup_of_surjective K hKnab (MonoidHom.id _) Function.surjective_id
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, hΓT⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hrk : 2 ≤ CFSG.Open.pRank p (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact h2
  have hΓ : CFSG.Open.rankThreeGamma 1 p (P : Subgroup X) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.1
      (CFSG.LocalAnalysis.UniquenessCase.UCK.glbCore_le_of_isStronglyPEmbedded hN P.isPGroup' hPN)
  have hout : Group.IsSolvable (Outer ↥K) := hSch ↥K hKs hKnab hcat
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded hN hPK
      (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  by_cases hcyc : IsCyclic (T : Subgroup ↥K)
  ·
    have hcycP : IsCyclic ↥((P : Subgroup X) ⊓ K) := by
      rw [hT] at hcyc
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe inf_le_right)
        (Subgroup.subgroupOfEquivOfLe inf_le_right).surjective
    rcases hCyc X K hKn hKs hKnab hcat hKC p hp hp2 P hcycP hrk hΓ with ⟨h3, -⟩ | h5
    · omega
    · obtain ⟨rfl, hv, ⟨e⟩⟩ := h5
      have hSz := CFSG.AGLEmbeddingD2.sz32Normal_of_mulEquiv ⟨.suzuki 2, hv⟩ rfl hKn hKC e
      have hD := hSz.data T
      refine Or.inl (isSolvable_of_isCoatom_normalizer hKC hout ?_ ?_ hle hne)
      · refine ⟨?_, fun Y hY => ?_⟩
        · intro htop
          have h1 := hD.card_normalizer
          rw [htop, Subgroup.card_top, hSz.card] at h1
          norm_num at h1
        · rcases hD.maximal hY.le with h | h
          · exact absurd h hY.ne'
          · exact h
      · exact hD.isSolvable_normalizer
  · by_cases hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
    · exact solvable_or_id_of_smallAut hp hp5 hp2 hO hKs hKnab hKdef hKC hcat T hcyc hΓT hAut
        hId hFi hJ4 hN hle hne hout
    · exact solvable_or_id_of_largeAut hp hp2 hKs hKnab hcat T hcyc hΓT hAut hTor
        hKC hout hle hne

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
