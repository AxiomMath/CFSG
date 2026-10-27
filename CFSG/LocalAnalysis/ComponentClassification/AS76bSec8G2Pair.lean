module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Root
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Swap
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

section Short

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem g2N_zero_v_b_c (D E F : K) :
    g2N 0 0 0 D E F =
      pinnedX .G2 K g2v D * (pinnedX .G2 K g2b E * pinnedX .G2 K g2c F) := by
  simp only [g2N, pinnedX_zero, one_mul, mul_assoc]

theorem rootSubgroup_v_inf_commutator_eq_bot :
    rootSubgroup .G2 K g2v ⊓ ⁅g2ShortCent K, g2ShortCent K⁆ = ⊥ := by
  obtain ⟨-, -, -, -, hset, -, hinf, -, hLv, θ, -, hθ, ψ', -, hψ'⟩ :=
    UnbalancedCatalog.even_G2_highest_short_root_centralizer K
  have hθval : ∀ y : Multiplicative (Fin 2 → K),
      θ y = pinnedX .G2 K g2b (y.toAdd 0) * pinnedX .G2 K g2c (y.toAdd 1) := fun y => by
    rw [← hθ y.toAdd, ofAdd_toAdd]
  have hθA : θ.range ≤ g2ShortRadical K := by
    rintro _ ⟨y, rfl⟩
    refine ⟨0, y.toAdd 0, y.toAdd 1, ?_⟩
    rw [hθval, g2N_zero_v_b_c, pinnedX_zero, one_mul]
  have hLθ : g2RankOne K g2ia ≤ normalizer (θ.range : Set (ModGL .G2 K)) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Multiplicative.ofAdd ((ψ' ⟨l, hl⟩ : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) y.toAdd), ?_⟩
      rw [← hψ' ⟨l, hl⟩ y.toAdd, ofAdd_toAdd]
    · rintro ⟨y, hy⟩
      refine ⟨Multiplicative.ofAdd ((ψ' ⟨l, hl⟩⁻¹ : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) y.toAdd), ?_⟩
      rw [← hψ' ⟨l, hl⟩⁻¹ y.toAdd, ofAdd_toAdd, hy]
      simp only [InvMemClass.coe_inv, inv_inv]
      group
  have hvN : ∀ d : K, θ.range ⊔ g2RankOne K g2ia ≤ centralizer {pinnedX .G2 K g2v d} := by
    intro d
    refine sup_le ?_ fun l hl => mem_centralizer_singleton_iff.2 (hLv l hl d).eq
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff, hθval]
    rw [mul_assoc, ← (commute_v_c d _).eq, ← mul_assoc, ← (commute_v_b d _).eq, mul_assoc]
  have hcomm : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ θ.range ⊔ g2RankOne K g2ia := by
    have hdec : ∀ x ∈ g2ShortCent K, ∃ d : K, ∃ n ∈ θ.range ⊔ g2RankOne K g2ia,
        x = n * pinnedX .G2 K g2v d := by
      intro x hx
      have hx' : x ∈ ((g2ShortRadical K : Set (ModGL .G2 K)) *
          (g2RankOne K g2ia : Set (ModGL .G2 K))) := by
        rw [← hset]
        exact hx
      obtain ⟨q, ⟨D, E, F, rfl⟩, l, hl, rfl⟩ := Set.mem_mul.1 hx'
      refine ⟨D, θ (Multiplicative.ofAdd ![E, F]) * l,
        mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right hl), ?_⟩
      have hc := mem_centralizer_singleton_iff.1
        (hvN D (mul_mem (mem_sup_left ⟨Multiplicative.ofAdd ![E, F], rfl⟩) (mem_sup_right hl)))
      rw [hc, g2N_zero_v_b_c, hθval]
      simp [mul_assoc]
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨d, n, hn, rfl⟩ := hdec x hx
    obtain ⟨d', n', hn', rfl⟩ := hdec y hy
    rw [RankTwoL3Even.commutatorElement_mul_mul_of_commute
      (mem_centralizer_singleton_iff.1 (hvN d hn')).symm
      (mem_centralizer_singleton_iff.1 (hvN d' hn)).symm (by
        rw [← pinnedX_add, ← pinnedX_add, add_comm])]
    exact RankTwoL3Even.commutatorElement_mem' hn hn'
  rw [eq_bot_iff]
  rintro z ⟨hzv, hzN⟩
  rw [mem_bot]
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hzv
  have hzN' := hcomm hzN
  rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hLθ] at hzN'
  obtain ⟨l, hl, _, ⟨y, rfl⟩, hly⟩ := hzN'
  change l * θ y = pinnedX .G2 K g2v d at hly
  have hlA : l ∈ g2ShortRadical K := by
    have h1 : l = pinnedX .G2 K g2v d * (θ y)⁻¹ := by rw [← hly]; group
    rw [h1]
    exact mul_mem ⟨d, 0, 0, by rw [g2N_zero_v_b_c, pinnedX_zero, pinnedX_zero, one_mul,
      mul_one]⟩ (inv_mem (hθA ⟨y, rfl⟩))
  have hl1 : l = 1 := by
    have : l ∈ g2ShortRadical K ⊓ g2RankOne K g2ia := mem_inf.2 ⟨hlA, hl⟩
    rwa [hinf, mem_bot] at this
  rw [hl1, one_mul, hθval] at hly
  have h2 : g2N (0 : K) 0 0 0 (y.toAdd 0) (y.toAdd 1) = g2N 0 0 0 d 0 0 := by
    rw [g2N_zero_v_b_c, g2N_zero_v_b_c, pinnedX_zero, pinnedX_zero, pinnedX_zero, one_mul,
      one_mul, mul_one, hly]
  obtain ⟨-, -, -, hd, -, -⟩ := g2N_injective h2
  rw [← hd, pinnedX_zero]

end Short

section Pinned

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {X₀ : Type*} [Group X₀] {ψ : normalizer (A : Set G) →* MulAut X₀}

omit [Finite G] in
theorem exists_conj_psi_eq
    (hψ : IsActionHom A (MulAut.conj : X₀ →* MulAut X₀).range ψ) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) (ht₀N : t₀ ∈ normalizer (A : Set G)) {x₀ z : X₀}
    (hx₀ : ψ ⟨t₀, ht₀N⟩ = MulAut.conj x₀) (hz : IsConj x₀ z) :
    ∃ a ∈ A, ∃ t ∈ rightConjugate T a, t ≠ 1 ∧
      ∃ htN : t ∈ normalizer (A : Set G), ψ ⟨t, htN⟩ = MulAut.conj z := by
  obtain ⟨h, hh⟩ := isConj_iff.1 hz
  obtain ⟨a, ha, hψa⟩ := hψ.exists_eq (MulAut.conj h⁻¹) ⟨h⁻¹, rfl⟩
  have haN := le_normalizer ha
  refine ⟨a, ha, a⁻¹ * t₀ * a, ?_, ?_, mul_mem (mul_mem (inv_mem haN) ht₀N) haN, ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht₀
  · intro h1
    apply ht₀1
    calc t₀ = a * (a⁻¹ * t₀ * a) * a⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  · rw [psi_mul (mul_mem (inv_mem haN) ht₀N) haN, psi_mul (inv_mem haN) ht₀N, psi_inv haN,
      hψa, hx₀, ← hh, ← map_inv, ← map_mul, ← map_mul, inv_inv]

end Pinned

section G2

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K]

@[expose] def G2Pinned
    (ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K))
    (T : Subgroup G) (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  ∃ t ∈ T, t ≠ 1 ∧ ∃ (htN : t ∈ normalizer (A : Set G)) (y : ↥(adjointGroup .G2 K)),
    (y : ModGL .G2 K) = pinnedX .G2 K γ 1 ∧ ψ ⟨t, htN⟩ = MulAut.conj y

variable {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem g2_exists_pinned
    [CharP K 2] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (hK4 : 4 ≤ Nat.card K)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ) :
    ∃ a ∈ A, (G2Pinned ψ (rightConjugate T a) g2c ∧
        ActsIn ψ (rightConjugate T a) (rootSubgroup .G2 K g2c)) ∨
      (G2Pinned ψ (rightConjugate T a) g2v ∧
        ActsIn ψ (rightConjugate T a) (rootSubgroup .G2 K g2v)) := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc.T_ne_bot
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have ht₀N := hc.le_normalizer ht₀
  obtain ⟨x₀, hx₀⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht₀ ht₀N
  have hord : orderOf x₀ = 2 := orderOf_eq_prime (sq_eq_one_of_psi_eq_conj hZ hc h32 ht₀ ht₀N hx₀)
    (ne_one_of_psi_eq_conj hc h32 hψ ht₀ ht₀1' ht₀N hx₀)
  rcases UnbalancedCatalog.even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) x₀
    hord with hlong | hshort
  · obtain ⟨a, ha, t, ht, ht1, htN, hψt⟩ := exists_conj_psi_eq hψ ht₀ ht₀1' ht₀N hx₀ hlong
    obtain ⟨hperf, hcent⟩ := h184 K hK4
    refine ⟨a, ha, Or.inl ⟨⟨t, ht, ht1, htN, _, rfl, hψt⟩, ?_⟩⟩
    exact actsIn_of_perfect h4 h32 h34 (sec3_conj hc ha) hOut hψ ht ht1 htN hψt inf_le_left
      hperf inf_le_right fun y hy _ => hcent ▸ hy
  · obtain ⟨a, ha, t, ht, ht1, htN, hψt⟩ := exists_conj_psi_eq hψ ht₀ ht₀1' ht₀N hx₀ hshort
    obtain ⟨hperf, -, hcent⟩ := h184s K hK4
    refine ⟨a, ha, Or.inr ⟨⟨t, ht, ht1, htN, _, rfl, hψt⟩, ?_⟩⟩
    have hle : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ g2ShortCent K :=
      (commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb
    exact actsIn_of_perfect h4 h32 h34 (sec3_conj hc ha) hOut hψ ht ht1 htN hψt
      (hle.trans inf_le_left) hperf (hle.trans inf_le_right) hcent

theorem g2_not_mixed
    [CharP K 2] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) (hK4 : 4 ≤ Nat.card K)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hRp : G2Pinned ψ (rightConjugate R g⁻¹) g2v)
    (hR : ActsIn ψ (rightConjugate R g⁻¹) (rootSubgroup .G2 K g2v)) : False := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
  obtain ⟨hperf, hcent⟩ := h184 K hK4
  obtain ⟨hperfs, hincls, hinvs⟩ := h184s K hK4
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hX : CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) = rightConjugate
      (CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))) g := by
    rw [hc.perfectCore_eq h32 h4 h34 hOut, RankTwoClassical.rightConjugate_perfectCore,
      RankTwoClassical.rightConjugate_inf, ← AS76b.centralizer_rightConjugate,
      RankTwoClassical.rightConjugate_inv_rightConjugate]
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc.T_ne_bot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htN := hc.le_normalizer ht
  obtain ⟨p, hpA, hpR⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht htN
  have hψp : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj x := by
    have h1 : ψ ⟨t⁻¹ * p, mul_mem (inv_mem htN) (le_normalizer hpA)⟩ = 1 :=
      (hψ.eq_one_iff _).2 (hc.sylowR.le hpR)
    rw [psi_mul (inv_mem htN) (le_normalizer hpA), psi_inv htN, inv_mul_eq_one] at h1
    rw [← h1, hx]
  have hp2 : p ^ 2 = 1 := by
    have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hpR
    calc p ^ 2 = (t * (t⁻¹ * p)) ^ 2 := by rw [mul_inv_cancel_left]
      _ = t ^ 2 * (t⁻¹ * p) ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [(hc.elemT h32).2 t ht, (hc.elemR h32).2 _ hpR, one_mul]
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply ht1'
    have htR : t ∈ R := by simpa using hpR
    have : t ∈ R ⊓ T := mem_inf.2 ⟨htR, ht⟩
    rwa [hc.inf_eq_bot, mem_bot] at this
  have hD : ⁅(g2LongCent K).subgroupOf (adjointGroup .G2 K),
      (g2LongCent K).subgroupOf (adjointGroup .G2 K)⁆ =
        (g2LongCent K).subgroupOf (adjointGroup .G2 K) :=
    commutator_subgroupOf_eq inf_le_left hperf
  have hPX : ((g2LongCent K).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) ≤
        (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range :=
    map_le_range _ _
  have hP : ⁅((g2LongCent K).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)),
      ((g2LongCent K).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))⁆ =
        ((g2LongCent K).subgroupOf (adjointGroup .G2 K)).map
          (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) := by
    rw [← map_commutator, hD]
  have hTP : ∀ u ∈ T, ∀ huN : u ∈ normalizer (A : Set G),
      ∀ s ∈ ((g2LongCent K).subgroupOf (adjointGroup .G2 K)).map
        (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)),
      ψ ⟨u, huN⟩ * s = s * ψ ⟨u, huN⟩ := by
    intro u hu huN s hs
    obtain ⟨y, hy⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ hu huN
    have hyC : (y : ModGL .G2 K) ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      rw [hcent]
      exact hT u hu huN y hy
    obtain ⟨d, hd, rfl⟩ := hs
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 (mem_inf.1 hyC).2 d (mem_subgroupOf.1 hd)).symm
  have hML : leviLift ψ (((g2LongCent K).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))) ≤
        A ⊓ centralizer (T : Set G) :=
    le_inf leviLift_le fun l hl => mem_centralizer_iff.2 fun u hu =>
      (mem_centralizer_singleton_iff.1 (leviLift_le_centralizer hψ (hc.le_normalizer hu)
        (hTP u hu _) hl)).symm
  have hpX₁ : p ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := by
    refine CFSG.Quasithin.le_perfectCore_of_perfect hML (commutator_leviLift hψ hPX hP) ?_
    refine mem_leviLift_of_pow hψ hPX hP hZA' (mem_liftIn.2 ⟨hpA, ?_⟩) (k := 1)
      (by rw [pow_one]; exact hp2)
    rw [hψp]
    exact ⟨x, mem_subgroupOf.2 (mem_inf.2 ⟨x.2,
      rootSubgroup_le_centralizer g2c (hT t ht htN x hx)⟩), rfl⟩
  have hpZ : ∀ y ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)), y * p = p * y := by
    intro y hy
    obtain ⟨hyA, hyT⟩ := mem_inf.1 (CFSG.Quasithin.perfectCore_le _ hy)
    have h1 : t * y = y * t := mem_centralizer_iff.1 hyT t ht
    have h2 : y * (t⁻¹ * p) = (t⁻¹ * p) * y := (hc.commute_of_mem hyA hpR).eq
    calc y * p = y * (t * (t⁻¹ * p)) := by rw [mul_inv_cancel_left]
      _ = t * (y * (t⁻¹ * p)) := by rw [← mul_assoc, ← h1, mul_assoc]
      _ = t * (t⁻¹ * p) * y := by rw [h2, ← mul_assoc]
      _ = p * y := by rw [mul_inv_cancel_left]
  have hqX₂ : g * p * g⁻¹ ∈
      CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)) := by
    have h := hpX₁
    rw [hX, mem_rightConjugate_iff] at h
    exact h
  have hqZ : ∀ y ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)),
      y * (g * p * g⁻¹) = g * p * g⁻¹ * y := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := by
      rw [hX, mem_rightConjugate_iff]
      simpa [mul_assoc] using hy
    have h := hpZ _ hy'
    calc y * (g * p * g⁻¹) = g * (g⁻¹ * y * g * p) * g⁻¹ := by group
      _ = g * (p * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * p * g⁻¹ * y := by group
  have hqA : g * p * g⁻¹ ∈ A :=
    (mem_inf.1 (CFSG.Quasithin.perfectCore_le _ hqX₂)).1
  have hqN := le_normalizer hqA
  obtain ⟨w, hw⟩ := hψ.map_mem _ hqA
  have hle : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ g2ShortCent K :=
    (commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb
  have hDs : ⁅(⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K),
      (⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)⁆ =
        (⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K) :=
    commutator_subgroupOf_eq (hle.trans inf_le_left) hperfs
  have hPXs : ((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) ≤
        (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range :=
    map_le_range _ _
  have hPs : ⁅((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)),
      ((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))⁆ =
        ((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)).map
          (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) := by
    rw [← map_commutator, hDs]
  have hRP : ∀ u ∈ rightConjugate R g⁻¹, ∀ huN : u ∈ normalizer (A : Set G),
      ∀ s ∈ ((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)).map
        (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)),
      ψ ⟨u, huN⟩ * s = s * ψ ⟨u, huN⟩ := by
    intro u hu huN s hs
    obtain ⟨y, hy⟩ := exists_psi_eq_conj hc.swap h32 h4 h34 hψ hu huN
    have hyC : (y : ModGL .G2 K) ∈ g2Centralizer K
        ((⁅g2ShortCent K, g2ShortCent K⁆ : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) :=
      hincls (hR u hu huN y hy)
    obtain ⟨d, hd, rfl⟩ := hs
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 (mem_inf.1 hyC).2 d (mem_subgroupOf.1 hd)).symm
  have hM₂ : leviLift ψ (((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf (adjointGroup .G2 K)).map
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))) ≤
        CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect (le_inf leviLift_le fun l hl =>
      mem_centralizer_iff.2 fun u hu => (mem_centralizer_singleton_iff.1
        (leviLift_le_centralizer hψ (hc.swap.le_normalizer hu) (hRP u hu _) hl)).symm)
      (commutator_leviLift hψ hPXs hPs)
  have hw2 : (w : ModGL .G2 K) ^ 2 = 1 := by
    have hq2 : (g * p * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2, mul_one, mul_inv_cancel]
    have h1 : MulAut.conj (w ^ 2) = 1 := by
      rw [map_pow, hw, ← psi_pow hqN 2]
      have e : (⟨(g * p * g⁻¹) ^ 2, pow_mem hqN 2⟩ : normalizer (A : Set G)) = 1 :=
        Subtype.ext hq2
      rw [e, map_one]
    rw [← map_one (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))] at h1
    rw [← Subgroup.coe_pow, hinj h1, OneMemClass.coe_one]
  have hwV : (w : ModGL .G2 K) ∈ rootSubgroup .G2 K g2v := by
    refine hinvs _ (mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun d hd => ?_⟩) hw2
    have hdC : d ∈ adjointGroup .G2 K := (hle.trans inf_le_left) hd
    obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ hPXs hPs
      (⟨⟨d, hdC⟩, mem_subgroupOf.2 hd, rfl⟩ :
        MulAut.conj ⟨d, hdC⟩ ∈ ((⁅g2ShortCent K, g2ShortCent K⁆).subgroupOf
          (adjointGroup .G2 K)).map
          (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)))
    have hlN := le_normalizer (leviLift_le hl)
    have h := congrArg ψ (Subtype.ext (hqZ l (hM₂ hl)) :
      (⟨l * (g * p * g⁻¹), mul_mem hlN hqN⟩ : normalizer (A : Set G)) =
        ⟨g * p * g⁻¹ * l, mul_mem hqN hlN⟩)
    rw [psi_mul hlN hqN, psi_mul hqN hlN, hlψ, ← hw, ← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hinj h)
  obtain ⟨r₀, hr₀, -, hr₀N, y₀, hy₀, hψr₀⟩ := hRp
  have hX₂A : CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)) ≤ A :=
    (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  have hY : ⁅(CFSG.Quasithin.perfectCore
      (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))).subgroupOf (normalizer (A : Set G)),
      (CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))).subgroupOf
      (normalizer (A : Set G))⁆ =
        (CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))).subgroupOf
          (normalizer (A : Set G)) :=
    commutator_subgroupOf_eq (hX₂A.trans le_normalizer) (CFSG.Quasithin.perfectCore_perfect _)
  have hYmap : ((CFSG.Quasithin.perfectCore
      (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))).subgroupOf (normalizer (A : Set G))).map ψ ≤
        ((g2ShortCent K).subgroupOf (adjointGroup .G2 K)).map
          (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) := by
    rintro _ ⟨⟨y, hyN⟩, hy, rfl⟩
    have hy' := mem_subgroupOf.1 hy
    obtain ⟨hyA, hyR⟩ := mem_inf.1 (CFSG.Quasithin.perfectCore_le _ hy')
    obtain ⟨z, hz⟩ := hψ.map_mem y hyA
    have hyr : y * r₀ = r₀ * y := (mem_centralizer_iff.1 hyR r₀ hr₀).symm
    have h := congrArg ψ (Subtype.ext hyr :
      (⟨y * r₀, mul_mem hyN hr₀N⟩ : normalizer (A : Set G)) = ⟨r₀ * y, mul_mem hr₀N hyN⟩)
    rw [psi_mul hyN hr₀N, psi_mul hr₀N hyN, ← hz, hψr₀, ← map_mul, ← map_mul] at h
    have hzy := congrArg Subtype.val (hinj h)
    refine ⟨z, mem_subgroupOf.2 (mem_inf.2 ⟨z.2, mem_centralizer_singleton_iff.2 ?_⟩), hz⟩
    rw [← hy₀]
    exact hzy
  have hqY : ψ ⟨g * p * g⁻¹, hqN⟩ ∈ (⁅(g2ShortCent K).subgroupOf (adjointGroup .G2 K),
      (g2ShortCent K).subgroupOf (adjointGroup .G2 K)⁆).map
        (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) := by
    have h1 : ψ ⟨g * p * g⁻¹, hqN⟩ ∈ ((CFSG.Quasithin.perfectCore
        (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))).subgroupOf
          (normalizer (A : Set G))).map ψ :=
      ⟨⟨g * p * g⁻¹, hqN⟩, mem_subgroupOf.2 hqX₂, rfl⟩
    rw [← hY, map_commutator] at h1
    rw [map_commutator]
    exact commutator_mono hYmap hYmap h1
  obtain ⟨w', hw', hw'eq⟩ := hqY
  rw [← hw] at hw'eq
  rw [hinj hw'eq] at hw'
  have hwC' : (w : ModGL .G2 K) ∈ ⁅g2ShortCent K, g2ShortCent K⁆ := by
    have h := mem_map_of_mem (adjointGroup .G2 K).subtype hw'
    rwa [map_commutator, subgroupOf_map_subtype,
      inf_of_le_left (show g2ShortCent K ≤ adjointGroup .G2 K from inf_le_left)] at h
  have hw1 : w = 1 := by
    have h : (w : ModGL .G2 K) ∈ rootSubgroup .G2 K g2v ⊓ ⁅g2ShortCent K, g2ShortCent K⁆ :=
      mem_inf.2 ⟨hwV, hwC'⟩
    rw [rootSubgroup_v_inf_commutator_eq_bot, mem_bot] at h
    exact Subtype.ext h
  have hqK : g * p * g⁻¹ ∈ centralizer (A : Set G) := by
    refine (hψ.eq_one_iff ⟨g * p * g⁻¹, hqN⟩).1 ?_
    rw [← hw, hw1, map_one]
  have hq2 : (g * p * g⁻¹) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, show g * p * g⁻¹ * (g * p * g⁻¹) = g * p ^ 2 * g⁻¹ by rw [sq]; group, hp2,
      mul_one, mul_inv_cancel]
  have hq1 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZA' (mem_inf.2 ⟨hqA, hqK⟩)) hq2
  apply hp1
  calc p = g⁻¹ * (g * p * g⁻¹) * g := by group
    _ = 1 := by rw [hq1, mul_one, inv_mul_cancel]

theorem g2_exists_longLong
    [CharP K 2] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) (hK4 : 4 ≤ Nat.card K)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ) :
    ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧
      ((G2Pinned ψ T' g2c ∧ ActsIn ψ T' (rootSubgroup .G2 K g2c) ∧
          G2Pinned ψ (rightConjugate R g'⁻¹) g2c ∧
          ActsIn ψ (rightConjugate R g'⁻¹) (rootSubgroup .G2 K g2c)) ∨
        (G2Pinned ψ T' g2v ∧ ActsIn ψ T' (rootSubgroup .G2 K g2v))) := by
  obtain ⟨a, ha, hlong | hshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc hOut hK4 hψ
  · have hc₁ := sec3_conj hc ha
    obtain ⟨b, hb, hRlong | hRshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc₁.swap hOut hK4 hψ
    · refine ⟨rightConjugate T a, b⁻¹ * (g * a), sec3_mul_left hc₁ (inv_mem hb),
        Or.inl ⟨hlong.1, hlong.2, ?_, ?_⟩⟩
      · rw [rightConjugate_inv_mul_inv]
        exact hRlong.1
      · rw [rightConjugate_inv_mul_inv]
        exact hRlong.2
    · exfalso
      refine g2_not_mixed h4 h32 h184 h184s (sec3_mul_left hc₁ (inv_mem hb)) hOut hZA hK4 hψ
        hlong.2 ?_ ?_
      · rw [rightConjugate_inv_mul_inv]
        exact hRshort.1
      · rw [rightConjugate_inv_mul_inv]
        exact hRshort.2
  · exact ⟨rightConjugate T a, g * a, sec3_conj hc ha, Or.inr hshort⟩

end G2

end CFSG.ComponentClassification.RankTwoExceptional
