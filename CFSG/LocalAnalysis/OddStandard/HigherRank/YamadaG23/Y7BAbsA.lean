module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_forall_conj_mem {K : Subgroup G} {x : G}
    (h : ∀ y ∈ K, x * y * x⁻¹ ∈ K) : x ∈ normalizer (K : Set G) :=
  Subgroup.mem_normalizer_fintype h

theorem exists_mem_normalizer_comm_mem {Q U M : Subgroup G} (hQ : IsPGroup 2 Q) (hUQ : U ≤ Q)
    (hMU : M < U) {t : G} (ht : t * t = 1) (htU : ∀ u ∈ U, t * u * t⁻¹ ∈ U)
    (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M) :
    ∃ u ∈ U, u ∉ M ∧ (∀ m ∈ M, u * m * u⁻¹ ∈ M) ∧ ⁅t, u⁆ ∈ M := by
  have hU2 : IsPGroup 2 U := hQ.to_le hUQ
  have htU' : t ∈ normalizer (U : Set G) := mem_normalizer_of_forall_conj_mem htU
  have htM' : t ∈ normalizer (M : Set G) := mem_normalizer_of_forall_conj_mem htM
  set N : Subgroup G := U ⊓ normalizer (M : Set G) with hNdef
  have hMN : M ≤ N := fun m hm => ⟨hMU.le hm, Subgroup.le_normalizer hm⟩
  have hM'_lt_top : M.subgroupOf U < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact not_le_of_gt hMU (Subgroup.subgroupOf_eq_top.mp h)
  haveI hU_nil : Group.IsNilpotent ↥U := hU2.isNilpotent
  have hNC : NormalizerCondition ↥U := Group.normalizerCondition_of_isNilpotent
  obtain ⟨y, hyN', hyM'⟩ :=
    (SetLike.lt_iff_le_and_exists.mp (hNC (M.subgroupOf U) hM'_lt_top)).2
  have hyNorm : (y : G) ∈ normalizer (M : Set G) :=
    mem_normalizer_of_forall_conj_mem fun m hm => by
      have hz : (⟨m, hMU.le hm⟩ : ↥U) ∈ M.subgroupOf U := hm
      have hz2 := (Subgroup.mem_normalizer_iff.mp hyN' (⟨m, hMU.le hm⟩ : ↥U)).mp hz
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        Subtype.coe_mk] using hz2
  have hyN : (y : G) ∈ N := ⟨y.2, hyNorm⟩
  have hy_not_M : (y : G) ∉ M := hyM'
  have hM_lt_N : M < N := by
    refine lt_of_le_of_ne hMN ?_
    intro hNM
    exact hy_not_M (hNM ▸ hyN)
  have htN : t ∈ normalizer (N : Set G) :=
    mem_normalizer_of_forall_conj_mem fun n hn => by
      refine ⟨(Subgroup.mem_normalizer_iff.mp htU' n).mp hn.1, ?_⟩
      exact (normalizer (M : Set G)).mul_mem
        ((normalizer (M : Set G)).mul_mem htM' hn.2)
        ((normalizer (M : Set G)).inv_mem htM')
  have htN' : ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp htN n).mp hn
  have hNQ : N ≤ Q := inf_le_left.trans hUQ
  have hN2 : IsPGroup 2 N := hQ.to_le hNQ
  let M' : Subgroup ↥N := M.subgroupOf N
  haveI hM'normal : M'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mpr inf_le_right
  let α := ↥N ⧸ M'
  letI : Fintype α := M'.fintypeQuotientOfFiniteIndex
  let τ : ↥N → ↥N := fun x => ⟨t * (x : G) * t⁻¹, htN' x x.2⟩
  let σfun : α → α := Quotient.map' τ (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have hmem : τ (a⁻¹ * b) ∈ M' := by
      show t * (((a⁻¹ * b : ↥N) : G)) * t⁻¹ ∈ M
      exact htM _ hab
    have heq : (τ a)⁻¹ * τ b = τ (a⁻¹ * b) := by
      apply Subtype.ext
      simp only [τ, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      group
    rw [heq]
    exact hmem)
  have hτ_inv : Function.Involutive τ := fun x => by
    apply Subtype.ext
    simp only [τ, Subtype.coe_mk]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    calc t * (t * (x : G) * t⁻¹) * t⁻¹
        = (t * t) * (x : G) * (t⁻¹ * t⁻¹) := by group
      _ = (t * t) * (x : G) * (t * t) := by rw [htinv]
      _ = (x : G) := by rw [ht, one_mul, mul_one]
  have hσ_inv : Function.Involutive σfun := fun q => by
    induction q using Quotient.inductionOn' with
    | h x => simp only [σfun, Quotient.map'_mk'', hτ_inv x]
  let σ : Equiv.Perm α := Equiv.ofBijective σfun hσ_inv.bijective
  have hσ2 : σ ^ 2 = 1 := by
    ext q
    show σfun (σfun q) = q
    exact hσ_inv q
  have hcard : 2 ∣ Fintype.card α := by
    have hidx : Fintype.card α = M'.index :=
      (Nat.card_eq_fintype_card).symm.trans (Subgroup.index_eq_card (H := M')).symm
    have hlt : 1 < M'.index :=
      Subgroup.one_lt_index_of_ne_top fun h =>
        not_le_of_gt hM_lt_N (Subgroup.subgroupOf_eq_top.mp h)
    rcases (hN2.to_quotient M').card_eq_or_dvd with h1 | h1
    · exfalso
      have hne : Nat.card α ≠ 1 := by
        rw [Nat.card_eq_fintype_card, hidx]
        exact hlt.ne'
      exact hne h1
    · rwa [Nat.card_eq_fintype_card] at h1
  let a : α := QuotientGroup.mk (1 : ↥N)
  have hτ1 : τ (1 : ↥N) = 1 := by
    apply Subtype.ext
    simp only [τ, Subtype.coe_mk, Subgroup.coe_one]
    group
  have ha : σ a = a := by
    change σfun (QuotientGroup.mk (1 : ↥N)) = QuotientGroup.mk (1 : ↥N)
    simp only [σfun, Quotient.map'_mk'', hτ1]
  obtain ⟨b, hb_fixed, hba⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hcard
    (show σ ^ 2 ^ 1 = 1 by simpa using hσ2) ha
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective b
  refine ⟨(x : G), x.2.1, ?_, ?_, ?_⟩
  · intro hxM
    have hxM' : x ∈ M' := hxM
    have hxa : QuotientGroup.mk x = a := by
      change QuotientGroup.mk x = QuotientGroup.mk (1 : ↥N)
      exact QuotientGroup.eq.mpr (by simpa using M'.inv_mem hxM')
    exact hba (hx.symm.trans hxa)
  · intro m hm
    exact (Subgroup.mem_normalizer_iff.mp x.2.2 m).mp hm
  · have hfix : σfun (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [hx]; exact hb_fixed
    have hrel : ((τ x)⁻¹ * x : ↥N) ∈ M' := by
      have h2 : ((τ x : ↥N) : α) = ((x : ↥N) : α) := by
        simpa only [σfun, Quotient.map'_mk''] using hfix
      exact QuotientGroup.eq.mp h2
    set w : G := (((τ x)⁻¹ * x : ↥N) : G) with hw
    have hwM : w ∈ M := by rw [hw]; exact hrel
    have hτx_eq : (τ x : G) = (x : G) * w⁻¹ := by
      have h1 : ((τ x : G))⁻¹ * (x : G) = w := by rw [hw]; rfl
      rw [← h1]; group
    have hcomm_eq : ⁅t, (x : G)⁆ = (x : G) * w⁻¹ * (x : G)⁻¹ := by
      rw [commutatorElement_def, ← show (τ x : G) = t * (x : G) * t⁻¹ from rfl, hτx_eq]
    have hmem : (x : G) * w⁻¹ * (x : G)⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp x.2.2 w⁻¹).mp (M.inv_mem hwM)
    rwa [hcomm_eq]

theorem isPGroup_of_prime_order_mem {p : ℕ} [Fact p.Prime] {X K : Subgroup G}
    (hK : IsPGroup p K) (hKX : K ≤ X)
    (h : ∀ x ∈ X, ∀ q : ℕ, q.Prime → q ≠ p → x ^ q = 1 → x ∈ K) : IsPGroup p X := by
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd ?_ ?_)
  · exact Nat.card_ne_zero.mpr ⟨⟨1, X.one_mem⟩, inferInstance⟩
  · intro d hdprime hddvd
    haveI : Fact d.Prime := ⟨hdprime⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' d hddvd
    have hxq : (x : G) ^ d = 1 := by
      rw [← hxord, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
    by_contra hdp
    have hxK : (x : G) ∈ K := h (x : G) x.2 d hdprime hdp hxq
    obtain ⟨k, hk⟩ := hK.exists_orderOf_eq_pow (⟨(x : G), hxK⟩ : ↥K)
    rw [Subgroup.orderOf_mk] at hk
    have hd : d = p ^ k := by rw [← hxord, ← Subgroup.orderOf_coe, hk]
    have hdvd : d ∣ p ^ k := ⟨1, by rw [hd, mul_one]⟩
    exact hdp (Nat.prime_eq_prime_of_dvd_pow hdprime (Fact.out : p.Prime) hdvd)

theorem comm_mem_of_odd_pow_eq_one {X W M : Subgroup G} {t : G} (hMW : M ≤ W)
    (hMn : ∀ w ∈ W, ∀ m ∈ M, w * m * w⁻¹ ∈ M) (hab : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ M)
    (hsq : ∀ w ∈ W, w ^ 2 ∈ M) (hX : ∀ x ∈ X, ∀ w ∈ W, ⁅x, w⁆ ∈ M)
    (hc : ∀ x ∈ X, ⁅x, t⁆ ∈ W) {x : G} (hx : x ∈ X) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) :
    ⁅x, t⁆ ∈ M := by
  have hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro w hw
    have h := hX x hx w hw
    rw [commutatorElement_def] at h
    have : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact W.mul_mem (hMW h) hw
  have hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    intro m hm
    have h := hX x hx m (hMW hm)
    rw [commutatorElement_def] at h
    have : x * m * x⁻¹ = (x * m * x⁻¹ * m⁻¹) * m := by group
    rw [this]
    exact M.mul_mem h hm
  have hn1 : (⁅x, t⁆)⁻¹ * x * ⁅x, t⁆ * x⁻¹ ∈ M := by
    have h := hX x hx ⁅x, t⁆ (hc x hx)
    rw [commutatorElement_def] at h
    have heq : (⁅x, t⁆)⁻¹ * x * ⁅x, t⁆ * x⁻¹
        = (⁅x, t⁆)⁻¹ * (x * ⁅x, t⁆ * x⁻¹ * (⁅x, t⁆)⁻¹) * ⁅x, t⁆ := by group
    rw [heq]
    simpa using hMn _ (W.inv_mem (hc x hx)) _ h
  have hnk : ∀ k : ℕ, (⁅x, t⁆)⁻¹ * x ^ k * ⁅x, t⁆ * (x ^ k)⁻¹ ∈ M := by
    intro k
    induction k with
    | zero =>
      show (⁅x, t⁆)⁻¹ * x ^ 0 * ⁅x, t⁆ * (x ^ 0)⁻¹ ∈ M
      simp only [pow_zero, mul_one, inv_one, inv_mul_cancel]
      exact M.one_mem
    | succ k ih =>
      rw [pow_succ', mul_inv_rev]
      have heq : (⁅x, t⁆)⁻¹ * (x * x ^ k) * ⁅x, t⁆ * ((x ^ k)⁻¹ * x⁻¹)
          = ((⁅x, t⁆)⁻¹ * x * ⁅x, t⁆ * x⁻¹)
            * (x * ((⁅x, t⁆)⁻¹ * x ^ k * ⁅x, t⁆ * (x ^ k)⁻¹) * x⁻¹) := by
        group
      rw [heq]
      exact M.mul_mem hn1 (hxM _ ih)
  have hAk : ∀ k : ℕ, ⁅x ^ k, t⁆ * ((⁅x, t⁆) ^ k)⁻¹ ∈ M := by
    intro k
    induction k with
    | zero => simp [commutatorElement_def]
    | succ k ih =>
      have hx_succ : x ^ (k + 1) = x ^ k * x := pow_succ x k
      have hc_succ : (⁅x, t⁆) ^ (k + 1) = ⁅x, t⁆ * (⁅x, t⁆) ^ k := pow_succ' ⁅x, t⁆ k
      rw [hx_succ, hc_succ, mul_inv_rev]
      have heq : ⁅x ^ k * x, t⁆ * (((⁅x, t⁆) ^ k)⁻¹ * (⁅x, t⁆)⁻¹)
          = ⁅x, t⁆ * (((⁅x, t⁆)⁻¹ * x ^ k * ⁅x, t⁆ * (x ^ k)⁻¹)
              * (⁅x ^ k, t⁆ * ((⁅x, t⁆) ^ k)⁻¹)) * (⁅x, t⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact hMn _ (hc x hx) _ (M.mul_mem (hnk k) ih)
  have hAn := hAk n
  have hxnt : ⁅x ^ n, t⁆ = 1 := by rw [hxn]; simp [commutatorElement_def]
  rw [hxnt, one_mul] at hAn
  have hcxpow : (⁅x, t⁆) ^ n ∈ M := by simpa using M.inv_mem hAn
  obtain ⟨m, hm⟩ := hn
  have hsplit : (⁅x, t⁆) ^ n = ⁅x, t⁆ * ((⁅x, t⁆) ^ 2) ^ m := by
    rw [hm, pow_succ', pow_mul]
  have hcx2 : (⁅x, t⁆) ^ 2 ∈ M := hsq _ (hc x hx)
  have hpow2 : ((⁅x, t⁆) ^ 2) ^ m ∈ M := M.pow_mem hcx2 m
  exact (M.mul_mem_cancel_right hpow2).mp (hsplit ▸ hcxpow)

end CFSG.OddStandard.HigherRank.YamadaG23
