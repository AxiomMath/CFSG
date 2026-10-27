module

public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.Open.Defs

public section

namespace CFSG.AGLEmbedding

theorem coprime_le_centralizer_of_forall_pow_eq_one {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Q L : Subgroup X} (hQ : IsPGroup p Q)
    (hL : Nat.Coprime (Nat.card L) (Nat.card Q))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set X))
    (hfix : ∀ y ∈ L, ∀ x ∈ Q, x ^ p = 1 → y * x = x * y) :
    L ≤ Subgroup.centralizer (Q : Set X) := by
  let _ : MulDistribMulAction L Q :=
    MulDistribMulAction.compHom Q (Q.normalizerMonoidHom.comp (Subgroup.inclusion hLQ))
  have : Fact (IsPGroup p Q) := ⟨hQ⟩
  have hsmul : ∀ (a : L) (x : Q), ((a • x : Q) : X) = a * x * (a : X)⁻¹ := fun _ _ => rfl
  have hΩ : ActsTriviallyOnSubgroup L Q (omega₁ Q (p := p)) := by
    intro a x hx
    change x ∈ Subgroup.closure {x : Q | x ^ (p ^ 1) = 1} at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      apply Subtype.ext
      have hx' : (x : X) ^ p = 1 := by
        have h1 : x ^ (p ^ 1) = 1 := hx
        rw [pow_one] at h1
        simpa using congrArg Subtype.val h1
      rw [hsmul, hfix a a.2 x x.2 hx', mul_inv_cancel_right]
    | one => exact smul_one a
    | mul x y _ _ hx hy => rw [smul_mul', hx, hy]
    | inv x _ hx => rw [smul_inv', hx]
  have htriv := theorem_1_11 (G := Q) (A := L) hp2 hL hΩ
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := congrArg Subtype.val (htriv ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hsmul] at h1
  calc x * y = y * x * y⁻¹ * y := by rw [h1]
    _ = y * x := by group

theorem isPGroup_automizer_of_forall_orderOf_eq_mem_center {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hall : ∀ t : K, orderOf t = p → t ∈ Subgroup.center K) (Q : Subgroup K)
    (hQ : IsPGroup p Q) :
    IsPGroup p (Subgroup.normalizer (Q : Set K) ⧸
      (Subgroup.centralizer (Q : Set K)).subgroupOf (Subgroup.normalizer (Q : Set K))) := by
  have hp : p.Prime := Fact.out
  set N := Subgroup.normalizer (Q : Set K)
  set C := (Subgroup.centralizer (Q : Set K)).subgroupOf N
  have hprimes : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card (N ⧸ C) → q = p := by
    intro q hq hdvd
    by_contra hqp
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨S⟩ : Nonempty (Sylow q N) := inferInstance
    apply (S.mapSurjective (QuotientGroup.mk'_surjective C)).ne_bot_of_dvd_card hdvd
    rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (S.isPGroup'.map N.subtype)
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hQ
    have hcent := coprime_le_centralizer_of_forall_pow_eq_one hp2 hQ
      (L := (S : Subgroup N).map N.subtype)
      (by rw [ha, hb]; exact Nat.coprime_pow_primes a b hq hp hqp) (Subgroup.map_subtype_le _)
      (by
        intro y _ x _ hx
        rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hx) with h1 | h1
        · rw [orderOf_eq_one_iff.mp h1, mul_one, one_mul]
        · exact Subgroup.mem_center_iff.mp (hall x h1) y)
    intro s hs
    exact Subgroup.mem_subgroupOf.mpr (hcent ⟨s, hs, rfl⟩)
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprimes)

theorem exists_orderOf_eq_not_mem_center {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hK : Open.IsQuasisimple K)
    (hdvd : p ∣ Nat.card (K ⧸ Subgroup.center K)) :
    ∃ t : K, orderOf t = p ∧ t ∉ Subgroup.center K := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra! hall
  obtain ⟨N, hNn, hNcop, k, hk⟩ := (GroupTheory.frobenius_normal_p_complement (G := K) p).1.2
    (isPGroup_automizer_of_forall_orderOf_eq_mem_center hodd hall)
  have : N.Normal := hNn
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have hquot : IsPGroup p (K ⧸ N) := IsPGroup.of_card (n := k) (by
      rw [← Subgroup.index_eq_card]
      exact hk)
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hquot.isNilpotent
  rw [hNtop, Subgroup.card_top] at hNcop
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hNcop.symm
    (hdvd.trans (Subgroup.card_quotient_dvd_card _))

theorem exists_mem_sylow_orderOf_eq_not_mem_center {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hK : Open.IsQuasisimple K)
    (hdvd : p ∣ Nat.card (K ⧸ Subgroup.center K)) (T : Sylow p K) :
    ∃ t ∈ (T : Subgroup K), orderOf t = p ∧ t ∉ Subgroup.center K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, htZ⟩ := exists_orderOf_eq_not_mem_center hp hodd hK hdvd
  have hZ : IsPGroup p (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hP⟩ := hZ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K T P
  have htmem : t ∈ ((g • T : Sylow p K) : Subgroup K) := hP (Subgroup.mem_zpowers t)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at htmem
  refine ⟨_, htmem, ?_, fun hc => htZ ?_⟩
  · rw [MulAut.smul_def, ← ht]
    exact MulEquiv.orderOf_eq _ t
  · have heq : t = (MulAut.conj g) ((MulAut.conj g)⁻¹ • t) := by
      rw [MulAut.smul_def, MulAut.apply_inv_self]
    rw [heq, MulAut.conj_apply, Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
    exact hc

end CFSG.AGLEmbedding
