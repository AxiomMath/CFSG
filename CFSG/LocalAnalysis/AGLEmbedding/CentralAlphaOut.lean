module

public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_sup_left_eq_of_normal (K H : Subgroup G) [K.Normal] :
    H.relIndex (K ⊔ H) = H.relIndex K := by
  have h1 := Subgroup.relIndex_mul_relIndex (K ⊓ H) H (K ⊔ H) inf_le_right le_sup_right
  have h2 := Subgroup.relIndex_mul_relIndex (K ⊓ H) K (K ⊔ H) inf_le_left le_sup_left
  rw [Subgroup.inf_relIndex_right] at h1
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_sup_left] at h2
  have hpos : 0 < K.relIndex H :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card K H) Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (h2.symm.trans (mul_comm _ _)))

theorem not_dvd_relIndex_sylow_of_normal {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (N : Subgroup G) [N.Normal] : ¬ p ∣ (P : Subgroup G).relIndex N := by
  rw [← relIndex_sup_left_eq_of_normal N (P : Subgroup G)]
  exact fun h => P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))

theorem le_inf_sup_of_le_sup_of_normal {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {K C : Subgroup G} [K.Normal] [C.Normal] (hP : (P : Subgroup G) ≤ K ⊔ C) :
    (P : Subgroup G) ≤ (P : Subgroup G) ⊓ K ⊔ C := by
  set H : Subgroup G := (P : Subgroup G) ⊓ K ⊔ C with hH
  have hKH : K ⊔ H = K ⊔ C := by
    rw [hH, ← sup_assoc, sup_eq_left.mpr (inf_le_right : (P : Subgroup G) ⊓ K ≤ K)]
  have hcop : ¬ p ∣ H.relIndex (K ⊔ C) := by
    rw [← hKH, relIndex_sup_left_eq_of_normal]
    intro h
    refine not_dvd_relIndex_sylow_of_normal P K ?_
    rw [← Subgroup.inf_relIndex_right]
    exact h.trans (Subgroup.relIndex_dvd_of_le_left K le_sup_left)
  have hHS : H ≤ (P : Subgroup G) ⊔ C := sup_le_sup_right inf_le_left C
  have hSKC : (P : Subgroup G) ⊔ C ≤ K ⊔ C := sup_le hP le_sup_right
  have hdvd : H.relIndex ((P : Subgroup G) ⊔ C) ∣ H.relIndex (K ⊔ C) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex H _ _ hHS hSKC)
  have hpow : H.relIndex ((P : Subgroup G) ⊔ C) ∣ Nat.card (P : Subgroup G) := by
    refine (Subgroup.relIndex_dvd_of_le_left _ (le_sup_right : C ≤ H)).trans ?_
    rw [Subgroup.relIndex_sup_right]
    exact Subgroup.relIndex_dvd_card C P
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  rw [hn, Nat.dvd_prime_pow Fact.out] at hpow
  obtain ⟨j, -, hj⟩ := hpow
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hdvd
    exact hcop ((dvd_pow_self p hj0).trans hdvd)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_sup_left.trans hj

omit [Finite G] in
theorem exists_mul_eq_of_le_inf_sup {P K C : Subgroup G} [C.Normal] (hP : P ≤ P ⊓ K ⊔ C)
    {r : G} (hr : r ∈ P) : ∃ t ∈ P ⊓ K, ∃ c ∈ P ⊓ C, t * c = r := by
  have h : r ∈ ((P ⊓ K ⊔ C : Subgroup G) : Set G) := hP hr
  rw [Subgroup.mul_normal, Set.mem_mul] at h
  obtain ⟨t, ht, c, hc, rfl⟩ := h
  exact ⟨t, ht, c, ⟨by simpa using P.mul_mem (P.inv_mem ht.1) hr, hc⟩, rfl⟩

end Sylow

section OutTwo

variable {X : Type} [Group X] {p : ℕ}

theorem exists_inv_mul_mem_centralizer_of_kOutTwoGroup (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} [K.Normal] (hout : KOutTwoGroup K) {r : X} {n : ℕ} (hr : r ^ p ^ n = 1) :
    ∃ κ ∈ K, κ⁻¹ * r ∈ Subgroup.centralizer (K : Set X) := by
  set φ : MulAut K := MulAut.conjNormal r with hφ
  obtain ⟨k, hk⟩ := hout φ
  have hord : orderOf φ ∣ p ^ n :=
    (orderOf_map_dvd _ r).trans (orderOf_dvd_of_pow_eq_one hr)
  have hcop : (2 ^ k).Coprime (orderOf φ) :=
    Nat.Coprime.coprime_dvd_right hord
      (Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.mp (hm ▸ pow_mem hk m :
    φ ∈ (MulAut.conj : K →* MulAut K).range)
  refine ⟨κ, κ.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  have h := congrArg (fun f : MulAut K => ((f ⟨g, hg⟩ : K) : X)) hκ
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hφ,
    MulAut.conjNormal_apply] at h
  calc g * ((κ : X)⁻¹ * r) = (κ : X)⁻¹ * ((κ : X) * g * (κ : X)⁻¹) * r := by group
    _ = (κ : X)⁻¹ * (r * g * r⁻¹) * r := by rw [h]
    _ = (κ : X)⁻¹ * r * g := by group

theorem le_sup_centralizer_of_kOutTwoGroup (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X}
    [K.Normal] (hout : KOutTwoGroup K) {R : Subgroup X} (hR : IsPGroup p R) :
    R ≤ K ⊔ Subgroup.centralizer (K : Set X) := by
  intro r hr
  obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
  obtain ⟨κ, hκK, hκC⟩ := exists_inv_mul_mem_centralizer_of_kOutTwoGroup hp hp2 hout
    (r := r) (n := n) (by simpa using congrArg Subtype.val hn)
  simpa using Subgroup.mul_mem_sup hκK hκC

theorem exists_mul_eq_of_kOutTwoGroup [Finite X] (hp : p.Prime) (hp2 : p ≠ 2) (R : Sylow p X)
    {K : Subgroup X} [K.Normal] (hout : KOutTwoGroup K) {r : X} (hr : r ∈ (R : Subgroup X)) :
    ∃ t ∈ (R : Subgroup X) ⊓ K,
      ∃ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), t * c = r := by
  have : Fact p.Prime := ⟨hp⟩
  exact exists_mul_eq_of_le_inf_sup (le_inf_sup_of_le_sup_of_normal R
    (le_sup_centralizer_of_kOutTwoGroup hp hp2 hout R.isPGroup')) hr

end OutTwo

section Outcomes

variable {X : Type*} [Group X] {p : ℕ}

theorem le_zpowers_of_le_centralizer_of_decomp (hp : p.Prime) {R K A : Subgroup X} {z : X}
    (hz : ∀ y ∈ R, y ∈ Subgroup.centralizer (R : Set X) → orderOf y = p →
      y ∈ Subgroup.zpowers z)
    (hdec : ∀ r ∈ R, ∃ t ∈ R ⊓ K, ∃ c ∈ R ⊓ Subgroup.centralizer (K : Set X), t * c = r)
    (hAT : A ≤ R ⊓ K) (hAC : A ≤ Subgroup.centralizer ((R ⊓ K : Subgroup X) : Set X))
    (hA : IsElemAbelian p A) : A ≤ Subgroup.zpowers z := by
  have : Fact p.Prime := ⟨hp⟩
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact one_mem _
  refine hz a (hAT ha).1 (Subgroup.mem_centralizer_iff.mpr fun r hr => ?_)
    (orderOf_eq_prime (hA.2 a ha) ha1)
  obtain ⟨t, ht, c, hc, rfl⟩ := hdec r hr
  have hta : t * a = a * t := Subgroup.mem_centralizer_iff.mp (hAC ha) t ht
  have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a (hAT ha).2
  rw [mul_assoc, ← hca, ← mul_assoc, hta, mul_assoc]

theorem mem_inf_of_pow_eq_one_of_decomp (hp : p.Prime) {R K : Subgroup X} {z : X}
    (hzR : z ∈ R) (hzK : z ∈ K)
    (hC : ∀ c ∈ R ⊓ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ Subgroup.zpowers z)
    (hdec : ∀ r ∈ R, ∃ t ∈ R ⊓ K, ∃ c ∈ R ⊓ Subgroup.centralizer (K : Set X), t * c = r)
    (hexp : ∀ t ∈ R ⊓ K, t ^ p = 1) {r : X} (hr : r ∈ R) (hrp : r ^ p = 1) : r ∈ R ⊓ K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, c, hc, rfl⟩ := hdec r hr
  have hcomm : Commute t c := Subgroup.mem_centralizer_iff.mp hc.2 t ht.2
  have hcp : c ^ p = 1 := by
    rwa [hcomm.mul_pow, hexp t ht, one_mul] at hrp
  by_cases hc1 : c = 1
  · rwa [hc1, mul_one]
  have hzT : Subgroup.zpowers z ≤ R ⊓ K := Subgroup.zpowers_le.mpr ⟨hzR, hzK⟩
  exact (R ⊓ K).mul_mem ht (hzT (hC c hc (orderOf_eq_prime hcp hc1)))

theorem le_normalizer_of_decomp {R K A : Subgroup X}
    (hdec : ∀ r ∈ R, ∃ t ∈ R ⊓ K, ∃ c ∈ R ⊓ Subgroup.centralizer (K : Set X), t * c = r)
    (hAK : A ≤ K) (hTN : R ⊓ K ≤ Subgroup.normalizer (A : Set X)) :
    R ≤ Subgroup.normalizer (A : Set X) := by
  intro r hr
  obtain ⟨t, ht, c, hc, rfl⟩ := hdec r hr
  exact Subgroup.mul_mem _ (hTN ht) (Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAK) hc.2))

end Outcomes

theorem false_of_outTwo {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (R : Sylow p X) (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) {K : Subgroup X} [K.Normal]
    {z : X} (hzR : z ∈ (R : Subgroup X)) (hzK : z ∈ K) (hzp : orderOf z = p)
    (hz : ∀ y ∈ (R : Subgroup X), y ∈ Subgroup.centralizer (R : Set X) → orderOf y = p →
      y ∈ Subgroup.zpowers z)
    (hC : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
      c ∈ Subgroup.zpowers z)
    (hout : KOutTwoGroup K)
    {v : X} (hvR : v ∈ (R : Subgroup X)) (hvp : orderOf v = p)
    (hv : Open.pRank p ((R : Subgroup X) ⊓ Subgroup.centralizer ({v} : Set X)) ≤ 2)
    (he : (∃ A : Subgroup X, A ≤ (R : Subgroup X) ⊓ K ∧
          A ≤ Subgroup.centralizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
          IsElemAbelian p A ∧ Nat.card A = p ^ 2) ∨
        ((∀ t ∈ (R : Subgroup X) ⊓ K, t ^ p = 1) ∧
          Open.pRank p ((R : Subgroup X) ⊓ K) ≤ 3) ∨
        (∃ A : Subgroup X, A ≤ (R : Subgroup X) ⊓ K ∧
          (R : Subgroup X) ⊓ K ≤ Subgroup.normalizer (A : Set X) ∧ IsElemAbelian p A ∧
          p ^ (p + 1) ≤ Nat.card A)) :
    False := by
  have hdec : ∀ r ∈ (R : Subgroup X), ∃ t ∈ (R : Subgroup X) ⊓ K,
      ∃ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), t * c = r :=
    fun r hr => exists_mul_eq_of_kOutTwoGroup hp hp2 R hout hr
  rcases he with ⟨A, hAT, hAC, hA, hAcard⟩ | ⟨hexp, hrank⟩ | ⟨A, hAT, hTN, hA, hAcard⟩
  · have hle := Subgroup.card_le_of_le
      (le_zpowers_of_le_centralizer_of_decomp hp hz hdec hAT hAC hA)
    rw [Nat.card_zpowers, hzp, hAcard] at hle
    have := hp.two_le
    nlinarith
  · obtain ⟨E, hER, hE, hEcard⟩ := pRank_attained p hp (R : Subgroup X)
    have hET : E ≤ (R : Subgroup X) ⊓ K := fun e he =>
      mem_inf_of_pow_eq_one_of_decomp hp hzR hzK hC hdec hexp (hER he) (hE.2 e he)
    have hle : Open.pRank p (R : Subgroup X) ≤ Open.pRank p ((R : Subgroup X) ⊓ K) :=
      le_csSup (pRank_bddAbove p hp _) ⟨E, hET, hE, hEcard⟩
    omega
  · have hle := card_le_of_normal_elemAbelian_of_pRank_centralizer_le_two hp
      (hAT.trans inf_le_left) (le_normalizer_of_decomp hdec (hAT.trans inf_le_right) hTN) hA
      hvR (by rw [← hvp]; exact pow_orderOf_eq_one v) hv
    have := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_add_one p)
    omega

end CFSG.AGLEmbedding
