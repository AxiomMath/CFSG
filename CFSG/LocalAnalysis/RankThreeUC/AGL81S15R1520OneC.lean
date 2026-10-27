module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Subgroup

theorem exists_complement_normalizer_sylow {A : Type*} [Group A] [Finite A] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p A) :
    ∃ C : Subgroup A, C ≤ normalizer (Q : Set A) ∧ ¬ p ∣ Nat.card C ∧
      ∀ r ∈ normalizer (Q : Set A), ∃ q ∈ (Q : Subgroup A), ∃ c ∈ C, r = q * c := by
  have hQR : (Q : Subgroup A) ≤ normalizer (Q : Set A) := le_normalizer
  set N : Subgroup ↥(normalizer (Q : Set A)) := (Q : Subgroup A).subgroupOf (normalizer (Q : Set A))
    with hN
  haveI : N.Normal := (normal_subgroupOf_iff_le_normalizer hQR).2 le_rfl
  have hNcard : Nat.card ↥N = Nat.card ↥(Q : Subgroup A) :=
    Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv
  have hidx : ¬ p ∣ N.index := fun h =>
    Q.not_dvd_index (h.trans (relIndex_dvd_index_of_le hQR))
  have hcop : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hNcard]
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hidx)
  obtain ⟨H, hH⟩ := exists_right_complement'_of_coprime hcop
  refine ⟨H.map (normalizer (Q : Set A)).subtype, map_subtype_le H, ?_, ?_⟩
  · rw [← Nat.card_congr
      (H.equivMapOfInjective _ (normalizer (Q : Set A)).subtype_injective).toEquiv]
    have h1 := hH.card_mul_card
    have h2 := N.card_mul_index
    have h3 : Nat.card H = N.index := Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
    rw [h3]
    exact hidx
  · intro r hr
    obtain ⟨⟨n, c⟩, hnc⟩ := hH.2 ⟨r, hr⟩
    have hval : (n : ↥(normalizer (Q : Set A))) * (c : ↥(normalizer (Q : Set A))) = ⟨r, hr⟩ := hnc
    have hr' : r = ((n : ↥(normalizer (Q : Set A))) : A) * ((c : ↥(normalizer (Q : Set A))) : A) :=
      (congrArg Subtype.val hval).symm
    exact ⟨_, mem_subgroupOf.1 n.2, _, ⟨c, c.2, rfl⟩, hr'⟩

theorem le_of_isPGroup_of_not_dvd_index {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    {Q B : Subgroup A} [B.Normal] (hQ : IsPGroup p Q) (hB : ¬ p ∣ B.index) : Q ≤ B := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have h1 : B.relIndex Q ∣ p ^ k := hk ▸ relIndex_dvd_card B Q
  have h2 : B.relIndex (Q ⊔ B) ∣ B.index := relIndex_dvd_index_of_le le_sup_right
  rw [sup_comm, relIndex_sup_left] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).1 h1
  have hj0 : j = 0 := by
    by_contra hne
    exact hB ((dvd_pow_self p hne).trans (hj ▸ h2))
  exact relIndex_eq_one.1 (by rw [hj, hj0, pow_zero])

theorem relIndex_sup_left_of_normal {K : Type*} [Group K] [Finite K] (B₀ D : Subgroup K)
    [B₀.Normal] : D.relIndex (B₀ ⊔ D) = (B₀ ⊓ D).relIndex B₀ := by
  have h1 := relIndex_mul_relIndex (B₀ ⊓ D) D (B₀ ⊔ D) inf_le_right le_sup_right
  have h2 := relIndex_mul_relIndex (B₀ ⊓ D) B₀ (B₀ ⊔ D) inf_le_left le_sup_left
  rw [inf_relIndex_right] at h1
  rw [relIndex_sup_left] at h2
  have hne : B₀.relIndex D ≠ 0 := index_ne_zero_of_finite
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (h1.trans (h2.symm.trans (mul_comm _ _)))

theorem not_two_dvd_index_of_sup_eq_top {K : Type*} [Group K] [Finite K] {S B₀ D : Subgroup K}
    [B₀.Normal] (hSD : S ≤ D) (hSB : S ≤ B₀) (hsup : B₀ ⊔ D = ⊤)
    (hS : ¬ 2 ∣ S.relIndex B₀) : ¬ 2 ∣ D.index := by
  have h2 := relIndex_sup_left_of_normal B₀ D
  rw [hsup, relIndex_top_right] at h2
  have h3 : (B₀ ⊓ D).relIndex B₀ ∣ S.relIndex B₀ :=
    relIndex_dvd_of_le_left B₀ (le_inf hSB hSD)
  rw [← h2] at h3
  exact fun h => hS (h.trans h3)

theorem card_sup_dvd_mul_of_normal {K : Type*} [Group K] (S C : Subgroup K) [S.Normal] :
    Nat.card ↥(S ⊔ C) ∣ Nat.card S * Nat.card C := by
  have h1 := relIndex_mul_card S (S ⊔ C)
  rw [inf_sup_self, relIndex_sup_left] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_dvd_mul_left _ (relIndex_dvd_card S C)

theorem exists_threePrime_cover {K : Type*} [Group K] [Finite K] {S B₀ : Subgroup K}
    [S.Normal] [B₀.Normal] (hSB : S ≤ B₀) (hS : IsPGroup 2 S) (hS2 : ¬ 2 ∣ S.relIndex B₀)
    (h3 : ¬ 3 ∣ B₀.index) :
    ∃ D : Subgroup K, S ≤ D ∧ ¬ 3 ∣ Nat.card D ∧ B₀ ⊔ D = ⊤ ∧ ¬ 2 ∣ D.index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hQB : (Q : Subgroup K) ≤ B₀ := le_of_isPGroup_of_not_dvd_index Q.isPGroup' h3
  have hfr : normalizer (Q : Set K) ⊔ B₀ = ⊤ := Sylow.normalizer_sup_eq_top' Q hQB
  obtain ⟨C, hCR, hC3, hRC⟩ := exists_complement_normalizer_sylow Q
  have hsup : B₀ ⊔ (S ⊔ C) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hfr]
    refine sup_le ?_ le_sup_left
    intro r hr
    obtain ⟨q, hq, c, hc, rfl⟩ := hRC r hr
    exact mul_mem_sup (hQB hq) ((le_sup_right : C ≤ S ⊔ C) hc)
  refine ⟨S ⊔ C, le_sup_left, ?_, hsup, not_two_dvd_index_of_sup_eq_top le_sup_left hSB hsup hS2⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have h2 : ¬ 3 ∣ Nat.card S := by
    rw [hk]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  exact fun h => (Nat.Prime.dvd_mul Nat.prime_three).1 ((h.trans (card_sup_dvd_mul_of_normal S C)))
    |>.elim h2 hC3

theorem exists_threePrime_cover_of_normalizes {M : Type*} [Group M] [Finite M]
    {K S B₀ : Subgroup M} (hSB : S ≤ B₀) (hBK : B₀ ≤ K)
    (hSn : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S) (hBn : ∀ k ∈ K, ∀ b ∈ B₀, k * b * k⁻¹ ∈ B₀)
    (hS : IsPGroup 2 S) (hS2 : ¬ 2 ∣ S.relIndex B₀) (h3 : ¬ 3 ∣ B₀.relIndex K) :
    ∃ D : Subgroup M, S ≤ D ∧ D ≤ K ∧ ¬ 3 ∣ Nat.card D ∧ B₀ ⊔ D = K ∧ ¬ 2 ∣ D.relIndex K := by
  have hSK : S ≤ K := hSB.trans hBK
  haveI hSN : (S.subgroupOf K).Normal := ⟨fun n hn g => hSn g g.2 n hn⟩
  haveI hBN : (B₀.subgroupOf K).Normal := ⟨fun n hn g => hBn g g.2 n hn⟩
  obtain ⟨D₁, hSD₁, hD₃, hsup, hodd⟩ := exists_threePrime_cover
    (S := S.subgroupOf K) (B₀ := B₀.subgroupOf K) (fun x hx => hSB hx) hS.comap_subtype
    (by rwa [relIndex_subgroupOf hBK]) h3
  have hinj : Function.Injective K.subtype := K.subtype_injective
  refine ⟨D₁.map K.subtype, ?_, map_subtype_le D₁, ?_, ?_, ?_⟩
  · rw [← map_subgroupOf_eq_of_le hSK]
    exact map_mono hSD₁
  · rw [← Nat.card_congr (D₁.equivMapOfInjective _ hinj).toEquiv]
    exact hD₃
  · have := congrArg (Subgroup.map K.subtype) hsup
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hBK, Subgroup.map_top, range_subtype] at this
  · rw [relIndex]
    change ¬ 2 ∣ ((D₁.map K.subtype).comap K.subtype).index
    rwa [comap_map_eq_self_of_injective hinj]

theorem not_dvd_relIndex_inf_normal {M : Type*} [Group M] [Finite M] {p : ℕ} {T W : Subgroup M}
    [W.Normal] (hT : ¬ p ∣ T.index) : ¬ p ∣ (T ⊓ W).relIndex W := by
  have h := relIndex_sup_left_of_normal W T
  rw [inf_comm] at h
  rw [← h]
  exact fun hd => hT (hd.trans (relIndex_dvd_index_of_le le_sup_right))

theorem normalizer_sup_eq_top_of_sylow {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {S W : Subgroup M} [W.Normal] (hSW : S ≤ W) (hS : IsPGroup p S) (hSi : ¬ p ∣ S.relIndex W) :
    normalizer (S : Set M) ⊔ W = ⊤ := by
  have hS' : IsPGroup p (S.subgroupOf W) := hS.comap_subtype
  have hSi' : ¬ p ∣ (S.subgroupOf W).index := hSi
  have h := Sylow.normalizer_sup_eq_top (hS'.toSylow hSi')
  rwa [show ((hS'.toSylow hSi' : Subgroup W)).map W.subtype = S by
    rw [IsPGroup.toSylow_coe, map_subgroupOf_eq_of_le hSW]] at h

theorem exists_conj_le_of_not_dvd_index {M : Type*} [Group M] [Finite M] {T D : Subgroup M}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hD : ¬ 2 ∣ D.index) :
    ∃ g : M, ∀ x ∈ T, g⁻¹ * x * g ∈ D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  have hR : IsPGroup 2 ((R₀ : Subgroup ↥D).map D.subtype) := R₀.isPGroup'.map D.subtype
  have hRi : ¬ 2 ∣ ((R₀ : Subgroup ↥D).map D.subtype).index := by
    rw [index_map_subtype]
    exact fun h => ((Nat.Prime.dvd_mul Nat.prime_two).1 h).elim R₀.not_dvd_index hD
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (hR.toSylow hRi) (hT.toSylow hTi)
  refine ⟨g, fun x hx => ?_⟩
  have hx' : x ∈ ((g • hR.toSylow hRi : Sylow 2 M) : Subgroup M) := by
    rw [hg, IsPGroup.toSylow_coe]
    exact hx
  rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, mem_pointwise_smul_iff_inv_smul_mem] at hx'
  have : g⁻¹ * x * g ∈ (R₀ : Subgroup ↥D).map D.subtype := by simpa [MulAut.conj_apply] using hx'
  exact map_subtype_le _ this

end CFSG.LocalAnalysis.RankThreeUC.S15
