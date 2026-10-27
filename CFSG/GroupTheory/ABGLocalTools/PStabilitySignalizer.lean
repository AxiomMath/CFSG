module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
import CFSG.GroupTheory.ABGLocalTools.Criteria
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] {p : ℕ}

section Coprime

variable [Finite H]

theorem exists_invariant_isSylowOf_ge_of_coprime {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {A K P : Subgroup H} (hA : IsPGroup q A) (hAK : A ≤ normalizer (K : Set H))
    (hK : ¬ q ∣ Nat.card K) (hPK : P ≤ K) (hP : IsPGroup r P)
    (hAP : A ≤ normalizer (P : Set H)) :
    ∃ R : Subgroup H, IsSylowOf r R K ∧ P ≤ R ∧ A ≤ normalizer (R : Set H) := by
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A K hAK
  obtain ⟨Q, hPQ, hQ⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing q r hq hr hA
    ((Nat.Prime.coprime_iff_not_dvd hq).mpr hK) (P.subgroupOf K) hP.comap_subtype
    (CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_subgroup A K P hAK hAP)
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hPQ
  · apply CFSG.SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A K hAK
    change ∀ a : A, ∀ x ∈ (Q : Subgroup K), a • x ∈ (Q : Subgroup K)
    intro a x hx
    have hmem := Subgroup.smul_mem_pointwise_smul x a (Q : Subgroup K) hx
    rwa [← Sylow.pointwise_smul_def, hQ a] at hmem

end Coprime

section Maximal

variable [Finite H] [Fact p.Prime]

omit [Finite H] in
theorem inf_eq_bot_of_isPGroup_two (hp : p ≠ 2) {Q D : Subgroup H} (hQ : IsPGroup p Q)
    (hD : IsPGroup 2 D) : Q ⊓ D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp Q D hQ hD)

omit [Finite H] in
theorem IsMaximalPSignalizer.eq_of_le (hp : p ≠ 2) {D R Q : Subgroup H} (hD : IsPGroup 2 D)
    (hR : IsMaximalPSignalizer D p R) (hRQ : R ≤ Q) (hQ : IsPGroup p Q)
    (hDQ : D ≤ normalizer (Q : Set H)) : Q = R :=
  hR.2 Q ⟨hQ, hDQ, inf_eq_bot_of_isPGroup_two hp hQ hD⟩ hRQ

theorem IsMaximalPSignalizer.isSylowOf_of_odd (hp : p ≠ 2) {D R W : Subgroup H}
    (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (hRW : R ≤ W)
    (hW : Odd (Nat.card W)) (hDW : D ≤ normalizer (W : Set H)) : IsSylowOf p R W := by
  obtain ⟨Q, hQ, hRQ, hDQ⟩ := exists_invariant_isSylowOf_ge_of_coprime Nat.prime_two Fact.out hD
    hDW hW.not_two_dvd_nat hRW hR.1.1 hR.1.2.1
  rwa [hR.eq_of_le hp hD hRQ hQ.isPGroup hDQ] at hQ

theorem odd_card_sup_oddCore (hp : p ≠ 2) {R : Subgroup H} (hR : IsPGroup p R) :
    Odd (Nat.card (R ⊔ oddCore H : Subgroup H)) := by
  have hpp : p.Prime := Fact.out
  have h1 := Subgroup.relIndex_mul_card (oddCore H) (R ⊔ oddCore H)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_right] at h1
  rw [← h1]
  refine Odd.mul ?_ (odd_card_oddCore (H := H))
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : (oddCore H).relIndex R ∣ p ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp).mp hdvd
  rw [hj]
  exact (hpp.odd_of_ne_two hp).pow

theorem IsMaximalPSignalizer.isSylowOf_sup_oddCore (hp : p ≠ 2) {D R : Subgroup H}
    (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) :
    IsSylowOf p R (R ⊔ oddCore H) := by
  refine hR.isSylowOf_of_odd hp hD le_sup_left (odd_card_sup_oddCore hp hR.1.1) ?_
  refine le_trans (le_inf hR.1.2.1 ?_) (inf_normalizer_le_normalizer_sup R (oddCore H))
  rw [normalizer_eq_top]
  exact le_top

theorem IsMaximalPSignalizer.isSylowOf_inf_oddCore (hp : p ≠ 2) {D R : Subgroup H}
    (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) :
    IsSylowOf p (R ⊓ oddCore H) (oddCore H) :=
  (hR.isSylowOf_sup_oddCore hp hD).inf_of_le_normalizer le_sup_right
    (by rw [normalizer_eq_top]; exact le_top)

theorem IsMaximalPSignalizer.isSylowOf_inf_of_le_oddCore (hp : p ≠ 2) {D R N : Subgroup H}
    [N.Normal] (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (hN : N ≤ oddCore H) :
    IsSylowOf p (R ⊓ N) N := by
  have h := (hR.isSylowOf_inf_oddCore hp hD).inf_of_le_normalizer hN
    (by rw [normalizer_eq_top]; exact le_top)
  rwa [inf_assoc, inf_eq_right.mpr hN] at h

theorem IsMaximalPSignalizer.isSylowOf_inf_Op_p'p_of_le_oddCore (hp : p ≠ 2)
    {D R : Subgroup H} (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R)
    (hO : pPrimeCore p H ≤ oddCore H) :
    IsSylowOf p (R ⊓ Op_p'p p H) (Op_p'p p H) :=
  hR.isSylowOf_inf_of_le_oddCore hp hD (Op_p'p_le_oddCore hp hO)

theorem IsMaximalPSignalizer.isSylowOf_inf_oddCore_solvableRadical (hp : p ≠ 2)
    {D R : Subgroup H} (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (S : Sylow 2 H)
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype) :
    IsSylowOf p (R ⊓ oddCore H) (solvableRadical H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hR.isSylowOf_inf_oddCore hp hD
  rw [isSylowOf_iff] at h1 ⊢
  obtain ⟨hle, hpg, hdvd⟩ := h1
  have hOS : oddCore H ≤ solvableRadical H := by rw [hrad]; exact le_sup_left
  refine ⟨hle.trans hOS, hpg, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hOS]
  have hZ : IsPGroup 2 ((center S).map (S : Subgroup H).subtype) :=
    (S.isPGroup'.to_subgroup _).map _
  have h2 : ¬ p ∣ (oddCore H).relIndex (solvableRadical H) :=
    not_dvd_relIndex_of_le_sup hp hZ (le_of_eq hrad)
  exact fun h => (Nat.Prime.dvd_mul Fact.out).mp h |>.elim hdvd h2

theorem IsMaximalPSignalizer.isSylowOf_inf_Op_p'p_of_le_solvableRadical (hp : p ≠ 2)
    {D R : Subgroup H} (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (S : Sylow 2 H)
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype)
    (hO : pPrimeCore p H ≤ solvableRadical H) :
    IsSylowOf p (R ⊓ Op_p'p p H) (Op_p'p p H) := by
  have h1 := (hR.isSylowOf_inf_oddCore_solvableRadical hp hD S hrad).inf_of_le_normalizer
    (Op_p'p_le_solvableRadical hO) (by rw [normalizer_eq_top]; exact le_top)
  have hle : R ⊓ oddCore H ⊓ Op_p'p p H ≤ R ⊓ Op_p'p p H :=
    inf_le_inf_right _ inf_le_left
  have heq := h1.eq_of_le hle inf_le_right (hR.1.1.to_le inf_le_left)
  rw [← heq] at h1
  exact h1

end Maximal

section Covers

variable [Finite H] [Fact p.Prime]

theorem pCore_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : ¬ p ∣ B.index) : pCore p G ≤ B := by
  have hdvd1 : B.relIndex (pCore p G ⊔ B) ∣ B.index := relIndex_dvd_index_of_le le_sup_right
  rw [relIndex_sup_eq_relIndex_of_normal] at hdvd1
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
  have hdvd2 : B.relIndex (pCore p G) ∣ p ^ k := hk ▸ relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hB
    rw [hj] at hdvd1
    exact (dvd_pow_self p hj0).trans hdvd1
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact hj

theorem pCore_quotient_le_map_of_not_dvd_index {K A : Subgroup H} [K.Normal]
    (h : ¬ p ∣ (A ⊔ K).index) : pCore p (H ⧸ K) ≤ A.map (QuotientGroup.mk' K) := by
  apply pCore_le_of_not_dvd_index
  have := index_comap_of_surjective (A.map (QuotientGroup.mk' K)) (QuotientGroup.mk'_surjective K)
  rw [← this, comap_map_eq, QuotientGroup.ker_mk']
  exact h

theorem pCore_quotient_le_map_of_isSylowOf {K R : Subgroup H} [K.Normal]
    (h : IsSylowOf p (R ⊓ (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K))
      ((pCore p (H ⧸ K)).comap (QuotientGroup.mk' K))) :
    pCore p (H ⧸ K) ≤ R.map (QuotientGroup.mk' K) := by
  set f := QuotientGroup.mk' K with hf
  set N := pCore p (H ⧸ K) with hN
  set Y := N.comap f with hY
  have hKY : K ≤ Y := by
    intro k hk
    rw [hY, mem_comap, hf, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact one_mem _
  obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.mp h
  have hYN : Y.map f = N := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective K) N
  have h1 : ((R ⊓ Y).map f).relIndex N = ((R ⊓ Y) ⊔ K).relIndex Y := by
    rw [← hYN, ← relIndex_comap, comap_map_eq, hf, QuotientGroup.ker_mk']
  have hle : (R ⊓ Y) ⊔ K ≤ Y := sup_le inf_le_right hKY
  have h2 := relIndex_mul_relIndex (R ⊓ Y) ((R ⊓ Y) ⊔ K) Y le_sup_left hle
  have hdvd' : ¬ p ∣ ((R ⊓ Y).map f).relIndex N := by
    rw [h1]
    intro hd
    exact hdvd (h2 ▸ hd.mul_left _)
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := H ⧸ K)).exists_card_eq
  have hdvd2 : ((R ⊓ Y).map f).relIndex N ∣ p ^ k := hk ▸ relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hdvd'
    exact hdvd' (dvd_pow_self p hj0)
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact hj.trans (map_mono inf_le_left)

omit [Fact p.Prime] in
theorem relIndex_sup_dvd_relIndex {A B K : Subgroup H} [K.Normal] (hAB : A ≤ B) :
    (A ⊔ K).relIndex (B ⊔ K) ∣ A.relIndex B := by
  have e1 := relIndex_mul_relIndex A B (B ⊔ K) hAB le_sup_left
  have e2 := relIndex_mul_relIndex A (A ⊔ K) (B ⊔ K) le_sup_left (sup_le_sup_right hAB K)
  have e3 : B.relIndex (B ⊔ K) = B.relIndex K := by
    rw [sup_comm]
    exact relIndex_sup_eq_relIndex_of_normal K B
  have e4 : A.relIndex (A ⊔ K) = A.relIndex K := by
    rw [sup_comm]
    exact relIndex_sup_eq_relIndex_of_normal K A
  have e5 := relIndex_mul_relIndex (A ⊓ K) (B ⊓ K) K (inf_le_inf_right K hAB) inf_le_right
  rw [inf_relIndex_right, inf_relIndex_right] at e5
  have hne : B.relIndex K ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have key : A.relIndex B * B.relIndex K =
      ((A ⊓ K).relIndex (B ⊓ K) * (A ⊔ K).relIndex (B ⊔ K)) * B.relIndex K := by
    calc A.relIndex B * B.relIndex K = A.relIndex B * B.relIndex (B ⊔ K) := by rw [e3]
      _ = A.relIndex (A ⊔ K) * (A ⊔ K).relIndex (B ⊔ K) := by rw [e1, e2]
      _ = (A ⊓ K).relIndex (B ⊓ K) * B.relIndex K * (A ⊔ K).relIndex (B ⊔ K) := by
          rw [e4, e5]
      _ = _ := by ring
  rw [Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) key]
  exact dvd_mul_left _ _

omit [Finite H] [Fact p.Prime] in
theorem mem_normalizer_of_conj_mem {g : H} {K : Subgroup H} (h1 : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (h2 : ∀ k ∈ K, g⁻¹ * k * g ∈ K) : g ∈ normalizer (K : Set H) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨h1 k, fun hk => ?_⟩
  have := h2 _ hk
  simpa [mul_assoc] using this

omit [Finite H] in
theorem odd_card_of_isPGroup (hp : p ≠ 2) {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

omit [Finite H] in
theorem card_comap_mk' (N : Subgroup H) [N.Normal] (V : Subgroup (H ⧸ N)) :
    Nat.card (V.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card V := by
  have hNV : N ≤ V.comap (QuotientGroup.mk' N) := by
    intro n hn
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have h1 := relIndex_mul_card N (V.comap (QuotientGroup.mk' N))
  rw [inf_eq_left.mpr hNV] at h1
  have h2 : N.relIndex (V.comap (QuotientGroup.mk' N)) = Nat.card V := by
    have h := relIndex_comap (H := (⊥ : Subgroup (H ⧸ N))) (QuotientGroup.mk' N)
      (V.comap (QuotientGroup.mk' N))
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N), relIndex_bot_left] at h
    exact h
  rw [← h1, h2, mul_comm]

theorem IsMaximalPSignalizer.exists_sylow_le_normalizer_of_not_sq_dvd (hp : p ≠ 2)
    {D R : Subgroup H} (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R)
    (hsq : ¬ p ^ 2 ∣ Nat.card (H ⧸ oddCore H)) :
    ∃ P : Sylow p H, R ≤ P ∧ (P : Subgroup H) ≤ normalizer (R : Set H) := by
  obtain ⟨P, hRP⟩ := hR.1.1.exists_le_sylow
  refine ⟨P, hRP, ?_⟩
  set φ := QuotientGroup.mk' (oddCore H) with hφ
  have hPO : (P : Subgroup H) ⊓ oddCore H = R ⊓ oddCore H :=
    (hR.isSylowOf_inf_oddCore hp hD).eq_of_le (inf_le_inf_right _ hRP) inf_le_right
      (P.isPGroup'.to_le inf_le_left)
  have hPbar : ∀ x ∈ (P : Subgroup H), ∀ y ∈ (P : Subgroup H), φ x * φ y = φ y * φ x := by
    have hpg : IsPGroup p ((P : Subgroup H).map φ) := P.isPGroup'.map φ
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra hk1
      apply hsq
      have hdvd : p ^ k ∣ Nat.card (H ⧸ oddCore H) := hk ▸ card_subgroup_dvd_card _
      exact (pow_dvd_pow p (by omega)).trans hdvd
    have hcomm : ∀ a b : (P : Subgroup H).map φ, a * b = b * a := by
      interval_cases k
      · have : Subsingleton ((P : Subgroup H).map φ) := by
          rw [pow_zero] at hk
          exact (Nat.card_eq_one_iff_unique.mp hk).1
        intro a b
        exact Subsingleton.elim _ _
      · have : IsCyclic ((P : Subgroup H).map φ) :=
          isCyclic_of_prime_card (p := p) (by simpa using hk)
        intro a b
        exact (IsCyclic.commGroup.mul_comm a b)
    intro x hx y hy
    have := hcomm ⟨φ x, mem_map_of_mem φ hx⟩ ⟨φ y, mem_map_of_mem φ hy⟩
    exact congrArg Subtype.val this
  have hconj : ∀ x ∈ (P : Subgroup H), ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx r hr
    have hcO : x * r * x⁻¹ * r⁻¹ ∈ oddCore H := by
      have h := hPbar x hx r (hRP hr)
      rw [hφ] at h
      rw [← QuotientGroup.ker_mk' (oddCore H), MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [h]
      group
    have hcP : x * r * x⁻¹ * r⁻¹ ∈ (P : Subgroup H) :=
      mul_mem (mul_mem (mul_mem hx (hRP hr)) (inv_mem hx)) (inv_mem (hRP hr))
    have hcR : x * r * x⁻¹ * r⁻¹ ∈ R := by
      have : x * r * x⁻¹ * r⁻¹ ∈ (P : Subgroup H) ⊓ oddCore H := ⟨hcP, hcO⟩
      rw [hPO] at this
      exact this.1
    have := mul_mem hcR hr
    simpa using this
  intro x hx
  exact mem_normalizer_of_conj_mem (hconj x hx) (fun r hr => by
    simpa using hconj x⁻¹ (inv_mem hx) r hr)

theorem IsMaximalPSignalizer.covers_of_signalizerCover_oddCore (hp : p ≠ 2)
    {D R : Subgroup H} (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R)
    (hcov : SignalizerCover (D.map (QuotientGroup.mk' (oddCore H)))) (K : Subgroup H)
    [hK : K.Normal] : pCore p (H ⧸ K) ≤ R.map (QuotientGroup.mk' K) := by
  have hpp : p.Prime := Fact.out
  set φ := QuotientGroup.mk' (oddCore H) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  by_cases hKO : K ≤ oddCore H
  ·
    apply pCore_quotient_le_map_of_isSylowOf
    set Y := (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K) with hY
    have hYn : Y.Normal := (pCore_normal (p := p) (G := H ⧸ K)).comap _
    have hYodd : Odd (Nat.card Y) := by
      rw [hY, card_comap_mk' K]
      refine Odd.mul ?_ (odd_card_of_isPGroup hp (pCore_isPGroup (p := p) (G := H ⧸ K)))
      exact Odd.of_dvd_nat (odd_card_oddCore (H := H)) (card_dvd_of_le hKO)
    exact hR.isSylowOf_inf_of_le_oddCore hp hD (le_oddCore_of_normal hYn hYodd)
  ·
    obtain ⟨L₀, hL₀, hV⟩ := hcov
    have hRodd : Odd (Nat.card (R.map φ)) := odd_card_of_isPGroup hp (hR.1.1.map φ)
    have hDR : D.map φ ≤ normalizer ((R.map φ : Subgroup (H ⧸ oddCore H)) : Set _) :=
      (map_mono hR.1.2.1).trans (le_normalizer_map φ)
    obtain ⟨V, hRV, hVodd, hDV, hidx⟩ := hV (R.map φ) hRodd hDR
    set W := V.comap φ with hW
    have hWodd : Odd (Nat.card W) := by
      rw [hW, hφ, card_comap_mk']
      exact (odd_card_oddCore (H := H)).mul hVodd
    have hDW : D ≤ normalizer (W : Set H) :=
      (Subgroup.map_le_iff_le_comap.mp hDV).trans (le_normalizer_comap φ)
    have hRW : R ≤ W := (le_comap_map φ R).trans (comap_mono hRV)
    have hsyl : IsSylowOf p R W := hR.isSylowOf_of_odd hp hD hRW hWodd hDW
    apply pCore_quotient_le_map_of_not_dvd_index
    have hKbar : K.map φ ≠ ⊥ := by
      intro hbot
      apply hKO
      rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have hL₀K : L₀ ≤ K.map φ := hL₀ _ (hK.map φ hφs) hKbar
    have hidxWK : ¬ p ∣ (W ⊔ K).index := by
      have hOW : oddCore H ≤ W ⊔ K := by
        intro x hx
        apply le_sup_left (b := K)
        rw [hW, mem_comap, hφ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
        exact one_mem _
      have h1 : (W ⊔ K).index = ((W ⊔ K).map φ).index := by
        rw [← index_comap_of_surjective ((W ⊔ K).map φ) hφs, comap_map_eq, hφ,
          QuotientGroup.ker_mk', sup_eq_left.mpr hOW]
      have h2 : (W ⊔ K).map φ = V ⊔ K.map φ := by
        rw [Subgroup.map_sup, hW, map_comap_eq_self_of_surjective hφs]
      have h3 : ((W ⊔ K).map φ).index ∣ (L₀ ⊔ V).index := by
        rw [h2]
        exact index_dvd_of_le (sup_le (hL₀K.trans le_sup_right) le_sup_left)
      have h4 : (L₀ ⊔ V).index ≠ 0 := index_ne_zero_of_finite
      rw [h1]
      intro hd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h4) (hd.trans h3)
      have h2p := hpp.two_le
      omega
    have hrel : ¬ p ∣ (R ⊔ K).relIndex (W ⊔ K) := fun hd =>
      (isSylowOf_iff.mp hsyl).2.2 (hd.trans (relIndex_sup_dvd_relIndex hRW))
    rw [← relIndex_mul_index (sup_le_sup_right hRW K)]
    intro hd
    rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
    · exact hrel h
    · exact hidxWK h

theorem IsMaximalPSignalizer.normal_or_covers_of_oddCore (hp : p ≠ 2) {D R : Subgroup H}
    (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R)
    (hcover : SignalizerCover (D.map (QuotientGroup.mk' (oddCore H))) ∨
      ¬ p ^ 2 ∣ Nat.card (H ⧸ oddCore H)) :
    (∃ P : Sylow p H, R ≤ P ∧ (P : Subgroup H) ≤ normalizer (R : Set H)) ∨
      ∀ (K : Subgroup H) [K.Normal], pCore p (H ⧸ K) ≤ R.map (QuotientGroup.mk' K) := by
  rcases hcover with hcov | hsq
  · exact Or.inr fun K _ => hR.covers_of_signalizerCover_oddCore hp hD hcov K
  · exact Or.inl (hR.exists_sylow_le_normalizer_of_not_sq_dvd hp hD hsq)

omit [Finite H] [Fact p.Prime] in
theorem mem_normalizer_map_subtype_of_characteristic {M : Subgroup H} {C : Subgroup M}
    [hC : C.Characteristic] {d : H} (hd : d ∈ normalizer (M : Set H)) :
    d ∈ normalizer ((C.map M.subtype : Subgroup H) : Set H) := by
  set α := normalizerMonoidHom M ⟨d, hd⟩ with hαdef
  have hα : ∀ m : M, ((α m : M) : H) = d * m * d⁻¹ := fun m =>
    normalizerMonoidHom_apply_apply_coe M ⟨d, hd⟩ m
  have hfix : C.comap α.toMonoidHom = C := hC.fixed α
  have hiff : ∀ m : M, α m ∈ C ↔ m ∈ C := fun m => by
    conv_rhs => rw [← hfix]
    rfl
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨α m, (hiff m).mpr hm, hα m⟩
  · rintro ⟨m', hm', hm'eq⟩
    have hhM : h ∈ M := (mem_normalizer_iff.mp hd h).mpr (hm'eq ▸ m'.2)
    refine ⟨⟨h, hhM⟩, (hiff _).mp ?_, rfl⟩
    have : α ⟨h, hhM⟩ = m' := Subtype.ext (by rw [hα]; exact hm'eq.symm)
    rw [this]
    exact hm'

theorem card_solvableRadical_of_eq {S : Sylow 2 H}
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype) :
    Nat.card (solvableRadical H) =
      Nat.card (oddCore H) * Nat.card ((center S).map (S : Subgroup H).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := (center S).map (S : Subgroup H).subtype
  have hZ2 : IsPGroup 2 Z := (S.isPGroup'.to_subgroup _).map _
  have hOZ : oddCore H ⊓ Z = ⊥ := by
    have hodd : Odd (Nat.card (oddCore H ⊓ Z : Subgroup H)) :=
      Odd.of_dvd_nat (odd_card_oddCore (H := H)) (card_dvd_of_le inf_le_left)
    obtain ⟨k, hk⟩ := (hZ2.to_le inf_le_right).exists_card_eq
    rcases k with _ | k
    · exact card_eq_one.mp (by simpa using hk)
    · exfalso
      rw [hk] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩)
  have h1 := relIndex_mul_card (oddCore H) (solvableRadical H)
  rw [inf_eq_left.mpr (by rw [hrad]; exact le_sup_left), hrad, relIndex_sup_left] at h1
  have h2 := relIndex_mul_card (oddCore H) Z
  rw [hOZ, card_bot, mul_one] at h2
  rw [hrad, ← h1, h2, mul_comm]

theorem comap_pCore_le_solvableRadical {K : Subgroup H} [K.Normal]
    (hK : K ≤ solvableRadical H) :
    (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K) ≤ solvableRadical H := by
  set Y := (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K) with hY
  have hYn : Y.Normal := (pCore_normal (p := p) (G := H ⧸ K)).comap _
  have hKY : K ≤ Y := by
    intro k hk
    rw [hY, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact one_mem _
  have hKsolv : Group.IsSolvable K := by
    have := solvableRadical_isSolvable (H := H)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK)
      (Subgroup.inclusion_injective hK)
  have hNsolv : Group.IsSolvable (pCore p (H ⧸ K)) := by
    have := (pCore_isPGroup (p := p) (G := H ⧸ K)).isNilpotent
    infer_instance
  let g : Y →* pCore p (H ⧸ K) :=
    ((QuotientGroup.mk' K).comp Y.subtype).codRestrict _ fun y => y.2
  have hker : g.ker ≤ (Subgroup.inclusion hKY).range := by
    intro y hy
    have h1 : ((g y : pCore p (H ⧸ K)) : H ⧸ K) = 1 := by rw [MonoidHom.mem_ker.mp hy]; rfl
    have h2 : ((g y : pCore p (H ⧸ K)) : H ⧸ K) = QuotientGroup.mk' K (y : H) := rfl
    rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨y, h1⟩, rfl⟩
  have hYsolv : Group.IsSolvable Y := Group.isSolvable_of_ker_le_range _ g hker
  exact le_sSup ⟨hYn, hYsolv⟩

theorem IsMaximalPSignalizer.normal_or_covers_of_solvableRadical (hp : p ≠ 2)
    {D R : Subgroup H} (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (S : Sylow 2 H)
    (hZ : IsCyclic (center S))
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype)
    (hcover : SignalizerCover (D.map (QuotientGroup.mk' (solvableRadical H)))) :
    (∃ P : Sylow p H, R ≤ P ∧ (P : Subgroup H) ≤ normalizer (R : Set H)) ∨
      ∀ (K : Subgroup H) [K.Normal], pCore p (H ⧸ K) ≤ R.map (QuotientGroup.mk' K) := by
  have hpp : p.Prime := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Or.inr fun K hK => ?_
  set φ := QuotientGroup.mk' (solvableRadical H) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set Z := (center S).map (S : Subgroup H).subtype with hZdef
  have hZS : Z ≤ solvableRadical H := by rw [hrad]; exact le_sup_right
  by_cases hKS : K ≤ solvableRadical H
  ·
    apply pCore_quotient_le_map_of_isSylowOf
    have hY := comap_pCore_le_solvableRadical (p := p) hKS
    have hYn : ((pCore p (H ⧸ K)).comap (QuotientGroup.mk' K)).Normal :=
      (pCore_normal (p := p) (G := H ⧸ K)).comap _
    have h1 := (hR.isSylowOf_inf_oddCore_solvableRadical hp hD S hrad).inf_of_le_normalizer hY
      (by rw [normalizer_eq_top]; exact le_top)
    have heq := h1.eq_of_le (inf_le_inf_right _ inf_le_left) inf_le_right
      (hR.1.1.to_le inf_le_left)
    rw [← heq] at h1
    exact h1
  · obtain ⟨L₀, hL₀, hV⟩ := hcover
    have hRodd : Odd (Nat.card (R.map φ)) := odd_card_of_isPGroup hp (hR.1.1.map φ)
    have hDR : D.map φ ≤ normalizer ((R.map φ : Subgroup (H ⧸ solvableRadical H)) : Set _) :=
      (map_mono hR.1.2.1).trans (le_normalizer_map φ)
    obtain ⟨V, hRV, hVodd, hDV, hidx⟩ := hV (R.map φ) hRodd hDR
    set W := V.comap φ with hW
    have hDW : D ≤ normalizer (W : Set H) :=
      (Subgroup.map_le_iff_le_comap.mp hDV).trans (le_normalizer_comap φ)
    have hRW : R ≤ W := (le_comap_map φ R).trans (comap_mono hRV)
    have hSW : solvableRadical H ≤ W := by
      intro x hx
      rw [hW, mem_comap, hφ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hZW : IsSylowOf 2 Z W := by
      rw [isSylowOf_iff]
      refine ⟨hZS.trans hSW, (S.isPGroup'.to_subgroup _).map _, ?_⟩
      have h1 := relIndex_mul_card Z W
      rw [inf_eq_left.mpr (hZS.trans hSW), hW, hφ, card_comap_mk',
        card_solvableRadical_of_eq hrad] at h1
      have h2 : Z.relIndex W = Nat.card (oddCore H) * Nat.card V := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Z))
        rw [h1]
        ring
      rw [h2]
      exact ((odd_card_oddCore (H := H)).mul hVodd).not_two_dvd_nat
    obtain ⟨T, hT⟩ := hZW.exists_sylow_eq_subgroupOf
    have hTcyc : IsCyclic T := by
      have e : (T : Subgroup W) ≃* Z :=
        (MulEquiv.subgroupCongr hT).trans (subgroupOfEquivOfLe (hZS.trans hSW))
      have : IsCyclic Z := by
        have e' : center S ≃* Z := (center S).equivMapOfInjective _ (Subtype.val_injective)
        exact isCyclic_of_surjective e'.toMonoidHom e'.surjective
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    obtain ⟨-, -, -, ⟨-, hOodd, hOidx, -⟩, hOchar⟩ := cyclic_sylow_normal_odd_complement T hTcyc
    set O' := (pPrimeCore 2 W).map W.subtype with hO'
    have hO'odd : Odd (Nat.card O') := by
      rw [hO', Nat.card_congr ((pPrimeCore 2 W).equivMapOfInjective _
        W.subtype_injective).toEquiv.symm]
      exact hOodd
    have hDO' : D ≤ normalizer (O' : Set H) := fun d hd =>
      mem_normalizer_map_subtype_of_characteristic (hDW hd)
    have hRO' : R ≤ O' := by
      have hq : IsPGroup 2 (W ⧸ pPrimeCore 2 W) := by
        rw [IsPGroup.iff_card, ← index_eq_card, hOidx]
        exact T.isPGroup'.exists_card_eq
      have hle := CFSG.QuasiDihedralFusion.le_of_odd_of_isPGroup_quotient (pPrimeCore 2 W) hq
        (R.subgroupOf W) (by
          rw [Nat.card_congr (subgroupOfEquivOfLe hRW).toEquiv]
          exact odd_card_of_isPGroup hp hR.1.1)
      intro r hr
      exact ⟨⟨r, hRW hr⟩, hle hr, rfl⟩
    have hsyl : IsSylowOf p R O' := hR.isSylowOf_of_odd hp hD hRO' hO'odd hDO'
    have hO'W : O' ≤ W := map_subtype_le _
    apply pCore_quotient_le_map_of_not_dvd_index
    have hKbar : K.map φ ≠ ⊥ := by
      intro hbot
      apply hKS
      rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have hL₀K : L₀ ≤ K.map φ := hL₀ _ (hK.map φ hφs) hKbar
    have hidxWK : ¬ p ∣ (W ⊔ K).index := by
      have hSWK : solvableRadical H ≤ W ⊔ K := hSW.trans le_sup_left
      have h1 : (W ⊔ K).index = ((W ⊔ K).map φ).index := by
        rw [← index_comap_of_surjective ((W ⊔ K).map φ) hφs, comap_map_eq, hφ,
          QuotientGroup.ker_mk', sup_eq_left.mpr hSWK]
      have h2 : (W ⊔ K).map φ = V ⊔ K.map φ := by
        rw [Subgroup.map_sup, hW, map_comap_eq_self_of_surjective hφs]
      have h3 : ((W ⊔ K).map φ).index ∣ (L₀ ⊔ V).index := by
        rw [h2]
        exact index_dvd_of_le (sup_le (hL₀K.trans le_sup_right) le_sup_left)
      have h4 : (L₀ ⊔ V).index ≠ 0 := index_ne_zero_of_finite
      rw [h1]
      intro hd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h4) (hd.trans h3)
      have h2p := hpp.two_le
      omega
    have hidxO'W : ¬ p ∣ (O' ⊔ K).relIndex (W ⊔ K) := by
      intro hd
      have h1 := hd.trans (relIndex_sup_dvd_relIndex hO'W)
      have h2 : O'.relIndex W = (pPrimeCore 2 W).index := by
        rw [hO', relIndex, subgroupOf, comap_map_eq_self_of_injective W.subtype_injective]
      rw [h2, hOidx] at h1
      obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
      rw [hk] at h1
      have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h1)
      exact hp this
    have hrel : ¬ p ∣ (R ⊔ K).relIndex (O' ⊔ K) := fun hd =>
      (isSylowOf_iff.mp hsyl).2.2 (hd.trans (relIndex_sup_dvd_relIndex hRO'))
    rw [← relIndex_mul_index (sup_le_sup_right hRO' K),
      ← relIndex_mul_index (sup_le_sup_right hO'W K)]
    intro hd
    rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
    · exact hrel h
    · rcases (Nat.Prime.dvd_mul hpp).mp h with h' | h'
      · exact hidxO'W h'
      · exact hidxWK h'

end Covers


section Ambient

omit [Group H] in
theorem subgroupOf_mem_pSignalizers_iff {G : Type*} [Group G] {K D X : Subgroup G}
    (hDK : D ≤ K) (hXK : X ≤ K) :
    X.subgroupOf K ∈ pSignalizers (D.subgroupOf K) p ↔
      IsPGroup p X ∧ D ≤ normalizer (X : Set G) ∧ X ⊓ D = ⊥ := by
  have e : X.subgroupOf K ≃* X := subgroupOfEquivOfLe hXK
  refine and_congr ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩ (and_congr ?_ ?_)
  · constructor
    · intro h d hd
      have hn := h (show (⟨d, hDK hd⟩ : K) ∈ D.subgroupOf K from hd)
      rw [mem_normalizer_iff] at hn ⊢
      intro x
      constructor
      · intro hx
        exact (hn ⟨x, hXK hx⟩).mp hx
      · intro hx
        have hxK : x ∈ K := by
          have hdK := hDK hd
          have : d⁻¹ * (d * x * d⁻¹) * d ∈ K := mul_mem (mul_mem (inv_mem hdK) (hXK hx)) hdK
          simpa [mul_assoc] using this
        exact (hn ⟨x, hxK⟩).mpr hx
    · intro h d hd
      have hn := h (mem_subgroupOf.mp hd)
      rw [mem_normalizer_iff] at hn ⊢
      intro x
      exact hn x
  · have h1 : X.subgroupOf K ⊓ D.subgroupOf K = (X ⊓ D).subgroupOf K := (comap_inf _ _ _).symm
    rw [h1, subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr (inf_le_left.trans hXK)]

omit [Group H] in
theorem isMaximalPSignalizer_subgroupOf_iff {G : Type*} [Group G] {K D R : Subgroup G}
    (hDK : D ≤ K) (hRK : R ≤ K) :
    IsMaximalPSignalizer (D.subgroupOf K) p (R.subgroupOf K) ↔
      (IsPGroup p R ∧ D ≤ normalizer (R : Set G) ∧ R ⊓ D = ⊥) ∧
        ∀ R' : Subgroup G, R' ≤ K → IsPGroup p R' → D ≤ normalizer (R' : Set G) →
          R' ⊓ D = ⊥ → R ≤ R' → R' = R := by
  rw [IsMaximalPSignalizer, subgroupOf_mem_pSignalizers_iff hDK hRK]
  refine and_congr_right fun _ =>
    ⟨fun h R' hR'K hp' hn' hb' hRR' => ?_, fun h R'' hmem'' hRR'' => ?_⟩
  · have := h (R'.subgroupOf K) ((subgroupOf_mem_pSignalizers_iff hDK hR'K).mpr ⟨hp', hn', hb'⟩)
      (subgroupOf_mono K hRR')
    rw [subgroupOf_inj, inf_eq_left.mpr hR'K, inf_eq_left.mpr hRK] at this
    exact this
  · set R' := R''.map K.subtype with hR'def
    have hR'K : R' ≤ K := map_subtype_le _
    have hsub : R'.subgroupOf K = R'' := by
      rw [hR'def, subgroupOf, comap_map_eq_self_of_injective K.subtype_injective]
    rw [← hsub] at hmem'' hRR''
    obtain ⟨hp', hn', hb'⟩ := (subgroupOf_mem_pSignalizers_iff hDK hR'K).mp hmem''
    have hRR' : R ≤ R' := by
      have := map_mono (f := K.subtype) hRR''
      rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hRK,
        inf_eq_left.mpr hR'K] at this
    rw [← hsub, h R' hR'K hp' hn' hb' hRR']

end Ambient

end CFSG.ABGLocalTools
