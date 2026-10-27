module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mem_coreActionKernel {S L : Subgroup G} (hS : IsPGroup 2 S) {q s : G}
    (hqS : q ∈ S) (hq : q ∈ coreActionKernel L) (hsS : s ∈ S) (hsL : s ∈ L) :
    q * s = s * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : s⁻¹ * q⁻¹ * s * q ∈ oddIn L := (mem_coreActionKernel.mp hq).2 s hsL
  have h2 : s⁻¹ * q⁻¹ * s * q ∈ S :=
    mul_mem (mul_mem (mul_mem (inv_mem hsS) (inv_mem hqS)) hsS) hqS
  have hSO : S ⊓ oddIn L = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hodd : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  have h3 : s⁻¹ * q⁻¹ * s * q = 1 := by
    have h4 : s⁻¹ * q⁻¹ * s * q ∈ S ⊓ oddIn L := mem_inf.mpr ⟨h2, h1⟩
    rw [hSO] at h4
    exact h4
  calc q * s = s * q * (s⁻¹ * q⁻¹ * s * q)⁻¹ := by group
    _ = s * q := by rw [h3, inv_one, mul_one]

omit [Finite G] in
theorem mem_normalizer_omegaOne {Q : Subgroup G} {s : G} (hs : s ∈ normalizer (Q : Set G)) :
    s ∈ normalizer (omegaOne Q : Set G) := by
  have key : ∀ g ∈ normalizer (Q : Set G), ∀ h ∈ omegaOne Q, g * h * g⁻¹ ∈ omegaOne Q := by
    intro g hg h hh
    have hle : omegaOne Q ≤ (omegaOne Q).comap (MulAut.conj g).toMonoidHom := by
      rw [omegaOne, closure_le]
      rintro x ⟨hxQ, hx2⟩
      show g * x * g⁻¹ ∈ Subgroup.closure _
      refine subset_closure ⟨(mem_normalizer_iff.mp hg x).mp hxQ, ?_⟩
      rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx2, mul_one,
        mul_inv_cancel]
    exact hle hh
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key s hs h, fun hh => ?_⟩
  have h1 := key s⁻¹ (inv_mem hs) _ hh
  rwa [show s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h by group] at h1

theorem exists_orderOf_four_of_ne_omegaOne {S Q : Subgroup G} (hS : IsPGroup 2 S)
    (hQS : Q ≤ S) (hSQ : S ≤ normalizer (Q : Set G)) (hE : IsElemTwo (omegaOne Q))
    (hne : Q ≠ omegaOne Q) :
    ∃ y ∈ Q, orderOf y = 4 ∧ y * y ∈ omegaOne Q ∧
      ∀ s ∈ S, s⁻¹ * y⁻¹ * s * y ∈ omegaOne Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMQ : omegaOne Q ≤ Q := omegaOne_le Q
  have hMS : omegaOne Q ≤ S := hMQ.trans hQS
  have hSM : S ≤ normalizer (omegaOne Q : Set G) := fun s hs => mem_normalizer_omegaOne (hSQ hs)
  have hMn : ((omegaOne Q).subgroupOf S).Normal :=
    (normal_subgroupOf_iff_le_normalizer hMS).mpr hSM
  have hQn : (Q.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hQS).mpr hSQ
  set φ := QuotientGroup.mk' ((omegaOne Q).subgroupOf S) with hφ
  have hφ1 : ∀ x : ↥S, φ x = 1 ↔ (x : G) ∈ omegaOne Q := fun x => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  set N := (Q.subgroupOf S).map φ with hN
  have hNn : N.Normal := hQn.map φ (QuotientGroup.mk'_surjective _)
  have hS' : IsPGroup 2 (↥S ⧸ (omegaOne Q).subgroupOf S) :=
    hS.of_surjective φ (QuotientGroup.mk'_surjective _)
  obtain ⟨q, hqQ, hqM⟩ : ∃ q ∈ Q, q ∉ omegaOne Q := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hMQ)
  have hNne : N ≠ ⊥ := by
    intro h
    have h1 : φ ⟨q, hQS hqQ⟩ ∈ N := mem_map_of_mem φ (mem_subgroupOf.mpr hqQ)
    rw [h, mem_bot, hφ1] at h1
    exact hqM h1
  have hNnorm : (⊤ : Subgroup (↥S ⧸ (omegaOne Q).subgroupOf S)) ≤ normalizer (N : Set _) :=
    fun g _ => mem_normalizer_iff.mpr fun h => ⟨fun hh => hNn.conj_mem h hh g, fun hh => by
      have h1 := hNn.conj_mem _ hh g⁻¹
      rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1⟩
  obtain ⟨zb, hzN, hz2, hzc⟩ :=
    GSLit.exists_involution_mem_center (hS'.to_subgroup ⊤) le_top hNnorm hNne
  obtain ⟨y', hy'Q, hy'z⟩ := hzN
  have hyQ : (y' : G) ∈ Q := mem_subgroupOf.mp hy'Q
  have hz1 : zb ≠ 1 := by rintro rfl; simp at hz2
  have hyM : (y' : G) ∉ omegaOne Q := fun h => hz1 (hy'z ▸ (hφ1 y').mpr h)
  have hyyM : (y' : G) * y' ∈ omegaOne Q := by
    have h1 : φ (y' * y') = 1 := by
      rw [map_mul, hy'z, ← pow_two, ← hz2, pow_orderOf_eq_one]
    exact (hφ1 _).mp h1
  have hcomm : ∀ s ∈ S, s⁻¹ * (y' : G)⁻¹ * s * y' ∈ omegaOne Q := by
    intro s hs
    have h1 := hzc (φ ⟨s, hs⟩) (mem_top _)
    have h2 : φ ((⟨s, hs⟩ : ↥S)⁻¹ * y'⁻¹ * ⟨s, hs⟩ * y') = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy'z]
      calc (φ ⟨s, hs⟩)⁻¹ * zb⁻¹ * φ ⟨s, hs⟩ * zb =
            (φ ⟨s, hs⟩)⁻¹ * zb⁻¹ * (φ ⟨s, hs⟩ * zb) := by group
        _ = 1 := by rw [h1]; group
    exact (hφ1 _).mp h2
  have h4 : orderOf (y' : G) = 2 ^ (1 + 1) := orderOf_eq_prime_pow (n := 1)
    (by rw [pow_one, pow_two]; exact fun h => hyM (subset_closure ⟨hyQ, h⟩))
    (by rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]; exact hE.2 _ hyyM)
  exact ⟨y', hyQ, h4.trans (by norm_num), hyyM, hcomm⟩

omit [Finite G] in
theorem mem_coreActionKernel_of_conj_eq_inv {K : Subgroup G} {d w : G}
    (hd : d ∈ normalizer (K : Set G)) (hodd : Odd (orderOf d)) (hw : w ∈ coreActionKernel K)
    (hwd : w * d * w⁻¹ = d⁻¹) : d ∈ coreActionKernel K := by
  have hN := normalizer_le_normalizer_coreActionKernel K hd
  have h1 : d * w * d⁻¹ ∈ coreActionKernel K := (mem_normalizer_iff.mp hN w).mp hw
  have h2 : d * d ∈ coreActionKernel K := by
    have h3 : d * d = (d * w * d⁻¹) * w⁻¹ := by
      calc d * d = d * (w * d * w⁻¹)⁻¹ := by rw [hwd, inv_inv]
        _ = (d * w * d⁻¹) * w⁻¹ := by group
    rw [h3]
    exact mul_mem h1 (inv_mem hw)
  obtain ⟨k, hk⟩ := hodd
  have h5 : d = (d * d) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf d + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h5]
  exact pow_mem h2 _

omit [Finite G] in
theorem pRank_le_of_forall_isElemTwo [Finite G] {H : Subgroup G} {r : ℕ}
    (h : ∀ E : Subgroup G, E ≤ H → IsElemTwo E → Nat.card E ≤ 2 ^ r) : pRank 2 ↥H ≤ r := by
  refine csSup_le' fun k ⟨B, hBe, hBc⟩ => ?_
  have hE : IsElemTwo (B.map H.subtype) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hc := hBe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
      exact congrArg (fun w : B => ((w : ↥H) : G)) hc
    · rintro _ ⟨x, hx, rfl⟩
      have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x hx
      have h2' := congrArg Subtype.val h2
      rw [← pow_two]
      exact h2'
  have h1 := h _ (map_subtype_le _) hE
  rw [card_map_of_injective H.subtype_injective, hBc] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

end CFSG.ComponentClassification.GrSLit.GrS5
