module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec12N_index_two {Γ : Type*} [Group Γ] [Finite Γ] {E : Subgroup Γ} [E.Normal]
    (hE : E.index = 2 ∨ E.index = 6) {y : Γ} (hy2 : y * y = 1) (hy : y ∉ E) :
    ∃ H0 : Subgroup Γ, H0.Normal ∧ H0.index = 2 ∧ y ∉ H0 := by
  rcases hE with h2 | h6
  · exact ⟨E, inferInstance, h2, hy⟩
  · haveI : Finite (Γ ⧸ E) :=
      Finite.of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
    have hcardQ : Nat.card (Γ ⧸ E) = 6 := h6
    have h3dvd : 3 ^ 1 ∣ Nat.card (Γ ⧸ E) := by rw [hcardQ]; norm_num
    obtain ⟨P, hPcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := Γ ⧸ E) 3 (n := 1) h3dvd
    have hPcard' : Nat.card P = 3 := by simpa using hPcard
    have hPidx : P.index = 2 := by
      have h := Subgroup.card_mul_index (H := P)
      rw [hPcard', hcardQ] at h
      omega
    haveI : P.Normal := Subgroup.normal_of_index_eq_two hPidx
    have hyq1 : (y : Γ ⧸ E) ≠ 1 := fun h => hy ((QuotientGroup.eq_one_iff y).mp h)
    have hyq2 : (y : Γ ⧸ E) * (y : Γ ⧸ E) = 1 := by
      rw [← QuotientGroup.mk'_apply E y, ← map_mul, hy2, map_one]
    have hyqord : orderOf (y : Γ ⧸ E) = 2 :=
      orderOf_eq_prime (p := 2) (by simpa [pow_two] using hyq2) hyq1
    have hyqP : (y : Γ ⧸ E) ∉ P := by
      intro hymem
      have hdvd : orderOf (y : Γ ⧸ E) ∣ Nat.card P :=
        Subgroup.orderOf_dvd_natCard P hymem
      rw [hyqord, hPcard'] at hdvd
      norm_num at hdvd
    refine ⟨P.comap (QuotientGroup.mk' E), inferInstance, ?_, ?_⟩
    · have hidx : (P.comap (QuotientGroup.mk' E)).index = P.index :=
        Subgroup.index_comap_of_surjective (H := P) (QuotientGroup.mk'_surjective E)
      rw [hidx, hPidx]
    · intro hmem
      exact hyqP (Subgroup.mem_comap.mp hmem)

theorem sec12N_of_hom {G : Type*} [Group G] {N : Subgroup G} {Γ : Type*} [Group Γ]
    (f : ↥N →* Γ) (hf : Function.Surjective f) {H0 : Subgroup Γ} [H0.Normal]
    (hidx : H0.index = 2) {t : G} (htN : t ∈ N) (ht : f ⟨t, htN⟩ ∉ H0) :
    ∃ N0 : Subgroup G, N0 ≤ N ∧ (N0.subgroupOf N).Normal ∧ N0.relIndex N = 2 ∧ t ∉ N0 := by
  refine ⟨(H0.comap f).map N.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have h : ((H0.comap f).map N.subtype).subgroupOf N = H0.comap f :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [h]
    infer_instance
  · have h : ((H0.comap f).map N.subtype).subgroupOf N = H0.comap f :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    change (((H0.comap f).map N.subtype).subgroupOf N).index = 2
    rw [h, Subgroup.index_comap_of_surjective _ hf]
    exact hidx
  · intro hmem
    obtain ⟨n, hn, hnt⟩ := Subgroup.mem_map.mp hmem
    have : n = ⟨t, htN⟩ := Subtype.ext hnt
    exact ht (this ▸ hn)

end CFSG.OddStandard.SmallF3.Omega
