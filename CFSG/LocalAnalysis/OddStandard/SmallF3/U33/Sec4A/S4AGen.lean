module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_or_mem_or_mul_mem_of_relIndex_two {S K : Subgroup G} (hK : K ≤ S)
    (hKi : K.relIndex S = 2) {a b : G} (ha : a ∈ S) (hb : b ∈ S) :
    a ∈ K ∨ b ∈ K ∨ a * b ∈ K := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := K.subgroupOf S) hKi
    (a := (⟨a, ha⟩ : S)) (b := (⟨b, hb⟩ : S))
  by_cases haK : a ∈ K
  · exact Or.inl haK
  · by_cases hbK : b ∈ K
    · exact Or.inr (Or.inl hbK)
    · refine Or.inr (Or.inr ?_)
      have haK' : (⟨a, ha⟩ : S) ∉ K.subgroupOf S := fun hh => haK (Subgroup.mem_subgroupOf.mp hh)
      have hbK' : (⟨b, hb⟩ : S) ∉ K.subgroupOf S := fun hh => hbK (Subgroup.mem_subgroupOf.mp hh)
      exact Subgroup.mem_subgroupOf.mp (h.mpr (iff_of_false haK' hbK'))

theorem relIndex_le_two_of_forall {N C : Subgroup G} (hCN : C ≤ N) (a : G) (haN : a ∈ N)
    (h : ∀ n ∈ N, n ∈ C ∨ a⁻¹ * n ∈ C) : C.relIndex N ≤ 2 := by
  rw [Subgroup.relIndex, Subgroup.index]
  let f : Bool → (↥N ⧸ C.subgroupOf N) := fun b =>
    cond b ((⟨a, haN⟩ : ↥N) : ↥N ⧸ C.subgroupOf N) ((1 : ↥N) : ↥N ⧸ C.subgroupOf N)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective (s := C.subgroupOf N) x
    by_cases hn : (n : G) ∈ C
    · refine ⟨false, ?_⟩
      show ((1 : ↥N) : ↥N ⧸ C.subgroupOf N) = (n : ↥N ⧸ C.subgroupOf N)
      rw [QuotientGroup.eq]
      simpa [Subgroup.mem_subgroupOf] using hn
    · refine ⟨true, ?_⟩
      show ((⟨a, haN⟩ : ↥N) : ↥N ⧸ C.subgroupOf N) = (n : ↥N ⧸ C.subgroupOf N)
      rw [QuotientGroup.eq]
      have hc : a⁻¹ * (n : G) ∈ C := (h (n : G) n.2).resolve_left hn
      simpa [Subgroup.mem_subgroupOf] using hc
  calc Nat.card (↥N ⧸ C.subgroupOf N) ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]

theorem eq_of_relIndex_le_two_of_odd {N C S : Subgroup G} (hCN : C ≤ N) (hSC : S ≤ C)
    (hS : ¬ 2 ∣ S.relIndex N) (h2 : C.relIndex N ≤ 2) : C = N := by
  have hdvd : C.relIndex N ∣ S.relIndex N := Subgroup.relIndex_dvd_of_le_left (L := N) hSC
  have hSne : S.relIndex N ≠ 0 := fun h0 => hS (h0.symm ▸ dvd_zero 2)
  have hCne : C.relIndex N ≠ 0 := fun h0 => hSne (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have hodd : ¬ 2 ∣ C.relIndex N := fun h => hS (h.trans hdvd)
  have hcases : C.relIndex N = 1 ∨ C.relIndex N = 2 := by
    rcases lt_or_ge (C.relIndex N) 2 with hlt | hge
    · left
      have hle1 : C.relIndex N ≤ 1 := Nat.le_of_lt_succ hlt
      rcases lt_or_ge (C.relIndex N) 1 with hlt1 | hge1
      · exact absurd (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt1)) hCne
      · exact le_antisymm hle1 hge1
    · exact Or.inr (le_antisymm h2 hge)
  rcases hcases with h1 | h1
  · exact le_antisymm hCN (Subgroup.relIndex_eq_one.mp h1)
  · exact absurd (h1.symm ▸ dvd_refl 2) hodd

theorem exists_conj_le_of_isPGroup {H S Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 2 Q)
    (hSH : S ≤ H) (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.relIndex H) :
    ∃ k ∈ H, ∀ q ∈ Q, k * q * k⁻¹ ∈ S := by
  have hQ' : IsPGroup 2 (Q.subgroupOf H) := hQ.comap_subtype
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.comap_subtype
  let S₀ : Sylow 2 ↥H := hS'.toSylow hSi
  obtain ⟨R, hQR⟩ := hQ'.exists_le_sylow
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex S₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥H) S₀ R
  have hS₀ : (S₀ : Subgroup ↥H) = S.subgroupOf H := rfl
  have hconj : (c⁻¹ : ↥H) • R = S₀ := by
    rw [← hc, ← mul_smul, inv_mul_cancel, one_smul]
  refine ⟨(c⁻¹ : ↥H), (c⁻¹ : ↥H).2, fun q hq => ?_⟩
  have hqQ' : (⟨q, hQH hq⟩ : ↥H) ∈ Q.subgroupOf H := hq
  have hqR : (⟨q, hQH hq⟩ : ↥H) ∈ (R : Subgroup ↥H) := hQR hqQ'
  have hconj_sub : MulAut.conj (c⁻¹ : ↥H) • (R : Subgroup ↥H) = (S₀ : Subgroup ↥H) := by
    rw [← Sylow.coe_subgroup_smul, hconj]
  have hmem : MulAut.conj (c⁻¹ : ↥H) • (⟨q, hQH hq⟩ : ↥H) ∈ (S₀ : Subgroup ↥H) := by
    rw [← hconj_sub]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hqR
  rw [hS₀, Subgroup.mem_subgroupOf] at hmem
  simpa only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem exists_sylow_coe_eq {S : Subgroup G} (hS : IsPGroup 2 S) (hi : ¬ 2 ∣ S.index) :
    ∃ Sy : Sylow 2 G, (Sy : Subgroup G) = S :=
  ⟨hS.toSylow hi, hS.toSylow_coe hi⟩

theorem exists_sylow_gt {S : Subgroup G} (hS : IsPGroup 2 S) (hi : 2 ∣ S.index) :
    ∃ Sy : Sylow 2 G, S < (Sy : Subgroup G) := by
  obtain ⟨Sy, hle⟩ := hS.exists_le_sylow
  refine ⟨Sy, lt_of_le_of_ne hle ?_⟩
  intro heq
  exact Sy.not_dvd_index (heq ▸ hi)

theorem exists_mem_normalizer_not_mem {S Q : Subgroup G} (hQ : IsPGroup 2 Q) (hSQ : S < Q) :
    ∃ n ∈ Q, n ∈ normalizer (S : Set G) ∧ n ∉ S := by
  haveI := hQ.isNilpotent
  have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
  have hlt : S.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact not_le_of_gt hSQ (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨n, hn_mem, hn_not⟩ := SetLike.exists_of_lt (hnc (S.subgroupOf Q) hlt)
  refine ⟨(n : G), n.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hQ' : h ∈ Q := hSQ.le hh
      have key : (⟨h, hQ'⟩ : ↥Q) ∈ S.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hh
      have := (Subgroup.mem_normalizer_iff.mp hn_mem (⟨h, hQ'⟩ : ↥Q)).mp key
      exact Subgroup.mem_subgroupOf.mp this
    · intro hh
      have hQ' : h ∈ Q := by
        have hmem : (n : G) * h * (n : G)⁻¹ ∈ Q := hSQ.le hh
        have h2 : (n : G)⁻¹ * ((n : G) * h * (n : G)⁻¹) * (n : G) ∈ Q :=
          Q.mul_mem (Q.mul_mem (Q.inv_mem n.2) hmem) n.2
        convert h2 using 1
        group
      have key : n * (⟨h, hQ'⟩ : ↥Q) * n⁻¹ ∈ S.subgroupOf Q := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hh
      have := (Subgroup.mem_normalizer_iff.mp hn_mem (⟨h, hQ'⟩ : ↥Q)).mpr key
      exact Subgroup.mem_subgroupOf.mp this
  · intro hnS
    exact hn_not (Subgroup.mem_subgroupOf.mpr hnS)

theorem mem_normalizer_of_conj_mem {W : Subgroup G} {g : G}
    (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq ?_)
  · rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    simpa using h w hw
  · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
