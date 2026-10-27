module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.Data.Nat.Prime.Defs
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {Ω : Type*} [Group Ω]

private theorem pCoreOf_le_pCoreOf_of_normal_pcm {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {A B : Subgroup G} (hle : A ≤ B) (hN : (A.subgroupOf B).Normal) :
    CFSG.Open.pCoreOf p A ≤ CFSG.Open.pCoreOf p B := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    ((CFSG.LieType.BorelTits.pCoreOf_le p A).trans hle) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p A)
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p A)

private theorem pCoreOf_le_pCore_of_isSubnormal_pcm {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {S : Subgroup G} (h : S.IsSubnormal) :
    CFSG.Open.pCoreOf p S ≤ CFSG.pCore p G := by
  induction h with
  | top =>
      exact CFSG.LieType.BorelTits.map_pCore_le p (G := (⊤ : Subgroup G)) (H := G)
        (⊤ : Subgroup G).subtype fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  | step S K hle hK hN ih =>
      exact (pCoreOf_le_pCoreOf_of_normal_pcm hle hN).trans ih

private theorem isPGroup_le_pCore_of_isSubnormal_pcm {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {A : Subgroup G} (hsub : A.IsSubnormal) (hp : IsPGroup p A) :
    A ≤ CFSG.pCore p G := by
  have hself : (A.subgroupOf A).Normal := by
    rw [Subgroup.subgroupOf_self]; infer_instance
  exact (CFSG.LieType.BorelTits.le_pCoreOf p le_rfl hself hp).trans
    (pCoreOf_le_pCore_of_isSubnormal_pcm hsub)

private theorem isPGroup_of_forall_pow_mem_pCore_pcm {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] {M : Subgroup Q} (h : ∀ m ∈ M, ∃ k : ℕ, m ^ p ^ k ∈ CFSG.pCore p Q) :
    IsPGroup p M := by
  intro m
  obtain ⟨k, hk⟩ := h (m : Q) m.2
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup p (G := Q)) ⟨(m : Q) ^ p ^ k, hk⟩
  refine ⟨k + j, ?_⟩
  refine Subtype.ext ?_
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hj

private def pcmPreimage_pcm (p : ℕ) (H C : Subgroup Ω) [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] : Subgroup Ω :=
  ((CFSG.pCore p (H ⧸ C.subgroupOf H)).comap (QuotientGroup.mk' (C.subgroupOf H))).map H.subtype

private theorem pcmPreimage_contains_C_pcm (p : ℕ) {H C : Subgroup Ω} [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] (hCH : C ≤ H) : C ≤ pcmPreimage_pcm p H C := by
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hCH hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have hx1 : QuotientGroup.mk' (C.subgroupOf H) ⟨x, hCH hx⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := C.subgroupOf H) ⟨x, hCH hx⟩).mpr
      (Subgroup.mem_subgroupOf.mpr hx)
  rw [hx1]
  exact (CFSG.pCore p (H ⧸ C.subgroupOf H)).one_mem

private theorem pcmPreimage_le_H_pcm (p : ℕ) (H C : Subgroup Ω) [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] : pcmPreimage_pcm p H C ≤ H :=
  Subgroup.map_subtype_le _

private theorem pcmPreimage_normalized_pcm (p : ℕ) (H C : Subgroup Ω) [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] : H ≤ normalizer (pcmPreimage_pcm p H C : Set Ω) := by
  let π : H →* (H ⧸ C.subgroupOf H) := QuotientGroup.mk' (C.subgroupOf H)
  let K : Subgroup H := (CFSG.pCore p (H ⧸ C.subgroupOf H)).comap π
  have hKnormal : K.Normal :=
    (CFSG.LieType.BorelTits.pCore_normal p (G := H ⧸ C.subgroupOf H)).comap π
  have hmap : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map (f := H.subtype), Subgroup.range_subtype]
  have h1 := Subgroup.le_normalizer_map (H := K) H.subtype
  rw [Subgroup.normalizer_eq_top_iff.mpr hKnormal, hmap] at h1
  exact h1

private theorem pcmPreimage_pow_mem_pcm (p : ℕ) (H C : Subgroup Ω) [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] :
    ∀ x ∈ pcmPreimage_pcm p H C, ∃ k : ℕ, x ^ p ^ k ∈ C := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_comap] at hy
  obtain ⟨k, hk⟩ :=
    (CFSG.LieType.BorelTits.pCore_isPGroup p (G := H ⧸ C.subgroupOf H)).exists_pow_pow_eq_one
      ⟨QuotientGroup.mk' (C.subgroupOf H) y, hy⟩
  have hy1 : QuotientGroup.mk' (C.subgroupOf H) (y ^ p ^ k) = 1 := by
    rw [map_pow]
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hk
  have hker : y ^ p ^ k ∈ C.subgroupOf H :=
    (QuotientGroup.eq_one_iff (N := C.subgroupOf H) (y ^ p ^ k)).mp hy1
  exact ⟨k, by simpa using Subgroup.mem_subgroupOf.mp hker⟩

private theorem pcmPreimage_maximal_pcm (p : ℕ) (H C : Subgroup Ω) [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] :
    ∀ N : Subgroup Ω, N ≤ H → H ≤ normalizer (N : Set Ω) →
      (∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ pcmPreimage_pcm p H C) → N ≤ pcmPreimage_pcm p H C := by
  intro N hNH hHN hpowN
  let π : H →* (H ⧸ C.subgroupOf H) := QuotientGroup.mk' (C.subgroupOf H)
  let K : Subgroup H := (CFSG.pCore p (H ⧸ C.subgroupOf H)).comap π
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  let M : Subgroup (H ⧸ C.subgroupOf H) := (N.subgroupOf H).map π
  have hMn : M.Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  have hMp : IsPGroup p M := by
    refine isPGroup_of_forall_pow_mem_pCore_pcm (M := M) ?_
    intro m hm
    obtain ⟨y, hy, hmy⟩ := Subgroup.mem_map.mp hm
    have hyN : (y : Ω) ∈ N := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨k, hk⟩ := hpowN (y : Ω) hyN
    have hyk : y ^ p ^ k ∈ K := by
      obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp hk
      have hzy : z = y ^ p ^ k := by
        apply H.subtype_injective
        rw [map_pow]
        exact hze
      rw [← hzy]
      exact hz
    refine ⟨k, ?_⟩
    rw [← hmy, ← map_pow]
    exact Subgroup.mem_comap.mp hyk
  have hMle : M ≤ CFSG.pCore p (H ⧸ C.subgroupOf H) :=
    CFSG.LieType.BorelTits.le_pCore p hMn hMp
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hNH hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  exact hMle (Subgroup.mem_map.mpr ⟨⟨x, hNH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)

private theorem pcmPreimage_subnormal_pcm (p : ℕ) (H C : Subgroup Ω) [Finite Ω] [Fact p.Prime]
    [(C.subgroupOf H).Normal] :
    ∀ Ks D : Subgroup Ω, Ks ≤ H → (Ks.subgroupOf H).IsSubnormal → D ≤ Ks →
      Ks ≤ normalizer (D : Set Ω) → (∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ C) →
      D ≤ pcmPreimage_pcm p H C := by
  intro Ks D hKsH hKssub hDKs hKsn hpowD
  let π : H →* (H ⧸ C.subgroupOf H) := QuotientGroup.mk' (C.subgroupOf H)
  let S : Subgroup (H ⧸ C.subgroupOf H) := (Ks.subgroupOf H).map π
  let A : Subgroup (H ⧸ C.subgroupOf H) := (D.subgroupOf H).map π
  have hSsub : S.IsSubnormal :=
    Subgroup.IsSubnormal.map (f := π) (QuotientGroup.mk'_surjective _) hKssub
  have hAS : A ≤ S := Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono H hDKs)
  have hAnorm : (A.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAS, Subgroup.le_normalizer_iff]
    intro s hs a ha
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hs
    obtain ⟨d, hd, hda⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨k * d * k⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (Subgroup.le_normalizer_iff.mp hKsn (k : Ω) (Subgroup.mem_subgroupOf.mp hk)
          (d : Ω) (Subgroup.mem_subgroupOf.mp hd))
    · simp only [map_mul, map_inv, hks, hda]
  have hAsub : A.IsSubnormal := Subgroup.IsSubnormal.step A S hAS hSsub hAnorm
  have hAp : IsPGroup p A := by
    intro a
    obtain ⟨d, hd, hda⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨k, hk⟩ := hpowD (d : Ω) (Subgroup.mem_subgroupOf.mp hd)
    have hker : (d : H) ^ p ^ k ∈ C.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (by simpa only [Subgroup.coe_pow] using hk)
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [show (a : H ⧸ C.subgroupOf H) = π d from hda.symm, ← map_pow]
    exact (QuotientGroup.eq_one_iff (N := C.subgroupOf H) (d ^ p ^ k)).mpr hker
  have hAle : A ≤ CFSG.pCore p (H ⧸ C.subgroupOf H) :=
    isPGroup_le_pCore_of_isSubnormal_pcm hAsub hAp
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hKsH (hDKs hx)⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  exact hAle (Subgroup.mem_map.mpr ⟨⟨x, hKsH (hDKs hx)⟩,
    Subgroup.mem_subgroupOf.mpr hx, rfl⟩)

theorem exists_pCore_quotient_preimage {p : ℕ} [Fact p.Prime] [Finite Ω] {H C : Subgroup Ω}
    (hCH : C ≤ H) (hHC : H ≤ normalizer (C : Set Ω)) :
    ∃ P : Subgroup Ω, C ≤ P ∧ P ≤ H ∧ H ≤ normalizer (P : Set Ω) ∧
      (∀ x ∈ P, ∃ k : ℕ, x ^ p ^ k ∈ C) ∧
      (∀ N : Subgroup Ω, N ≤ H → H ≤ normalizer (N : Set Ω) →
        (∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ P) → N ≤ P) ∧
      ∀ K D : Subgroup Ω, K ≤ H → (K.subgroupOf H).IsSubnormal → D ≤ K →
        K ≤ normalizer (D : Set Ω) → (∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ C) → D ≤ P := by
  have hCn : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
  exact ⟨pcmPreimage_pcm p H C, pcmPreimage_contains_C_pcm p hCH, pcmPreimage_le_H_pcm p H C,
    pcmPreimage_normalized_pcm p H C, pcmPreimage_pow_mem_pcm p H C,
    pcmPreimage_maximal_pcm p H C, pcmPreimage_subnormal_pcm p H C⟩

end CFSG.GroupTheory
