module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem le_normalizer_of_isNormalE16In {P B : Subgroup G} (hB : IsNormalE16In P B) :
    P ≤ normalizer (B : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hB.1).mp hB.2.2

theorem sec76_move_into_S [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) {s₁ : G} (hs₁C : s₁ ∈ centralizer ({t} : Set G))
    (hs₁2 : orderOf s₁ = 2) (hs₁P : s₁ ∈ centralizer ((S ⊓ L : Subgroup G) : Set G)) :
    ∃ s₂ ∈ S, s₂ ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ∧
      ∃ c ∈ centralizer ({t} : Set G), s₂ = c * s₁ * c⁻¹ := by
  classical
  let P : Subgroup G := S ⊓ L
  let N₀ : Subgroup G := centralizer ({t} : Set G) ⊓ normalizer (P : Set G)
  have hSN₀ : S ≤ N₀ := by
    intro s hs
    have hsC : s ∈ centralizer ({t} : Set G) := hctx.sylow.1 hs
    have hsN : s ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 s hsC
    have hsNorm : s ∈ normalizer (P : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hsN⟩
    exact Subgroup.mem_inf.mpr ⟨hsC, hsNorm⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hctx.sylow
  have hSylN₀ : IsSylow2Of S N₀ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl.of_le hSN₀ inf_le_left)
  have hK : IsPGroup 2 (Subgroup.zpowers s₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs₁2]; norm_num)
  have hs₁N₀ : s₁ ∈ N₀ := ⟨hs₁C, Subgroup.centralizer_le_normalizer _ hs₁P⟩
  have hKN₀ : Subgroup.zpowers s₁ ≤ N₀ := Subgroup.zpowers_le.mpr hs₁N₀
  obtain ⟨c, hcN₀, hcmove⟩ := exists_conj_le_of_isSylow2Of hSylN₀ hK hKN₀
  refine ⟨c * s₁ * c⁻¹, hcmove s₁ (Subgroup.mem_zpowers s₁), ?_, c, hcN₀.1, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
  have hcp : c⁻¹ * p * c ∈ P := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp ((normalizer (P : Set G)).inv_mem hcN₀.2) p).mp hp
  calc p * (c * s₁ * c⁻¹) = c * ((c⁻¹ * p * c) * s₁) * c⁻¹ := by group
    _ = c * (s₁ * (c⁻¹ * p * c)) * c⁻¹ := by rw [hs₁P (c⁻¹ * p * c) hcp]
    _ = (c * s₁ * c⁻¹) * p := by group

theorem sec76_exists_B [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (h75a : Asc82Lemma75a)
    (h75b : Asc82Lemma75b) {t : G} {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z)
    {s : G} (hsN : s ∈ normalizer (L : Set G))
    (hs : s ∈ centralizer ((S ⊓ L : Subgroup G) : Set G))
    (hα : ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) :
    ∃ B : Subgroup G, IsNormalE16In (S ⊓ L) B ∧
      ∃ n ∈ L ⊓ normalizer (B : Set G), s * n ≠ n * s := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨B₁, B₂, hne, hB₁, hB₂, -⟩ := h75a G t L S z hctx
  have hB1c : ∀ b ∈ B₁, s * b = b * s := fun b hb => (hs b (hB₁.1 hb)).symm
  have hcent := hP.cent_B_opp G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36) B₁ B₂
    hB₁ hB₂ hne z hctx.z_mem_centerIn hctx.pocket s hsN hB1c (hcon B₁ hB₁) hα
  have hB2c : ∀ n ∈ L ⊓ normalizer (B₂ : Set G), (s * z) * n = n * (s * z) := hcent.1
  have hz_comm : ∀ n ∈ L ⊓ normalizer (B₂ : Set G), z * n = n * z := by
    intro n hn
    have h1 := hB2c n hn
    have h2 := hcon B₂ hB₂ n hn
    have h3 : s * (z * n) = s * (n * z) := by
      calc s * (z * n) = (s * z) * n := by group
        _ = n * (s * z) := h1
        _ = (n * s) * z := by group
        _ = (s * n) * z := by rw [h2]
        _ = s * (n * z) := by group
    exact mul_left_cancel h3
  have hcl : conjClassIn (L ⊓ normalizer (B₂ : Set G)) z = {z} := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [Set.mem_singleton_iff]
      have hzh := hz_comm h hh
      rw [← hzh]
      group
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨1, (L ⊓ normalizer (B₂ : Set G)).one_mem, by group⟩
  have hB2_eq : B₂ = Subgroup.zpowers z := by
    rw [(h75b G t L S z hctx B₂ hB₂).2.2.2, hcl, Subgroup.zpowers_eq_closure]
  have hcard : Nat.card B₂ = 2 := by
    rw [hB2_eq, Nat.card_zpowers, hctx.pocket.1]
  exact absurd (hB₂.2.1.2.symm.trans hcard) (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
