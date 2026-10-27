module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.StronglyEmbedded

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

theorem stronglyEmbedded_map_quotient_three {C : Type} [Group C] [Finite C]
    {B J M' : Subgroup C} [B.Normal] (hBJ : B < J) (hJ3 : IsPGroup 3 J) (hJidx : ¬ 3 ∣ J.index)
    (hJM : J ≤ M') (hM' : M' ≠ ⊤)
    (hU : ∀ U : Subgroup C, B ≤ U → U ≤ J → U ≠ B → Subgroup.normalizer (U : Set C) ≤ M') :
    GLBStronglyEmbedded 3 (M'.map (QuotientGroup.mk' B)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' B with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective B
  have hBM : B ≤ M' := hBJ.le.trans hJM
  set M₁ := M'.map π with hM₁
  have hJbp : IsPGroup 3 (J.map π) := hJ3.map π
  have hJbidx : ¬ 3 ∣ (J.map π).index := by
    have h := Subgroup.index_map J π
    rw [hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hBJ.le,
      MonoidHom.range_eq_top_of_surjective _ hπs] at h
    rw [h]
    simpa using hJidx
  let R : Sylow 3 (C ⧸ B) := IsPGroup.toSylow hJbp hJbidx
  have hR : (R : Subgroup (C ⧸ B)) = J.map π := rfl
  have hRM : (R : Subgroup (C ⧸ B)) ≤ M₁ := by
    rw [hR]; exact Subgroup.map_mono hJM
  have hR1 : (R : Subgroup (C ⧸ B)) ≠ ⊥ := by
    rw [hR]
    intro hbot
    have : J ≤ B := by
      intro x hx
      have hx' : π x ∈ (J.map π) := Subgroup.mem_map_of_mem π hx
      rw [hbot, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).mp hx'
    exact absurd (lt_of_lt_of_le hBJ this) (lt_irrefl _)
  have hM₁top : M₁ ≠ ⊤ := by
    intro htop
    apply hM'
    have h1 : M'.map π = ⊤ := htop
    have h2 := Subgroup.comap_map_eq π M'
    rw [h1, Subgroup.comap_top, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hBM] at h2
    exact h2.symm
  have hN₀ : ∀ Y : Subgroup (C ⧸ B), Y ≤ (R : Subgroup (C ⧸ B)) → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set (C ⧸ B)) ≤ M₁ := by
    intro Y hYR hY1
    set U := Y.comap π with hUdef
    have hBU : B ≤ U := by
      intro b hb
      have h1 : π b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
      rw [hUdef, Subgroup.mem_comap, h1]
      exact Y.one_mem
    have hUJ : U ≤ J := by
      intro x hx
      have hx' : π x ∈ (J.map π) := hR ▸ hYR hx
      obtain ⟨j, hj, hjx⟩ := hx'
      have : j⁻¹ * x ∈ B := by
        rw [← QuotientGroup.eq]; exact hjx
      have hxj : x = j * (j⁻¹ * x) := by group
      rw [hxj]
      exact J.mul_mem hj (hBJ.le this)
    have hUB : U ≠ B := by
      intro hUB
      apply hY1
      have : Y = U.map π := (Subgroup.map_comap_eq_self_of_surjective hπs Y).symm
      rw [this, hUB, hπ, QuotientGroup.map_mk'_self]
    have hNU := hU U hBU hUJ hUB
    intro n hn
    obtain ⟨c, rfl⟩ := hπs n
    have hcU : c ∈ Subgroup.normalizer (U : Set C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have hn' := (Subgroup.mem_normalizer_iff.mp hn) (π u)
      simp only [hUdef, Subgroup.mem_comap, map_mul, map_inv]
      exact hn'
    exact ⟨c, hNU hcU, rfl⟩
  have hN : ∀ Y : Subgroup (C ⧸ B), Y ≤ M₁ → IsPGroup 3 Y → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set (C ⧸ B)) ≤ M₁ := by
    intro Y hYM hYp hY1
    obtain ⟨m, hm⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_conjugate_le_sylow_of_le 3 R hRM
      hYM hYp
    have hY'1 : Y.map (MulAut.conj (m : C ⧸ B)).toMonoidHom ≠ ⊥ := by
      intro h
      apply hY1
      rwa [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (m : C ⧸ B)).injective] at h
    have h1 := hN₀ _ hm hY'1
    refine CFSG.AGLEmbedding.le_of_map_conj_le (K := Subgroup.normalizer (Y : Set (C ⧸ B)))
      (m := (m : C ⧸ B)) m.2 ?_
    rw [Subgroup.map_equiv_normalizer_eq]
    exact h1
  exact CFSG.AGLEmbeddingD2.stronglyEmbedded_of_normalizer_le Nat.prime_three hM₁top R hRM hR1 hN

end CFSG.LocalAnalysis.RankThreeTheoremC
