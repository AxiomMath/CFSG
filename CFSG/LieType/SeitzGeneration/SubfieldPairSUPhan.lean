module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUClose
public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.RankThree.PartOne.SEITZ2.EmbVec

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.LieType.SeitzGeneration.Centers

section Emb

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

export CFSG.RankThree.PartOne.SEITZ2 (embVec embVec_blockIdx embVec_of_not_mem embVec_smul
  embVec_add herm_embVec_left herm_embVec_embVec)

theorem isRat_embVec {k : Subfield K} {i : ℕ} {v : Fin 2 → K} (hv : ∀ x, v x ∈ k) :
    IsRat k (embVec m i v) := by
  intro l
  simp only [embVec]
  split_ifs
  · exact hv 0
  · exact hv 1
  · exact k.zero_mem

theorem herm_one_pair (l : K) (hl : σ l * l = -1) : herm σ ![1, l] ![1, l] = 0 := by
  simp [herm_def, Fin.sum_univ_two, hl]

theorem herm_one_pair_ne {l₁ l₂ : K} (h₁ : σ l₁ * l₁ = -1) (hd : l₁ ≠ l₂) :
    herm σ ![1, l₁] ![1, l₂] ≠ 0 := by
  have hσ0 : σ l₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at h₁
    exact zero_ne_one (neg_eq_zero.1 h₁.symm).symm
  intro h
  simp only [herm_def, Fin.sum_univ_two] at h
  simp at h
  apply hd
  apply mul_left_cancel₀ hσ0
  linear_combination h₁ - h

theorem eq_comb_one_pair {l₁ l₂ : K} (hd : l₁ ≠ l₂) (a : Fin 2 → K) :
    a = ((l₂ * a 0 - a 1) / (l₂ - l₁)) • ![1, l₁] + ((a 1 - l₁ * a 0) / (l₂ - l₁)) • ![1, l₂] := by
  have : l₂ - l₁ ≠ 0 := sub_ne_zero.2 hd.symm
  funext x
  fin_cases x <;> simp <;> field_simp <;> ring

theorem isCenter_embVec_of_rat (hσ : ∀ c, σ (σ c) = c) {k : Subfield K} {m : ℕ} (i : Fin m)
    {H : Subgroup (SUid σ (m + 1))}
    (hrat : ∀ a : Fin (m + 1) → K, IsRat k a → herm σ a a = 0 → IsCenter H a)
    {l₁ l₂ : K} (m₁ : l₁ ∈ k) (m₂ : l₂ ∈ k) (hd : l₁ ≠ l₂) (n₁ : σ l₁ * l₁ = -1)
    (n₂ : σ l₂ * l₂ = -1) (a : Fin 2 → K) (ha : herm σ a a = 0) :
    IsCenter H (embVec (m + 1) i a) := by
  have h2 : (i : ℕ) + 2 ≤ m + 1 := by omega
  have hone : ∀ x, (![1, l₁] : Fin 2 → K) x ∈ k := by
    intro x; fin_cases x
    · exact k.one_mem
    · exact m₁
  have hone' : ∀ x, (![1, l₂] : Fin 2 → K) x ∈ k := by
    intro x; fin_cases x
    · exact k.one_mem
    · exact m₂
  have c₁ : IsCenter H (embVec (m + 1) i ![1, l₁]) :=
    hrat _ (isRat_embVec hone) (by rw [herm_embVec_embVec h2]; exact herm_one_pair l₁ n₁)
  have c₂ : IsCenter H (embVec (m + 1) i ![1, l₂]) :=
    hrat _ (isRat_embVec hone') (by rw [herm_embVec_embVec h2]; exact herm_one_pair l₂ n₂)
  have hne : herm σ (embVec (m + 1) i ![1, l₁]) (embVec (m + 1) i ![1, l₂]) ≠ 0 := by
    rw [herm_embVec_embVec h2]
    exact herm_one_pair_ne n₁ hd
  have hcomb := eq_comb_one_pair hd a
  set x : K := (l₂ * a 0 - a 1) / (l₂ - l₁)
  set y : K := (a 1 - l₁ * a 0) / (l₂ - l₁)
  have hemb : embVec (m + 1) i a =
      x • embVec (m + 1) i ![1, l₁] + y • embVec (m + 1) i ![1, l₂] := by
    rw [← embVec_smul, ← embVec_smul, ← embVec_add, ← hcomb]
  rw [hemb]
  refine isCenter_of_pair_span hσ c₁ c₂ hne ?_
  rw [← hemb, herm_embVec_embVec h2]
  exact ha

end Emb

section Block

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem blockEmb2_smul_tv {m : ℕ} (i : Fin m) {t : Su K ℓ f 2} {a : Fin 2 → K} {c : K}
    (h : ∀ w, t • w = w + (c * herm (unitaryInvolution K ℓ f) a w) • a) (v : Fin (m + 1) → K) :
    blockEmb2 K ℓ f m i t • v = v + (c * herm (unitaryInvolution K ℓ f)
      (embVec (m + 1) i a) v) • embVec (m + 1) i a := by
  have h2 : (i : ℕ) + 2 ≤ m + 1 := by omega
  funext l
  rw [smul_def]
  by_cases hl : (i : ℕ) ≤ l.val ∧ l.val < i + 2
  · obtain ⟨x, rfl⟩ : ∃ x : Fin 2, blockIdx i h2 x = l :=
      ⟨⟨l.val - i, by omega⟩, Fin.ext (by simp [blockIdx]; omega)⟩
    show (blockMat (m + 1) i ((t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
      (blockIdx i h2 x) = _
    rw [blockMat_mulVec_blockIdx h2]
    have := congrFun (h (fun y => v (blockIdx i h2 y))) x
    rw [smul_def] at this
    rw [this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, embVec_blockIdx h2,
      herm_embVec_left h2]
  · show (blockMat (m + 1) i ((t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) l = _
    rw [blockMat_mulVec_of_not_mem _ _ hl, Pi.add_apply, Pi.smul_apply, embVec_of_not_mem a hl]
    simp

theorem eq_top_of_plane_centers (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : ℓ ^ f ≠ 2) {m : ℕ}
    (H : Subgroup (Su K ℓ f (m + 1)))
    (hc : ∀ (i : Fin m) (a : Fin 2 → K), herm (unitaryInvolution K ℓ f) a a = 0 →
      IsCenter H (embVec (m + 1) i a)) : H = ⊤ := by
  have hU := isUnitaryInvolution_unitaryInvolution hK
  have hT : T (unitaryInvolution K ℓ f) 2 = ⊤ :=
    T_eq_top hU (le_refl 2) (fun h => absurd h (by norm_num))
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq m]
  refine iSup_le fun i => ?_
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ T (unitaryInvolution K ℓ f) 2 := by rw [hT]; trivial
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, c, ha, hct, hga⟩ := hg
    obtain ⟨g', hg', hg'a⟩ := (hc i a ha).2 c hct
    have : blockEmb2 K ℓ f m i g = g' := ext_smul _ fun v => by
      rw [blockEmb2_smul_tv i hga, hg'a]
    rw [this]
    exact hg'
  | one => rw [map_one]; exact H.one_mem
  | mul a b _ _ ha hb => rw [map_mul]; exact H.mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact H.inv_mem ha

end Block

end CFSG.LieType.SeitzGeneration.SUPair
