module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits Module
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

section Commuting

theorem mul_comm_of_inf_eq_bot_su (h2 : (2 : K) ≠ 0) {i₁ i₂ : Su K p f n}
    (h₁ : suMat i₁ * suMat i₁ = 1) (h₂ : suMat i₂ * suMat i₂ = 1)
    (hc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁)
    (hV : eigSpace (suMat i₁) (-1) ⊓ eigSpace (suMat i₂) (-1) = ⊥) {x y : Su K p f n}
    (hx : x ∈ longRootGroupSU K p f (suMat i₁)) (hy : y ∈ longRootGroupSU K p f (suMat i₂)) :
    x * y = y * x := by
  apply suToSL_injective (σ := unitaryInvolution K p f)
  rw [map_mul, map_mul]
  exact mul_comm_of_inf_eq_bot h2 h₁ h₂ hc hV hx hy

end Commuting

section Dichotomy

theorem inf_eq_bot_or_exists_su_frame (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hn : 3 ≤ n) {i₁ i₂ : Su K p f n} (h₁ : suMat i₁ * suMat i₁ = 1)
    (h₂ : suMat i₂ * suMat i₂ = 1) (hc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁)
    (hd₁ : finrank K (eigSpace (suMat i₁) (-1)) = 2)
    (hd₂ : finrank K (eigSpace (suMat i₂) (-1)) = 2) (hne : i₁ ≠ i₂) :
    eigSpace (suMat i₁) (-1) ⊓ eigSpace (suMat i₂) (-1) = ⊥ ∨
      ∃ g : Su K p f n, suMat i₁ * suMat g = suMat g * negBlock K n 0 ∧
        suMat i₂ * suMat g = suMat g * negBlock K n 1 := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hf := toLin'_mul_self h₁
  have hg := toLin'_mul_self h₂
  have hfg := toLin'_mul_comm hc
  have hint := isInternal_jointEigenspace h2 hf hg hfg
  set d : Bool × Bool → ℕ := fun s => finrank K (jointEig (suMat i₁) (suMat i₂) s) with hd
  have E1 : 2 = d (false, true) + d (false, false) := by
    rw [← hd₁]
    exact finrank_eigenspace_eq h2 hg hfg false
  have E2 : 2 = d (true, false) + d (false, false) := by
    rw [← hd₂]
    exact finrank_eigenspace_eq' h2 hf hfg false
  have E3 : n = d (true, true) + d (true, false) + (d (false, true) + d (false, false)) := by
    have := finrank_eq_sum_of_isInternal (jointEig (suMat i₁) (suMat i₂)) hint
    rw [Module.finrank_fin_fun, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
      Fintype.sum_bool] at this
    exact this
  have hmm : d (false, false) = 0 ∨ d (false, false) = 1 ∨ d (false, false) = 2 := by omega
  rcases hmm with h0 | h1 | h2'
  · left
    have : jointEig (suMat i₁) (suMat i₂) (false, false) = ⊥ := Submodule.finrank_eq_zero.mp h0
    exact this
  · right
    refine (exists_su_frame hσ h2 (by omega) h₁ h₂ hc (pat n) ?_).imp fun g hg' => ?_
    · rintro ⟨_ | _, _ | _⟩
      · rw [card_pat_ff hn]
        show 1 = d (false, false)
        omega
      · rw [card_pat_ft hn]
        show 1 = d (false, true)
        omega
      · rw [card_pat_tf hn]
        show 1 = d (true, false)
        omega
      · rw [card_pat_tt hn]
        show n - 3 = d (true, true)
        omega
    · rw [diagonal_pat_fst, diagonal_pat_snd] at hg'
      exact hg'
  · exfalso
    have hz1 : jointEig (suMat i₁) (suMat i₂) (false, true) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by change d (false, true) = 0; omega)
    have hz2 : jointEig (suMat i₁) (suMat i₂) (true, false) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by change d (true, false) = 0; omega)
    have := eq_of_jointEigenspace_mixed_eq_bot h2 hf hg hfg hz2 hz1
    exact hne (suMat_injective (Matrix.toLin'.injective this))

end Dichotomy

section Generation

theorem B12_map_blockEmb {m : ℕ} (hm : 3 ≤ m) :
    (B12 K p f).map (blockEmb K p f m 3 0 (by omega)) =
      (blockEmb K p f m 2 0 (by omega)).range := by
  rw [B12, embSUid_two_eq_blockEmb, ← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (blockEmb_comp (K := K) (p := p) (f := f) (by omega) (by omega))

theorem B23_map_blockEmb {m : ℕ} (hm : 3 ≤ m) :
    (B23 K p f).map (blockEmb K p f m 3 0 (by omega)) =
      (blockEmb K p f m 2 1 (by omega)).range := by
  rw [B23, embSUid_zero_eq_blockEmb, ← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (blockEmb_comp (K := K) (p := p) (f := f) (by omega) (by omega))

theorem range_blockEmb_three (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {m : ℕ} (hm : 3 ≤ m) :
    (blockEmb K p f m 3 0 (by omega)).range =
      (blockEmb K p f m 2 0 (by omega)).range ⊔ (blockEmb K p f m 2 1 (by omega)).range := by
  rw [MonoidHom.range_eq_map,
    ← CFSG.ClassicalInvolution.Phan.B12_sup_B23 hK (prime_pow_ne_two_of_ne_two hp f),
    Subgroup.map_sup, B12_map_blockEmb hm, B23_map_blockEmb hm]

end Generation

section NonCommuting

theorem not_comm_blockEmb_zero_one (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ∃ A : Su K p f 2, blockEmb K p f n 2 0 (by omega) A *
        blockEmb K p f n 2 1 (by omega) (negOneSU K p f) ≠
      blockEmb K p f n 2 1 (by omega) (negOneSU K p f) * blockEmb K p f n 2 0 (by omega) A := by
  refine ⟨rotSU (unitaryInvolution K p f), ?_⟩
  intro h
  have h1 := congr_fun (congr_fun (congrArg suMat h) ⟨0, by omega⟩) ⟨1, by omega⟩
  have e : suMat (blockEmb K p f n 2 1 (by omega : 1 + 2 ≤ n) (negOneSU K p f)) =
      negBlock K n 1 := by
    rw [suMat_blockEmb, suMat_negOneSU]
    rfl
  rw [suMat_mul, suMat_mul, e, negBlock_eq_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h1
  have e2 : suMat (blockEmb K p f n 2 0 (by omega : 0 + 2 ≤ n) (rotSU (unitaryInvolution K p f)))
      ⟨0, by omega⟩ ⟨1, by omega⟩ = -1 := by
    rw [suMat_blockEmb]
    have := blockMat_apply_blockIdx (m := n) (i := 0) (k := 2) (by omega)
      (rotMat : Matrix (Fin 2) (Fin 2) K) 0 1
    have e3 : (rotMat : Matrix (Fin 2) (Fin 2) K) 0 1 = -1 := by simp [rotMat]
    rw [e3] at this
    exact this
  rw [e2] at h1
  norm_num at h1
  exact h2 (by linear_combination h1)

end NonCommuting

section Main

theorem unitaryBlockStandardPair_of_normalized {X : Type} [Group X] {θ : Su K p f 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {W U V : Subgroup X} (hW : θ.range = W)
    (hU : (B12 K p f).map θ = U) (hV : (B23 K p f).map θ = V) :
    UnitaryBlockStandardPair K p f W U V := by
  have e : (MulAut.conj (1 : Su K p f 3)⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  refine ⟨θ, 1, hW, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [e, Subgroup.map_id]
    exact hU
  · rw [e, Subgroup.map_id]
    exact hV

theorem exists_injective_hom_of_su_frame (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hn : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} (g : Su K p f n)
    (h₁ : L₁ = (blockEmb K p f n 2 0 (by omega)).range.map (MulAut.conj g).toMonoidHom)
    (h₂ : L₂ = (blockEmb K p f n 2 1 (by omega)).range.map (MulAut.conj g).toMonoidHom) :
    ∃ θ : Su K p f 3 →* Su K p f n, Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
      (B12 K p f).map θ = L₁ ∧ (B23 K p f).map θ = L₂ ∧
      (∀ A : Su K p f 2, θ (embSUid (unitaryInvolution K p f) 2 A) =
        g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) ∧
      (∀ A : Su K p f 2, θ (embSUid (unitaryInvolution K p f) 0 A) =
        g * blockEmb K p f n 2 1 (by omega) A * g⁻¹) := by
  refine ⟨(MulAut.conj g).toMonoidHom.comp (blockEmb K p f n 3 0 (by omega)), ?_, ?_, ?_, ?_,
    fun A => ?_, fun A => ?_⟩
  · exact (MulAut.conj g).injective.comp (blockEmb_injective _)
  · rw [MonoidHom.range_comp, range_blockEmb_three hK hp hn, Subgroup.map_sup, h₁, h₂]
  · rw [← Subgroup.map_map, B12_map_blockEmb hn, h₁]
  · rw [← Subgroup.map_map, B23_map_blockEmb hn, h₂]
  · rw [embSUid_two_eq_blockEmb]
    exact congrArg (fun x => g * x * g⁻¹) (blockEmb_comp_apply (K := K) (p := p) (f := f)
      (by omega) (by omega) A)
  · rw [embSUid_zero_eq_blockEmb]
    exact congrArg (fun x => g * x * g⁻¹) (blockEmb_comp_apply (K := K) (p := p) (f := f)
      (by omega) (by omega) A)

theorem inf_eq_bot_or_exists_conj_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    minusSpaceSU i₁ ⊓ minusSpaceSU i₂ = ⊥ ∨
      ∃ g : Su K p f n,
        L₁ = (blockEmb K p f n 2 0 (by omega)).range.map (MulAut.conj g).toMonoidHom ∧
        L₂ = (blockEmb K p f n 2 1 (by omega)).range.map (MulAut.conj g).toMonoidHom ∧
        i₁ = g * blockEmb K p f n 2 0 (by omega) (negOneSU K p f) * g⁻¹ ∧
        i₂ = g * blockEmb K p f n 2 1 (by omega) (negOneSU K p f) * g⁻¹ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hcc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁ := by
    rw [← suMat_mul, ← suMat_mul, hc.eq]
  rcases inf_eq_bot_or_exists_su_frame hK h2 hn3 h₁.coe_mul_self h₂.coe_mul_self hcc
    (h₁.finrank_minusSpaceSU h2) (h₂.finrank_minusSpaceSU h2) hne with hV | ⟨g, hP1, hP2⟩
  · exact Or.inl hV
  · refine Or.inr ⟨g, ?_, ?_, ?_, ?_⟩
    · rw [h₁.eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq g hP1,
        range_blockEmb_eq_longRootGroupSU h2 (by omega)]
    · rw [h₂.eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq g hP2,
        range_blockEmb_eq_longRootGroupSU h2 (by omega)]
    · have : i₁ * g = g * blockEmb K p f n 2 0 (by omega) (negOneSU K p f) := by
        apply suMat_injective
        rw [suMat_mul, suMat_mul, suMat_blockEmb, suMat_negOneSU]
        exact hP1
      rw [eq_mul_inv_iff_mul_eq, this]
    · have : i₂ * g = g * blockEmb K p f n 2 1 (by omega) (negOneSU K p f) := by
        apply suMat_injective
        rw [suMat_mul, suMat_mul, suMat_blockEmb, suMat_negOneSU]
        exact hP2
      rw [eq_mul_inv_iff_mul_eq, this]

theorem lemma_6_5_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    ((∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∧ minusSpaceSU i₁ ≤ fixSpaceSU i₂ ∧
        minusSpaceSU i₂ ≤ fixSpaceSU i₁ ∧ minusSpaceSU i₁ ⊓ minusSpaceSU i₂ = ⊥) ∨
      (i₂ ∉ Subgroup.centralizer (L₁ : Set (Su K p f n)) ∧
        ∃ θ : Su K p f 3 →* Su K p f n, Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
          (B12 K p f).map θ = L₁ ∧ (B23 K p f).map θ = L₂) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hcc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁ := by
    rw [← suMat_mul, ← suMat_mul, hc.eq]
  rcases inf_eq_bot_or_exists_conj_su hK hp hn3 h₁ h₂ hc hne with hV | ⟨g, e₁, e₂, -, hi₂⟩
  · left
    refine ⟨?_, eigSpace_neg_one_le_one h₂.coe_mul_self hcc hV,
      eigSpace_neg_one_le_one h₁.coe_mul_self hcc.symm (by rwa [inf_comm]), hV⟩
    intro x hx y hy
    rw [h₁.eq_longRootGroupSU h2] at hx
    rw [h₂.eq_longRootGroupSU h2] at hy
    exact mul_comm_of_inf_eq_bot_su h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy
  · right
    refine ⟨?_, (exists_injective_hom_of_su_frame hK hp hn3 g e₁ e₂).imp fun θ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩
    intro hmem
    obtain ⟨A, hA⟩ := not_comm_blockEmb_zero_one (K := K) (p := p) (f := f) h2 hn3
    have hx : g * blockEmb K p f n 2 0 (by omega) A * g⁻¹ ∈ L₁ := by
      rw [e₁]
      exact Subgroup.mem_map.mpr ⟨_, ⟨A, rfl⟩, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hmem _ hx
    rw [hi₂] at h
    apply hA
    calc blockEmb K p f n 2 0 (by omega) A * blockEmb K p f n 2 1 (by omega) (negOneSU K p f)
        = g⁻¹ * (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹ *
            (g * blockEmb K p f n 2 1 (by omega) (negOneSU K p f) * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * blockEmb K p f n 2 1 (by omega) (negOneSU K p f) * g⁻¹ *
            (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹)) * g := by rw [h]
      _ = blockEmb K p f n 2 1 (by omega) (negOneSU K p f) * blockEmb K p f n 2 0 (by omega) A := by
          group

theorem lemma_6_5_su_involutions (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂)
    (hnot : i₂ ∉ Subgroup.centralizer (L₁ : Set (Su K p f n))) :
    ∃ θ : Su K p f 3 →* Su K p f n, Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
      (B12 K p f).map θ = L₁ ∧ (B23 K p f).map θ = L₂ ∧
      θ (embSUid (unitaryInvolution K p f) 2 (negOneSU K p f)) = i₁ ∧
      θ (embSUid (unitaryInvolution K p f) 0 (negOneSU K p f)) = i₂ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hcc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁ := by
    rw [← suMat_mul, ← suMat_mul, hc.eq]
  rcases inf_eq_bot_or_exists_conj_su hK hp hn3 h₁ h₂ hc hne with hV | ⟨g, e₁, e₂, hi₁, hi₂⟩
  · exfalso
    apply hnot
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [h₁.eq_longRootGroupSU h2] at hx
    have hy : i₂ ∈ longRootGroupSU K p f (suMat i₂) := by
      rw [← h₂.eq_longRootGroupSU h2]
      exact h₂.mem
    exact mul_comm_of_inf_eq_bot_su h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy
  · obtain ⟨θ, hinj, hrange, hU, hV, hθ₁, hθ₂⟩ :=
      exists_injective_hom_of_su_frame hK hp hn3 g e₁ e₂
    exact ⟨θ, hinj, hrange, hU, hV, (hθ₁ _).trans hi₁.symm, (hθ₂ _).trans hi₂.symm⟩

theorem rot_mul_negOneSU_pair :
    embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f)) *
        embSUid (unitaryInvolution K p f) 2 (negOneSU K p f) =
      (embSUid (unitaryInvolution K p f) 2 (negOneSU K p f) *
          embSUid (unitaryInvolution K p f) 0 (negOneSU K p f)) *
        embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f)) := by
  apply suMat_injective
  simp only [suMat_mul]
  change embPair 0 (rotMat : Matrix (Fin 2) (Fin 2) K) * embPair 2 (suMat (negOneSU K p f)) =
    (embPair 2 (suMat (negOneSU K p f)) * embPair 0 (suMat (negOneSU K p f))) *
      embPair 0 (rotMat : Matrix (Fin 2) (Fin 2) K)
  rw [suMat_negOneSU]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [embPair, rotMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem rot_mul_blockEmb_negOneSU (hn3 : 3 ≤ n) :
    blockEmb K p f n 3 0 (by omega) (embSUid (unitaryInvolution K p f) 0
        (rotSU (unitaryInvolution K p f))) *
        blockEmb K p f n 2 0 (by omega) (negOneSU K p f) =
      (blockEmb K p f n 2 0 (by omega) (negOneSU K p f) *
          blockEmb K p f n 2 1 (by omega) (negOneSU K p f)) *
        blockEmb K p f n 3 0 (by omega) (embSUid (unitaryInvolution K p f) 0
          (rotSU (unitaryInvolution K p f))) := by
  have h := congrArg (blockEmb K p f n 3 0 (by omega))
    (rot_mul_negOneSU_pair (K := K) (p := p) (f := f))
  simp only [map_mul] at h
  have e1 : blockEmb K p f n 3 0 (by omega) (embSUid (unitaryInvolution K p f) 2
      (negOneSU K p f)) = blockEmb K p f n 2 0 (by omega) (negOneSU K p f) := by
    rw [embSUid_two_eq_blockEmb]
    exact blockEmb_comp_apply (K := K) (p := p) (f := f) (by omega) (by omega) _
  have e2 : blockEmb K p f n 3 0 (by omega) (embSUid (unitaryInvolution K p f) 0
      (negOneSU K p f)) = blockEmb K p f n 2 1 (by omega) (negOneSU K p f) := by
    rw [embSUid_zero_eq_blockEmb]
    exact blockEmb_comp_apply (K := K) (p := p) (f := f) (by omega) (by omega) _
  rw [e1, e2] at h
  exact h

theorem exists_isLongRootSU2_third (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂)
    (hnot : i₂ ∉ Subgroup.centralizer (L₁ : Set (Su K p f n))) :
    ∃ L₃ : Subgroup (Su K p f n), IsLongRootSU2 K p f hn L₃ (i₁ * i₂) ∧ L₃ ≤ L₁ ⊔ L₂ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hcc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁ := by
    rw [← suMat_mul, ← suMat_mul, hc.eq]
  rcases inf_eq_bot_or_exists_conj_su hK hp hn3 h₁ h₂ hc hne with hV | ⟨g, e₁, e₂, hi₁, hi₂⟩
  · exfalso
    apply hnot
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [h₁.eq_longRootGroupSU h2] at hx
    have hy : i₂ ∈ longRootGroupSU K p f (suMat i₂) := by
      rw [← h₂.eq_longRootGroupSU h2]
      exact h₂.mem
    exact mul_comm_of_inf_eq_bot_su h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy
  · set w : Su K p f n := blockEmb K p f n 3 0 (by omega) (embSUid (unitaryInvolution K p f) 0
      (rotSU (unitaryInvolution K p f))) with hw
    have key : w * rootInvSU K p f hn * w⁻¹ =
        blockEmb K p f n 2 0 (by omega) (negOneSU K p f) *
          blockEmb K p f n 2 1 (by omega) (negOneSU K p f) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact rot_mul_blockEmb_negOneSU hn3
    refine ⟨(rootSU2 K p f hn).map (MulAut.conj (g * w)).toMonoidHom, ⟨g * w, rfl, ?_⟩, ?_⟩
    · rw [hi₁, hi₂]
      calc g * blockEmb K p f n 2 0 (by omega) (negOneSU K p f) * g⁻¹ *
            (g * blockEmb K p f n 2 1 (by omega) (negOneSU K p f) * g⁻¹)
          = g * (blockEmb K p f n 2 0 (by omega) (negOneSU K p f) *
              blockEmb K p f n 2 1 (by omega) (negOneSU K p f)) * g⁻¹ := by group
        _ = g * (w * rootInvSU K p f hn * w⁻¹) * g⁻¹ := by rw [key]
        _ = g * w * rootInvSU K p f hn * (g * w)⁻¹ := by group
    · have hsup : L₁ ⊔ L₂ =
          (blockEmb K p f n 3 0 (by omega)).range.map (MulAut.conj g).toMonoidHom := by
        rw [e₁, e₂, ← Subgroup.map_sup, ← range_blockEmb_three hK hp hn3]
      rw [hsup]
      rintro _ ⟨x, hx, rfl⟩
      have hx3 : x ∈ (blockEmb K p f n 3 0 (by omega)).range := by
        rw [range_blockEmb_three hK hp hn3]
        exact Subgroup.mem_sup_left hx
      have hwr : w ∈ (blockEmb K p f n 3 0 (by omega)).range := ⟨_, rfl⟩
      refine ⟨w * x * w⁻¹, ?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwr hx3) (Subgroup.inv_mem _ hwr)
      · simp [mul_assoc]

theorem mem_centralizer_iff_forall_comm_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    i₂ ∈ Subgroup.centralizer (L₁ : Set (Su K p f n)) ↔ ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  constructor
  · intro hmem
    rcases lemma_6_5_su hK hp hn3 h₁ h₂ hc hne with h | ⟨hnot, -⟩
    · exact h.1
    · exact absurd hmem hnot
  · intro h
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => h x hx i₂ h₂.mem

theorem forall_comm_of_mem_centralizer_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂)
    (hmem : i₂ ∈ Subgroup.centralizer (L₁ : Set (Su K p f n))) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x :=
  (mem_centralizer_iff_forall_comm_su hK hp hn3 h₁ h₂ hc hne).mp hmem

theorem unitaryBlockStandardPair_of_not_mem_centralizer (hK : Nat.card K = (p ^ f) ^ 2)
    (hp : p ≠ 2) {hn : 2 ≤ n} (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)}
    {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂)
    (hnot : i₂ ∉ Subgroup.centralizer (L₁ : Set (Su K p f n))) :
    UnitaryBlockStandardPair K p f (L₁ ⊔ L₂) L₁ L₂ := by
  rcases lemma_6_5_su hK hp hn3 h₁ h₂ hc hne with ⟨hcomm, -⟩ | ⟨-, θ, hinj, hrange, hU, hV⟩
  · exact absurd ((mem_centralizer_iff_forall_comm_su hK hp hn3 h₁ h₂ hc hne).mpr hcomm) hnot
  · exact unitaryBlockStandardPair_of_normalized
      (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) hrange hU hV

theorem commute_or_unitaryBlockStandardPair (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn : 2 ≤ n} (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∨
      (i₂ ∉ Subgroup.centralizer (L₁ : Set (Su K p f n)) ∧
        UnitaryBlockStandardPair K p f (L₁ ⊔ L₂) L₁ L₂) := by
  by_cases hmem : i₂ ∈ Subgroup.centralizer (L₁ : Set (Su K p f n))
  · exact Or.inl ((mem_centralizer_iff_forall_comm_su hK hp hn3 h₁ h₂ hc hne).mp hmem)
  · exact Or.inr ⟨hmem, unitaryBlockStandardPair_of_not_mem_centralizer hK hp hn3 h₁ h₂ hc hne
      hmem⟩

theorem unitaryBlockStandardPair_map {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K p f W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    UnitaryBlockStandardPair K p f (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

end Main

end CFSG.ClassicalInvolution.Models
