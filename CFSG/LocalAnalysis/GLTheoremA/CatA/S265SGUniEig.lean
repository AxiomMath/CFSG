module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniPairs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniLevi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossUni
open CFSG.LocalAnalysis.RankFourTheoremC.TorusU

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

private theorem SG.exists_joint_pair {ω : K} (hω : IsPrimitiveRoot ω 3) {ι : Type}
    {S : ι → (Fin n → K) →ₗ[K] (Fin n → K)} (hcomm : ∀ i j, Commute (S i) (S j))
    (T : Finset ι) {W₁ W₂ : Submodule K (Fin n → K)}
    (h₁ : ∀ i ∈ T, ∀ x ∈ W₁, S i x ∈ W₁) (h₂ : ∀ i ∈ T, ∀ x ∈ W₂, S i x ∈ W₂)
    {u₀ w₀ : Fin n → K} (hu : u₀ ∈ W₁) (hw : w₀ ∈ W₂) (hne : herm σ u₀ w₀ ≠ 0)
    (hSp : ∀ i, S i ^ 3 = 1) :
    ∃ u ∈ W₁, ∃ w ∈ W₂, (∀ i ∈ T, ∃ a : K, S i u = a • u) ∧ (∀ i ∈ T, ∃ a : K, S i w = a • w) ∧
      herm σ u w = 1 := by
  classical
  induction T using Finset.induction_on generalizing W₁ W₂ u₀ w₀ with
  | empty =>
    refine ⟨u₀, hu, (herm σ u₀ w₀)⁻¹ • w₀, W₂.smul_mem _ hw, by simp, by simp, ?_⟩
    rw [herm_smul_right, inv_mul_cancel₀ hne]
  | insert s T hs ih =>
    haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
    have hp0 : ((3 : ℕ) : K) ≠ 0 := (hω.neZero').out
    have hs₁ := h₁ s (Finset.mem_insert_self s T)
    have hs₂ := h₂ s (Finset.mem_insert_self s T)
    have hsum : ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        herm σ (spec ω (S s) 3 i u₀) (spec ω (S s) 3 j w₀) ≠ 0 := by
      have e1 := sum_spec (S := S s) hω (by norm_num) hp0 u₀
      have e2 := sum_spec (S := S s) hω (by norm_num) hp0 w₀
      have : herm σ u₀ w₀ = ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
          herm σ (spec ω (S s) 3 i u₀) (spec ω (S s) 3 j w₀) := by
        conv_lhs => rw [← e1, ← e2]
        rw [herm_sum_left]
        exact Finset.sum_congr rfl fun i _ => herm_sum_right _ _ _
      rw [← this]
      exact hne
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    obtain ⟨j, -, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have hstab : ∀ (W : Submodule K (Fin n → K)) (m : ℕ), (∀ t ∈ insert s T, ∀ x ∈ W, S t x ∈ W) →
        ∀ t ∈ T, ∀ x ∈ W ⊓ Module.End.eigenspace (S s) (ω ^ m),
          S t x ∈ W ⊓ Module.End.eigenspace (S s) (ω ^ m) := by
      intro W m hW t ht x hx
      obtain ⟨hxW, hxE⟩ := Submodule.mem_inf.mp hx
      refine Submodule.mem_inf.mpr ⟨hW t (Finset.mem_insert_of_mem ht) x hxW, ?_⟩
      have hx2 := Module.End.mem_eigenspace_iff.mp hxE
      rw [Module.End.mem_eigenspace_iff]
      have hc := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f x) (hcomm s t).eq
      simp only [Module.End.mul_apply] at hc
      rw [hc, hx2, map_smul]
    obtain ⟨u, hu1, w, hw1, hue, hwe, huw⟩ := ih (W₁ := W₁ ⊓ Module.End.eigenspace (S s) (ω ^ i))
      (W₂ := W₂ ⊓ Module.End.eigenspace (S s) (ω ^ j)) (hstab W₁ i h₁) (hstab W₂ j h₂)
      ⟨spec_mem hs₁ hu i, Module.End.mem_eigenspace_iff.mpr (S_spec hω (by norm_num) (hSp s) i u₀)⟩
      ⟨spec_mem hs₂ hw j, Module.End.mem_eigenspace_iff.mpr (S_spec hω (by norm_num) (hSp s) j w₀)⟩
      hij
    refine ⟨u, hu1.1, w, hw1.1, fun t ht => ?_, fun t ht => ?_, huw⟩
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨ω ^ i, Module.End.mem_eigenspace_iff.mp hu1.2⟩
      · exact hue t ht
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨ω ^ j, Module.End.mem_eigenspace_iff.mp hw1.2⟩
      · exact hwe t ht

private theorem SG.eigen_fixed {ω : K} (hω : IsPrimitiveRoot ω 3) (hσω : σ ω = ω)
    {S : (Fin n → K) →ₗ[K] (Fin n → K)} (hSp : S ^ 3 = 1)
    (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) {u : Fin n → K} {a : K} (hu : S u = a • u)
    (hne : herm σ u u ≠ 0) : S u = u := by
  have hu0 : u ≠ 0 := fun h0 => hne (by rw [h0, herm_zero_left])
  have h3 : a ^ 3 = 1 := eigen_cube hSp hu hu0
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one h3
  have hσa : σ a = a := by rw [← hi, map_pow, hσω]
  have h2 : a * a = 1 := by
    have h1 := hS u u
    rw [hu, herm_smul_left, herm_smul_right, hσa, ← mul_assoc] at h1
    exact mul_right_cancel₀ hne (by rw [one_mul]; exact h1)
  have ha1 : a = 1 := by
    calc a = a * (a * a) := by rw [h2, mul_one]
      _ = a ^ 3 := by ring
      _ = 1 := h3
  rw [hu, ha1, one_smul]

structure SG.PFam {ι κ : Type} [DecidableEq κ] (σ : K ≃+* K)
    (S : ι → (Fin n → K) →ₗ[K] (Fin n → K)) (c : κ → Fin n → K) (τ : κ → κ) : Prop where
  inv : ∀ i, τ (τ i) = i
  gram : ∀ i j, herm σ (c i) (c j) = if j = τ i then 1 else 0
  eigen : ∀ s i, ∃ a : K, S s (c i) = a • c i

private theorem SG.exists_piece_family (hσ : IsUnitaryInvolution σ) {ω : K}
    (hω : IsPrimitiveRoot ω 3) (hσω : σ ω = ω) {ι : Type} [Fintype ι]
    {S : ι → (Fin n → K) →ₗ[K] (Fin n → K)}
    (hcomm : ∀ i j, Commute (S i) (S j)) (hSp : ∀ i, S i ^ 3 = 1)
    (hS : ∀ i x y, herm σ (S i x) (S i y) = herm σ x y) {κ : Type} [Fintype κ] [DecidableEq κ]
    (hn : Fintype.card κ < n) {c : κ → Fin n → K} {τ : κ → κ} (hc : SG.PFam σ S c τ) :
    (∃ u w : Fin n → K, (∀ s, ∃ a : K, S s u = a • u) ∧ (∀ s, ∃ a : K, S s w = a • w) ∧
        herm σ u u = 0 ∧ herm σ w w = 0 ∧ herm σ u w = 1 ∧
        ∀ j, herm σ (c j) u = 0 ∧ herm σ (c j) w = 0) ∨
      (∃ e : Fin n → K, (∀ s, S s e = e) ∧ herm σ e e = 1 ∧ ∀ j, herm σ (c j) e = 0) := by
  classical
  let Q : (Fin n → K) →ₗ[K] (Fin n → K) :=
    LinearMap.id - ∑ j, (hermL σ (c (τ j))).smulRight (c j)
  have hQy : ∀ y, Q y = y - ∑ j, herm σ (c (τ j)) y • c j := fun y => by simp [Q]
  have hQ1 : ∀ y j, herm σ (c j) (Q y) = 0 := by
    intro y j
    rw [hQy, herm_sub_right, herm_sum_right]
    simp only [herm_smul_right, hc.gram]
    simp [hc.inv]
  obtain ⟨y, hy⟩ := exists_aniso_of_card_lt hσ hn c Q
    (fun y => by
      rw [hQy, sub_sub_cancel]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    hQ1
  have hu0 : ∀ s j, ∃ a : K, S s (c j) = a • c j ∧ σ a ≠ 0 := by
    intro s j
    obtain ⟨a, ha⟩ := hc.eigen s j
    obtain ⟨b, hb⟩ := hc.eigen s (τ j)
    refine ⟨a, ha, fun h0 => ?_⟩
    have h1 := hS s (c j) (c (τ j))
    rw [ha, hb, herm_smul_left, herm_smul_right, hc.gram, if_pos rfl, h0] at h1
    simp at h1
  have hWst : ∀ s, ∀ x ∈ perp σ c, S s x ∈ perp σ c := by
    intro s x hx j
    obtain ⟨a, ha, ha0⟩ := hu0 s j
    have h1 := hS s (c j) x
    rw [ha, herm_smul_left, mem_perp.mp hx j] at h1
    exact (mul_eq_zero.mp h1).resolve_left ha0
  obtain ⟨u, hu, w, hw, hue, hwe, huw⟩ := SG.exists_joint_pair hω hcomm Finset.univ
    (W₁ := perp σ c) (W₂ := perp σ c) (fun s _ => hWst s) (fun s _ => hWst s)
    (mem_perp.mpr (hQ1 y)) (mem_perp.mpr (hQ1 y)) hy hSp
  have fixed : ∀ v, v ∈ perp σ c → (∀ s ∈ Finset.univ, ∃ a : K, S s v = a • v) →
      herm σ v v ≠ 0 → ∃ e : Fin n → K, (∀ s, S s e = e) ∧ herm σ e e = 1 ∧
        ∀ j, herm σ (c j) e = 0 := by
    intro v hv hve hvv
    obtain ⟨a, ha⟩ := exists_smul_norm_one hσ hvv
    refine ⟨a • v, fun s => ?_, ha, fun j => ?_⟩
    · obtain ⟨b, hb⟩ := hve s (Finset.mem_univ s)
      rw [map_smul, SG.eigen_fixed hω hσω (hSp s) (hS s) hb hvv]
    · rw [herm_smul_right, mem_perp.mp hv j, mul_zero]
  by_cases hu0' : herm σ u u = 0
  · by_cases hw0' : herm σ w w = 0
    · exact Or.inl ⟨u, w, fun s => hue s (Finset.mem_univ s), fun s => hwe s (Finset.mem_univ s),
        hu0', hw0', huw, fun j => ⟨mem_perp.mp hu j, mem_perp.mp hw j⟩⟩
    · exact Or.inr (fixed w hw hwe hw0')
  · exact Or.inr (fixed u hu hue hu0')

theorem SG.exists_pair_family (hσ : IsUnitaryInvolution σ) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hσω : σ ω = ω) {ι : Type} [Fintype ι] {S : ι → (Fin n → K) →ₗ[K] (Fin n → K)}
    (hcomm : ∀ i j, Commute (S i) (S j)) (hSp : ∀ i, S i ^ 3 = 1)
    (hS : ∀ i x y, herm σ (S i x) (S i y) = herm σ x y) {κ : Type} [Fintype κ] [DecidableEq κ]
    (hn : Fintype.card κ + 2 ≤ n) {c : κ → Fin n → K} {τ : κ → κ} (hc : SG.PFam σ S c τ) :
    ∃ u w : Fin n → K, (∀ s, ∃ a : K, S s u = a • u) ∧ (∀ s, ∃ a : K, S s w = a • w) ∧
      herm σ u u = 0 ∧ herm σ w w = 0 ∧ herm σ u w = 1 ∧
      ∀ j, herm σ (c j) u = 0 ∧ herm σ (c j) w = 0 := by
  rcases SG.exists_piece_family hσ hω hσω hcomm hSp hS (by omega) hc with
    h | ⟨e, he1, he2, he3⟩
  · exact h
  · have hc' : SG.PFam σ S (fun o : Option κ => Option.elim o e c) (Option.map τ) := by
      refine ⟨fun o => ?_, fun o o' => ?_, fun s o => ?_⟩
      · cases o <;> simp [hc.inv]
      · cases o with
        | none =>
          cases o' with
          | none => simp [he2]
          | some j => simpa using herm_eq_zero_comm σ hσ.invol (he3 j)
        | some i =>
          cases o' with
          | none => simpa using he3 i
          | some j => simpa using hc.gram i j
      · cases o with
        | none => exact ⟨1, by simp [he1 s]⟩
        | some i => exact hc.eigen s i
    rcases SG.exists_piece_family hσ hω hσω hcomm hSp hS
        (by rw [Fintype.card_option]; omega) hc' with
      ⟨u, w, hu, hw, huu, hww, huw, hperp⟩ | ⟨e2, he21, he22, he23⟩
    · exact ⟨u, w, hu, hw, huu, hww, huw, fun j => hperp (some j)⟩
    · have h12 : herm σ e e2 = 0 := he23 none
      have h21 : herm σ e2 e = 0 := herm_eq_zero_comm σ hσ.invol h12
      obtain ⟨a, ha⟩ := hσ.exists_norm_neg_one
      obtain ⟨ε, hε, hε1⟩ := hσ.exists_norm_one_ne_one
      have hε0 : (1 - ε) ≠ 0 := sub_ne_zero.mpr (Ne.symm hε1)
      have hc1 : ∀ j, herm σ (c j) e2 = 0 := fun j => he23 (some j)
      refine ⟨e + a • e2, (1 - ε)⁻¹ • (e + (a * ε) • e2), fun s => ⟨1, ?_⟩, fun s => ⟨1, ?_⟩,
        ?_, ?_, ?_, fun j => ⟨?_, ?_⟩⟩
      · rw [map_add, map_smul, he1 s, he21 s, one_smul]
      · rw [map_smul, map_add, map_smul, he1 s, he21 s, one_smul]
      · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he2, he22, h12,
          h21]
        linear_combination ha
      · have hv : herm σ (e + (a * ε) • e2) (e + (a * ε) • e2) = 0 := by
          simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he2, he22,
            h12, h21, map_mul]
          linear_combination (σ a * a) * hε + ha
        rw [herm_smul_left, herm_smul_right, hv]
        simp
      · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he2, he22, h12,
          h21]
        have e1 : (1 - ε) * (1 - ε)⁻¹ = 1 := mul_inv_cancel₀ hε0
        linear_combination ((1 - ε)⁻¹ * ε) * ha + e1
      · rw [herm_add_right, herm_smul_right, he3 j, hc1 j]
        simp
      · rw [herm_smul_right, herm_add_right, herm_smul_right, he3 j, hc1 j]
        simp

end CFSG.LocalAnalysis.GLTheoremA.S265

end
