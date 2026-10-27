module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniSpec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace CrossUni

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.RankFourTheoremC.TorusU

section Pairs

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {S : (Fin n → K) →ₗ[K] (Fin n → K)}

structure PairedFam {ι : Type} [DecidableEq ι] (σ : K ≃+* K) (S : (Fin n → K) →ₗ[K] (Fin n → K))
    (c : ι → Fin n → K) (τ : ι → ι) : Prop where
  inv : ∀ i, τ (τ i) = i
  gram : ∀ i j, herm σ (c i) (c j) = if j = τ i then 1 else 0
  eigen : ∀ i, ∃ a : K, S (c i) = a • c i

theorem exists_aniso_of_card_lt (hσ : IsUnitaryInvolution σ) {ι : Type} [Fintype ι]
    (hk : Fintype.card ι < n) (s : ι → Fin n → K) (P : (Fin n → K) →ₗ[K] (Fin n → K))
    (hP : ∀ y, y - P y ∈ Submodule.span K (Set.range s))
    (hPs : ∀ y j, herm σ (s j) (P y) = 0) : ∃ y, herm σ (P y) (P y) ≠ 0 := by
  by_contra! h
  have hpol : ∀ y y', herm σ (P y) (P y') = 0 := fun y y' =>
    herm_eq_zero_of_forall_isotropic hσ (S := LinearMap.range P)
      (by rintro _ ⟨z, rfl⟩; exact h z) ⟨y, rfl⟩ ⟨y', rfl⟩
  have hspan : ∀ y, ∀ w ∈ Submodule.span K (Set.range s), herm σ (P y) w = 0 := by
    intro y w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      exact herm_eq_zero_comm σ hσ.invol (hPs y j)
    | zero => exact herm_zero_right σ _
    | add w w' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
    | smul c w _ h1 => rw [herm_smul_right, h1, mul_zero]
  have hP0 : ∀ y, P y = 0 := by
    intro y
    apply eq_zero_of_herm σ
    intro y'
    have : y' = P y' + (y' - P y') := by abel
    rw [this, herm_add_right, hpol, hspan y _ (hP y'), add_zero]
  have htop : Submodule.span K (Set.range s) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    simpa [hP0 y] using hP y
  have hle := finrank_range_le_card (R := K) s
  rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun] at hle
  omega

theorem exists_piece (hσ : IsUnitaryInvolution σ) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hσω : σ ω = ω) (hSp : S ^ 3 = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hn : Fintype.card ι < n) {c : ι → Fin n → K}
    {τ : ι → ι} (hc : PairedFam σ S c τ) :
    (∃ u w : Fin n → K, S u = ω • u ∧ S w = ω ^ 2 • w ∧ herm σ u u = 0 ∧ herm σ w w = 0 ∧
        herm σ u w = 1 ∧ ∀ j, herm σ (c j) u = 0 ∧ herm σ (c j) w = 0) ∨
      (∃ e : Fin n → K, S e = e ∧ herm σ e e = 1 ∧ ∀ j, herm σ (c j) e = 0) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have hp0 : ((3 : ℕ) : K) ≠ 0 := (hω.neZero').out
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
  have hzW : Q y ∈ perp σ c := mem_perp.mpr (hQ1 y)
  have hu0 : ∀ j, ∃ a : K, S (c j) = a • c j ∧ σ a ≠ 0 := by
    intro j
    obtain ⟨a, ha⟩ := hc.eigen j
    obtain ⟨b, hb⟩ := hc.eigen (τ j)
    refine ⟨a, ha, fun h0 => ?_⟩
    have h1 := hS (c j) (c (τ j))
    rw [ha, hb, herm_smul_left, herm_smul_right, hc.gram, if_pos rfl, h0] at h1
    simp at h1
  have hWst : ∀ x ∈ perp σ c, S x ∈ perp σ c := by
    intro x hx j
    obtain ⟨a, ha, ha0⟩ := hu0 j
    have h1 := hS (c j) x
    rw [ha, herm_smul_left, mem_perp.mp hx j] at h1
    exact (mul_eq_zero.mp h1).resolve_left ha0
  have hsp : ∀ i, S (spec ω S 3 i (Q y)) = ω ^ i • spec ω S 3 i (Q y) := fun i =>
    S_spec hω (by norm_num) hSp i (Q y)
  have hmem : ∀ i, spec ω S 3 i (Q y) ∈ perp σ c := fun i => spec_mem hWst hzW i
  have hsum : spec ω S 3 0 (Q y) + spec ω S 3 1 (Q y) + spec ω S 3 2 (Q y) = Q y := by
    have := sum_spec (S := S) hω (by norm_num) hp0 (Q y)
    simpa [Finset.sum_range_succ] using this
  have hne : ∀ i j : ℕ, ¬ 3 ∣ i + j → σ (ω ^ i) * ω ^ j ≠ 1 := by
    intro i j hdiv h
    rw [map_pow, hσω, ← pow_add] at h
    exact hdiv ((hω.pow_eq_one_iff_dvd _).1 h)
  set z0 := spec ω S 3 0 (Q y) with hz0
  set z1 := spec ω S 3 1 (Q y) with hz1
  set z2 := spec ω S 3 2 (Q y) with hz2
  have h01 : herm σ z0 z1 = 0 := herm_eq_zero_of_eigen' hS (hsp 0) (hsp 1) (hne 0 1 (by omega))
  have h02 : herm σ z0 z2 = 0 := herm_eq_zero_of_eigen' hS (hsp 0) (hsp 2) (hne 0 2 (by omega))
  have h10 : herm σ z1 z0 = 0 := herm_eq_zero_of_eigen' hS (hsp 1) (hsp 0) (hne 1 0 (by omega))
  have h11 : herm σ z1 z1 = 0 := herm_eq_zero_of_eigen' hS (hsp 1) (hsp 1) (hne 1 1 (by omega))
  have h20 : herm σ z2 z0 = 0 := herm_eq_zero_of_eigen' hS (hsp 2) (hsp 0) (hne 2 0 (by omega))
  have h22 : herm σ z2 z2 = 0 := herm_eq_zero_of_eigen' hS (hsp 2) (hsp 2) (hne 2 2 (by omega))
  have hzz : herm σ (Q y) (Q y) = herm σ z0 z0 + herm σ z1 z2 + herm σ z2 z1 := by
    conv_lhs => rw [← hsum]
    simp only [herm_add_left, herm_add_right]
    rw [h01, h02, h10, h11, h20, h22]
    ring
  by_cases h0 : herm σ z0 z0 = 0
  · left
    have h12 : herm σ z1 z2 ≠ 0 := by
      intro h
      apply hy
      rw [hzz, h0, h, herm_conj σ hσ.invol z1 z2, h, map_zero]
      simp
    refine ⟨z1, (herm σ z1 z2)⁻¹ • z2, by simpa using hsp 1, ?_, h11, ?_, ?_, fun j => ⟨?_, ?_⟩⟩
    · rw [map_smul, hsp 2, smul_comm]
    · rw [herm_smul_left, herm_smul_right, h22]
      simp
    · rw [herm_smul_right, inv_mul_cancel₀ h12]
    · exact mem_perp.1 (hmem 1) j
    · rw [herm_smul_right, mem_perp.1 (hmem 2) j, mul_zero]
  · right
    obtain ⟨a, ha⟩ := exists_smul_norm_one hσ h0
    refine ⟨a • z0, ?_, ha, fun j => ?_⟩
    · rw [map_smul]
      have := hsp 0
      simp only [pow_zero, one_smul] at this
      rw [this]
    · rw [herm_smul_right, mem_perp.1 (hmem 0) j, mul_zero]

theorem exists_pair (hσ : IsUnitaryInvolution σ) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hσω : σ ω = ω) (hSp : S ^ 3 = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hn : Fintype.card ι + 2 ≤ n) {c : ι → Fin n → K}
    {τ : ι → ι} (hc : PairedFam σ S c τ) :
    ∃ u w : Fin n → K, (∃ a : K, S u = a • u) ∧ (∃ a : K, S w = a • w) ∧ herm σ u u = 0 ∧
      herm σ w w = 0 ∧ herm σ u w = 1 ∧ ∀ j, herm σ (c j) u = 0 ∧ herm σ (c j) w = 0 := by
  rcases exists_piece hσ hω hσω hSp hS (by omega) hc with
    ⟨u, w, hu, hw, huu, hww, huw, hperp⟩ | ⟨e, he1, he2, he3⟩
  · exact ⟨u, w, ⟨ω, hu⟩, ⟨ω ^ 2, hw⟩, huu, hww, huw, hperp⟩
  · have hc' : PairedFam σ S (fun o : Option ι => Option.elim o e c) (Option.map τ) := by
      refine ⟨fun o => ?_, fun o o' => ?_, fun o => ?_⟩
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
        | none => exact ⟨1, by simp [he1]⟩
        | some i => exact hc.eigen i
    rcases exists_piece hσ hω hσω hSp hS (by rw [Fintype.card_option]; omega) hc' with
      ⟨u, w, hu, hw, huu, hww, huw, hperp⟩ | ⟨e2, he21, he22, he23⟩
    · exact ⟨u, w, ⟨ω, hu⟩, ⟨ω ^ 2, hw⟩, huu, hww, huw, fun j => hperp (some j)⟩
    · have h12 : herm σ e e2 = 0 := he23 none
      have h21 : herm σ e2 e = 0 := herm_eq_zero_comm σ hσ.invol h12
      obtain ⟨a, ha⟩ := hσ.exists_norm_neg_one
      obtain ⟨ε, hε, hε1⟩ := hσ.exists_norm_one_ne_one
      have hε0 : (1 - ε) ≠ 0 := sub_ne_zero.mpr (Ne.symm hε1)
      have hc1 : ∀ j, herm σ (c j) e2 = 0 := fun j => he23 (some j)
      refine ⟨e + a • e2, (1 - ε)⁻¹ • (e + (a * ε) • e2), ⟨1, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_,
        fun j => ⟨?_, ?_⟩⟩
      · rw [map_add, map_smul, he1, he21, one_smul]
      · rw [map_smul, map_add, map_smul, he1, he21, one_smul]
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

structure HypPairs {k : ℕ} (σ : K ≃+* K) (S : (Fin n → K) →ₗ[K] (Fin n → K))
    (u w : Fin k → Fin n → K) : Prop where
  uu : ∀ i j, herm σ (u i) (u j) = 0
  ww : ∀ i j, herm σ (w i) (w j) = 0
  uw : ∀ i j, herm σ (u i) (w j) = if i = j then 1 else 0
  eu : ∀ i, ∃ a : K, S (u i) = a • u i
  ew : ∀ i, ∃ a : K, S (w i) = a • w i

theorem HypPairs.paired {k : ℕ} {u w : Fin k → Fin n → K} (h : HypPairs σ S u w)
    (hinv : ∀ c, σ (σ c) = c) : PairedFam σ S (Sum.elim u w) Sum.swap := by
  refine ⟨fun i => Sum.swap_swap i, fun i j => ?_, fun i => ?_⟩
  · rcases i with i | i <;> rcases j with j | j
    · simp [h.uu i j]
    · simp [h.uw i j, eq_comm]
    · rw [Sum.elim_inr, Sum.elim_inl, herm_conj σ hinv, h.uw j i]
      by_cases hij : j = i
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · simp [h.ww i j]
  · rcases i with i | i
    · exact h.eu i
    · exact h.ew i

theorem exists_hypPairs (hσ : IsUnitaryInvolution σ) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hσω : σ ω = ω) (hSp : S ^ 3 = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) :
    ∀ k : ℕ, 2 * k ≤ n → ∃ u w : Fin k → Fin n → K, HypPairs σ S u w := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨u, w, h⟩ := ih (by omega)
    obtain ⟨u0, w0, hu, hw, hu0, hw0, huw0, hperp⟩ := exists_pair hσ hω hσω hSp hS
      (ι := Fin k ⊕ Fin k) (by simp [Fintype.card_sum]; omega) (h.paired hσ.invol)
    have hu0u : ∀ i, herm σ (u i) u0 = 0 := fun i => (hperp (Sum.inl i)).1
    have hu0w : ∀ i, herm σ (u i) w0 = 0 := fun i => (hperp (Sum.inl i)).2
    have hw0u : ∀ i, herm σ (w i) u0 = 0 := fun i => (hperp (Sum.inr i)).1
    have hw0w : ∀ i, herm σ (w i) w0 = 0 := fun i => (hperp (Sum.inr i)).2
    refine ⟨Fin.snoc (α := fun _ => Fin n → K) u u0, Fin.snoc (α := fun _ => Fin n → K) w w0,
      ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i => ?_, fun i => ?_⟩⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simpa using hu0
        | cast j =>
          simpa using herm_eq_zero_comm σ hσ.invol (hu0u j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using hu0u i
        | cast j => simpa using h.uu i j
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simpa using hw0
        | cast j =>
          simpa using herm_eq_zero_comm σ hσ.invol (hw0w j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using hw0w i
        | cast j => simpa using h.ww i j
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simpa using huw0
        | cast j =>
          have := herm_eq_zero_comm σ hσ.invol (hw0u j)
          simp [Fin.snoc_last, Fin.snoc_castSucc, this, (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp [Fin.snoc_last, Fin.snoc_castSucc, hu0w i, (Fin.castSucc_lt_last i).ne]
        | cast j => simpa using h.uw i j
    · induction i using Fin.lastCases with
      | last => simpa using hu
      | cast i => simpa using h.eu i
    · induction i using Fin.lastCases with
      | last => simpa using hw
      | cast i => simpa using h.ew i

end Pairs

end CrossUni

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
