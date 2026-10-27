module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLLtProof

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Matrix CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_root_of_generic_le [CharP K 2] {k : Subfield K} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hnd : n ≤ d) (hn : 3 ≤ n) (hK : Nat.card K = Nat.card k ^ d)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)} (hk : slSub n k ≤ H) {v φ : Fin n → K}
    (hφv : φ ⬝ᵥ v = 0) (hτ : tv v φ hφv ∈ H) (hφ0 : φ ≠ 0)
    (hgen : ∀ ψ : Fin n → K, (∀ i, ψ i ∈ k) → ψ ⬝ᵥ v = 0 → ψ = 0) :
    ∃ a ∉ k, ∃ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij a ∈ H := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (funext h)
  obtain ⟨m₁, hm₁j, -⟩ := exists_fin_ne_ne' hn j j
  obtain ⟨m₂, hm₂j, hm₂m₁⟩ := exists_fin_ne_ne' hn j m₁
  have ha₁ : v m₁ ≠ 0 := by
    intro h0
    have h1 := hgen (Pi.single m₁ 1) (single_rat m₁) (by rw [single_dotProduct, h0, mul_zero])
    simpa using congrFun h1 m₁
  have ha₂ : v m₂ / v m₁ ∉ k := by
    intro hc
    set ψ : Fin n → K := (Pi.single m₂ 1 : Fin n → K) - (v m₂ / v m₁) • (Pi.single m₁ 1 : Fin n → K)
      with hψdef
    have hψ : ∀ i, ψ i ∈ k := by
      intro i
      rw [hψdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact k.sub_mem (single_rat m₂ i) (k.mul_mem hc (single_rat m₁ i))
    have hdot : ψ ⬝ᵥ v = 0 := by
      rw [hψdef, sub_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct,
        smul_eq_mul]
      field_simp
      ring
    have h1 := congrFun (hgen ψ hψ hdot) m₂
    simp [hψdef, hm₂m₁] at h1
  have hu : ∀ c₁ ∈ k, ∀ c₂ ∈ k, u2 (c₁ * v m₁ + c₂ * v m₂) ∈ restrictSubgroup H j v := by
    intro c₁ hc₁ c₂ hc₂
    set ψ : Fin n → K := c₁ • (Pi.single m₁ 1 : Fin n → K) + c₂ • (Pi.single m₂ 1 : Fin n → K)
      with hψdef
    have hψrat : ∀ i, ψ i ∈ k := fun i => by
      rw [hψdef, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      exact k.add_mem (k.mul_mem hc₁ (single_rat m₁ i)) (k.mul_mem hc₂ (single_rat m₂ i))
    have hψj0 : ψ j = 0 := by
      rw [hψdef]
      simp [hm₁j, hm₂j]
    have hψj : ψ ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0 := by
      rw [dotProduct_single_one]
      exact hψj0
    have hψv : ψ ⬝ᵥ v = c₁ * v m₁ + c₂ * v m₂ := by
      rw [hψdef, add_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct,
        single_dotProduct]
      simp
    refine ⟨tv (Pi.single j 1) ψ hψj, hk (tv_mem_slSub hψj (single_rat j) hψrat),
      rows ψ 0, ?_, ?_⟩
    · rw [tv_coe, colPair_mul]
      simp
    · rw [mul_colPair, u2_coe]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [hψv, hψj0]
  have hl : l2 (φ j) ∈ restrictSubgroup H j v := by
    refine ⟨tv v φ hφv, hτ, rows 0 φ, ?_, ?_⟩
    · rw [tv_coe, colPair_mul]
      simp
    · rw [mul_colPair, l2_coe]
      ext r c
      fin_cases r <;> fin_cases c <;> simp [hφv]
  have hM : restrictSubgroup H j v = ⊤ :=
    sl2_eq_top_of_root_groups hd hd2 hK ha₁ ha₂ hj hu hl
  obtain ⟨a, haS⟩ : ∃ a : K, a ∉ Set.range
      (fun c : ↥(Finset.univ.erase j) → k => ∑ m : ↥(Finset.univ.erase j), (c m : K) * v m.1) := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective
        (fun c : ↥(Finset.univ.erase j) → k => ∑ m : ↥(Finset.univ.erase j), (c m : K) * v m.1) :=
      fun a => h a
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [hK, Nat.card_fun, Nat.card_eq_fintype_card (α := ↥(Finset.univ.erase j)),
      Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin] at h1
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right h2 (by omega)))
  have ha0 : a ≠ 0 := fun h => haS ⟨0, by simp [h]⟩
  have hau : u2 a ∈ restrictSubgroup H j v := hM ▸ Subgroup.mem_top _
  obtain ⟨g, hg, Ψ, hgΨ, hXΨ⟩ := hau
  rw [mul_colPair, u2_coe] at hXΨ
  have e00 := congrFun (congrFun hXΨ 0) 0
  have e01 := congrFun (congrFun hXΨ 0) 1
  have e10 := congrFun (congrFun hXΨ 1) 0
  have e11 := congrFun (congrFun hXΨ 1) 1
  simp at e00 e01 e10 e11
  have hgmat : (g : Matrix (Fin n) (Fin n) K) =
      1 + (vecMulVec (Pi.single j 1) (Ψ 0) + vecMulVec v (Ψ 1)) := by
    rw [hgΨ, colPair_mul]
  suffices key : ∃ γ : Fin n → K, ∃ hγ : γ ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0,
      tv (Pi.single j 1) γ hγ ∈ H ∧ ∃ m, γ m ∉ k by
    obtain ⟨γ, hγ, hmem, m, hm⟩ := key
    obtain ⟨l, hl, hroot⟩ := root_mem_of_tv_single hk hn hγ hmem m
    exact ⟨γ m, hm, j, l, hl, hroot⟩
  by_cases hβ : Ψ 1 = 0
  ·
    have hα : Ψ 0 ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0 := by
      rw [dotProduct_single_one]
      exact e00
    have hgtv : g = tv (Pi.single j 1) (Ψ 0) hα := by
      apply Subtype.ext
      rw [hgmat, tv_coe, hβ]
      simp
    refine ⟨Ψ 0, hα, hgtv ▸ hg, ?_⟩
    by_contra hall
    push Not at hall
    apply haS
    refine ⟨fun m => ⟨Ψ 0 m.1, hall m.1⟩, ?_⟩
    show ∑ m : ↥(Finset.univ.erase j), Ψ 0 m.1 * v m.1 = a
    rw [Finset.sum_coe_sort (Finset.univ.erase j) (fun m => Ψ 0 m * v m),
      Finset.sum_erase _ (by rw [e00, zero_mul])]
    exact e01.symm
  ·
    have hZ : Ψ * colPair j v = !![0, a; 0, 0] := by
      rw [mul_colPair, e00, ← e01, ← e10, e11]
    have hNN : (colPair j v * Ψ) * (colPair j v * Ψ) =
        vecMulVec (Pi.single j 1) (a • Ψ 1) := by
      have h1 : (colPair j v * Ψ) * (colPair j v * Ψ) = colPair j v * ((Ψ * colPair j v) * Ψ) := by
        simp only [Matrix.mul_assoc]
      have h2 : (!![0, a; 0, 0] : Matrix (Fin 2) (Fin 2) K) * Ψ = rows (a • Ψ 1) 0 := by
        ext r m
        fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, rows]
      rw [h1, hZ, h2, colPair_mul]
      simp
    have hgg : ((g * g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + vecMulVec (Pi.single j 1) (a • Ψ 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hgΨ]
      have h3 : (1 + colPair j v * Ψ) * (1 + colPair j v * Ψ) =
          1 + (colPair j v * Ψ + colPair j v * Ψ) +
            (colPair j v * Ψ) * (colPair j v * Ψ) := by
        noncomm_ring
      rw [h3, matrix_add_self, hNN]
      simp
    have hγ : (a • Ψ 1) ⬝ᵥ (Pi.single j 1 : Fin n → K) = 0 := by
      rw [smul_dotProduct, dotProduct_single_one, ← e10, smul_zero]
    have hggtv : g * g = tv (Pi.single j 1) (a • Ψ 1) hγ := Subtype.ext hgg
    refine ⟨a • Ψ 1, hγ, hggtv ▸ H.mul_mem hg hg, ?_⟩
    by_contra hall
    push Not at hall
    have h0 := hgen (a • Ψ 1) hall (by rw [smul_dotProduct, e11, smul_zero])
    exact hβ ((smul_eq_zero.mp h0).resolve_left ha0)


theorem not_generic_of_lt {k : Subfield K} {d : ℕ} (hK : Nat.card K = Nat.card k ^ d)
    (hnd : d < n) (v : Fin n → K) :
    ¬ ∀ ψ : Fin n → K, (∀ i, ψ i ∈ k) → ψ ⬝ᵥ v = 0 → ψ = 0 := by
  intro hgen
  have hinj : Function.Injective (fun c : Fin n → k => ∑ m, (c m : K) * v m) := by
    intro c c' h
    have h1 : (fun m => ((c m : K) - (c' m : K))) ⬝ᵥ v = 0 := by
      simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h
    have h2 := hgen _ (fun i => k.sub_mem (c i).2 (c' i).2) h1
    funext m
    exact Subtype.ext (sub_eq_zero.mp (congrFun h2 m))
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [hK, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h1
  have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
  exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right h2 hnd))

theorem subfieldPairSL_two_gen [CharP K 2] (k : Subfield K) {p : ℕ} (hp : p.Prime) (hK : Nat.card K = Nat.card k ^ p)
    (hp2 : p ≠ 2) {n : ℕ} (hn3 : 3 ≤ n) (A : GL (Fin n) K)
    (hne : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k) :
    Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
      ((slSub n k).map (slConjugation n K A).toMonoidHom :
        Set (SpecialLinearGroup (Fin n) K))) = ⊤ := by
  set G₀ := slSub n k with hG₀
  set G₁ := G₀.map (slConjugation n K A).toMonoidHom with hG₁
  set H := Subgroup.closure ((G₀ : Set (SpecialLinearGroup (Fin n) K)) ∪
    (G₁ : Set (SpecialLinearGroup (Fin n) K))) with hH
  have hk : G₀ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hk1 : G₁ ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  by_contra hHtop
  have NIR : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij a ∉ H :=
    fun a ha i j hij hmem => hHtop (eq_top_of_root_not_mem hk hn3 hp hK ha hij hmem)
  have hd2 := hp2
  have hall : ∀ (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0), tv v φ h ∈ H → v ≠ 0 → tv v φ h ∈ G₀ := by
    intro v φ h hmem hv0
    by_cases hφ0 : φ = 0
    · subst hφ0
      have h1 : tv v 0 h = 1 := Subtype.ext (by simp [tv_coe])
      rw [h1]
      exact G₀.one_mem
    · rcases tv_mem_slSub_or_generic hk hn3 NIR h hmem hv0 with hrat | hgen
      · exact hrat
      · by_cases hnp : n ≤ p
        · obtain ⟨a, ha, i, j, hij, hmem'⟩ :=
            exists_root_of_generic_le hp hd2 hnp hn3 hK hk h hmem hφ0 hgen
          exact absurd hmem' (NIR a ha i j hij)
        · exact absurd hgen (not_generic_of_lt hK (by omega) v)
  have hroot : ∀ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k →
      slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ G₀ := by
    intro i j hij c hc
    have h1 : slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ H :=
      hk1 (Subgroup.mem_map_of_mem _ (transvection_mem_slSub hij hc))
    have hne0 : (A : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K) ≠ 0 := by
      intro h0
      have h2 := congrArg (fun w => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) h0
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      simpa using congrFun h2 i
    rw [transvection_eq_tv hij c, slConjugation_tv] at h1 ⊢
    exact hall _ _ _ h1 hne0
  exact hne (map_conj_slSub_eq A hroot)


theorem subfieldPairSL_gen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : Subfield K) (hK : Nat.card K = Nat.card k ^ p) {n : ℕ} (hn3 : 3 ≤ n)
    (A : GL (Fin n) K)
    (hne : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k) :
    Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
      ((slSub n k).map (slConjugation n K A).toMonoidHom :
        Set (SpecialLinearGroup (Fin n) K))) = ⊤ := by
  by_cases h2 : CharP K 2
  · exact subfieldPairSL_two_gen k hp hK hp2 hn3 A hne
  · exact subfieldPairSL_odd hp hp2 hK (three_le_card_of_not_charP_two h2) hn3 A hne

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
