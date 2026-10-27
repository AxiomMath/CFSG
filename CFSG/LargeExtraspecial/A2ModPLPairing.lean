module

public import CFSG.LargeExtraspecial.A2ModCfgSL

import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ' : SpecialLinearGroup (Fin 4) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}
  {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V}

theorem IsPointMaps.polar_eq_zero_of_dotProduct_eq_zero
    (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ') (hP : IsPointMaps ρ' Q P Pd)
    {v φ : Fin 4 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hvφ : φ ⬝ᵥ v = 0) :
    QuadraticMap.polar Q (P v) (Pd φ) = 0 := by
  have hT := hA.isTypeA (tv_mem_transvectionSet hv hφ hvφ)
  have hmem : P v + Pd φ ∈ commSpace (ρ' (tv v φ)) := by
    rw [hP.commSpace_tv v φ hv hφ hvφ]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))
  have h0 := hT.2.2.2.2 _ hmem
  rw [QuadraticMap.map_add Q, hP.map_eq_zero v, hP.map_eq_zero_dual φ, zero_add, zero_add] at h0
  exact h0

theorem IsPointMaps.exists_polar_eq (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ')
    (hP : IsPointMaps ρ' Q P Pd) :
    ∃ c₀ : ZMod 2, ∀ v φ : Fin 4 → ZMod 2,
      QuadraticMap.polar Q (P v) (Pd φ) = c₀ * (φ ⬝ᵥ v) := by
  let B1 : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) :=
    (QuadraticMap.polarBilin Q).compl₁₂ P Pd
  let B2 : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) := Matrix.toBilin' 1
  have hB1 : ∀ v φ, B1 v φ = QuadraticMap.polar Q (P v) (Pd φ) := fun v φ => rfl
  have hoff : ∀ i j : Fin 4, i ≠ j →
      QuadraticMap.polar Q (P (Pi.single i 1)) (Pd (Pi.single j 1)) = 0 := by
    intro i j hij
    refine hP.polar_eq_zero_of_dotProduct_eq_zero hA (v := Pi.single i 1) (φ := Pi.single j 1)
      ?_ ?_ ?_
    · exact Pi.single_ne_zero_iff.mpr one_ne_zero
    · exact Pi.single_ne_zero_iff.mpr one_ne_zero
    · rw [dotProduct]
      simp [Pi.single_apply, hij]
  have hdiag : ∀ i j : Fin 4,
      QuadraticMap.polar Q (P (Pi.single i 1)) (Pd (Pi.single i 1)) =
        QuadraticMap.polar Q (P (Pi.single j 1)) (Pd (Pi.single j 1)) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h0 := hP.polar_eq_zero_of_dotProduct_eq_zero hA
        (v := Pi.single i 1 + Pi.single j 1) (φ := Pi.single i 1 + Pi.single j 1) ?_ ?_ ?_
      · rw [map_add, map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
          QuadraticMap.polar_add_right, hoff i j hij, hoff j i (Ne.symm hij)] at h0
        rw [add_zero, zero_add] at h0
        exact (CharTwo.add_eq_zero).mp h0
      · intro h
        have := congrFun h i
        simp [Pi.single_apply, hij] at this
      · intro h
        have := congrFun h i
        simp [Pi.single_apply, hij] at this
      · simp [add_dotProduct, dotProduct_add, Pi.single_apply, hij, Ne.symm hij]
        decide
  refine ⟨QuadraticMap.polar Q (P (Pi.single 0 1)) (Pd (Pi.single 0 1)), ?_⟩
  have hB : B1 = (QuadraticMap.polar Q (P (Pi.single 0 1)) (Pd (Pi.single 0 1))) • B2 := by
    refine LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin 4)) fun i j => ?_
    simp only [Pi.basisFun_apply, LinearMap.smul_apply, smul_eq_mul, B2, Matrix.toBilin'_single,
      Matrix.one_apply, hB1]
    by_cases hij : i = j
    · subst hij
      simp [hdiag i 0]
    · simp [hij, hoff i j hij]
  intro v φ
  have h1 := LinearMap.congr_fun₂ hB v φ
  rw [hB1] at h1
  rw [h1]
  simp [B2, Matrix.toBilin'_apply', dotProduct_comm]


theorem polar_zero_of_forall_map_eq_zero {x y : V}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : Q (x + y) = 0) : QuadraticMap.polar Q x y = 0 := by
  rw [QuadraticMap.polar, hx, hy, hxy]
  simp

theorem IsPointMaps.polar_left_eq_zero (hP : IsPointMaps ρ' Q P Pd) (v v' : Fin 4 → ZMod 2) :
    QuadraticMap.polar Q (P v) (P v') = 0 :=
  polar_zero_of_forall_map_eq_zero (hP.map_eq_zero v) (hP.map_eq_zero v') (by
    rw [← map_add]; exact hP.map_eq_zero _)

theorem IsPointMaps.polar_right_eq_zero (hP : IsPointMaps ρ' Q P Pd) (φ φ' : Fin 4 → ZMod 2) :
    QuadraticMap.polar Q (Pd φ) (Pd φ') = 0 :=
  polar_zero_of_forall_map_eq_zero (hP.map_eq_zero_dual φ) (hP.map_eq_zero_dual φ') (by
    rw [← map_add]; exact hP.map_eq_zero_dual _)

theorem IsPointMaps.finrank_range_sup [FiniteDimensional (ZMod 2) V]
    (hP : IsPointMaps ρ' Q P Pd) :
    finrank (ZMod 2) ↥(LinearMap.range P ⊔ LinearMap.range Pd) = 8 := by
  have h := hP.finrank_commSpaceOf_top
  rw [hP.commSpaceOf_top] at h
  simpa using h

theorem IsPointMaps.polar_eq_dotProduct [FiniteDimensional (ZMod 2) V]
    (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ') (hP : IsPointMaps ρ' Q P Pd)
    (hdim : finrank (ZMod 2) V < 16) (v φ : Fin 4 → ZMod 2) :
    QuadraticMap.polar Q (P v) (Pd φ) = φ ⬝ᵥ v := by
  obtain ⟨c₀, hc₀⟩ := hP.exists_polar_eq hA
  have hc1 : c₀ = 1 := by
    by_contra hne
    have h0 : c₀ = 0 := by
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c₀ with h | h
      · exact h
      · exact absurd h hne
    have hiso : ∀ x ∈ LinearMap.range P ⊔ LinearMap.range Pd,
        ∀ y ∈ LinearMap.range P ⊔ LinearMap.range Pd, QuadraticMap.polar Q x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ⟨v, rfl⟩, b, ⟨φ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ⟨v', rfl⟩, b', ⟨φ', rfl⟩, rfl⟩ := Submodule.mem_sup.mp hy
      have hcomm : QuadraticMap.polar Q (Pd φ) (P v') = 0 := by
        rw [QuadraticMap.polar_comm, hc₀, h0, zero_mul]
      rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
        hP.polar_left_eq_zero, hP.polar_right_eq_zero, hc₀, hcomm, h0]
      simp
    have hle : LinearMap.range P ⊔ LinearMap.range Pd ≤
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
          (LinearMap.range P ⊔ LinearMap.range Pd) := by
      intro y hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      exact hiso x hx y hy
    have hnd := hA.nondegenerate
    have h1 := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, hP.finrank_range_sup] at h1
    omega
  rw [hc₀, hc1, one_mul]


theorem IsPointMaps.inf_orthogonal_eq_bot [FiniteDimensional (ZMod 2) V]
    (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ') (hP : IsPointMaps ρ' Q P Pd)
    (hdim : finrank (ZMod 2) V < 16) :
    (LinearMap.range P ⊔ LinearMap.range Pd) ⊓
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (LinearMap.range P ⊔ LinearMap.range Pd) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxW, hxo⟩ := Submodule.mem_inf.mp hx
  obtain ⟨a, ⟨v, rfl⟩, b, ⟨φ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hxW
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxo
  have h1 : ∀ v' : Fin 4 → ZMod 2, φ ⬝ᵥ v' = 0 := by
    intro v'
    have h := hxo (P v') (Submodule.mem_sup_left (LinearMap.mem_range_self P v'))
    have h' : QuadraticMap.polar Q (P v') (P v + Pd φ) = 0 := h
    rw [QuadraticMap.polar_add_right, hP.polar_left_eq_zero,
      hP.polar_eq_dotProduct hA hdim, zero_add] at h'
    exact h'
  have h2 : ∀ φ' : Fin 4 → ZMod 2, φ' ⬝ᵥ v = 0 := by
    intro φ'
    have h := hxo (Pd φ') (Submodule.mem_sup_right (LinearMap.mem_range_self Pd φ'))
    have h' : QuadraticMap.polar Q (Pd φ') (P v + Pd φ) = 0 := h
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm Q (Pd φ') (P v),
      hP.polar_eq_dotProduct hA hdim, hP.polar_right_eq_zero, add_zero] at h'
    exact h'
  have hφ : φ = 0 := by
    ext i
    have := h1 (Pi.single i 1)
    simpa [dotProduct, Pi.single_apply] using this
  have hv : v = 0 := by
    ext i
    have := h2 (Pi.single i 1)
    simpa [dotProduct, Pi.single_apply] using this
  rw [hφ, hv, map_zero, map_zero, add_zero]
  exact Submodule.zero_mem _

theorem IsPointMaps.sup_orthogonal_eq_top [FiniteDimensional (ZMod 2) V]
    (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ') (hP : IsPointMaps ρ' Q P Pd)
    (hdim : finrank (ZMod 2) V < 16) :
    (LinearMap.range P ⊔ LinearMap.range Pd) ⊔
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (LinearMap.range P ⊔ LinearMap.range Pd) = ⊤ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range P ⊔ LinearMap.range Pd)
    (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (LinearMap.range P ⊔ LinearMap.range Pd))
  rw [hP.inf_orthogonal_eq_bot hA hdim, finrank_bot, add_zero,
    LinearMap.BilinForm.finrank_orthogonal hA.nondegenerate, hP.finrank_range_sup] at h
  have h8 : 8 ≤ finrank (ZMod 2) V := by
    have := Submodule.finrank_le (LinearMap.range P ⊔ LinearMap.range Pd)
    rw [hP.finrank_range_sup] at this
    exact this
  apply Submodule.eq_top_of_finrank_eq
  omega


theorem IsPointMaps.apply_eq_self_of_commute (hP : IsPointMaps ρ' Q P Pd)
    {c : V ≃ₗ[ZMod 2] V} (hc : ∀ g, c * ρ' g = ρ' g * c) :
    ∀ x ∈ LinearMap.range P ⊔ LinearMap.range Pd, c x = x := by
  have hline : ∀ v φ : Fin 4 → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
      c (P v) ∈ Submodule.span (ZMod 2) {P v, Pd φ} ∧
        c (Pd φ) ∈ Submodule.span (ZMod 2) {P v, Pd φ} := by
    intro v φ hv hφ hvφ
    have hconj : ρ' (tv v φ) = c * ρ' (tv v φ) * c⁻¹ := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have hsp := hP.commSpace_tv v φ hv hφ hvφ
    have hmap : Submodule.map (c : V →ₗ[ZMod 2] V) (commSpace (ρ' (tv v φ))) =
        commSpace (ρ' (tv v φ)) := by
      rw [← commSpace_conj, ← hconj]
    rw [hsp] at hmap
    have hPv : P v ∈ Submodule.span (ZMod 2) {P v, Pd φ} := Submodule.subset_span (by simp)
    have hPd : Pd φ ∈ Submodule.span (ZMod 2) {P v, Pd φ} := Submodule.subset_span (by simp)
    refine ⟨?_, ?_⟩
    · rw [← hmap]
      exact Submodule.mem_map_of_mem hPv
    · rw [← hmap]
      exact Submodule.mem_map_of_mem hPd
  have hPfix : ∀ v : Fin 4 → ZMod 2, c (P v) = P v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, map_zero, map_zero]
    · obtain ⟨φ₁, φ₂, h1, h2, h12, hd1, -, hd2, -⟩ :=
        exists_two_ne_zero_dotProduct_eq_zero (n := 4) le_rfl v v
      obtain ⟨a₁, b₁, e₁⟩ := Submodule.mem_span_pair.mp (hline v φ₁ hv h1 hd1).1
      obtain ⟨a₂, b₂, e₂⟩ := Submodule.mem_span_pair.mp (hline v φ₂ hv h2 hd2).1
      have e : a₁ • P v + b₁ • Pd φ₁ = a₂ • P v + b₂ • Pd φ₂ := e₁.trans e₂.symm
      have hx : (a₁ - a₂) • P v ∈ LinearMap.range P ⊓ LinearMap.range Pd := by
        refine ⟨LinearMap.mem_range.mpr ⟨(a₁ - a₂) • v, by simp⟩, LinearMap.mem_range.mpr
          ⟨b₂ • φ₂ - b₁ • φ₁, ?_⟩⟩
        rw [map_sub, map_smul, map_smul, sub_smul]
        have : a₁ • P v - a₂ • P v = b₂ • Pd φ₂ - b₁ • Pd φ₁ := by
          rw [sub_eq_sub_iff_add_eq_add, e]
          abel
        exact this.symm
      rw [hP.range_inf_range, Submodule.mem_bot] at hx
      have hPv0 : P v ≠ 0 := fun h => hv (hP.injective (by rw [h, map_zero]))
      have ha : a₁ = a₂ := by
        rcases smul_eq_zero.mp hx with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hPv0
      have hb : b₁ • φ₁ + b₂ • φ₂ = 0 := by
        apply hP.injective_dual
        rw [map_add, map_smul, map_smul, map_zero]
        have h3 : b₁ • Pd φ₁ = b₂ • Pd φ₂ := by
          have := e
          rw [ha] at this
          exact add_left_cancel this
        rw [h3]
        exact ZModModule.add_self _
      have hb1 := (CFSG.GroupTheory.GLnTwoSplitting.eq_zero_of_smul_add_smul_eq_zero h1 h2 h12 hb).1
      rw [hb1, zero_smul, add_zero] at e₁
      have hne : c (P v) ≠ 0 := fun h => hPv0 (c.injective (by rw [h, map_zero]))
      rw [← e₁] at hne ⊢
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a₁ with h | h
      · rw [h, zero_smul] at hne
        exact absurd rfl hne
      · rw [h, one_smul]
  have hPdfix : ∀ φ : Fin 4 → ZMod 2, c (Pd φ) = Pd φ := by
    intro φ
    by_cases hφ : φ = 0
    · rw [hφ, map_zero, map_zero]
    · obtain ⟨v₁, v₂, h1, h2, h12, hd1, -, hd2, -⟩ :=
        exists_two_ne_zero_dotProduct_eq_zero (n := 4) le_rfl φ φ
      have hd1' : φ ⬝ᵥ v₁ = 0 := by rw [dotProduct_comm]; exact hd1
      have hd2' : φ ⬝ᵥ v₂ = 0 := by rw [dotProduct_comm]; exact hd2
      obtain ⟨a₁, b₁, e₁⟩ := Submodule.mem_span_pair.mp (hline v₁ φ h1 hφ hd1').2
      obtain ⟨a₂, b₂, e₂⟩ := Submodule.mem_span_pair.mp (hline v₂ φ h2 hφ hd2').2
      have e : a₁ • P v₁ + b₁ • Pd φ = a₂ • P v₂ + b₂ • Pd φ := e₁.trans e₂.symm
      have hx : (b₁ - b₂) • Pd φ ∈ LinearMap.range P ⊓ LinearMap.range Pd := by
        refine ⟨LinearMap.mem_range.mpr ⟨a₂ • v₂ - a₁ • v₁, ?_⟩,
          LinearMap.mem_range.mpr ⟨(b₁ - b₂) • φ, by simp⟩⟩
        rw [map_sub, map_smul, map_smul, sub_smul]
        have : b₁ • Pd φ - b₂ • Pd φ = a₂ • P v₂ - a₁ • P v₁ := by
          rw [sub_eq_sub_iff_add_eq_add, add_comm]
          exact e
        exact this.symm
      rw [hP.range_inf_range, Submodule.mem_bot] at hx
      have hPd0 : Pd φ ≠ 0 := fun h => hφ (hP.injective_dual (by rw [h, map_zero]))
      have hb : b₁ = b₂ := by
        rcases smul_eq_zero.mp hx with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hPd0
      have ha : a₁ • v₁ + a₂ • v₂ = 0 := by
        apply hP.injective
        rw [map_add, map_smul, map_smul, map_zero]
        have h3 : a₁ • P v₁ = a₂ • P v₂ := by
          have := e
          rw [hb] at this
          exact add_right_cancel this
        rw [h3]
        exact ZModModule.add_self _
      have ha1 := (CFSG.GroupTheory.GLnTwoSplitting.eq_zero_of_smul_add_smul_eq_zero h1 h2 h12 ha).1
      rw [ha1, zero_smul, zero_add] at e₁
      have hne : c (Pd φ) ≠ 0 := fun h => hPd0 (c.injective (by rw [h, map_zero]))
      rw [← e₁] at hne ⊢
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases b₁ with h | h
      · rw [h, zero_smul] at hne
        exact absurd rfl hne
      · rw [h, one_smul]
  intro x hx
  obtain ⟨a, ⟨v, rfl⟩, b, ⟨φ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, hPfix, hPdfix]

end CFSG.LargeExtraspecial.A2Mod
