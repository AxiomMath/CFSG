module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinRankSix
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIEvenClassicalBlock
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSocle

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem conjAut_mem_inner_of_card_two {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2)
    (A : GL (Fin n) K) : conjAut n K A ∈ OuterAutomorphisms.inner (projectiveSL n K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    by_contra h
    have h0 : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det A).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
    have h3 : 2 < Fintype.card K := Fintype.two_lt_card_iff.mpr
      ⟨0, 1, (A : Matrix (Fin n) (Fin n) K).det, zero_ne_one, h0.symm, fun h' => h h'.symm⟩
    rw [← Nat.card_eq_fintype_card, hK] at h3
    omega
  set g : Matrix.SpecialLinearGroup (Fin n) K := ⟨A, hdet⟩
  have hA : A = Matrix.SpecialLinearGroup.toGL g := Units.ext rfl
  rw [hA, conjAut_toGL]
  exact ⟨_, rfl⟩

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

theorem not_mem_innAut_of_even (hnab : ∃ a b : Y, a * b ≠ b * a)
    {t : Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y t n 2 f) {p m : ℕ} {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : τ ∉ innAut Y := by
  rintro ⟨t₀, rfl⟩
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have ht2 : orderOf t₀ = 2 := by
    rw [← orderOf_injective _ (conj_injective_of_center hZ) t₀]
    exact hτ
  obtain ⟨B, hB, -⟩ := exists_isComponent_of_eq (centralizer_eq_fixedPoints_conj t₀) hL
  exact OutcomeLocal.no_component_of_even_classical_model ht hY t₀ ht2 B hB

theorem hinConcl_psl_even (hnab : ∃ a b : Y, a * b ≠ b * a) {n e : ℕ} (hn : 3 ≤ n)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSL n 2 e)
    (hYalt : ∀ k : ℕ, 5 ≤ k → IsEmpty (Y ≃* alternatingGroup (Fin k))) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ := by
  classical
  have hout := not_mem_innAut_of_even hnab (Or.inl rfl) hY hτ hL
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨⟨-, he, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ := id hY
  set L' := (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y) with hL'
  have hsrc : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m ∨
      Nonempty (↥L' ⧸ center ↥L' ≃* alternatingGroup (Fin 7)) ∨
      Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 3 2 2 :=
    Or.inl (statedSrc_layerMap hZ hL)
  have hWalt : ∀ k : ℕ, 5 ≤ k →
      IsEmpty (↥(generalizedFitting (MulAut Y)) ≃* alternatingGroup (Fin k)) :=
    fun k hk => ⟨fun e' => (hYalt k hk).false (eW.trans e')⟩
  obtain ⟨ρ₀, hinj, -, -, -, -, -, c₀, hrows⟩ :=
    OutcomeLocal.faithful_even_higher_linear_socle_small_source_involution_selector hWs hWnab
      hWC hτ (hLW τ) (isComponentOf_map_conj_layer hZ hL) hp hp2 hm hsrc hWalt hn he hK
      (eW.symm.trans (φ₀.trans (SymmetricLocal.statedProjEquivProjectiveSL n K)))
  rcases hrows with ⟨σ, hF, -⟩ | hG
  · rcases hF with ⟨hn3, he2, -⟩ | ⟨-, -, h34, -⟩
    · subst hn3 he2
      exact hinConcl_of_list hout
        (Or.inr (Or.inr (Or.inl (Or.inl ⟨by simp [Blueprint.classicalTags], hY⟩))))
    · exact absurd h34
        (UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated
          (statedSrc_layerMap hZ hL)).2.2
  · obtain ⟨-, -, hCWmap, -, -, -, hG59⟩ := hG
    rcases hG59 with ⟨-, -, hp5, hf1, -⟩ | ⟨hn5, he1, -, -, -, hcent, -, -, hN6, -⟩
    · subst hp5 hf1
      norm_num at h16
    · subst hn5 he1
      refine hinConcl_of_not_inner hout (not_sectionalTwoRankLE_of_perm_six hnab hinj
        (N := (Subgroup.map (conjAut 5 K)
          (FourGroupEvenCanonical.matrixIsometryGroup
            ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).map
          (MulAut.conj (conjAut 5 K c₀)).toMonoidHom) ?_ ?_)
      · obtain ⟨eN⟩ := hN6
        exact ⟨((Subgroup.map (conjAut 5 K) (FourGroupEvenCanonical.matrixIsometryGroup
          ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).equivMapOfInjective _
            (MulAut.conj (conjAut 5 K c₀)).injective).symm.trans eN⟩
      · rw [hCWmap]
        rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        refine ⟨?_, ⟨conjAut 5 K g, ?_, rfl⟩⟩
        · change conjAut 5 K c₀ * conjAut 5 K g * (conjAut 5 K c₀)⁻¹ ∈ _
          rw [← map_inv, ← map_mul, ← map_mul]
          exact conjAut_mem_inner_of_card_two (by rw [hK, pow_one]) _
        · rw [hcent]
          exact ⟨g, hg, 0, by norm_num, by rw [pow_zero, mul_one]⟩

theorem hinConcl_psu_even (hnab : ∃ a b : Y, a * b ≠ b * a) {n e : ℕ}
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSU n 2 e) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ := by
  classical
  have hout := not_mem_innAut_of_even hnab (Or.inr (Or.inl rfl)) hY hτ hL
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨⟨-, he, hn, hne⟩, K, _, _, hK, ⟨φ₀⟩⟩ := hY
  have hUd : UnitaryFieldData 2 e K := ⟨Nat.prime_two, he, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬ (n = 3 ∧ 2 ^ e = 2) := fun ⟨h3, h2⟩ => hne (by rw [h3, h2])
  set L' := (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y) with hL'
  have hsrc : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m ∨
      Nonempty (↥L' ⧸ center ↥L' ≃* alternatingGroup (Fin 7)) ∨
      Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 3 2 2 :=
    Or.inl (statedSrc_layerMap hZ hL)
  obtain ⟨-, -, -, -, -, H₀, C, hC, -, θ₀, -, ρC, -, hinjC, σ, -, -, Cl, hCl, -, -, -, -, -, -,
    -, hCWmap, hrows, -⟩ :=
    OutcomeLocal.faithful_even_unitary_socle_small_source_involution_selector hWs hWnab hWC hτ
      (hLW τ) (isComponentOf_map_conj_layer hZ hL) hp hp2 hm hsrc hUd hn hq
      (eW.symm.trans (φ₀.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hUd (by omega)).symm))
  rcases hrows with ⟨-, -, hp5, hf1, -⟩ | ⟨-, -, -, -, -, -, -, hN6, -⟩ |
      ⟨-, -, -, -, -, -, -, -, hN6, -⟩
  · subst hp5 hf1
    norm_num at h16
  · exact hinConcl_of_not_inner hout
      (not_sectionalTwoRankLE_of_perm_six hnab hinjC hN6 hCWmap.ge)
  · exact hinConcl_of_not_inner hout
      (not_sectionalTwoRankLE_of_perm_six hnab hinjC hN6 hCWmap.ge)

theorem hinConcl_psp_even (hnab : ∃ a b : Y, a * b ≠ b * a)
    {r e : ℕ} (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSp r 2 e) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) {τ : MulAut Y} (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ := by
  classical
  have hout := not_mem_innAut_of_even hnab (Or.inr (Or.inr (Or.inl rfl))) hY hτ hL
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  obtain ⟨⟨-, he, hr, hne⟩, K, _, _, hK, ⟨φ₀⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hre : ¬ (r = 2 ∧ e = 1) := fun ⟨hr2, he1⟩ => hne (by rw [hr2, he1]; rfl)
  set L' := (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y) with hL'
  have hsrc : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m ∨
      Nonempty (↥L' ⧸ center ↥L' ≃* alternatingGroup (Fin 7)) ∨
      Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 3 2 2 :=
    Or.inl (statedSrc_layerMap hZ hL)
  obtain ⟨-, -, -, -, hr2, -, -, -, -, -, -, -, -, hρ₂⟩ :=
    OutcomeLocal.faithful_even_symplectic_socle_small_source_involution_selector hWs hWnab hWC
      hτ (hLW τ) (isComponentOf_map_conj_layer hZ hL) hp hp2 hm hsrc hr he hre hK
      (eW.symm.trans φ₀)
  subst hr2
  obtain ⟨ρ₂, hinj₂, -, -, hlet⟩ := hρ₂ (eW.symm.trans φ₀) (frobeniusEquiv K 2)
    (fun t => frobeniusEquiv_apply K 2 t) (UnbalancedCatalog.SpChain.exceptionalAut K)
    (fun g => UnbalancedCatalog.SpChain.exceptionalAut_proj g)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨eN⟩, -, h, -, -, hCW₂, -⟩ := hlet
  refine hinConcl_of_not_inner hout (not_sectionalTwoRankLE_of_perm_six hnab hinj₂ ?_ hCW₂.ge)
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective).symm.trans eN⟩

end CFSG.ComponentClassification.HarrisLit.Hin
