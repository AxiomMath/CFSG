module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSp44
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21H

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

section Torus

variable {K : Type} [Field K]

private def dvec (s : Fin 2 → Kˣ) : Fin 2 ⊕ Fin 2 → K :=
  Sum.elim (fun i => (s i : K)) fun i => (((s i)⁻¹ : Kˣ) : K)

private theorem coe_torusHom_eq (s : Fin 2 → Kˣ) :
    (((SymplecticTorusWeyl.torusHom s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = diagonal (dvec s) :=
  SymplecticTorusWeyl.coe_torusHom s

private theorem entry_eq_zero_of_commute_diagonal
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {d : Fin 2 ⊕ Fin 2 → K}
    (h : M * diagonal d = diagonal d * M) {i j : Fin 2 ⊕ Fin 2} (hij : d i ≠ d j) :
    M i j = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  by_contra hM
  apply hij
  exact mul_right_cancel₀ hM (by rw [← h1, mul_comm])

private theorem dvec_separate (ω : Kˣ) (hω1 : ω ≠ 1) (hω2 : ω⁻¹ ≠ ω) (i j : Fin 2 ⊕ Fin 2)
    (hij : i ≠ j) :
    dvec (K := K) ![ω, 1] i ≠ dvec ![ω, 1] j ∨ dvec (K := K) ![1, ω] i ≠ dvec ![1, ω] j := by
  have h1 : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have h2 : (ω : K)⁻¹ ≠ (ω : K) := fun h => hω2 (Units.ext (by simpa using h))
  have h3 : (ω : K)⁻¹ ≠ 1 := fun h => hω1 (Units.ext (inv_eq_one.1 h))
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [dvec, h1, h1.symm, h2, h2.symm, h3, h3.symm] at hij ⊢

private theorem mem_torus_of_offDiag_zero {v : StatedSp 2 K}
    (hoff : ∀ i j : Fin 2 ⊕ Fin 2, i ≠ j →
      ((v : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j = 0) :
    v ∈ SymplecticTorusWeyl.torus 2 K := by
  obtain ⟨d, hd⟩ : ∃ d : Fin 2 ⊕ Fin 2 → K,
      ((v : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = diagonal d := by
    refine ⟨fun i =>
      ((v : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i i, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.1 v.2
  rw [hd] at hsp
  have key : ∀ k : Fin 2, d (Sum.inl k) * d (Sum.inr k) = 1 := by
    intro k
    have := congrFun (congrFun hsp (Sum.inl k)) (Sum.inr k)
    simpa [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.fromBlocks_apply₁₂, Matrix.one_apply] using this
  refine ⟨fun k => ⟨d (Sum.inl k), d (Sum.inr k), key k, by rw [mul_comm]; exact key k⟩, ?_⟩
  apply SymplecticTorusWeyl.statedSp_ext
  rw [SymplecticTorusWeyl.coe_torusHom, hd]
  congr 1
  funext i
  rcases i with k | k <;> simp

theorem torus_mem_of_commute {ω : Kˣ} (hω1 : ω ≠ 1) (hω2 : ω⁻¹ ≠ ω) {v : StatedSp 2 K}
    (hv : ∀ t ∈ SymplecticTorusWeyl.torus 2 K, v * t = t * v) :
    v ∈ SymplecticTorusWeyl.torus 2 K := by
  apply mem_torus_of_offDiag_zero
  intro i j hij
  have hmat : ∀ s : Fin 2 → Kˣ,
      ((v : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * diagonal (dvec s) =
        diagonal (dvec s) *
          ((v : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro s
    have := congrArg (fun x : StatedSp 2 K =>
      ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
      (hv _ (SymplecticTorusWeyl.torusHom_mem_torus s))
    simpa [coe_torusHom_eq] using this
  rcases dvec_separate ω hω1 hω2 i j hij with h | h
  · exact entry_eq_zero_of_commute_diagonal (hmat ![ω, 1]) h
  · exact entry_eq_zero_of_commute_diagonal (hmat ![1, ω]) h

end Torus

theorem exists_unit_gf4 : ∃ ω : (GaloisField 2 2)ˣ, ω ≠ 1 ∧ ω⁻¹ ≠ ω := by
  have : Nontrivial (GaloisField 2 2)ˣ :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [card_units_gf4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : (GaloisField 2 2)ˣ)
  refine ⟨ω, hω, fun h => hω ?_⟩
  have h2 : ω * ω = 1 := by
    calc ω * ω = ω⁻¹ * ω := by rw [h]
      _ = 1 := inv_mul_cancel ω
  calc ω = ω ^ 3 := by rw [pow_succ, pow_two, h2, one_mul]
    _ = 1 := units_gf4_pow_three ω

theorem torus_mem_of_commute_gf4 {v : StatedSp 2 (GaloisField 2 2)}
    (hv : ∀ t ∈ SymplecticTorusWeyl.torus 2 (GaloisField 2 2), v * t = t * v) :
    v ∈ SymplecticTorusWeyl.torus 2 (GaloisField 2 2) := by
  obtain ⟨ω, hω1, hω2⟩ := exists_unit_gf4
  exact torus_mem_of_commute hω1 hω2 hv

theorem nonempty_mulEquiv_statedSp44 {E : Type} [Group E] (h : Blueprint.LieModel E .PSp 2 2 2) :
    Nonempty (E ≃* StatedSp 2 (GaloisField 2 2)) := by
  have hc : StatedClassicalModel E .PSp 2 2 2 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 2 (by norm_num)]
  let φ : K ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(e.trans (Adapters.RankTwoModelTransports.statedProjCongr
    (Adapters.RankTwoModelTransports.glCongr φ) (ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
    (Adapters.RankTwoModelTransports.glCongr_statedScalars φ))).trans statedProjSp44Equiv⟩

theorem no_involution_centralizes_nine_sp44 {E : Type} [Group E]
    (h : Blueprint.LieModel E .PSp 2 2 2) (u : E) (hu : u * u = 1) (hu1 : u ≠ 1) (P : Subgroup E)
    (hP : Nat.card P = 9) : ¬ (∀ x ∈ P, u * x = x * u) := by
  intro hcomm
  obtain ⟨φ⟩ := nonempty_mulEquiv_statedSp44 h
  have hP' : Nat.card (P.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hP]
  obtain ⟨g, hg⟩ := exists_map_conj_of_sylow
    (P₀ := SymplecticTorusWeyl.torus 2 (GaloisField 2 2)) (P := P.map φ.toMonoidHom)
    (by rw [card_torus_gf4, factorization_card_sp44]) (by rw [hP', card_torus_gf4]; norm_num)
  have hvt : ∀ t ∈ SymplecticTorusWeyl.torus 2 (GaloisField 2 2),
      (g⁻¹ * φ u * g) * t = t * (g⁻¹ * φ u * g) := by
    intro t ht
    have hmem : g * t * g⁻¹ ∈ P.map φ.toMonoidHom := by
      rw [hg]
      exact ⟨t, ht, rfl⟩
    obtain ⟨x, hx, hxt⟩ := hmem
    have h2 : φ u * φ x = φ x * φ u := by
      rw [← map_mul, ← map_mul, hcomm x hx]
    have h3 : φ u * (g * t * g⁻¹) = g * t * g⁻¹ * φ u := by
      have := h2
      rwa [show φ x = g * t * g⁻¹ from hxt] at this
    calc g⁻¹ * φ u * g * t = g⁻¹ * (φ u * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * φ u) * g := by rw [h3]
      _ = t * (g⁻¹ * φ u * g) := by group
  have hmem := torus_mem_of_commute_gf4 hvt
  have h3 : (g⁻¹ * φ u * g) ^ 3 = 1 := isElemAbelian_torus_gf4.2 _ hmem
  have hsq : (g⁻¹ * φ u * g) * (g⁻¹ * φ u * g) = 1 := by
    have : φ u * φ u = 1 := by rw [← map_mul, hu, map_one]
    calc g⁻¹ * φ u * g * (g⁻¹ * φ u * g) = g⁻¹ * (φ u * φ u) * g := by group
      _ = 1 := by rw [this]; group
  have hv1 : g⁻¹ * φ u * g = 1 := by
    calc g⁻¹ * φ u * g = (g⁻¹ * φ u * g) ^ 3 := by
          rw [pow_succ, pow_two, hsq, one_mul]
      _ = 1 := h3
  apply hu1
  have : φ u = 1 := by
    calc φ u = g * (g⁻¹ * φ u * g) * g⁻¹ := by group
      _ = 1 := by rw [hv1]; group
  exact φ.injective (by rw [this, map_one])

end CFSG.EvenSporadicStandard.M22Std.P21H
