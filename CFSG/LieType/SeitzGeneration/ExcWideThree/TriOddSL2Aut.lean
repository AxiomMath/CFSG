module

public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups commutatorElement

noncomputable section

theorem triOdd_exists_ne_zero_sq_ne_one {K : Type} [Field K] (hK4 : 4 ≤ Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · rcases mul_self_eq_one_iff.mp (show a * a = 1 by rw [← sq]; exact h a ha) with h1 | h1 <;>
        simp [h1]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
  have h3 : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
  omega

theorem triOdd_commutatorElement_center_mul {G : Type*} [Group G] {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) (a b : G) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hz hw
  have hconj : ∀ {c : G}, (∀ g, g * c = c * g) → ∀ X : G, c * X * c⁻¹ = X := by
    intro c hc X
    rw [← hc X, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
      = z * (a * w * b * a⁻¹) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = a * w * b * a⁻¹ * (b⁻¹ * w⁻¹) := by rw [hconj hz]
    _ = w * a * b * a⁻¹ * (b⁻¹ * w⁻¹) := by rw [hw a]
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := hconj hw _

theorem triOdd_sl2_hom_eq_of_mk_eq {K : Type} [Field K] (hK4 : 4 ≤ Nat.card K)
    (f g : SL(2, K) →* SL(2, K))
    (h : ∀ M, QuotientGroup.mk' (Subgroup.center SL(2, K)) (f M) =
      QuotientGroup.mk' (Subgroup.center SL(2, K)) (g M)) (M : SL(2, K)) :
    f M = g M := by
  obtain ⟨a, ha, hasq⟩ := triOdd_exists_ne_zero_sq_ne_one hK4
  have hc : ∀ N, ∃ z ∈ Subgroup.center SL(2, K), f N = z * g N := fun N =>
    ⟨f N / g N, QuotientGroup.eq_iff_div_mem.mp (h N), by rw [div_mul_cancel]⟩
  have hle : commutator SL(2, K) ≤ f.eqLocus g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨z, hz, hzx⟩ := hc x
    obtain ⟨w, hw, hwy⟩ := hc y
    show f ⁅x, y⁆ = g ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement, hzx, hwy,
      triOdd_commutatorElement_center_mul hz hw]
  have hM : M ∈ commutator SL(2, K) := by
    rw [Matrix.SL2.commutator_eq_top ha hasq]
    exact Subgroup.mem_top M
  exact hle hM

@[expose] def triOddInducedPSL (K : Type) [Field K] :
    MulAut SL(2, K) →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) where
  toFun ρ := QuotientGroup.congr (Subgroup.center SL(2, K)) (Subgroup.center SL(2, K)) ρ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance ρ)
  map_one' := by
    ext x
    obtain ⟨M, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, K)) x
    rfl
  map_mul' ρ τ := by
    ext x
    obtain ⟨M, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, K)) x
    rfl

theorem triOddInducedPSL_mk {K : Type} [Field K] (ρ : MulAut SL(2, K)) (M : SL(2, K)) :
    triOddInducedPSL K ρ (QuotientGroup.mk' (Subgroup.center SL(2, K)) M) =
      QuotientGroup.mk' (Subgroup.center SL(2, K)) (ρ M) := rfl

theorem triOdd_eq_or_eq_of_pow_three {G : Type*} [Group G] [Finite G] [IsCyclic G] {σ δ : G}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hδ3 : δ ^ 3 = 1) : δ = 1 ∨ δ = σ ∨ δ = σ ^ 2 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hσ2 : σ ^ 2 ≠ 1 := by
    intro h
    apply hσ1
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, h]; group
  have hσσ2 : σ ≠ σ ^ 2 := by
    intro h
    apply hσ1
    calc σ = σ ^ 2 * σ⁻¹ := by group
      _ = 1 := by rw [← h]; group
  have hsub : ({1, σ, σ ^ 2, δ} : Finset G) ⊆ Finset.univ.filter fun a => a ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
    · exact hδ3
  have hA : (1 : G) ∉ ({σ, σ ^ 2, δ} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσ1 h.symm, fun h => hσ2 h.symm, fun h => h1 h.symm⟩
  have hB : σ ∉ ({σ ^ 2, δ} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hσσ2, fun h => h2 h.symm⟩
  have hC : σ ^ 2 ≠ δ := fun h => h3 h.symm
  have hcard : ({1, σ, σ ^ 2, δ} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB, Finset.card_pair hC]
  have hle := Finset.card_le_card hsub
  have hcyc := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  omega

theorem triOdd_exists_fixed_not_isSquare {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (s : K ≃+* K) (hs3 : s ^ 3 = 1) :
    ∃ ν : K, s ν = ν ∧ ¬ IsSquare ν := by
  have h3 : ∀ x, s (s (s x)) = x := fun x => by
    have h := congrArg (fun e : K ≃+* K => e x) hs3
    simp only [pow_three, RingAut.mul_apply] at h
    exact h
  obtain ⟨f, hf⟩ : ∃ f : {x : K // s x = x} → {x : K // s x = x}, ∀ x, (f x).1 = x.1 ^ 2 :=
    ⟨fun x => ⟨x.1 ^ 2, by rw [map_pow, x.2]⟩, fun _ => rfl⟩
  have hfi : ¬ Function.Injective f := by
    intro hinj
    have h := hinj (show f ⟨1, map_one s⟩ = f ⟨-1, by rw [map_neg, map_one]⟩ from
      Subtype.ext (by rw [hf, hf]; simp))
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (congrArg Subtype.val h).symm
  obtain ⟨⟨ν, hν⟩, hνf⟩ : ∃ y, ∀ x, f x ≠ y := by
    by_contra hcon
    push Not at hcon
    exact hfi (Finite.injective_iff_surjective.mpr hcon)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hνf ⟨0, map_zero s⟩ (Subtype.ext (by rw [hf]; simp))
  refine ⟨ν, hν, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨N, hN⟩ : ∃ N, N = y * s y * s (s y) := ⟨_, rfl⟩
  have hNs : s N = N := by
    rw [hN, map_mul, map_mul, h3]
    ring
  have hNsq : N ^ 2 = ν ^ 3 := by
    have e1 : s y * s y = ν := by rw [← map_mul s y y, ← hy, hν]
    have e2 : s (s y) * s (s y) = ν := by
      rw [← map_mul s (s y) (s y), ← map_mul s y y, ← hy, hν, hν]
    calc N ^ 2 = (y * y) * (s y * s y) * (s (s y) * s (s y)) := by rw [hN]; ring
      _ = ν ^ 3 := by rw [e1, e2, ← hy]; ring
  apply hνf ⟨N / ν, by rw [map_div₀, hNs, hν]⟩
  apply Subtype.ext
  rw [hf]
  show (N / ν) ^ 2 = ν
  rw [div_pow, hNsq, div_eq_iff (pow_ne_zero 2 hν0)]
  ring

theorem triOdd_isSquare_mul {K : Type} [Field K] [Finite K] {a b : K} (ha : ¬ IsSquare a)
    (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, (mul_zero 0).symm⟩
  have hb0 : b ≠ 0 := by rintro rfl; exact hb ⟨0, (mul_zero 0).symm⟩
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

theorem triOdd_exists_fixed_mul_mem_range {K : Type} [Field K] [Finite K] (s : K ≃+* K) {ν : K}
    (hνs : s ν = ν) (hν : ¬ IsSquare ν) (g : Matrix.ProjGenLinGroup (Fin 2) K) :
    ∃ f : Matrix.ProjGenLinGroup (Fin 2) K, pgl2FieldAut K s f = f ∧
      g * f ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  by_cases hA : IsSquare (Matrix.GeneralLinearGroup.det A : K)
  · refine ⟨1, map_one _, ?_⟩
    rw [mul_one]
    exact (pgl2_mk_mem_psl2_range_iff_det_isSquare A).mpr hA
  · have hν0 : ν ≠ 0 := by rintro rfl; exact hν ⟨0, (mul_zero 0).symm⟩
    have hdet : (Matrix.diagonal ![ν, 1]).det ≠ 0 := by
      simp [Matrix.det_diagonal, Fin.prod_univ_two, hν0]
    obtain ⟨D, hD⟩ : ∃ D : GL (Fin 2) K, (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![ν, 1] :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl⟩
    refine ⟨Matrix.ProjGenLinGroup.mk D, ?_, ?_⟩
    · rw [pgl2FieldAut_apply]
      change pgl2RingEquiv s (QuotientGroup.mk' _ D) = QuotientGroup.mk' _ D
      rw [pgl2RingEquiv_mk]
      congr 1
      ext i j
      rw [Matrix.GeneralLinearGroup.map_apply, hD]
      fin_cases i <;> fin_cases j <;> simp [hνs]
    · rw [← map_mul Matrix.ProjGenLinGroup.mk A D, pgl2_mk_mem_psl2_range_iff_det_isSquare,
        map_mul, Units.val_mul]
      have hDdet : (Matrix.GeneralLinearGroup.det D : K) = ν := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, hD]
        simp [Matrix.det_diagonal, Fin.prod_univ_two]
      rw [hDdet]
      exact triOdd_isSquare_mul hA hν

theorem triOddSL2_aut_three {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (hK4 : 4 ≤ Nat.card K) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (ρ : MulAut (Matrix.SpecialLinearGroup (Fin 2) K)) (hρ : ρ ^ 3 = 1) :
    (∃ a : Matrix.SpecialLinearGroup (Fin 2) K, ∀ M, ρ M = a * M * a⁻¹) ∨
    (∃ (a : Matrix.SpecialLinearGroup (Fin 2) K) (s : K ≃+* K), (s = σ ∨ s = σ ^ 2) ∧
      ∀ M, ρ M = a * Matrix.SpecialLinearGroup.map s.toRingHom (a⁻¹ * M * a) * a⁻¹) := by
  have hρ3 : triOddInducedPSL K ρ ^ 3 = 1 := by rw [← map_pow, hρ, map_one]
  by_cases hD : triOddInducedPSL K ρ ∈ (pglAction K).range
  · left
    obtain ⟨g, hg⟩ := hD
    have hg3 : g ^ 3 = 1 :=
      CFSG.RankThree.PartTwo.KFacts.pglAction_injective (by rw [map_pow, hg, hρ3, map_one])
    obtain ⟨x, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_three hg3
    rw [pglAction_toPGL] at hg
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, K)) x
    have key : ∀ N, QuotientGroup.mk' (Subgroup.center SL(2, K)) (ρ N) =
        QuotientGroup.mk' (Subgroup.center SL(2, K)) (a * N * a⁻¹) := by
      intro N
      rw [← triOddInducedPSL_mk ρ N, ← hg, MulAut.conj_apply,
        map_mul (QuotientGroup.mk' (Subgroup.center SL(2, K))),
        map_mul (QuotientGroup.mk' (Subgroup.center SL(2, K))),
        map_inv (QuotientGroup.mk' (Subgroup.center SL(2, K)))]
    exact ⟨a, triOdd_sl2_hom_eq_of_mk_eq hK4 ρ.toMonoidHom (MulAut.conj a).toMonoidHom key⟩
  · right
    have hρ1 : triOddInducedPSL K ρ ≠ 1 := fun h => hD (by rw [h]; exact Subgroup.one_mem _)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (triOddInducedPSL K ρ) = 3 := orderOf_eq_prime hρ3 hρ1
    obtain ⟨s, hs, g, hg⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three
        (triOddInducedPSL K ρ) hord hD
    have hs3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    have hsσ : s = σ ∨ s = σ ^ 2 := by
      have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
      have : Finite (K ≃+* K) := Finite.of_injective _ DFunLike.coe_injective
      rcases triOdd_eq_or_eq_of_pow_three hσ3 hσ1 hs3 with h | h | h
      · rw [h, orderOf_one] at hs
        omega
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨ν, hνs, hν⟩ := triOdd_exists_fixed_not_isSquare hK2 s hs3
    obtain ⟨f, hfs, x, hx⟩ := triOdd_exists_fixed_mul_mem_range s hνs hν g
    have hcomm : psl2FieldAut K s * pglAction K f = pglAction K f * psl2FieldAut K s := by
      have h := CFSG.RankThree.PartTwo.KFacts.psl2FieldAut_mul_pglAction_mul_inv s f
      rw [hfs] at h
      calc psl2FieldAut K s * pglAction K f
          = psl2FieldAut K s * pglAction K f * (psl2FieldAut K s)⁻¹ * psl2FieldAut K s := by
            group
        _ = pglAction K f * psl2FieldAut K s := by rw [h]
    have hρ' : triOddInducedPSL K ρ =
        MulAut.conj x * psl2FieldAut K s * (MulAut.conj x)⁻¹ := by
      rw [← pglAction_toPGL K x, hx, hg, map_mul (pglAction K) g f]
      calc pglAction K g * psl2FieldAut K s * (pglAction K g)⁻¹
          = pglAction K g * (psl2FieldAut K s * pglAction K f) * (pglAction K f)⁻¹ *
              (pglAction K g)⁻¹ := by group
        _ = pglAction K g * (pglAction K f * psl2FieldAut K s) * (pglAction K f)⁻¹ *
              (pglAction K g)⁻¹ := by rw [hcomm]
        _ = pglAction K g * pglAction K f * psl2FieldAut K s *
              (pglAction K g * pglAction K f)⁻¹ := by group
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, K)) x
    have key : ∀ N, QuotientGroup.mk' (Subgroup.center SL(2, K)) (ρ N) =
        QuotientGroup.mk' (Subgroup.center SL(2, K))
          (a * Matrix.SpecialLinearGroup.map s.toRingHom (a⁻¹ * N * a) * a⁻¹) := by
      intro N
      rw [← triOddInducedPSL_mk ρ N, hρ', MulAut.mul_apply, MulAut.mul_apply,
        MulAut.conj_inv_apply, MulAut.conj_apply, psl2FieldAut_apply,
        map_mul (QuotientGroup.mk' (Subgroup.center SL(2, K))),
        map_mul (QuotientGroup.mk' (Subgroup.center SL(2, K))),
        map_inv (QuotientGroup.mk' (Subgroup.center SL(2, K))), ← psl2RingEquiv_mk,
        map_mul (QuotientGroup.mk' (Subgroup.center SL(2, K))),
        map_mul (QuotientGroup.mk' (Subgroup.center SL(2, K))),
        map_inv (QuotientGroup.mk' (Subgroup.center SL(2, K)))]
    exact ⟨a, s, hsσ, triOdd_sl2_hom_eq_of_mk_eq hK4 ρ.toMonoidHom
      ((MulAut.conj a).toMonoidHom.comp ((Matrix.SpecialLinearGroup.map s.toRingHom).comp
        (MulEquiv.toMonoidHom (MulAut.conj a)⁻¹))) key⟩

end

end CFSG.LieType.SeitzGeneration.ExcWideThree
