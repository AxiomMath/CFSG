module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.ComponentClassification.UnbalancedCatalog

section Extend

variable {k K W V : Type} [Field k] [Field K] [Algebra k K] [AddCommGroup W] [Module k W]
  [AddCommGroup V] [Module K V]

theorem tail_aniso_of_le_one {Q₀ : QuadraticForm k W} {R : QuadraticForm K V} (ι : W →+ V)
    (hι : ∀ w, R (ι w) = algebraMap k K (Q₀ w)) {δ : ℕ} (hδ : δ ≤ 1) (t : Fin δ → W)
    (ht : ∀ z : Fin δ → k, Q₀ (∑ j, z j • t j) = 0 → z = 0) :
    ∀ Z : Fin δ → K, R (∑ j, Z j • ι (t j)) = 0 → Z = 0 := by
  interval_cases δ
  · intro Z _
    funext i
    exact i.elim0
  · intro Z hZ
    have h0 : Q₀ (t 0) ≠ 0 := by
      intro h0
      have := ht (fun _ => 1) (by simpa using h0)
      exact one_ne_zero (congrFun this 0)
    simp only [Fin.sum_univ_one] at hZ
    rw [map_smul_eq_sq, hι] at hZ
    have : Z 0 ^ 2 = 0 := by
      rcases mul_eq_zero.mp hZ with h1 | h1
      · exact h1
      · exact absurd (by simpa using h1) h0
    funext i
    fin_cases i
    simpa using pow_eq_zero_iff (two_ne_zero) |>.mp this

@[expose] noncomputable def hypSplitExtendLeOne {Q₀ : QuadraticForm k W} {R : QuadraticForm K V}
    (ι : W →+ V) (hι : ∀ w, R (ι w) = algebraMap k K (Q₀ w)) {m δ : ℕ} (H : HypSplit Q₀ m δ)
    (hδ : δ ≤ 1) (bK : Basis (Fin m ⊕ Fin m ⊕ Fin δ) K V)
    (hbK : ∀ a, bK a = ι (H.b a)) : HypSplit R m δ where
  b := bK
  eval x y z := by
    have hpol : ∀ u w, polar R (ι u) (ι w) = algebraMap k K (polar Q₀ u w) := by
      intro u w
      simp only [QuadraticMap.polar, ← map_add, hι, map_sub]
    let P : Fin m → HypPair R := fun i =>
      { e := ι (H.b (.inl i))
        f := ι (H.b (.inr (.inl i)))
        Q_e := by rw [hι, H.Q_inl, map_zero]
        Q_f := by rw [hι, H.Q_inr, map_zero]
        polar_ef := by
          have h : polar Q₀ (H.b (.inl i)) (H.b (.inr (.inl i))) = 1 := (H.hypPair i).polar_ef
          rw [hpol, h, map_one] }
    have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := fun i j hij =>
      { ee := by
          have h : polar Q₀ (H.b (.inl i)) (H.b (.inl j)) = 0 := (H.hypPair_orth hij).ee
          show polar R (ι (H.b (.inl i))) (ι (H.b (.inl j))) = 0
          rw [hpol, h, map_zero]
        ef := by
          have h : polar Q₀ (H.b (.inl i)) (H.b (.inr (.inl j))) = 0 := (H.hypPair_orth hij).ef
          show polar R (ι (H.b (.inl i))) (ι (H.b (.inr (.inl j)))) = 0
          rw [hpol, h, map_zero]
        fe := by
          have h : polar Q₀ (H.b (.inr (.inl i))) (H.b (.inl j)) = 0 := (H.hypPair_orth hij).fe
          show polar R (ι (H.b (.inr (.inl i)))) (ι (H.b (.inl j))) = 0
          rw [hpol, h, map_zero]
        ff := by
          have h : polar Q₀ (H.b (.inr (.inl i))) (H.b (.inr (.inl j))) = 0 :=
            (H.hypPair_orth hij).ff
          show polar R (ι (H.b (.inr (.inl i)))) (ι (H.b (.inr (.inl j)))) = 0
          rw [hpol, h, map_zero] }
    have htail : ∀ j i, ι (H.b (.inr (.inr j))) ∈ (P i).perp := by
      intro j i
      rw [HypPair.mem_perp]
      have h := (HypPair.mem_perp).mp (H.tail_mem_perp j i)
      have h1 : polar Q₀ (H.b (.inl i)) (H.b (.inr (.inr j))) = 0 := h.1
      have h2 : polar Q₀ (H.b (.inr (.inl i))) (H.b (.inr (.inr j))) = 0 := h.2
      constructor
      · show polar R (ι (H.b (.inl i))) (ι (H.b (.inr (.inr j)))) = 0
        rw [hpol, h1, map_zero]
      · show polar R (ι (H.b (.inr (.inl i)))) (ι (H.b (.inr (.inr j)))) = 0
        rw [hpol, h2, map_zero]
    have hw : ∀ i, (∑ j, z j • ι (H.b (.inr (.inr j)))) ∈ (P i).perp := fun i =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (htail j i)
    have key : R (∑ i, x i • ι (H.b (.inl i)) + ∑ i, y i • ι (H.b (.inr (.inl i)))) =
        ∑ i, x i * y i := map_sum_hyp hP x y
    have key2 : polar R (∑ i, x i • ι (H.b (.inl i)) + ∑ i, y i • ι (H.b (.inr (.inl i))))
        (∑ j, z j • ι (H.b (.inr (.inr j)))) = 0 := polar_sum_hyp_eq_zero x y hw
    simp only [hbK]
    rw [QuadraticMap.map_add (⇑R), key, key2]
    ring
  aniso Z hZ := by
    simp only [hbK] at hZ
    exact tail_aniso_of_le_one ι hι hδ (fun j => H.b (.inr (.inr j))) H.aniso Z hZ

end Extend

section Descent

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_conj_eq_inr_of_orderOf_eq_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h2 : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hker : ∀ g : similarityPairs (coordinateQuadOdd n K),
      matrixProjectiveConjugationHom (coordinateQuadOdd n K) g = 1 ↔
        g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin (2 * n + 1)) a)
    (g : similarityPairs (coordinateQuadOdd n K)) (hσ : orderOf g.val.right = 2)
    (hg : matrixProjectiveConjugationHom (coordinateQuadOdd n K) g *
      matrixProjectiveConjugationHom (coordinateQuadOdd n K) g = 1) :
    ∃ Θ : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)),
      Θ * matrixProjectiveConjugationHom (coordinateQuadOdd n K) g * Θ⁻¹ =
        matrixProjectiveConjugationHom (coordinateQuadOdd n K)
          ⟨SemidirectProduct.inr g.val.right,
            inr_mem_similarityPairs _ _ (coordinateQuadOdd_field n g.val.right)⟩ := by
  classical
  have hd : 0 < 2 * n + 1 := by omega
  have hnd : (QuadraticMap.polarBilin (coordinateQuadOdd n K)).Nondegenerate :=
    (regular_coordinateQuadOdd n K (Ring.two_ne_zero h2) hn).1
  have hκ : matrixProjectiveConjugationHom (coordinateQuadOdd n K) (g ^ 2) = 1 := by
    rw [map_pow, pow_two, hg]
  obtain ⟨-, b, hb⟩ := (hker (g ^ 2)).mp hκ
  have hb' : (g.val ^ 2).left = sc b := hb
  obtain ⟨U, hUr, hUp, hUκ⟩ := exists_normalized_pair (coordinateQuadOdd n K) hd g hσ hb'
  have hσU : orderOf U.val.right = 2 := by rw [hUr]; exact hσ
  have hap' : ∀ v, (⇑(coordinateSemilinearMap U.val))^[2] v = v := fun v => by
    rw [iterate_coordinateSemilinearMap, hUp, coordinateSemilinearMap_one]
  have hQa : ∀ v, coordinateQuadOdd n K (coordinateSemilinearMap U.val v) =
      (multiplier (coordinateQuadOdd n K) U : K) * U.val.right (coordinateQuadOdd n K v) :=
    fun v => multiplier_spec (coordinateQuadOdd n K) U v
  have : Nonempty (Fin (2 * n + 1)) := ⟨⟨0, hd⟩⟩
  obtain ⟨-, -, c, Q₀, hQ₀, hnd₀, hfr, Φ, hΦ1, -⟩ :=
    exists_descent hℓ hf hK U.val.right hσU (coordinateSemilinearMap U.val)
      (coordinateSemilinearMap_smul U.val) hap' (coordinateQuadOdd n K) hnd
      (multiplier (coordinateQuadOdd n K) U : K) hQa
  have hfr' : finrank (fixedField U.val) (fixedSpace U.val) = 2 * n + 1 := hfr.trans (by simp)
  have : Finite (fixedField U.val) := inferInstance
  have : FiniteDimensional (fixedField U.val) (fixedSpace U.val) := Module.Finite.of_finite
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hnd₀
  have hdim : 2 * m + δ = 2 * n + 1 := H.finrank_eq.symm.trans hfr'
  obtain rfl : δ = 1 := by
    have := hδ
    omega
  have hnm : n = m := by omega
  subst hnm
  let ι : fixedSpace U.val →+ (Fin (2 * n + 1) → K) := (fixedSpace U.val).subtype.toAddMonoidHom
  have hι : ∀ w, ((c : K) • coordinateQuadOdd n K) (ι w) =
      algebraMap (fixedField U.val) K (Q₀ w) := by
    intro w
    have h1 := hQ₀ w
    change (c : K) * coordinateQuadOdd n K (w : Fin (2 * n + 1) → K) =
      ((Q₀ w : fixedField U.val) : K)
    exact h1.symm
  let bK : Basis (Fin n ⊕ Fin n ⊕ Fin 1) K (Fin (2 * n + 1) → K) := (H.b.baseChange K).map Φ
  have hbK : ∀ a, bK a = ι (H.b a) := by
    intro a
    show Φ ((H.b.baseChange K) a) = _
    rw [Basis.baseChange_apply, hΦ1, one_smul]
    rfl
  let HK : HypSplit ((c : K) • coordinateQuadOdd n K) n 1 :=
    hypSplitExtendLeOne ι hι H le_rfl bK hbK
  have hbK' : ∀ a, HK.b a = ((H.b a : fixedSpace U.val) : Fin (2 * n + 1) → K) := fun a => hbK a
  have hα : Q₀ (H.b (.inr (.inr 0))) ≠ 0 := H.Q_tail_one_ne_zero
  let u : (fixedField U.val)ˣ := Units.mk0 _ hα
  let uK : Kˣ := Units.map (algebraMap (fixedField U.val) K).toMonoidHom u
  have huK : (uK : K) = ((c : K) • coordinateQuadOdd n K) (HK.b (.inr (.inr 0))) := by
    rw [hbK', smul_form_coe hQ₀]
    rfl
  let bk := (H.scaled u).reindex (HypSplit.oddEquiv n)
  let bK' := (HK.scaled uK).reindex (HypSplit.oddEquiv n)
  have hb : ∀ a, bK' a = ((bk a : fixedSpace U.val) : Fin (2 * n + 1) → K) := fun a => by
    show ((HK.scaled uK).reindex (HypSplit.oddEquiv n)) a =
      (((H.scaled u).reindex (HypSplit.oddEquiv n)) a : fixedSpace U.val)
    rw [Basis.reindex_apply, Basis.reindex_apply]
    exact scaled_coe H HK hbK' u _
  have hν : ∀ v, coordinateQuadOdd n K (fun j => bK'.equivFun v ((oddIndexEquiv n).symm j)) =
      ((uK⁻¹ * c : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    have h1 := HK.displayOdd uK huK v
    have h2 : coordinateQuadOdd n K (fun j => bK'.equivFun v ((oddIndexEquiv n).symm j)) =
        StatedQuadOdd n K (bK'.equivFun v) := by
      rw [coordinateQuadOdd_apply]
      simp [StatedQuadOdd]
    rw [h2, Units.val_mul]
    change StatedQuadOdd n K (((HK.scaled uK).reindex (HypSplit.oddEquiv n)).equivFun v) = _ at h1
    rw [h1]
    have h3 : ((c : K) • coordinateQuadOdd n K) v = c * coordinateQuadOdd n K v := rfl
    rw [h3]
    ring
  let g' : similarityPairs (coordinateQuadOdd n K) :=
    ⟨SemidirectProduct.inr U.val.right,
      inr_mem_similarityPairs _ _ (coordinateQuadOdd_field n U.val.right)⟩
  obtain ⟨-, -, -, -, -, Θ, -, g'', hg''l, hg''r, hΘ⟩ := transports_of_basis (oddIndexEquiv n)
    (coordinateQuadOdd n K) (coordinateQuadOdd n K) U bk bK' hb (uK⁻¹ * c) hν g' (by simp [g'])
    rfl
  refine ⟨Θ, ?_⟩
  have h1 : Θ * matrixProjectiveConjugationHom (coordinateQuadOdd n K) g =
      matrixProjectiveConjugationHom (coordinateQuadOdd n K) g'' * Θ := by
    ext x
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hUκ]
    exact hΘ x
  rw [h1, mul_inv_cancel_right]
  congr 1
  exact Subtype.ext (SemidirectProduct.ext hg''l (hg''r.trans hUr))

end Descent

end CFSG.ComponentClassification.HarrisLit.T1
