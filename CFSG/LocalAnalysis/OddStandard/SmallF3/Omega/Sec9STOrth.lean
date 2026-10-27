module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STEven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem IsEvenFrame.exists_sep {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft) (hn : 3 ≤ n) {i j : Fin n}
    (hij : i ≠ j) :
    ∃ g ∈ Ft, (g : V ≃ₗ[ZMod 3] V) (b i) = -(b i) ∧ (g : V ≃ₗ[ZMod 3] V) (b j) = b j := by
  classical
  have hlt : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hki : k ≠ i := fun h => hk (by rw [h]; simp)
  have hkj : k ≠ j := fun h => hk (by rw [h]; simp)
  obtain ⟨g, hgmem, hact⟩ := hb.2 ({i, k} : Finset (Fin n)) (by
    rw [Finset.card_pair (Ne.symm hki)]; exact even_two)
  refine ⟨g, hgmem, ?_, ?_⟩
  · rw [hact i, if_pos (by simp), neg_one_smul]
  · rw [hact j, if_neg (by simp [Ne.symm hij, Ne.symm hkj]), one_smul]

theorem IsEvenFrame.polar_eq_zero {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft) (hn : 3 ≤ n) {i j : Fin n}
    (hij : i ≠ j) : QuadraticMap.polar Q (b i) (b j) = 0 := by
  obtain ⟨g, -, hgi, hgj⟩ := IsEvenFrame.exists_sep hb hn hij
  have hp : QuadraticMap.polar Q ((g : V ≃ₗ[ZMod 3] V) (b i))
      ((g : V ≃ₗ[ZMod 3] V) (b j)) = QuadraticMap.polar Q (b i) (b j) :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 (b i) (b j)
  rw [hgi, hgj, QuadraticMap.polar_neg_left] at hp
  have h2 : (2 : ZMod 3) * QuadraticMap.polar Q (b i) (b j) = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hp.symm
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

theorem IsEvenFrame.map_ne_zero (hQ : Q.Nondegenerate) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft)
    (hn : 3 ≤ n) (i : Fin n) : Q (b i) ≠ 0 := by
  intro hQi
  have hB : Q.polarBilin.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mpr hQ
  have hzero : b i = 0 := by
    refine hB.1 (b i) fun v => ?_
    rw [← b.sum_repr v]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul, QuadraticMap.polarBilin_apply_apply]
    by_cases hji : j = i
    · rw [hji]
      simp [hQi]
    · rw [IsEvenFrame.polar_eq_zero (b := b) (Ft := Ft) hb hn (i := i) (j := j)
        (fun h => hji h.symm), smul_zero]
  exact (b.ne_zero i) hzero

end CFSG.OddStandard.SmallF3.Omega
