module

public import CFSG.Timmesfeld.Transvection.QTwoThin
public import CFSG.OddTranspositions.Width
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.OddTranspositions CFSG.Timmesfeld.Transvection.QTwo Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_plane_vector_pair (Q : QuadraticForm (ZMod 2) V) {e f : V}
    (hef : QuadraticMap.polar Q e f = 1) :
    ∃ u t : V,
      u ∈ Submodule.span (ZMod 2) ({e, f} : Set V) ∧
      t ∈ Submodule.span (ZMod 2) ({e, f} : Set V) ∧
      Q u = 1 ∧ QuadraticMap.polar Q u t = 1 := by
  by_cases h0 : Q e = 1
  · exact ⟨e, f, Submodule.subset_span (by simp), Submodule.subset_span (by simp), h0, hef⟩
  · have h0' : Q e = 0 := by
      rcases zmod_two_eq_zero_or_one (Q e) with h | h
      · exact h
      · exact absurd h h0
    by_cases h1 : Q f = 1
    · refine ⟨f, e, Submodule.subset_span (by simp), Submodule.subset_span (by simp), h1, ?_⟩
      rw [QuadraticMap.polar_comm Q f e]
      exact hef
    · have h1' : Q f = 0 := by
        rcases zmod_two_eq_zero_or_one (Q f) with h | h
        · exact h
        · exact absurd h h1
      refine ⟨e + f, e, ?_, Submodule.subset_span (by simp), ?_, ?_⟩
      · exact Submodule.add_mem _
          (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      · have hsum : Q (e + f) = Q e + Q f + QuadraticMap.polar Q e f := by
          rw [QuadraticMap.polar]
          abel
        rw [hsum, h0', h1', hef]
        simp
      · rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self,
          QuadraticMap.polar_comm Q f e, hef]
        rw [two_nsmul, CharTwo.add_self_eq_zero, zero_add]

theorem polar_span_pair_eq_zero (Q : QuadraticForm (ZMod 2) V)
    {a b c d x y : V}
    (hac : QuadraticMap.polar Q a c = 0) (had : QuadraticMap.polar Q a d = 0)
    (hbc : QuadraticMap.polar Q b c = 0) (hbd : QuadraticMap.polar Q b d = 0)
    (hx : x ∈ Submodule.span (ZMod 2) ({a, b} : Set V))
    (hy : y ∈ Submodule.span (ZMod 2) ({c, d} : Set V)) :
    QuadraticMap.polar Q x y = 0 := by
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨s', t', hst'⟩ := Submodule.mem_span_pair.mp hy
  rw [← hst, ← hst']
  simp [hac, had, hbc, hbd]

theorem exists_three_pairwise_orthogonal_vectors {m : ℕ} (hm : 3 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    ∃ v0 v1 v2 : Fin (2 * m) → ZMod 2,
      Q v0 = 1 ∧ Q v1 = 1 ∧ Q v2 = 1 ∧
      v0 ≠ 0 ∧ v1 ≠ 0 ∧ v2 ≠ 0 ∧
      v0 ≠ v1 ∧ v0 ≠ v2 ∧ v1 ≠ v2 ∧
      QuadraticMap.polar Q v0 v1 = 0 ∧
      QuadraticMap.polar Q v0 v2 = 0 ∧
      QuadraticMap.polar Q v1 v2 = 0 := by
  classical
  let b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2) := QuadraticMap.polarBilin Q
  have hbalt : b.IsAlt := fun x => by
    simpa [b, QuadraticMap.polarBilin_apply_apply] using polar_self_zmod_two (Q := Q) x
  have hndb : b.SeparatingLeft := by
    intro x hx
    exact hnd x fun y => by
      simpa [b, QuadraticMap.polarBilin_apply_apply] using hx y
  have hbn : b.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hbalt.isRefl).mpr hndb
  obtain ⟨m', bs, hbs⟩ := hbalt.exists_basis_toMatrix_eq_J hbn
  have hcard : Fintype.card (Fin m' ⊕ Fin m') = 2 * m := by
    rw [← Module.finrank_eq_card_basis bs, Module.finrank_fintype_fun_eq_card]
    simp
  have hm' : m' = m := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  subst m'
  let e : Fin m → (Fin (2 * m) → ZMod 2) := fun i => bs (Sum.inl i)
  let f : Fin m → (Fin (2 * m) → ZMod 2) := fun i => bs (Sum.inr i)
  have hJb : ∀ a c : Fin m ⊕ Fin m,
      b (bs a) (bs c) = Matrix.J (Fin m) (ZMod 2) a c := by
    intro a c
    rw [← LinearMap.BilinForm.toMatrix_apply bs b a c, hbs]
  have hJ : ∀ a c : Fin m ⊕ Fin m,
      QuadraticMap.polar Q (bs a) (bs c) = Matrix.J (Fin m) (ZMod 2) a c := by
    intro a c
    rw [← QuadraticMap.polarBilin_apply_apply Q (bs a) (bs c)]
    simpa [b] using hJb a c
  have hef : ∀ i : Fin m, QuadraticMap.polar Q (e i) (f i) = 1 := by
    intro i
    change QuadraticMap.polar Q (bs (Sum.inl i)) (bs (Sum.inr i)) = 1
    rw [hJ]
    simp [Matrix.J]
  have hplane : ∀ i : Fin m, ∃ u t : Fin (2 * m) → ZMod 2,
      u ∈ Submodule.span (ZMod 2)
        ({e i, f i} : Set (Fin (2 * m) → ZMod 2)) ∧
      t ∈ Submodule.span (ZMod 2)
        ({e i, f i} : Set (Fin (2 * m) → ZMod 2)) ∧
      Q u = 1 ∧ QuadraticMap.polar Q u t = 1 :=
    fun i => exists_plane_vector_pair Q (hef i)
  choose u t hu using hplane
  have hu_mem : ∀ i : Fin m, u i ∈ Submodule.span (ZMod 2)
      ({e i, f i} : Set (Fin (2 * m) → ZMod 2)) := fun i => (hu i).1
  have ht_mem : ∀ i : Fin m, t i ∈ Submodule.span (ZMod 2)
      ({e i, f i} : Set (Fin (2 * m) → ZMod 2)) := fun i => (hu i).2.1
  have huQ : ∀ i : Fin m, Q (u i) = 1 := fun i => (hu i).2.2.1
  have hut : ∀ i : Fin m, QuadraticMap.polar Q (u i) (t i) = 1 := fun i => (hu i).2.2.2
  have hcross : ∀ i j : Fin m, i ≠ j →
      QuadraticMap.polar Q (e i) (e j) = 0 ∧
      QuadraticMap.polar Q (e i) (f j) = 0 ∧
      QuadraticMap.polar Q (f i) (e j) = 0 ∧
      QuadraticMap.polar Q (f i) (f j) = 0 := by
    intro i j hij
    refine ⟨?_, ?_, ?_, ?_⟩
    · change QuadraticMap.polar Q (bs (Sum.inl i)) (bs (Sum.inl j)) = 0
      rw [hJ]
      simp [Matrix.J, hij]
    · change QuadraticMap.polar Q (bs (Sum.inl i)) (bs (Sum.inr j)) = 0
      rw [hJ]
      simp [Matrix.J, hij]
    · change QuadraticMap.polar Q (bs (Sum.inr i)) (bs (Sum.inl j)) = 0
      rw [hJ]
      simp [Matrix.J, hij]
    · change QuadraticMap.polar Q (bs (Sum.inr i)) (bs (Sum.inr j)) = 0
      rw [hJ]
      simp [Matrix.J, hij]
  have horth : ∀ i j : Fin m, i ≠ j → QuadraticMap.polar Q (u i) (u j) = 0 := by
    intro i j hij
    obtain ⟨hac, had, hbc, hbd⟩ := hcross i j hij
    exact polar_span_pair_eq_zero Q hac had hbc hbd (hu_mem i) (hu_mem j)
  have hune : ∀ i j : Fin m, i ≠ j → u i ≠ u j := by
    intro i j hij h
    obtain ⟨hac, had, hbc, hbd⟩ := hcross j i hij.symm
    have hzero : QuadraticMap.polar Q (u j) (t i) = 0 :=
      polar_span_pair_eq_zero Q hac had hbc hbd (hu_mem j) (ht_mem i)
    have h1 : QuadraticMap.polar Q (u j) (t i) = 1 := by
      rw [← h]
      exact hut i
    rw [hzero] at h1
    exact zero_ne_one h1
  have hu_ne : ∀ i : Fin m, u i ≠ 0 := by
    intro i h
    have := huQ i
    rw [h, QuadraticMap.map_zero] at this
    exact zero_ne_one this
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hi02 : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i2] at this
  have hi12 : i1 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i1, i2] at this
  exact ⟨u i0, u i1, u i2, huQ i0, huQ i1, huQ i2,
    hu_ne i0, hu_ne i1, hu_ne i2,
    hune i0 i1 hi01, hune i0 i2 hi02, hune i1 i2 hi12,
    horth i0 i1 hi01, horth i0 i2 hi02, horth i1 i2 hi12⟩

theorem exists_three_commuting_orthogonal_transvections {m : ℕ} (hm : 3 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    ∃ g0 g1 g2 : GL (Fin (2 * m)) (ZMod 2),
      g0 ∈ fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x) ∧
      g1 ∈ fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x) ∧
      g2 ∈ fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x) ∧
      g0 ∈ fischerTransvections (QuadraticMap.polar Q) (fun v => Q v = 1) ∧
      g1 ∈ fischerTransvections (QuadraticMap.polar Q) (fun v => Q v = 1) ∧
      g2 ∈ fischerTransvections (QuadraticMap.polar Q) (fun v => Q v = 1) ∧
      g0 ≠ g1 ∧ g0 ≠ g2 ∧ g1 ≠ g2 ∧
      Commute g0 g1 ∧ Commute g0 g2 ∧ Commute g1 g2 := by
  obtain ⟨v0, v1, v2, hv0, hv1, hv2, hv0', hv1', hv2', hv01, hv02, hv12,
    h01, h02, h12⟩ := exists_three_pairwise_orthogonal_vectors hm Q hnd
  refine ⟨orthTransvectionGL Q v0, orthTransvectionGL Q v1, orthTransvectionGL Q v2,
    tv_mem_group hv0, tv_mem_group hv1, tv_mem_group hv2,
    tv_mem hv0, tv_mem hv1, tv_mem hv2, ?_, ?_, ?_,
    (tv_commute_iff hnd hv0 hv1).mpr h01,
    (tv_commute_iff hnd hv0 hv2).mpr h02,
    (tv_commute_iff hnd hv1 hv2).mpr h12⟩
  · intro h
    exact hv01 (eq_of_tv_eq hnd hv0 hv1 h)
  · intro h
    exact hv02 (eq_of_tv_eq hnd hv0 hv2 h)
  · intro h
    exact hv12 (eq_of_tv_eq hnd hv1 hv2 h)

theorem exists_three_commuting_mem_of_orthogonal_case {G : Type*} [Group G] {D : Set G}
    {m : ℕ} (hm : 3 ≤ m) (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmodel : fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    ∃ y0 y1 y2 : G,
      y0 ∈ D ∧ y1 ∈ D ∧ y2 ∈ D ∧
      y0 ≠ y1 ∧ y0 ≠ y2 ∧ y1 ≠ y2 ∧
      Commute y0 y1 ∧ Commute y0 y2 ∧ Commute y1 y2 := by
  classical
  obtain ⟨g0, g1, g2, hg0H, hg1H, hg2H, hg0T, hg1T, hg2T,
    hg01, hg02, hg12, hc01, hc02, hc12⟩ :=
    exists_three_commuting_orthogonal_transvections hm Q hnd
  obtain ⟨φ, hD⟩ := hmodel
  let y0 : G := φ.symm ⟨g0, hg0H⟩
  let y1 : G := φ.symm ⟨g1, hg1H⟩
  let y2 : G := φ.symm ⟨g2, hg2H⟩
  have hy0D : y0 ∈ D := by
    rw [hD y0]
    simpa [y0] using hg0T
  have hy1D : y1 ∈ D := by
    rw [hD y1]
    simpa [y1] using hg1T
  have hy2D : y2 ∈ D := by
    rw [hD y2]
    simpa [y2] using hg2T
  have hy01 : y0 ≠ y1 := by
    intro h
    exact hg01 (by simpa [y0, y1] using φ.symm.injective h)
  have hy02 : y0 ≠ y2 := by
    intro h
    exact hg02 (by simpa [y0, y2] using φ.symm.injective h)
  have hy12 : y1 ≠ y2 := by
    intro h
    exact hg12 (by simpa [y1, y2] using φ.symm.injective h)
  have hcomm01 : Commute y0 y1 := by
    have hH : Commute (φ y0) (φ y1) := by
      rw [show φ y0 = ⟨g0, hg0H⟩ from φ.apply_symm_apply ⟨g0, hg0H⟩,
        show φ y1 = ⟨g1, hg1H⟩ from φ.apply_symm_apply ⟨g1, hg1H⟩]
      exact Subtype.ext hc01
    simpa [y0, y1] using hH.map φ.symm.toMonoidHom
  have hcomm02 : Commute y0 y2 := by
    have hH : Commute (φ y0) (φ y2) := by
      rw [show φ y0 = ⟨g0, hg0H⟩ from φ.apply_symm_apply ⟨g0, hg0H⟩,
        show φ y2 = ⟨g2, hg2H⟩ from φ.apply_symm_apply ⟨g2, hg2H⟩]
      exact Subtype.ext hc02
    simpa [y0, y2] using hH.map φ.symm.toMonoidHom
  have hcomm12 : Commute y1 y2 := by
    have hH : Commute (φ y1) (φ y2) := by
      rw [show φ y1 = ⟨g1, hg1H⟩ from φ.apply_symm_apply ⟨g1, hg1H⟩,
        show φ y2 = ⟨g2, hg2H⟩ from φ.apply_symm_apply ⟨g2, hg2H⟩]
      exact Subtype.ext hc12
    simpa [y1, y2] using hH.map φ.symm.toMonoidHom
  exact ⟨y0, y1, y2, hy0D, hy1D, hy2D, hy01, hy02, hy12,
    hcomm01, hcomm02, hcomm12⟩

theorem width_two_false_of_orthogonal_case {G : Type*} [Group G] {D : Set G}
    {m : ℕ} (hm : 3 ≤ m) (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmodel : fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    ¬ WidthLe D 2 := by
  obtain ⟨y0, y1, y2, hy0D, hy1D, hy2D, hy01, hy02, hy12, hcomm01, hcomm02, hcomm12⟩ :=
    exists_three_commuting_mem_of_orthogonal_case hm Q hnd hmodel
  intro hW
  rw [widthLe_two_iff] at hW
  exact hW y0 hy0D y1 hy1D y2 hy2D hy01 hy02 hy12
    ⟨hcomm01, hcomm02, hcomm12⟩

end CFSG.Fischer.Classification
