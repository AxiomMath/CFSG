module

public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open QuadraticMap Module

@[expose] def starNat (a : ℕ) : ℕ := if a < 6 then (if a % 2 = 0 then a + 1 else a - 1) else a

namespace KGE

open CFSG.ClassicalGroups.Orthogonal (HypPair)

theorem starNat_lt {a : ℕ} (ha : a < 6) : starNat a < 6 := by
  unfold starNat
  split_ifs <;> omega

theorem starNat_starNat (a : ℕ) : starNat (starNat a) = a := by
  unfold starNat
  split_ifs <;> omega

theorem starNat_inj {a b : ℕ} (h : starNat a = starNat b) : a = b := by
  rw [← starNat_starNat a, h, starNat_starNat]

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] {Q : QuadraticForm k W}

theorem map_hexad (P₁ P₂ P₃ : HypPair Q) (a : Fin 6) :
    Q (![P₁.e, P₁.f, P₂.e, P₂.f, P₃.e, P₃.f] a) = 0 := by
  fin_cases a <;> simp [HypPair.Q_e, HypPair.Q_f]

theorem polar_hexad {P₁ P₂ P₃ : HypPair Q} (h12 : P₁.Orth P₂) (h13 : P₁.Orth P₃)
    (h23 : P₂.Orth P₃) (a j : Fin 6) :
    polar Q (![P₁.e, P₁.f, P₂.e, P₂.f, P₃.e, P₃.f] a)
      (![P₁.e, P₁.f, P₂.e, P₂.f, P₃.e, P₃.f] j) = if j.val = starNat a.val then 1 else 0 := by
  fin_cases a <;> fin_cases j <;>
    simp [starNat, HypPair.Q_e, HypPair.Q_f, HypPair.polar_ef, HypPair.polar_fe, h12.ee,
      h12.ef, h12.fe, h12.ff, h13.ee, h13.ef, h13.fe, h13.ff, h23.ee, h23.ef, h23.fe, h23.ff,
      h12.symm.ee, h12.symm.ef, h12.symm.fe, h12.symm.ff, h13.symm.ee, h13.symm.ef,
      h13.symm.fe, h13.symm.ff, h23.symm.ee, h23.symm.ef, h23.symm.fe, h23.symm.ff]

theorem polar_sum_star {c : Fin 6 → W}
    (hc : ∀ a j : Fin 6, polar Q (c a) (c j) = if j.val = starNat a.val then 1 else 0)
    (x : Fin 6 → k) (a : Fin 6) :
    polar Q (∑ i, x i • c i) (c ⟨starNat a.val, starNat_lt a.isLt⟩) = x a := by
  rw [CFSG.LocalAnalysis.ComponentInitial.polar_sum_smul_left, Finset.sum_eq_single a]
  · rw [hc, if_pos rfl, mul_one]
  · intro i _ hia
    rw [hc, if_neg fun h => hia (Fin.ext (starNat_inj h).symm), mul_zero]
  · exact fun ha => absurd (Finset.mem_univ a) ha

theorem linearIndependent_of_polar {c : Fin 6 → W}
    (hc : ∀ a j : Fin 6, polar Q (c a) (c j) = if j.val = starNat a.val then 1 else 0) :
    LinearIndependent k c := by
  refine Fintype.linearIndependent_iff.2 fun x hx a => ?_
  rw [← polar_sum_star hc x a, hx, polar_zero_left]

theorem exists_basis_extend [FiniteDimensional k W] (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 3 ≤ m) (hdim : finrank k W = 2 * m) {c : Fin 6 → W}
    (hc : ∀ a j : Fin 6, polar Q (c a) (c j) = if j.val = starNat a.val then 1 else 0) :
    ∃ b : Basis (Fin (2 * m)) k W,
      (∀ (i : Fin 6) (a : Fin (2 * m)), a.val = i.val → b a = c i) ∧
      ∀ a j : Fin (2 * m), a.val < 6 →
        polar Q (b a) (b j) = if j.val = starNat a.val then 1 else 0 := by
  have hli := linearIndependent_of_polar hc
  set U := Submodule.span k (Set.range c) with hU
  set U' := LinearMap.BilinForm.orthogonal (polarBilin Q) U with hU'
  have hcompl : IsCompl U U' := by
    refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint fun x y hxy => ?_).mpr ?_
    · rw [polarBilin_apply_apply] at hxy ⊢
      rw [polar_comm]
      exact hxy
    · rw [Submodule.disjoint_def]
      intro y hy hy'
      obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy
      have hx : ∀ a, x a = 0 := fun a => by
        rw [← polar_sum_star hc x a, polar_comm]
        exact LinearMap.BilinForm.mem_orthogonal_iff.mp hy'
          (c ⟨starNat a.val, starNat_lt a.isLt⟩) (Submodule.subset_span ⟨_, rfl⟩)
      simp [hx]
  have hfr : finrank k U' = 2 * m - 6 := by
    rw [hU', LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hU, finrank_span_eq_card hli,
      Fintype.card_fin]
  let b' : Basis (Fin (2 * m - 6)) k U' := Module.finBasisOfFinrankEq k U' hfr
  let v : Fin 6 ⊕ Fin (2 * m - 6) → W := Sum.elim c (U'.subtype ∘ b')
  have hspan' : Submodule.span k (Set.range (U'.subtype ∘ b')) = U' := by
    rw [Set.range_comp, Submodule.span_image, b'.span_eq, Submodule.map_subtype_top]
  have hliv : LinearIndependent k v :=
    hli.sum_type (b'.linearIndependent.map' U'.subtype U'.ker_subtype)
      (by rw [hspan']; exact hcompl.disjoint)
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspan', hcompl.sup_eq_top]
  have hsum : 6 + (2 * m - 6) = 2 * m := by omega
  let E : Fin 6 ⊕ Fin (2 * m - 6) ≃ Fin (2 * m) := finSumFinEquiv.trans (finCongr hsum)
  have hbE : ∀ x, (Basis.mk hliv hsp).reindex E (E x) = v x := fun x => by
    rw [Basis.reindex_apply, Equiv.symm_apply_apply, Basis.mk_apply]
  have hEl : ∀ i : Fin 6, (E (Sum.inl i)).val = i.val := fun i => rfl
  have hEr : ∀ i : Fin (2 * m - 6), (E (Sum.inr i)).val = 6 + i.val := fun i => rfl
  refine ⟨(Basis.mk hliv hsp).reindex E, fun i a ha => ?_, fun a j ha => ?_⟩
  · obtain ⟨x, rfl⟩ := E.surjective a
    rcases x with i' | i'
    · have hii : i' = i := Fin.ext ((hEl i').symm.trans ha)
      subst hii
      exact hbE _
    · have := i.isLt
      rw [hEr] at ha
      omega
  · obtain ⟨x, rfl⟩ := E.surjective a
    obtain ⟨y, rfl⟩ := E.surjective j
    rcases x with i | i
    · rw [hbE, hbE, hEl]
      rcases y with i' | i'
      · rw [hEl]
        exact hc i i'
      · have := starNat_lt i.isLt
        rw [hEr, if_neg (by omega)]
        exact LinearMap.BilinForm.mem_orthogonal_iff.mp (b' i').2 (c i)
          (Submodule.subset_span ⟨i, rfl⟩)
    · rw [hEr] at ha
      omega

end KGE

theorem exists_adapted_basis {k W : Type*} [Field k] [Finite k] [CharP k 2] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {Q : QuadraticForm k W}
    (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} (hm : 4 ≤ m) (hdim : finrank k W = 2 * m)
    {u w : W} (huw : LinearIndependent k ![u, w]) (hu : Q u = 0) (hw : Q w = 0)
    (hp : polar Q u w = 0) :
    ∃ b : Basis (Fin (2 * m)) k W, (∀ a : Fin (2 * m), a.val = 0 → b a = u) ∧
      (∀ a : Fin (2 * m), a.val = 2 → b a = w) ∧
      (∀ a : Fin (2 * m), a.val < 6 → Q (b a) = 0) ∧
      ∀ a j : Fin (2 * m), a.val < 6 →
        polar Q (b a) (b j) = if j.val = starNat a.val then 1 else 0 := by
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ :=
    (ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms Q
      hQ).2.2.2.2.2 m hdim hm
  have hli2 : LinearIndependent k ![P₁.e, P₂.e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : polar Q (s • P₁.e + t • P₂.e) P₁.f = 0 := by rw [hst, polar_zero_left]
    have h2 : polar Q (s • P₁.e + t • P₂.e) P₂.f = 0 := by rw [hst, polar_zero_left]
    rw [polar_add_left, polar_smul_left, polar_smul_left, P₁.polar_ef, polar_comm Q P₂.e,
      h12.fe, smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero] at h1
    rw [polar_add_left, polar_smul_left, polar_smul_left, h12.ef, P₂.polar_ef, smul_eq_mul,
      smul_eq_mul, mul_one, mul_zero, zero_add] at h2
    exact ⟨h1, h2⟩
  obtain ⟨g, hg, hgu⟩ := RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq hQ
    ![P₁.e, P₂.e] ![u, w] hli2 huw
    (fun i => by fin_cases i <;> simp [hu, hw, P₁.Q_e, P₂.Q_e])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [hu, hw, P₁.Q_e, P₂.Q_e, hp, polar_comm Q w u, h12.ee, h12.symm.ee])
  have hg0 : g P₁.e = u := hgu 0
  have hg1 : g P₂.e = w := hgu 1
  have hc : ∀ a j : Fin 6, polar Q (g (![P₁.e, P₁.f, P₂.e, P₂.f, P₃.e, P₃.f] a))
      (g (![P₁.e, P₁.f, P₂.e, P₂.f, P₃.e, P₃.f] j)) = if j.val = starNat a.val then 1 else 0 :=
    fun a j => (ClassicalGroups.Orthogonal.polar_map_of_mem hg _ _).trans
      (KGE.polar_hexad h12 h13 h23 a j)
  obtain ⟨b, hbc, hb⟩ := KGE.exists_basis_extend hQ (by omega) hdim hc
  refine ⟨b, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, hb⟩
  · rw [hbc 0 a ha]
    exact hg0
  · rw [hbc 2 a ha]
    exact hg1
  · rw [hbc ⟨a.val, ha⟩ a rfl]
    exact (ClassicalGroups.Orthogonal.map_of_mem hg _).trans (KGE.map_hexad P₁ P₂ P₃ _)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus
