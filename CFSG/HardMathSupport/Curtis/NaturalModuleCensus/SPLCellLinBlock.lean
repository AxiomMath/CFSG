module

public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

variable {n : ℕ} {K : Type} [Field K]

noncomputable abbrev linEnd (y : GL (Fin n) K) : Module.End K (Fin n → K) :=
  Matrix.toLin' (y : Matrix (Fin n) (Fin n) K)

theorem not_isSolvable_subgroup_of_perfect {G : Type*} [Group G] (T Q : Subgroup G) (hQT : Q ≤ T)
    (hQ : ⁅Q, Q⁆ = Q) (hne : Q ≠ ⊥) : ¬ Group.IsSolvable T := by
  intro hT
  have hQ' : Group.IsPerfect Q := Subgroup.isPerfect_iff.2 hQ
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  have hs : Group.IsSolvable Q :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQT)
      (Subgroup.inclusion_injective hQT)
  exact Group.IsPerfect.not_isSolvable Q hs

section Squarefree

variable {p : ℕ}

theorem natCast_ne_zero_of_charP_two [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  intro h0
  rw [CharP.cast_eq_zero_iff K 2] at h0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm

theorem aeval_linEnd_X_pow_sub_C {y : GL (Fin n) K} (c : Kˣ)
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    aeval (linEnd y) (X ^ p - C (c : K) : K[X]) = 0 := by
  have h1 : (y : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) (c : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hyp
    simpa using this
  have h2 : linEnd y = Matrix.toLinAlgEquiv' (y : Matrix (Fin n) (Fin n) K) :=
    (toLinAlgEquiv'_eq_toLin' _).symm
  rw [h2]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [← map_pow, h1]
  rw [show (algebraMap K (Module.End K (Fin n → K)) (c : K)) =
    Matrix.toLinAlgEquiv' (Matrix.scalar (Fin n) (c : K)) from by
      rw [← AlgEquiv.commutes Matrix.toLinAlgEquiv' (c : K)]; rfl]
  exact sub_self _

theorem squarefree_minpoly_linEnd_of_pow_scalar (hpK : (p : K) ≠ 0) {y : GL (Fin n) K} (c : Kˣ)
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K (linEnd y)) := by
  have hsep : (X ^ p - C (c : K) : K[X]).Separable :=
    separable_X_pow_sub_C (c : K) hpK c.ne_zero
  exact squarefree_minpoly_of_aeval_eq_zero hsep.squarefree (aeval_linEnd_X_pow_sub_C c hyp)

theorem minpoly_linEnd_of_pow_scalar_irreducible (hp : p.Prime) {y : GL (Fin n) K} (c : Kˣ)
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) (hnp : ∀ b : K, b ^ p ≠ c)
    (hn0 : n ≠ 0) :
    minpoly K (linEnd y) = X ^ p - C (c : K) ∧ Irreducible (minpoly K (linEnd y)) := by
  have : NeZero n := ⟨hn0⟩
  have hirr : Irreducible (X ^ p - C (c : K) : K[X]) := X_pow_sub_C_irreducible_of_prime hp hnp
  have hmin : (X ^ p - C (c : K) : K[X]) = minpoly K (linEnd y) :=
    minpoly.eq_of_irreducible_of_monic hirr (aeval_linEnd_X_pow_sub_C c hyp)
      (monic_X_pow_sub_C _ hp.ne_zero)
  exact ⟨hmin.symm, hmin ▸ hirr⟩

end Squarefree

section Block

open scoped _root_.Classical

variable [Finite K] {y : GL (Fin n) K}

theorem finite_efac (a : primaryFactors (linEnd y)) : Finite (Efac (linEnd y) a) := by
  have : Module.Finite K (Efac (linEnd y) a) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finite
  exact Module.finite_of_finite K

theorem exists_finset_card_four_of_card (a : primaryFactors (linEnd y))
    (h : 4 ≤ Nat.card (Efac (linEnd y) a)) : ∃ s : Finset (Efac (linEnd y) a), s.card = 4 := by
  have := finite_efac a
  have := Fintype.ofFinite (Efac (linEnd y) a)
  have h4 : 4 ≤ (Finset.univ : Finset (Efac (linEnd y) a)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
  exact ⟨t, ht⟩

theorem card_K_le_card_efac (a : primaryFactors (linEnd y)) :
    Nat.card K ≤ Nat.card (Efac (linEnd y) a) := by
  have := finite_efac a
  exact Nat.card_le_card_of_injective _ (algebraMap K (Efac (linEnd y) a)).injective

theorem isQuasisimple_blockImage_of_card (hx : Squarefree (minpoly K (linEnd y)))
    (a : primaryFactors (linEnd y)) (ha : 2 ≤ mult (linEnd y) a)
    (hE : 3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a)) :
    CFSG.IsQuasisimple (blockImage hx a) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx))
    (isQuasisimple_blockSL a ha
      (hE.imp_right fun h => exists_finset_card_four_of_card a h))

theorem blockImage_le_range_toGL_of_card (hx : Squarefree (minpoly K (linEnd y)))
    (a : primaryFactors (linEnd y)) (ha : 2 ≤ mult (linEnd y) a)
    (hE : 3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a)) :
    blockImage hx a ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* _).range := by
  intro g hg
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  exact CFSG.RankThree.PartOne.KCUnitary.eq_one_of_perfect_of_comm
    (isQuasisimple_blockImage_of_card hx a ha hE).1 (fun u v : Kˣ => mul_comm u v)
    ((GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp (blockImage hx a).subtype) ⟨g, hg⟩

omit [Finite K] in
theorem blockImage_le_centralizer (hx : Squarefree (minpoly K (linEnd y)))
    (a : primaryFactors (linEnd y)) :
    blockImage hx a ≤ Subgroup.centralizer ({y} : Set (GL (Fin n) K)) :=
  (blockImage_le_range hx a).trans
    (range_commutantUnitsToGL_eq_centralizer y rfl).le

theorem not_isSolvable_autFix_of_block (hx : Squarefree (minpoly K (linEnd y)))
    (a : primaryFactors (linEnd y)) (ha : 2 ≤ mult (linEnd y) a)
    (hE : 3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a)) :
    ¬ Group.IsSolvable (autFix (conjAut n K y)) := by
  have hq := isQuasisimple_blockImage_of_card hx a ha hE
  have hle := blockImage_le_range_toGL_of_card hx a ha hE
  have hcen := blockImage_le_centralizer hx a
  set B := blockImage hx a with hB
  let toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K := SpecialLinearGroup.toGL
  have hinj : Function.Injective toGL := SpecialLinearGroup.toGL_injective
  let BS : Subgroup (SpecialLinearGroup (Fin n) K) := B.comap toGL
  have hBS : BS.map toGL = B := Subgroup.map_comap_eq_self hle
  have hperfBS : ⁅BS, BS⁆ = BS := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hBS]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect hq.1
  let Q : Subgroup (projectiveSL n K) := BS.map (proj n K)
  have hQperf : ⁅Q, Q⁆ = Q := by rw [← Subgroup.map_commutator, hperfBS]
  have hQfix : Q ≤ autFix (conjAut n K y) := by
    rintro _ ⟨g, hg, rfl⟩
    show conjAut n K y (proj n K g) = proj n K g
    rw [conjAut_proj]
    congr 1
    apply hinj
    have hc : toGL g * y = y * toGL g :=
      Subgroup.mem_centralizer_singleton_iff.1 (hcen hg)
    have e : toGL (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K y g) = y * toGL g * y⁻¹ :=
      Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact coe_slConjugation y g)
    rw [e, ← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hQne : Q ≠ ⊥ := by
    intro hQ
    have hker : BS ≤ (proj n K).ker := by
      intro g hg
      have : proj n K g ∈ Q := ⟨g, hg, rfl⟩
      rw [hQ] at this
      exact this
    have hcenS : BS ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [ker_proj, scalars_eq_center] at hker
      exact hker
    have hBSbot : BS = ⊥ := by
      rw [← hperfBS]
      refine le_bot_iff.1 (Subgroup.commutator_le.2 fun g hg h hh => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 (hcenS hg) h).symm
    have hBbot : B = ⊥ := by rw [← hBS, hBSbot, Subgroup.map_bot]
    have : Nontrivial (↥B ⧸ Subgroup.center ↥B) := hq.2.1.toNontrivial
    have : Nontrivial ↥B := (QuotientGroup.mk'_surjective (Subgroup.center ↥B)).nontrivial
    exact ((Subgroup.nontrivial_iff_ne_bot B).1 this) hBbot
  exact not_isSolvable_subgroup_of_perfect _ Q hQfix hQperf hQne

theorem not_isSolvable_autFix_of_mult_three (hx : Squarefree (minpoly K (linEnd y)))
    (a : primaryFactors (linEnd y)) (ha : 3 ≤ mult (linEnd y) a) :
    ¬ Group.IsSolvable (autFix (conjAut n K y)) :=
  not_isSolvable_autFix_of_block hx a (by omega) (Or.inl ha)

theorem not_isSolvable_autFix_of_mult_two (hx : Squarefree (minpoly K (linEnd y)))
    (hK : 4 ≤ Nat.card K) (a : primaryFactors (linEnd y)) (ha : 2 ≤ mult (linEnd y) a) :
    ¬ Group.IsSolvable (autFix (conjAut n K y)) :=
  not_isSolvable_autFix_of_block hx a ha (Or.inr (hK.trans (card_K_le_card_efac a)))

omit [Finite K] in
theorem centralizer_commute_of_mult_le_one (hx : Squarefree (minpoly K (linEnd y)))
    (h1 : ∀ a : primaryFactors (linEnd y), mult (linEnd y) a ≤ 1) :
    ∀ g ∈ Subgroup.centralizer ({y} : Set (GL (Fin n) K)),
      ∀ h ∈ Subgroup.centralizer ({y} : Set (GL (Fin n) K)), g * h = h * g := by
  intro g hg h hh
  rw [← range_commutantUnitsToGL_eq_centralizer y rfl, ← range_blockTheta hx] at hg hh
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨v, rfl⟩ := hh
  rw [← map_mul, ← map_mul]
  congr 1
  funext b
  exact commute_of_le_one (h1 b) _ _

theorem autFix_not_isSolvable_or_centralizer_commute (hx : Squarefree (minpoly K (linEnd y)))
    (hK : 4 ≤ Nat.card K) :
    ¬ Group.IsSolvable (autFix (conjAut n K y)) ∨
      ∀ g ∈ Subgroup.centralizer ({y} : Set (GL (Fin n) K)),
        ∀ h ∈ Subgroup.centralizer ({y} : Set (GL (Fin n) K)), g * h = h * g := by
  by_cases h1 : ∀ a : primaryFactors (linEnd y), mult (linEnd y) a ≤ 1
  · exact Or.inr (centralizer_commute_of_mult_le_one hx h1)
  · push Not at h1
    obtain ⟨a, ha⟩ := h1
    exact Or.inl (not_isSolvable_autFix_of_mult_two hx hK a (by omega))

section Irreducible

variable {y : GL (Fin n) K}

omit [Finite K] in
theorem eq_minpoly_of_mem_primaryFactors (hirr : Irreducible (minpoly K (linEnd y)))
    {a : K[X]} (ha : a ∈ primaryFactors (linEnd y)) : a = minpoly K (linEnd y) := by
  obtain ⟨hai, ham, had⟩ := mem_primaryFactors.1 ha
  exact eq_of_monic_of_associated ham (minpoly.monic (Algebra.IsIntegral.isIntegral _))
    (hai.associated_of_dvd hirr had)

omit [Finite K] in
theorem minpoly_mem_primaryFactors (hirr : Irreducible (minpoly K (linEnd y))) :
    minpoly K (linEnd y) ∈ primaryFactors (linEnd y) :=
  mem_primaryFactors.2 ⟨hirr, minpoly.monic (Algebra.IsIntegral.isIntegral _), dvd_rfl⟩

omit [Finite K] in
theorem finrank_eq_natDegree_mul_mult (hirr : Irreducible (minpoly K (linEnd y)))
    (a : primaryFactors (linEnd y)) :
    n = (minpoly K (linEnd y)).natDegree * mult (linEnd y) a := by
  have hx : Squarefree (minpoly K (linEnd y)) := hirr.squarefree
  have h := finrank_eq_sum_degree_mul_multiplicity hx
  rw [Module.finrank_fin_fun] at h
  refine h.trans ?_
  rw [Finset.sum_eq_single a]
  · rw [congrArg Polynomial.natDegree (eq_minpoly_of_mem_primaryFactors hirr a.2)]
  · intro b _ hb
    exact absurd (Subtype.ext ((eq_minpoly_of_mem_primaryFactors hirr b.2).trans
      (eq_minpoly_of_mem_primaryFactors hirr a.2).symm)) hb
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isCyclic_centralizer_of_irreducible_minpoly (hirr : Irreducible (minpoly K (linEnd y)))
    (hn : n = (minpoly K (linEnd y)).natDegree) :
    IsCyclic (Subgroup.centralizer ({y} : Set (GL (Fin n) K))) := by
  have hx : Squarefree (minpoly K (linEnd y)) := hirr.squarefree
  obtain ⟨a0⟩ : Nonempty (primaryFactors (linEnd y)) := ⟨⟨_, minpoly_mem_primaryFactors hirr⟩⟩
  have hm : mult (linEnd y) a0 = 1 := by
    have h := finrank_eq_natDegree_mul_mult hirr a0
    have hpos : 0 < (minpoly K (linEnd y)).natDegree := by
      by_contra h0
      have : (minpoly K (linEnd y)).natDegree = 0 := by omega
      rw [this] at hn
      subst hn
      have := hirr.natDegree_pos
      omega
    nlinarith
  have : Unique (primaryFactors (linEnd y)) :=
    ⟨⟨a0⟩, fun b => Subtype.ext ((eq_minpoly_of_mem_primaryFactors hirr b.2).trans
      (eq_minpoly_of_mem_primaryFactors hirr a0.2).symm)⟩
  have := finite_efac a0
  let f : (Efac (linEnd y) a0)ˣ →* PiGL (Efac (linEnd y)) (mult (linEnd y)) :=
    (MonoidHom.mulSingle (fun b : primaryFactors (linEnd y) =>
      GL (Fin (mult (linEnd y) b)) (Efac (linEnd y) b)) a0).comp
      (GeneralLinearGroup.scalar (Fin (mult (linEnd y) a0)))
  have hf : Function.Surjective f := by
    intro w
    have hmem : w a0 ∈ Subgroup.center (GL (Fin (mult (linEnd y) a0)) (Efac (linEnd y) a0)) :=
      Subgroup.mem_center_iff.mpr fun g => commute_of_le_one (by omega) g _
    rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    funext b
    have hb : b = a0 := Subsingleton.elim _ _
    subst hb
    simp [f, hc]
  have hcyc : IsCyclic (PiGL (Efac (linEnd y)) (mult (linEnd y))) := isCyclic_of_surjective f hf
  have hr : IsCyclic (blockTheta hx).range :=
    isCyclic_of_surjective (blockTheta hx).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  rw [← range_commutantUnitsToGL_eq_centralizer y rfl, ← range_blockTheta hx]
  exact hr

end Irreducible

theorem not_isSolvable_autFix_of_scalar_pow_irreducible {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {y : GL (Fin n) K} (c : Kˣ)
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) (hnp : ∀ b : K, b ^ p ≠ c)
    (hn : 2 * p ≤ n) : ¬ Group.IsSolvable (autFix (conjAut n K y)) := by
  have hx := squarefree_minpoly_linEnd_of_pow_scalar hpK c hyp
  obtain ⟨hmin, hirr⟩ := minpoly_linEnd_of_pow_scalar_irreducible hp c hyp hnp (by have := hp.two_le; omega)
  obtain ⟨a⟩ : Nonempty (primaryFactors (linEnd y)) :=
    ⟨⟨_, minpoly_mem_primaryFactors hirr⟩⟩
  have hdeg : (minpoly K (linEnd y)).natDegree = p := by
    rw [hmin, natDegree_X_pow_sub_C]
  have hnm := finrank_eq_natDegree_mul_mult hirr a
  rw [hdeg] at hnm
  have hm : 2 ≤ mult (linEnd y) a := by
    by_contra h
    push Not at h
    have : p * mult (linEnd y) a < p * 2 := Nat.mul_lt_mul_of_pos_left h hp.pos
    omega
  have ha : (a : K[X]) = minpoly K (linEnd y) := eq_minpoly_of_mem_primaryFactors hirr a.2
  have hcard : 4 ≤ Nat.card (Efac (linEnd y) a) := by
    have := finite_efac a
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Efac (linEnd y) a)]
    have hfr : Module.finrank K (Efac (linEnd y) a) = p := by
      rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, ha, hdeg]
    rw [hfr]
    have h2K : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card (α := K))
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left h2K 2
      _ ≤ Nat.card K ^ p := Nat.pow_le_pow_right (by omega) hp.two_le
  exact not_isSolvable_autFix_of_block hx a hm (Or.inr hcard)

theorem isCyclic_centralizer_of_scalar_pow_irreducible {p : ℕ} (hp : p.Prime) {y : GL (Fin n) K}
    (c : Kˣ) (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) (hnp : ∀ b : K, b ^ p ≠ c)
    (hn : n = p) : IsCyclic (Subgroup.centralizer ({y} : Set (GL (Fin n) K))) := by
  obtain ⟨hmin, hirr⟩ := minpoly_linEnd_of_pow_scalar_irreducible hp c hyp hnp
    (by have := hp.two_le; omega)
  refine isCyclic_centralizer_of_irreducible_minpoly (K := K) hirr ?_
  rw [hmin, natDegree_X_pow_sub_C, hn]


end Block

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
