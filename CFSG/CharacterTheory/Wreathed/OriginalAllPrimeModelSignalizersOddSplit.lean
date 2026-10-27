module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped Pointwise

section Orbits

variable {G X : Type*} [Group G] [MulAction G X]

theorem smul_mem_orbit_of_permutable_split {U C : Subgroup G}
    (hperm : (U : Set G) * (C : Set G) = (C : Set G) * (U : Set G)) {x : X}
    (hx : ∀ c ∈ C, c • x = x) {c : G} (hc : c ∈ C) {y : X} (hy : y ∈ MulAction.orbit U x) :
    c • y ∈ MulAction.orbit U x := by
  obtain ⟨u, rfl⟩ := hy
  have hcu : c * (u : G) ∈ (U : Set G) * (C : Set G) := by
    rw [hperm]
    exact Set.mul_mem_mul hc u.2
  obtain ⟨u', hu', c', hc', he⟩ := hcu
  refine ⟨⟨u', hu'⟩, ?_⟩
  change (u' : G) • x = c • ((u : G) • x)
  rw [← mul_smul, ← he, mul_smul, hx c' hc']

end Orbits

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem odd_card_of_two_ne_zero_split [Fintype F] (h2 : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have h' := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at h'
    exact_mod_cast h'
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hchar)

theorem ne_zero_of_mul_self_eq_neg_one_split {j : F} (hj : j * j = -1) : j ≠ 0 := by
  rintro rfl
  rw [mul_zero] at hj
  exact one_ne_zero (neg_eq_zero.mp hj.symm)

theorem smul_sqrt_eq_of_mem_modelC_split [Finite F] (h2 : (2 : F) ≠ 0)
    (hd : Odd (Nat.card Sigma)) {j : F} (hj : j * j = -1)
    {c : SemilinearExtension F b m hm heven Sigma hSigma}
    (hc : c ∈ modelC b m hm heven Sigma hSigma) : c • (some j : Omega F) = some j := by
  obtain ⟨G, hG⟩ := exists_projectiveMap_eq c.left
  rw [semilinear_smul_eq hG, fieldExtension_some, sigma_apply_sqrt hd h2 c.right hj]
  exact coordinateGLAction_fix_of_commute hj ((mem_modelC_iff_commute hG).mp hc)

theorem mem_modelC_of_smul_sqrt_split [Finite F] (h2 : (2 : F) ≠ 0)
    (hd : Odd (Nat.card Sigma)) {j : F} (hj : j * j = -1)
    {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hp : h • (some j : Omega F) = some j) (hn : h • (some (-j) : Omega F) = some (-j)) :
    h ∈ modelC b m hm heven Sigma hSigma := by
  obtain ⟨G, hG⟩ := exists_projectiveMap_eq h.left
  rw [semilinear_smul_eq hG, fieldExtension_some, sigma_apply_sqrt hd h2 h.right hj] at hp
  rw [semilinear_smul_eq hG, fieldExtension_some,
    sigma_apply_sqrt hd h2 h.right (neg_mul_neg_eq_neg_one hj)] at hn
  exact (mem_modelC_iff_commute hG).mpr (commute_weyl_of_coordinateGLAction_fix h2 hj hp hn)

theorem exists_mem_modelC_smul_none_split [Finite F] (hb : ¬ IsSquare b) {j : F}
    (hj : j * j = -1) {y : Omega F} (hy : y ≠ some j) (hy' : y ≠ some (-j)) :
    ∃ c ∈ modelC b m hm heven Sigma hSigma, c • (none : Omega F) = y := by
  cases y with
  | none => exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
  | some z =>
    have hz : z * z + 1 ≠ 0 := by
      intro h
      have hf : (z - j) * (z + j) = 0 := by linear_combination h - hj
      rcases mul_eq_zero.mp hf with h' | h'
      · exact hy (by rw [sub_eq_zero.mp h'])
      · exact hy' (by rw [eq_neg_of_add_eq_zero_left h'])
    obtain ⟨v, hv, hG⟩ := exists_mem_centralizer_projectiveMap_eq (m := m) (hm := hm)
      (heven := heven) hb (weylShift_commute z hz)
    refine ⟨SemidirectProduct.inl v, (inl_mem_modelC_iff v).mpr hv, ?_⟩
    rw [semilinear_smul_eq (h := SemidirectProduct.inl v) hG, fieldExtension_none]
    exact coordinateGLAction_weylShift_none z hz

theorem smul_sqrt_ne_neg_split [Fintype F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) {j : F} (hj : j * j = -1)
    {U : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hU : Odd (Nat.card U))
    (hperm : (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) =
      (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)))
    {u : SemilinearExtension F b m hm heven Sigma hSigma} (hu : u ∈ U) :
    u • (some j : Omega F) ≠ some (-j) := by
  intro hneg
  set A := MulAction.orbit U (some j : Omega F) with hA
  have hinv : ∀ c ∈ modelC b m hm heven Sigma hSigma, ∀ y ∈ A, c • y ∈ A := fun c hc y hy =>
    smul_mem_orbit_of_permutable_split hperm
      (fun c' hc' => smul_sqrt_eq_of_mem_modelC_split h2 hd hj hc') hc hy
  have hjA : (some j : Omega F) ∈ A := MulAction.mem_orbit_self _
  have hnA : (some (-j) : Omega F) ∈ A := ⟨⟨u, hu⟩, hneg⟩
  have hodd : Odd A.ncard := by
    apply Odd.of_dvd_nat hU
    rw [hA, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  have hne : (some j : Omega F) ≠ some (-j) := by
    intro h
    apply mul_ne_zero h2 (ne_zero_of_mul_self_eq_neg_one_split hj)
    have h' := Option.some_injective _ h
    linear_combination h'
  by_cases hex : ∃ y ∈ A, y ≠ some j ∧ y ≠ some (-j)
  · obtain ⟨y, hyA, hy, hy'⟩ := hex
    obtain ⟨c, hc, hcy⟩ := exists_mem_modelC_smul_none_split (Sigma := Sigma) (hSigma := hSigma)
      (hm := hm) (heven := heven) hb hj hy hy'
    have hnone : (none : Omega F) ∈ A := by
      have h' := hinv c⁻¹ (Subgroup.inv_mem _ hc) y hyA
      rwa [← hcy, inv_smul_smul] at h'
    have huniv : A = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      by_cases hx : x = some j
      · rw [hx]
        exact hjA
      by_cases hx' : x = some (-j)
      · rw [hx']
        exact hnA
      obtain ⟨c', hc', hcx⟩ := exists_mem_modelC_smul_none_split (Sigma := Sigma)
        (hSigma := hSigma) (hm := hm) (heven := heven) hb hj hx hx'
      rw [← hcx]
      exact hinv c' hc' none hnone
    rw [huniv, Set.ncard_univ, Finite.card_option] at hodd
    obtain ⟨k, hk⟩ := odd_card_of_two_ne_zero_split h2
    obtain ⟨l, hl⟩ := hodd
    omega
  · push Not at hex
    have hpair : A = {some j, some (-j)} := by
      ext x
      constructor
      · intro hx
        by_cases hx' : x = some j
        · exact Or.inl hx'
        · exact Or.inr (hex x hx hx')
      · rintro (rfl | rfl)
        · exact hjA
        · exact hnA
    rw [hpair, Set.ncard_pair hne] at hodd
    obtain ⟨l, hl⟩ := hodd
    omega

theorem exists_smul_sqrt_eq_none_split [Fintype F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) {j : F} (hj : j * j = -1)
    {U : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hU : Odd (Nat.card U))
    (hperm : (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) =
      (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)))
    (hfix : ¬ ∀ u ∈ U, u • (some j : Omega F) = some j) :
    ∃ u ∈ U, u • (some j : Omega F) = none := by
  push Not at hfix
  obtain ⟨u, hu, hne⟩ := hfix
  obtain ⟨c, hc, hcx⟩ := exists_mem_modelC_smul_none_split (Sigma := Sigma) (hSigma := hSigma)
    (hm := hm) (heven := heven) hb hj hne (smul_sqrt_ne_neg_split h2 hb hd hj hU hperm hu)
  have hmem := smul_mem_orbit_of_permutable_split hperm
    (fun c' hc' => smul_sqrt_eq_of_mem_modelC_split h2 hd hj hc') (Subgroup.inv_mem _ hc)
    (⟨⟨u, hu⟩, rfl⟩ : u • (some j : Omega F) ∈ MulAction.orbit U (some j : Omega F))
  rw [← hcx, inv_smul_smul] at hmem
  obtain ⟨⟨w, hw⟩, hw'⟩ := hmem
  exact ⟨w, hw, hw'⟩

theorem le_sup_rootGroup_of_fix_split [Finite F] (h2 : (2 : F) ≠ 0)
    (hd : Odd (Nat.card Sigma)) {j : F} (hj : j * j = -1)
    {U : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hfix : ∀ u ∈ U, u • (some j : Omega F) = some j) :
    U ≤ modelC b m hm heven Sigma hSigma ⊔ rootGroup b m hm heven Sigma hSigma j hj := by
  intro u hu
  have hx : u • (some (-j) : Omega F) ≠ some j := by
    intro h
    rw [← hfix u hu] at h
    have h' := Option.some_injective _ (smul_left_cancel u h)
    apply mul_ne_zero h2 (ne_zero_of_mul_self_eq_neg_one_split hj)
    linear_combination -h'
  obtain ⟨l, hl⟩ := exists_coordinateGLAction_rootSL_eq h2 j hj hx
  set r : SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL j hj l)) with hr
  have hr1 : r • (some j : Omega F) = some j := by
    rw [hr, inl_specialInclusion_smul]
    exact coordinateGLAction_rootSL_fix j hj l
  have hr2 : r • (some (-j) : Omega F) = u • some (-j) := by
    rw [hr, inl_specialInclusion_smul]
    exact hl
  have hw : r⁻¹ * u ∈ modelC b m hm heven Sigma hSigma := by
    apply mem_modelC_of_smul_sqrt_split h2 hd hj
    · rw [mul_smul, hfix u hu, inv_smul_eq_iff, hr1]
    · rw [mul_smul, inv_smul_eq_iff, hr2]
  have hu' : u = r * (r⁻¹ * u) := by group
  rw [hu']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (inl_rootSL_mem_rootGroup hj l))
    (Subgroup.mem_sup_left hw)

theorem le_sup_rootGroup_of_permutable [Fintype F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) {i : F} (hi : i * i = -1)
    {U : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hU : Odd (Nat.card U))
    (hperm : (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) =
      (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (U : Set (SemilinearExtension F b m hm heven Sigma hSigma))) :
    U ≤ modelC b m hm heven Sigma hSigma ⊔ rootGroup b m hm heven Sigma hSigma i hi ∨
      U ≤ modelC b m hm heven Sigma hSigma ⊔
        rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi) := by
  by_cases hfix : ∀ u ∈ U, u • (some i : Omega F) = some i
  · exact Or.inl (le_sup_rootGroup_of_fix_split h2 hd hi hfix)
  · refine Or.inr (le_sup_rootGroup_of_fix_split h2 hd (neg_mul_neg_eq_neg_one hi) ?_)
    by_contra hfix'
    obtain ⟨u, hu, hu'⟩ := exists_smul_sqrt_eq_none_split h2 hb hd hi hU hperm hfix
    obtain ⟨w, hw, hw'⟩ :=
      exists_smul_sqrt_eq_none_split h2 hb hd (neg_mul_neg_eq_neg_one hi) hU hperm hfix'
    apply smul_sqrt_ne_neg_split h2 hb hd hi hU hperm (U.mul_mem (U.inv_mem hw) hu)
    rw [mul_smul, hu', ← hw', inv_smul_smul]

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
