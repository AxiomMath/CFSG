module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8QTorus2

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KD4T
open scoped Pointwise

variable {L : Type} [Field L]

variable
  [E6Sub Tag.E8]

section RhoTorus

open CFSG.RankThree.PartOne.KE6

variable
  [E6Sub Tag.E8]

private def e8RhoRoot1 : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 0, -1, 0, 0]

private def e8RhoRoot2 : Fin Tag.E8.rank → ℤ := ![-1, 0, -1, -1, -1, -1, 0, 0]

private def e8RhoRoot3 : Fin Tag.E8.rank → ℤ := ![0, 1, 1, 2, 1, 0, 0, 0]


private lemma rhoτ_apply_one_three_two_four :
    rhoτ Tag.E8 (1 : Fin Tag.E8.rank) = 1 ∧ rhoτ Tag.E8 (2 : Fin Tag.E8.rank) = 4 ∧
      rhoτ Tag.E8 (3 : Fin Tag.E8.rank) = 3 ∧ rhoτ Tag.E8 (4 : Fin Tag.E8.rank) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (1 : Fin Tag.E8.rank) = e6Idx (1 : Fin Tag.E6.rank) from rfl, rhoτ_e6Idx,
      show rho6 (1 : Fin Tag.E6.rank) = 1 from by decide]
  · rw [show (2 : Fin Tag.E8.rank) = e6Idx (2 : Fin Tag.E6.rank) from rfl, rhoτ_e6Idx,
      show rho6 (2 : Fin Tag.E6.rank) = 4 from by decide]
    rfl
  · rw [show (3 : Fin Tag.E8.rank) = e6Idx (3 : Fin Tag.E6.rank) from rfl, rhoτ_e6Idx,
      show rho6 (3 : Fin Tag.E6.rank) = 3 from by decide]
  · rw [show (4 : Fin Tag.E8.rank) = e6Idx (4 : Fin Tag.E6.rank) from rfl, rhoτ_e6Idx,
      show rho6 (4 : Fin Tag.E6.rank) = 2 from by decide]
    rfl

private lemma torusElt_mem_stdLayer_rho {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {n₁ : ModGL Tag.E8 L} {ω : Lˣ}
    (hstd : StdTwist6 n₁ (rhoτ Tag.E8))
    (hωfix : Units.map (iterateFrobenius L ℓ f).toMonoidHom ω = ω)
    {i : Fin Tag.E8.rank} (hi : i ∈ e6Set Tag.E8) (hρ : rhoτ Tag.E8 i = i) :
    torusElt Tag.E8 L i ω ∈ stdLayer Tag.E8 ℓ f n₁ := by
  have hQ : torusElt Tag.E8 L i ω ∈ subsystemGroup Tag.E8 L (e6Set Tag.E8) :=
    subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi ω)
  refine mem_stdLayer.2 ⟨hQ, ?_⟩
  rw [units_map_entrywiseHom_torusElt, hωfix, conj_torusElt_of_hgen hstd.hgen hi ω, hρ]

private lemma torusElt_two_mul_four_mem_stdLayer_rho {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {n₁ : ModGL Tag.E8 L} {ω : Lˣ}
    (hstd : StdTwist6 n₁ (rhoτ Tag.E8))
    (hωfix : Units.map (iterateFrobenius L ℓ f).toMonoidHom ω = ω)
    (hρ2 : rhoτ Tag.E8 (2 : Fin Tag.E8.rank) = 4)
    (hρ4 : rhoτ Tag.E8 (4 : Fin Tag.E8.rank) = 2) :
    torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω ∈ stdLayer Tag.E8 ℓ f n₁ := by
  have h2 : (2 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (2 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have h4 : (4 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (4 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have hQ : torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω ∈
      subsystemGroup Tag.E8 L (e6Set Tag.E8) :=
    mul_mem (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus h2 ω))
      (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus h4 ω))
  refine mem_stdLayer.2 ⟨hQ, ?_⟩
  rw [map_mul, units_map_entrywiseHom_torusElt, units_map_entrywiseHom_torusElt, hωfix]
  rw [show n₁ * (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) * n₁⁻¹ =
      (n₁ * torusElt Tag.E8 L 2 ω * n₁⁻¹) * (n₁ * torusElt Tag.E8 L 4 ω * n₁⁻¹)
        from by group]
  rw [conj_torusElt_of_hgen hstd.hgen h2 ω, conj_torusElt_of_hgen hstd.hgen h4 ω, hρ2, hρ4]
  exact (torusElt_mul_comm 2 4 ω ω).symm

private lemma orderOf_torusElt_mul_two_four {ω : Lˣ} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hωq : ω ^ q = 1) (hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k) :
    orderOf (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hdiag2 : torusElt Tag.E8 L 2 ω ∈ diagonalGroup :=
    torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 2 ω)
  have hdiag4 : torusElt Tag.E8 L 4 ω ∈ diagonalGroup :=
    torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 4 ω)
  have hpow : (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) ^ q = 1 := by
    rw [(show Commute (torusElt Tag.E8 L 2 ω) (torusElt Tag.E8 L 4 ω) from
      torusElt_mul_comm 2 4 ω ω).mul_pow, ← torusElt_pow, ← torusElt_pow, hωq,
      torusElt_one, torusElt_one, one_mul]
  have hne : torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω ≠ 1 := by
    intro h1
    have h2 := congrArg (fun g => torusRootChar g (Pi.single 2 1)) h1
    rw [torusRootChar_one, torusRootChar_mul hdiag2 hdiag4,
      torusRootChar_torusElt_self, torusRootChar_torusElt_eq_one ω (by decide)] at h2
    simp only [mul_one] at h2
    have h3 : ω ^ 2 = 1 := by
      ext
      rwa [Units.val_pow_eq_pow_val, Units.val_one]
    have h4 : q ∣ 2 := hωdvd 2 h3
    rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h | h
    · exact hq.ne_one h
    · exact hq2 h
  exact orderOf_eq_prime hpow hne

private lemma rho_char_at_root_one {ω : Lˣ} :
    torusRootChar (torusElt Tag.E8 L 1 ω) e8RhoRoot1 = 1 ∧
      torusRootChar (torusElt Tag.E8 L 3 ω) e8RhoRoot1 = 1 ∧
      torusRootChar (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) e8RhoRoot1 =
        (ω : L) := by
  have hr : IsRoot Tag.E8 e8RhoRoot1 := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have s11 : (∑ j, Tag.cartan Tag.E8 (1 : Fin Tag.E8.rank) j * e8RhoRoot1 j) = 0 := by decide
  have s31 : (∑ j, Tag.cartan Tag.E8 (3 : Fin Tag.E8.rank) j * e8RhoRoot1 j) = 0 := by decide
  have s21 : (∑ j, Tag.cartan Tag.E8 (2 : Fin Tag.E8.rank) j * e8RhoRoot1 j) = 0 := by decide
  have s41 : (∑ j, Tag.cartan Tag.E8 (4 : Fin Tag.E8.rank) j * e8RhoRoot1 j) = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [torusRootChar_torusElt _ _ hr, s11]; simp
  · rw [torusRootChar_torusElt _ _ hr, s31]; simp
  · rw [torusRootChar_mul (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 2 ω))
      (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 4 ω)),
      torusRootChar_torusElt _ _ hr, torusRootChar_torusElt _ _ hr, s21, s41]; simp

private lemma rho_char_at_root_two {ω : Lˣ} :
    torusRootChar (torusElt Tag.E8 L 1 ω) e8RhoRoot2 = (ω : L) ∧
      torusRootChar (torusElt Tag.E8 L 3 ω) e8RhoRoot2 = 1 ∧
      torusRootChar (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) e8RhoRoot2 = 1 := by
  have hr : IsRoot Tag.E8 e8RhoRoot2 := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have s12 : (∑ j, Tag.cartan Tag.E8 (1 : Fin Tag.E8.rank) j * e8RhoRoot2 j) = 1 := by decide
  have s32 : (∑ j, Tag.cartan Tag.E8 (3 : Fin Tag.E8.rank) j * e8RhoRoot2 j) = 0 := by decide
  have s22 : (∑ j, Tag.cartan Tag.E8 (2 : Fin Tag.E8.rank) j * e8RhoRoot2 j) = 0 := by decide
  have s42 : (∑ j, Tag.cartan Tag.E8 (4 : Fin Tag.E8.rank) j * e8RhoRoot2 j) = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [torusRootChar_torusElt _ _ hr, s12]; simp
  · rw [torusRootChar_torusElt _ _ hr, s32]; simp
  · rw [torusRootChar_mul (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 2 ω))
      (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 4 ω)),
      torusRootChar_torusElt _ _ hr, torusRootChar_torusElt _ _ hr, s22, s42]; simp

private lemma rho_char_at_root_three {ω : Lˣ} :
    torusRootChar (torusElt Tag.E8 L 1 ω) e8RhoRoot3 = 1 ∧
      torusRootChar (torusElt Tag.E8 L 3 ω) e8RhoRoot3 = (ω : L) ∧
      torusRootChar (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) e8RhoRoot3 = 1 := by
  have hr : IsRoot Tag.E8 e8RhoRoot3 := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have s13 : (∑ j, Tag.cartan Tag.E8 (1 : Fin Tag.E8.rank) j * e8RhoRoot3 j) = 0 := by decide
  have s33 : (∑ j, Tag.cartan Tag.E8 (3 : Fin Tag.E8.rank) j * e8RhoRoot3 j) = 1 := by decide
  have s23 : (∑ j, Tag.cartan Tag.E8 (2 : Fin Tag.E8.rank) j * e8RhoRoot3 j) = 0 := by decide
  have s43 : (∑ j, Tag.cartan Tag.E8 (4 : Fin Tag.E8.rank) j * e8RhoRoot3 j) = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [torusRootChar_torusElt _ _ hr, s13]; simp
  · rw [torusRootChar_torusElt _ _ hr, s33]; simp
  · rw [torusRootChar_mul (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 2 ω))
      (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 4 ω)),
      torusRootChar_torusElt _ _ hr, torusRootChar_torusElt _ _ hr, s23, s43]; simp

private lemma independent_powers_rho {ω : Lˣ} {q : ℕ}
    (hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k) :
    ∀ m n k : ℕ, torusElt Tag.E8 L 1 ω ^ m * torusElt Tag.E8 L 3 ω ^ n *
        (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) ^ k = 1 →
      q ∣ m ∧ q ∣ n ∧ q ∣ k := by
  intro m n k h1
  obtain ⟨hda1, hdb1, hdc1⟩ := rho_char_at_root_one (ω := ω)
  obtain ⟨hda2, hdb2, hdc2⟩ := rho_char_at_root_two (ω := ω)
  obtain ⟨hda3, hdb3, hdc3⟩ := rho_char_at_root_three (ω := ω)
  have hdiag1 : torusElt Tag.E8 L 1 ω ∈ diagonalGroup :=
    torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 1 ω)
  have hdiag3 : torusElt Tag.E8 L 3 ω ∈ diagonalGroup :=
    torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 3 ω)
  have hdc_diag : torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω ∈ diagonalGroup :=
    mul_mem (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 2 ω))
      (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup 4 ω))
  have hchar : ∀ r : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 r →
      torusRootChar (torusElt Tag.E8 L 1 ω ^ m * torusElt Tag.E8 L 3 ω ^ n *
        (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) ^ k) r = 1 := by
    intro r hr
    rw [h1, torusRootChar_one]
  have hr1 : IsRoot Tag.E8 e8RhoRoot1 := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have hr2 : IsRoot Tag.E8 e8RhoRoot2 := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have hr3 : IsRoot Tag.E8 e8RhoRoot3 := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have hk : q ∣ k := by
    have h := hchar e8RhoRoot1 hr1
    rw [torusRootChar_mul_pow_three hdiag1 hdiag3 hdc_diag m n k, hda1, hdb1, hdc1] at h
    have h'u : ω ^ k = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa using h
    exact hωdvd k h'u
  have hm : q ∣ m := by
    have h := hchar e8RhoRoot2 hr2
    rw [torusRootChar_mul_pow_three hdiag1 hdiag3 hdc_diag m n k, hda2, hdb2, hdc2] at h
    have h'u : ω ^ m = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa using h
    exact hωdvd m h'u
  have hn : q ∣ n := by
    have h := hchar e8RhoRoot3 hr3
    rw [torusRootChar_mul_pow_three hdiag1 hdiag3 hdc_diag m n k, hda3, hdb3, hdc3] at h
    have h'u : ω ^ n = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa using h
    exact hωdvd n h'u
  exact ⟨hm, hn, hk⟩

theorem exists_three_qTorus_stdLayer_rho {K : Type} [Field K] [Algebra K L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ q)
    (hFr : ∀ x : K, (algebraMap K L x) ^ (ℓ ^ f) = algebraMap K L x)
    {n₁ : ModGL Tag.E8 L} (hstd : StdTwist6 n₁ (rhoτ Tag.E8)) :
    ∃ T : Subgroup (ModGL Tag.E8 L), T ≤ stdLayer Tag.E8 ℓ f n₁ ∧
      IsElemAbelian q T ∧ Nat.card T = q ^ 3 := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  set ζu : Kˣ := Units.mk0 ζ (hζ.ne_zero hq.ne_zero) with hζudef
  have hζu : IsPrimitiveRoot ζu q := (IsPrimitiveRoot.coe_units_iff).mp hζ
  set ω : Lˣ := Units.map (algebraMap K L).toMonoidHom ζu with hωdef
  have hωval : (ω : L) = algebraMap K L (ζu : K) := by rw [hωdef, Units.coe_map]; rfl
  have hωL : IsPrimitiveRoot (ω : L) q := by
    have h : (ω : L) = algebraMap K L ζ := by rw [hωval]; rfl
    rw [h]
    exact IsPrimitiveRoot.map_of_injective hζ (algebraMap K L).injective
  have hωfix : Units.map (iterateFrobenius L ℓ f).toMonoidHom ω = ω := by
    apply Units.ext
    rw [Units.coe_map, hωval]
    change (iterateFrobenius L ℓ f) (algebraMap K L (ζu : K)) = algebraMap K L (ζu : K)
    rw [iterateFrobenius_def]
    exact hFr (ζu : K)
  have hωq : ω ^ q = 1 := by
    rw [hωdef, ← map_pow, hζu.pow_eq_one, map_one]
  have hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k := by
    intro k hk
    have h : (ω : L) ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one]
    exact (hωL.pow_eq_one_iff_dvd k).1 h
  obtain ⟨hρ1, hρ2, hρ3, hρ4⟩ := rhoτ_apply_one_three_two_four
  have hmem1 : (1 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (1 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have hmem3 : (3 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (3 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have hmem : torusElt Tag.E8 L 1 ω ∈ stdLayer Tag.E8 ℓ f n₁ :=
    torusElt_mem_stdLayer_rho hstd hωfix hmem1 hρ1
  have hmem3' : torusElt Tag.E8 L 3 ω ∈ stdLayer Tag.E8 ℓ f n₁ :=
    torusElt_mem_stdLayer_rho hstd hωfix hmem3 hρ3
  have hdc_mem : torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω ∈
      stdLayer Tag.E8 ℓ f n₁ :=
    torusElt_two_mul_four_mem_stdLayer_rho hstd hωfix hρ2 hρ4
  have hord1 : orderOf (torusElt Tag.E8 L 1 ω) = q :=
    orderOf_torusElt_of_pow hωq hωdvd hq hq2
  have hord3 : orderOf (torusElt Tag.E8 L 3 ω) = q :=
    orderOf_torusElt_of_pow hωq hωdvd hq hq2
  have hord_dc : orderOf (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) = q :=
    orderOf_torusElt_mul_two_four hq hq2 hωq hωdvd
  have hcomm : Commute (torusElt Tag.E8 L 1 ω) (torusElt Tag.E8 L 3 ω) ∧
      Commute (torusElt Tag.E8 L 1 ω) (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) ∧
      Commute (torusElt Tag.E8 L 3 ω) (torusElt Tag.E8 L 2 ω * torusElt Tag.E8 L 4 ω) := by
    refine ⟨torusElt_mul_comm 1 3 ω ω, ?_, ?_⟩
    · exact (show Commute (torusElt Tag.E8 L 1 ω) (torusElt Tag.E8 L 2 ω) from
        torusElt_mul_comm 1 2 ω ω).mul_right
        (show Commute (torusElt Tag.E8 L 1 ω) (torusElt Tag.E8 L 4 ω) from
          torusElt_mul_comm 1 4 ω ω)
    · exact (show Commute (torusElt Tag.E8 L 3 ω) (torusElt Tag.E8 L 2 ω) from
        torusElt_mul_comm 3 2 ω ω).mul_right
        (show Commute (torusElt Tag.E8 L 3 ω) (torusElt Tag.E8 L 4 ω) from
          torusElt_mul_comm 3 4 ω ω)
  have hind := independent_powers_rho (L := L) hωdvd
  obtain ⟨T, hTle, hTel, hTcard⟩ :=
    exists_elemAbelian_three_of_commute hord1 hord3 hord_dc hcomm.1 hcomm.2.1 hcomm.2.2
      hind hmem hmem3' hdc_mem
  exact ⟨T, hTle, hTel, hTcard⟩

end RhoTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
