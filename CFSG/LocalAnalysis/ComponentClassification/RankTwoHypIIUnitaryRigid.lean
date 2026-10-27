module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIISymplecticFour
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public section

namespace CFSG.ComponentClassification.RankTwoHypIIY

open Subgroup

variable {W W' : Type*} [Group W] [Group W']

theorem TwoNilpotentCentral.map_mulEquiv {L : Subgroup W} (h : TwoNilpotentCentral L)
    (Φ : W ≃* W') : TwoNilpotentCentral (L.map Φ.toMonoidHom) := by
  intro P hPL hLP hPn
  have h0 := h (P.map Φ.symm.toMonoidHom) ?_ ?_ (hPn.map _)
  · intro y hy
    rw [mem_centralizer_iff]
    intro p hp
    have hyL : Φ.symm y ∈ L := by
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    have := mem_centralizer_iff.mp (h0 hyL) (Φ.symm p) ⟨p, hp, rfl⟩
    apply Φ.symm.injective
    simpa only [map_mul] using this
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨x, hx, hxp⟩ := hPL hp
    simp only [MulEquiv.coe_toMonoidHom] at hxp ⊢
    rw [← hxp, MulEquiv.symm_apply_apply]
    exact hx
  · intro l hl
    have hΦl : Φ l ∈ normalizer (P : Set W') := hLP ⟨l, hl, rfl⟩
    have := le_normalizer_map Φ.symm.toMonoidHom ⟨Φ l, hΦl, rfl⟩
    simpa using this

theorem RigidInvolution.map_mulEquiv' {X : Subgroup W} {X' : Subgroup W'} {t : W}
    (h : RigidInvolution X t) (Φ : W ≃* W') (hΦX : X.map Φ.toMonoidHom = X') :
    RigidInvolution X' (Φ t) := by
  obtain ⟨L, hLX, hLt, hNL, hLp, hL, hinv⟩ := h
  have hC : ∀ s, s ∈ centralizer ({Φ t} : Set W') ↔ Φ.symm s ∈ centralizer ({t} : Set W) := by
    intro s
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hs
      apply Φ.injective
      simp [map_mul, hs]
    · intro hs
      have := congrArg Φ hs
      simpa [map_mul] using this
  refine ⟨L.map Φ.toMonoidHom, ?_, ?_, ?_, ?_, hL.map_mulEquiv Φ, ?_⟩
  · rw [← hΦX]
    exact map_mono hLX
  · rintro _ ⟨l, hl, rfl⟩
    rw [hC]
    simpa using hLt hl
  · intro s hs
    have h1 := hNL ((hC s).mp hs)
    have := le_normalizer_map Φ.toMonoidHom ⟨Φ.symm s, h1, rfl⟩
    simpa using this
  · rw [← Subgroup.map_commutator, hLp]
  · intro s hs hsL hs2
    have hsL' : Φ.symm s ∈ centralizer (L : Set W) := by
      rw [mem_centralizer_iff]
      intro l hl
      have := mem_centralizer_iff.mp hsL (Φ l) ⟨l, hl, rfl⟩
      apply Φ.injective
      simpa [map_mul] using this
    rcases hinv (Φ.symm s) ((hC s).mp hs) hsL' (by rw [← map_pow, hs2, map_one]) with h1 | h1
    · left
      simpa using congrArg Φ h1
    · right
      simpa using congrArg Φ h1

end CFSG.ComponentClassification.RankTwoHypIIY

namespace CFSG.ComponentClassification.RankTwoHypIIUnitary

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
  UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  CFSG.ComponentClassification.RankTwoHypIIY CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

section Isometry

variable {k : Type} [Field k] [Finite k] {n : ℕ}

omit [Finite k] in
theorem nonempty_matrixIsometryGroup_mulEquiv_statedSp [CharP k 2] {C : GL (Fin n) k} {r : ℕ}
    (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) k) = blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) k) = 1 ∧ n = 2 * r + 1)) :
    Nonempty (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) k) ≃* StatedSp r k) := by
  rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(MulEquiv.subgroupCongr (congrArg matrixIsometryGroup h2)).trans
      (blockSwapIsometryEquivStatedSp (by omega))⟩
  · have hC1 : (C : Matrix (Fin n) (Fin n) k) =
        ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by rw [h1, Units.val_one]
    obtain ⟨e₂⟩ := nonempty_altIsometry_mulEquiv_statedSp _
      (dotForm_restrict_isAlt (k := k) (n := n)) (dotForm_restrict_nondegenerate h2)
      (finrank_dotForm_ker h2)
    exact ⟨((MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC1)).trans
      (oneRestrictEquiv h2)).trans e₂⟩

end Isometry

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem centralizer_inf_le_zpowers (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (hodd : (C : Matrix (Fin n) (Fin n) K) = 1 → Odd n)
    (Cl : GL (Fin n) h.fixedField)
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    centralizer {primeFormFieldHom h hC σ} ⊓
        centralizer ((((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range : Subgroup _) : Set (MulAut (primeFormP h
            (C : Matrix (Fin n) (Fin n) K)))) ≤
      zpowers (primeFormFieldHom h hC σ) := by
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨hcent, -, -, -, -, -, Θ, hΘ, hΘrange, hΘker, -, hΘN, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase Cl hCl σ hσ
  have hcaseL := canonical_case_of_map h hCl hcase
  have hcaseL' : (Cl : Matrix (Fin n) (Fin n) h.fixedField) = 1 ∨
      ∃ r, n = 2 * r ∧ (Cl : Matrix (Fin n) (Fin n) h.fixedField) = blockSwapJ n r := hcaseL
  obtain ⟨-, -, hβ2, -, -, -, hrest⟩ :=
    even_linear_canonical_graph_symplectic_centralizers h.one_le h.card_fixedField hn Cl hcaseL'
  have hCN := (hrest (by
    rcases hcase with h1 | ⟨r, hr, hJ⟩
    · right
      refine ⟨?_, hodd h1⟩
      rcases hcaseL with h2 | ⟨r, hr, hJ⟩
      · exact h2
      · exfalso
        obtain ⟨j, hj⟩ := hodd h1
        omega
    · left
      rcases hcaseL with h2 | ⟨r', hr', hJ'⟩
      · exfalso
        have h3 : (C : Matrix (Fin n) (Fin n) K) = 1 := by
          rw [← hCl, h2, Matrix.map_one _ (map_zero _) (map_one _)]
        have h4 := congrFun (congrFun (h3.symm.trans hJ) ⟨0, by omega⟩) ⟨0, by omega⟩
        rw [blockSwapJ_apply_self (by omega), one_apply_eq] at h4
        exact one_ne_zero h4
      · exact ⟨r', hr', hJ'⟩)).1
  intro s hs
  obtain ⟨hsM, hsN⟩ := mem_inf.mp hs
  set s' : centralizer {primeFormFieldHom h hC σ} := ⟨s, hsM⟩
  have hΘs : Θ s' ∈ centralizer {conjAut n h.fixedField Cl * dualAut n h.fixedField} ⊓
      centralizer (((matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)).map
        (conjAut n h.fixedField) : Subgroup _) : Set (MulAut (projectiveSL n h.fixedField))) := by
    refine mem_inf.mpr ⟨hΘrange ⟨s', rfl⟩, ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    rw [← hΘN] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxs : (x : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) * s =
        s * (x : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :=
      mem_centralizer_iff.mp hsN _ hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxs
  rw [hCN] at hΘs
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hΘs
  have hsemi : Θ s' ∈ semilinearAutGroup n h.fixedField := by
    obtain ⟨g, φ, hgφ⟩ := (hcent s).mp hsM
    have := hΘ g φ (hgφ ▸ hsM)
    rw [show s' = ⟨_, hgφ ▸ hsM⟩ from Subtype.ext hgφ, this]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
      (fieldAut_mem_semilinearAutGroup _)
  have hβ2' : (conjAut n h.fixedField Cl * dualAut n h.fixedField) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← sq, hβ2]
  have hΘ1 : Θ s' = 1 := by
    rw [← hj] at hsemi ⊢
    rcases Int.even_or_odd' j with ⟨i, rfl | rfl⟩
    · rw [_root_.zpow_mul, hβ2', _root_.one_zpow]
    · exfalso
      rw [_root_.zpow_add_one, _root_.zpow_mul, hβ2', _root_.one_zpow, one_mul] at hsemi
      apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := h.fixedField) hn
      have := mul_mem (inv_mem (linearAutGroup_le_semilinearAutGroup
        (conjAut_mem_linearAutGroup Cl))) hsemi
      rwa [inv_mul_cancel_left] at this
  have hker : s' ∈ Θ.ker := hΘ1
  rw [hΘker] at hker
  exact hker

theorem exists_fixed_gram {C : GL (Fin n) K}
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) :
    ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C := by
  have := fixedField_charP h
  rcases hcase with h1 | ⟨r, hr, hJ⟩
  · exact ⟨1, by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1]⟩
  · refine ⟨blockSwapGL (K := h.fixedField) (r := r) (by omega), ?_⟩
    rw [hJ]
    ext i j
    simp only [blockSwapGL, Matrix.map_apply, blockSwapJ, Matrix.of_apply]
    split_ifs <;> simp

theorem rigidInvolution_fieldBar (hn : 4 ≤ n) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    {r : ℕ} (hr : 2 ≤ r) (hsmall : ¬ (r = 2 ∧ f = 1))
    (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ n = 2 * r + 1))
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hX : primeFormFieldHom h hC σ ∉ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    RigidInvolution (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)))
      (primeFormFieldHom h hC σ) := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨r, h1, h2⟩
    · exact Or.inl h1
  have hodd : (C : Matrix (Fin n) (Fin n) K) = 1 → Odd n := by
    intro h1
    rcases hCr with ⟨h2, h3⟩ | ⟨-, h2⟩
    · exfalso
      have h4 := congrFun (congrFun (h1.symm.trans h3) ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [blockSwapJ_apply_self (by omega), one_apply_eq] at h4
      exact one_ne_zero h4
    · exact ⟨r, h2⟩
  obtain ⟨Cl, hCl⟩ := exists_fixed_gram h hcase
  obtain ⟨-, -, hinjU, hNinn, hNC, hNnormal, -, -, -, -, hord2, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h (by omega) hq hC hcase Cl hCl σ hσ
  have hCN := centralizer_inf_le_zpowers h (by omega) hq hC hcase hodd Cl hCl σ hσ
  have hClr : (n = 2 * r ∧ (Cl : Matrix (Fin n) (Fin n) h.fixedField) = blockSwapJ n r) ∨
      ((Cl : Matrix (Fin n) (Fin n) h.fixedField) = 1 ∧ n = 2 * r + 1) := by
    rcases canonical_case_of_map h hCl hcase with h1 | ⟨r', hr', hJ⟩
    · right
      refine ⟨h1, ?_⟩
      rcases hCr with ⟨h2, h3⟩ | ⟨-, h2⟩
      · exfalso
        have h4 : (C : Matrix (Fin n) (Fin n) K) = 1 := by
          rw [← hCl, h1, Matrix.map_one _ (map_zero _) (map_one _)]
        have h5 := congrFun (congrFun (h4.symm.trans h3) ⟨0, by omega⟩) ⟨0, by omega⟩
        rw [blockSwapJ_apply_self (by omega), one_apply_eq] at h5
        exact one_ne_zero h5
      · exact h2
    · left
      rcases hCr with ⟨h2, -⟩ | ⟨h2, h3⟩
      · exact ⟨h2, by rw [hJ, show r' = r by omega]⟩
      · exfalso
        exact absurd (hodd h2) (by rw [Nat.not_odd_iff_even]; exact ⟨r', by omega⟩)
  obtain ⟨eSp⟩ := nonempty_matrixIsometryGroup_mulEquiv_statedSp hClr
  have hkcard := h.card_fixedField
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp r h.fixedField) hkcard (by omega) ⟨MulEquiv.refl _⟩
  have hcond : 2 ≤ f ∨ 3 ≤ r := by
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · right
      by_contra hr3
      exact hsmall ⟨by omega, by have := h.one_le; omega⟩
    · left
      exact hf2
  have := (RankTwoHypIISymplectic.isSimpleGroup_and_perfect hkcard (by omega) hcond
    h.one_le).1
  set N := ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range
    with hN
  have eN : N ≃* StatedSp r h.fixedField := (MonoidHom.ofInjective hinjU).symm.trans eSp
  have hsimple : IsSimpleGroup N := (eN.trans eProj.symm).isSimpleGroup
  have heven : Even (Nat.card N) := by
    rw [Nat.card_congr eN.toEquiv]
    exact RankTwoHypIILinear.even_card_statedSp h.one_le hkcard (by omega)
  have h2 : primeFormFieldHom h hC σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (primeFormFieldHom h hC σ)
    rwa [hord2] at this
  exact RigidInvolution.of_isSimpleGroup_of_le_zpowers hX h2 hNinn hNC
    ((normal_subgroupOf_iff_le_normalizer hNC).mp hNnormal) hsimple heven hCN

theorem mem_centralizer_of_mem_centralizer_commutator {W G : Type*} [Group W] [Group G]
    {N : Subgroup W} (e : N ≃* G) (hG : centralizer (commutator G : Set G) = ⊥) {s : W}
    (hsN : s ∈ normalizer (N : Set W)) (hsL : s ∈ centralizer ((⁅N, N⁆ : Subgroup W) : Set W)) :
    s ∈ centralizer (N : Set W) := by
  rw [mem_centralizer_iff]
  intro n hn
  have hsnN : s * n * s⁻¹ ∈ N := (mem_normalizer_iff.mp hsN n).mp hn
  have hc : n⁻¹ * (s * n * s⁻¹) ∈ centralizer ((⁅N, N⁆ : Subgroup W) : Set W) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hna : n * a * n⁻¹ ∈ ⁅N, N⁆ :=
      (mem_normalizer_iff.mp (RankTwoHypIISymplectic.mem_normalizer_commutator
        (le_normalizer hn)) a).mp ha
    have h1 : s * (n * a * n⁻¹) * s⁻¹ = n * a * n⁻¹ := by
      rw [← mem_centralizer_iff.mp hsL _ hna, mul_inv_cancel_right]
    have h2 : s * a * s⁻¹ = a := by
      rw [← mem_centralizer_iff.mp hsL _ ha, mul_inv_cancel_right]
    have h3 : s * (n * a * n⁻¹) * s⁻¹ = (s * n * s⁻¹) * (s * a * s⁻¹) * (s * n * s⁻¹)⁻¹ := by
      group
    rw [h2] at h3
    rw [h3] at h1
    calc a * (n⁻¹ * (s * n * s⁻¹)) = n⁻¹ * (n * a * n⁻¹) * (s * n * s⁻¹) := by group
      _ = n⁻¹ * ((s * n * s⁻¹) * a * (s * n * s⁻¹)⁻¹) * (s * n * s⁻¹) := by rw [h1]
      _ = n⁻¹ * (s * n * s⁻¹) * a := by group
  have h1 := RankTwoHypIILinear.eq_one_of_mem_centralizer_commutator e hG
    (mul_mem (inv_mem hn) hsnN) hc
  rw [inv_mul_eq_one] at h1
  calc n * s = s * n * s⁻¹ * s := by rw [← h1]
    _ = s * n := by group

theorem rigidInvolution_fieldBar_five_two (hf : f = 1) {C : GL (Fin 5) K}
    (hC : IsPrimeFormGram C) (hC1 : (C : Matrix (Fin 5) (Fin 5) K) = 1) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = h.bar x) :
    RigidInvolution (inner (primeFormP h (C : Matrix (Fin 5) (Fin 5) K)))
      (primeFormFieldHom h hC σ) := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have : Finite (MulAut (primeFormP h (C : Matrix (Fin 5) (Fin 5) K))) := by
    have : Finite (primeFormP h (C : Matrix (Fin 5) (Fin 5) K)) := inferInstance
    exact Finite.of_injective (fun e : MulAut (primeFormP h (C : Matrix (Fin 5) (Fin 5) K)) =>
      (e : primeFormP h _ → primeFormP h _)) fun _ _ hab => MulEquiv.ext (congrFun hab)
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hcase : (C : Matrix (Fin 5) (Fin 5) K) = 1 ∨
      ∃ r, 5 = 2 * r ∧ (C : Matrix (Fin 5) (Fin 5) K) = blockSwapJ 5 r := Or.inl hC1
  obtain ⟨Cl, hCl⟩ := exists_fixed_gram h hcase
  obtain ⟨-, -, hinjU, hNinn, hNC, hNnormal, -, -, -, -, hord2, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h (by omega) hq hC hcase Cl hCl σ hσ
  have hCN := centralizer_inf_le_zpowers h (by omega) hq hC hcase (fun _ => ⟨2, rfl⟩) Cl hCl σ hσ
  have hCl1 : (Cl : Matrix (Fin 5) (Fin 5) h.fixedField) = 1 := by
    rcases canonical_case_of_map h hCl hcase with h1 | ⟨r, hr, -⟩
    · exact h1
    · omega
  obtain ⟨eSp⟩ := nonempty_matrixIsometryGroup_mulEquiv_statedSp (r := 2)
    (Or.inr ⟨hCl1, rfl⟩)
  have hk2 : Nat.card h.fixedField = 2 := by rw [h.card_fixedField, hf, pow_one]
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp 2 h.fixedField) h.card_fixedField (by omega) ⟨MulEquiv.refl _⟩
  set N := ((primeFormConjHom h (C : Matrix (Fin 5) (Fin 5) K)).comp (fixedIsometryHom h hCl)).range
    with hN
  let e : N ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (((MonoidHom.ofInjective hinjU).symm.trans eSp).trans eProj.symm).trans
      (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hk2)
  set L : Subgroup (MulAut (primeFormP h (C : Matrix (Fin 5) (Fin 5) K))) := ⁅N, N⁆ with hL
  have eL : L ≃* commutator CFSG.ComponentClassification.PresentationLocal.sympFour :=
    RankTwoHypIILinear.commutatorEquivOfMulEquiv e
  have hLsimple : IsSimpleGroup L := by
    have := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    exact eL.isSimpleGroup
  have hnc : ¬ ∀ a b : L, a * b = b * a := by
    intro hab
    apply CFSG.ComponentClassification.PresentationLocal.not_isMulCommutative_commutator_sympFour
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eL.symm.injective
    rw [map_mul, map_mul, hab]
  have hLp : ⁅L, L⁆ = L := commutator_eq_self_of_isSimpleGroup hLsimple hnc
  have heven : Even (Nat.card L) := by
    rw [Nat.card_congr (eL.trans
      CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating).toEquiv]
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_fin] at h
    have h' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      have : Nat.factorial 6 = 720 := by decide
      omega
    rw [h']
    decide
  have hLN : L ≤ N := by
    rw [hL, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hCNn : centralizer {primeFormFieldHom h hC σ} ≤
      normalizer (N : Set (MulAut (primeFormP h (C : Matrix (Fin 5) (Fin 5) K)))) :=
    (normal_subgroupOf_iff_le_normalizer hNC).mp hNnormal
  have h2 : primeFormFieldHom h hC σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (primeFormFieldHom h hC σ)
    rwa [hord2] at this
  refine ⟨L, hLN.trans hNinn, hLN.trans hNC,
    fun c hc => RankTwoHypIISymplectic.mem_normalizer_commutator (hCNn hc), hLp,
    twoNilpotentCentral_of_isSimpleGroup hLsimple hLp heven, ?_⟩
  intro s hs hsL _
  have hsN := mem_centralizer_of_mem_centralizer_commutator e
    CFSG.ComponentClassification.PresentationLocal.centralizer_commutator_sympFour (hCNn hs) hsL
  exact eq_one_or_eq_of_mem_zpowers h2 (hCN (mem_inf.mpr ⟨hs, hsN⟩))

theorem map_inner_congr {G G' : Type*} [Group G] [Group G'] (θ : G ≃* G') :
    (inner G).map (MulAut.congr θ).toMonoidHom = inner G' := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨θ x, (OuterAutomorphisms.congr_conj θ x).symm⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (θ.symm y), ⟨θ.symm y, rfl⟩, ?_⟩
    change MulAut.congr θ (MulAut.conj (θ.symm y)) = MulAut.conj y
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]

theorem rigid_or_bar (hn : 4 ≤ n) (h42 : ¬ (n = 4 ∧ f = 1))
    {α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hαX : α ∉ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hα2 : α ^ 2 = 1) :
    RigidInvolution (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) α ∨
      (Even n ∧ ∃ σ : K ≃+* K, (∀ x, σ x = h.bar x) ∧
        ∃ θ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
          α = θ * primeFormFieldHom h isPrimeFormGram_one σ * θ⁻¹) := by
  have : CharP K 2 := h.charP
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hC := isPrimeFormGram_one (n := n) (K := K)
  have hα1 : α ≠ 1 := fun h1 => hαX (h1 ▸ one_mem _)
  have hα : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  obtain ⟨hF, -, -, hD⟩ := even_unitary_involution_matrix_lifts h hC (by omega) hq α hα
  have hFbar : ∀ x, primeFormFieldFactor h hC (by omega) hq α x = h.bar x := by
    rcases hF with hF | hF
    · exfalso
      apply hαX
      refine hD α ?_ hα
      rw [← ker_primeFormFieldFactor h hC (by omega) hq, MonoidHom.mem_ker]
      exact hF
    · exact hF
  set φ := primeFormFieldFactor h hC (by omega) hq α with hφ
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC (by omega) hq α hα hFbar
  have hαθ : α = MulAut.congr θ (primeFormFieldHom h hC₀ φ) := MulEquiv.ext fun x => by
    rw [hθα x, MulAut.congr_apply]
    rfl
  have hinner := map_inner_congr θ
  have hX₀ : primeFormFieldHom h hC₀ φ ∉
      inner (primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) := by
    intro hin
    apply hαX
    rw [hαθ, ← hinner]
    exact ⟨_, hin, rfl⟩
  have htrans : RigidInvolution (inner (primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)))
      (primeFormFieldHom h hC₀ φ) → RigidInvolution
        (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) α := by
    intro hrig
    rw [hαθ]
    exact hrig.map_mulEquiv' (MulAut.congr θ) hinner
  rcases hcase₀ with h1 | ⟨r, hr, hJ⟩
  · rcases Nat.even_or_odd n with hev | hodd
    · right
      have hC₀1 : C₀ = 1 := Units.ext h1
      subst hC₀1
      exact ⟨hev, φ, hFbar, θ, MulEquiv.ext fun x => by rw [hαθ]; rfl⟩
    · left
      obtain ⟨r, hr⟩ := hodd
      apply htrans
      by_cases h52 : r = 2 ∧ f = 1
      · obtain ⟨rfl, hf1⟩ := h52
        subst hr
        exact rigidInvolution_fieldBar_five_two h hf1 hC₀ h1 φ hFbar
      · exact rigidInvolution_fieldBar h hn hC₀ (r := r) (by omega) h52 (Or.inr ⟨h1, hr⟩) φ
          hFbar hX₀
  · left
    apply htrans
    exact rigidInvolution_fieldBar h hn hC₀ (r := r) (by omega)
      (fun h' => h42 ⟨by omega, h'.2⟩) (Or.inl ⟨hr, hJ⟩) φ hFbar hX₀

end CFSG.ComponentClassification.RankTwoHypIIUnitary
