module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSULinearRadical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenUnitary

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag UnitaryFieldTransfer
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace UnitaryFieldTransfer

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_fixed_canonical {C : GL (Fin n) K}
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) :
    ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C := by
  have := fixedField_charP h
  rcases hcase with h1 | ⟨r, hr, hJ⟩
  · exact ⟨1, by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1]⟩
  · refine ⟨blockSwapGL (K := h.fixedField) (r := r) (by omega), ?_⟩
    rw [coe_blockSwapGL, hJ]
    ext i j
    simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
    split_ifs <;> simp

end UnitaryFieldTransfer

namespace NonalternatingRadical

theorem oddCore_matrixIsometryGroup_one_of_even {k : Type} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hn : Even n) (hn3 : 3 ≤ n) :
    CFSG.oddCore (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)) = ⊥ := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer
    (X := matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)) (R := radicalGroup i)
    (radicalGroup_le hn i) ?_ ?_ ?_
  · intro B hB g hg
    obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
    refine mem_radicalGroup_of_dotProduct hn (x := (B : Matrix (Fin n) (Fin n) k) *ᵥ v)
      (c := c) ?_ ?_
    · rw [onesVec_dotProduct_mulVec_of_mem hB, (mem_radicalW.mp hv).1]
    · rw [Units.val_mul, Units.val_mul, hc, conj_radicalMatrix hB]
  · refine EvenCatalog.oddCore_eq_bot_of_forall_two_pow fun r => ⟨1, ?_⟩
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, pow_one, sq, mul_self_of_mem_radicalGroup hn r.2]
    rfl
  · intro x hx hcx
    have hx' := eq_radical_of_centralizes (K := k) hn hn3 i hx 1 fun g hg => by
      rw [map_one, mul_one, ← map_mul, ← map_inv, ← map_mul, hcx g hg, mul_inv_cancel_right]
    exact ⟨1, by rw [pow_one, sq, mul_self_of_mem_radicalGroup hn hx'.2]⟩

end NonalternatingRadical

theorem even_unitary_canonical_field_involution_odd_core {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    {H : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))}
    (hH : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ≤ H) :
    CFSG.oddCore ↥(H ⊓ centralizer {primeFormFieldHom h hC σ}) = ⊥ := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := EvenCatalog.finite_mulAut_primeFormP (C := C) h
  obtain ⟨Cl, hCl⟩ := exists_fixed_canonical h hcase
  have hcaseL := canonical_case_of_map h hCl hcase
  obtain ⟨-, -, hinjU, hNinner, hNM, hNnormal, Θ, -, hΘrange, hΘker, hγ2, hΘN, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase Cl hCl σ hσ
  have hOodd :
      CFSG.oddCore (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) = ⊥ := by
    rcases hcaseL with h1 | ⟨r, hr, hJ⟩
    · rw [h1]
      rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
      · exact NonalternatingRadical.oddCore_matrixIsometryGroup_one_of_even hev hn
      · have hr1 : 1 ≤ r := by omega
        have h24 : 2 ≤ r ∨ 4 ≤ Nat.card h.fixedField := by
          by_contra! hcon
          rw [h.card_fixedField] at hcon
          have hf1 : f = 1 := by
            by_contra hf1
            have h4 : 4 ≤ 2 ^ f := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := h.one_le; omega)
            omega
          exact hq ⟨by omega, by rw [hf1, pow_one]⟩
        exact oddCore_matrixIsometryGroup_one (K := h.fixedField) h.one_le h.card_fixedField hr hr1
          h24
    · exact oddCore_matrixIsometryGroup_blockSwapJ h.one_le h.card_fixedField hn hr hJ
  have hNodd : CFSG.oddCore ↥((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)).range = ⊥ :=
    EvenCatalog.oddCore_eq_bot_of_mulEquiv (MonoidHom.ofInjective hinjU) hOodd
  have hcentL : ∀ y ∈ centralizer {conjAut n h.fixedField Cl * dualAut n h.fixedField},
      (∀ z ∈ (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)).map
        (conjAut n h.fixedField), y * z = z * y) → y ^ 2 = 1 := by
    intro y hy hyz
    have hyN : y ∈ centralizer (((matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n)
        h.fixedField)).map (conjAut n h.fixedField) : Subgroup (MulAut (projectiveSL n
          h.fixedField))) : Set (MulAut (projectiveSL n h.fixedField))) :=
      mem_centralizer_iff.mpr fun z hz => (hyz z hz).symm
    by_cases hev : (Cl : Matrix (Fin n) (Fin n) h.fixedField) = 1 ∧ Even n
    · obtain ⟨hCl1, hev⟩ := hev
      have hβ : conjAut n h.fixedField Cl * dualAut n h.fixedField = dualAut n h.fixedField := by
        rw [show Cl = 1 from Units.ext hCl1, map_one, one_mul]
      rw [hβ] at hy
      obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      apply NonalternatingRadical.sq_eq_one_of_mem_centralizer_radicalImage (K := h.fixedField)
        hev hn i
      refine mem_inf.mpr ⟨hy, ?_⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      have hgO : g ∈ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) := by
        rw [hCl1]
        exact NonalternatingRadical.radicalGroup_le hev i hg
      exact (hyz _ (mem_map_of_mem _ hgO)).symm
    · have hcase' : (∃ r, n = 2 * r ∧ (Cl : Matrix (Fin n) (Fin n) h.fixedField) =
          blockSwapJ n r) ∨ ((Cl : Matrix (Fin n) (Fin n) h.fixedField) = 1 ∧ Odd n) := by
        rcases hcaseL with h1 | h2
        · exact Or.inr ⟨h1, Nat.not_even_iff_odd.mp fun he => hev ⟨h1, he⟩⟩
        · exact Or.inl h2
      obtain ⟨-, -, hβ2, -, -, -, hrest⟩ :=
        even_linear_canonical_graph_symplectic_centralizers h.one_le h.card_fixedField hn Cl hcaseL
      have hyz' : y ∈ zpowers (conjAut n h.fixedField Cl * dualAut n h.fixedField) := by
        rw [← (hrest hcase').1]
        exact mem_inf.mpr ⟨hy, hyN⟩
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hyz'
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hβ2,
        _root_.one_zpow]
  have hγsq : primeFormFieldHom h hC σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (primeFormFieldHom h hC σ)
    rwa [hγ2] at this
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer
    (R := ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range)
    (le_inf (hNinner.trans hH) hNM) ?_ hNodd ?_
  · intro x hx r hr
    have hxM := (mem_inf.mp hx).2
    have := hNnormal.conj_mem ⟨r, hNM hr⟩ (mem_subgroupOf.mpr hr) ⟨x, hxM⟩
    rw [mem_subgroupOf] at this
    exact this
  · intro x hx hcx
    have hxM := (mem_inf.mp hx).2
    have h1 : (Θ ⟨x, hxM⟩) ^ 2 = 1 := by
      refine hcentL _ (hΘrange ⟨_, rfl⟩) fun z hz => ?_
      rw [← hΘN] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcx u (mem_subgroupOf.mp hu))
    have h2 : (⟨x, hxM⟩ : centralizer {primeFormFieldHom h hC σ}) ^ 2 ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_pow, h1]
    rw [hΘker, mem_subgroupOf, SubgroupClass.coe_pow] at h2
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp h2
    refine ⟨2, ?_⟩
    have hm' : x ^ 2 = primeFormFieldHom h hC σ ^ m := hm.symm
    calc x ^ 2 ^ 2 = (x ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
      _ = 1 := by
        rw [hm', ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          hγsq, _root_.one_zpow]

end CFSG.ComponentClassification.UnbalancedCatalog
