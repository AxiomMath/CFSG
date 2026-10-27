module

public import CFSG.LieType.Chevalley.EvenRootCommutatorRows
public import CFSG.LieType.Chevalley.F4FieldTwoEuclid
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps
open scoped commutatorElement

theorem f4_pairTable_invariants_injective :
    ∀ r₁ ∈ pairTable .F4, ∀ r₂ ∈ pairTable .F4,
      f4Euclid (orbitCertRoot .F4 r₁.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r₁.1) =
          f4Euclid (orbitCertRoot .F4 r₂.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r₂.1) →
        f4Euclid (orbitCertRoot .F4 r₁.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r₁.2.1) =
          f4Euclid (orbitCertRoot .F4 r₂.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r₂.2.1) →
        f4Euclid (orbitCertRoot .F4 r₁.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r₁.2.1) =
          f4Euclid (orbitCertRoot .F4 r₂.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r₂.2.1) →
        r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1 := by
  decide +kernel

theorem f4_pairTable_cases :
    ∀ r ∈ pairTable .F4,
      (f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1) =
          f4Euclid (orbitCertRoot .F4 r.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) ∧
        2 * (f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1)) =
          -(f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1)) ∧
        r.2.2.2.map (fun f => (f.1, f.2.1, f.2.2.2)) = [(1, 1, -1)]) ∨
      (f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1) = 2 ∧
        f4Euclid (orbitCertRoot .F4 r.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = 1 ∧
        f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = -1 ∧
        r.2.2.2.map (fun f => (f.1, f.2.1, f.2.2.2)) = [(1, 1, 1), (1, 2, 1)]) ∨
      (f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1) = 1 ∧
        f4Euclid (orbitCertRoot .F4 r.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = 2 ∧
        f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = -1 ∧
        r.2.2.2.map (fun f => (f.1, f.2.1, f.2.2.2)) = [(1, 1, -1), (2, 1, 1)]) ∨
      (¬(f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1) =
          f4Euclid (orbitCertRoot .F4 r.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) ∧
        2 * (f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1)) =
          -(f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1))) ∧
        ¬(f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1) = 2 ∧
          f4Euclid (orbitCertRoot .F4 r.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = 1 ∧
          f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = -1) ∧
        ¬(f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.1) = 1 ∧
          f4Euclid (orbitCertRoot .F4 r.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = 2 ∧
          f4Euclid (orbitCertRoot .F4 r.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 r.2.1) = -1) ∧
        (r.2.2.2.map (fun f => (f.1, f.2.1, f.2.2.2)) = [] ∨
          r.2.2.2.map (fun f => (f.1, f.2.1, f.2.2.2)) = [(1, 1, -2)])) := by
  decide +kernel

theorem f4_exists_commutator_factors
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s) (hne : r ≠ s)
    (hne' : r ≠ -s) :
    ∃ F : List (ℕ × ℕ × ℤ), (∀ f ∈ F, IsRoot .F4 (f.1 • r + f.2.1 • s)) ∧
      ⁅pinnedX .F4 R r 1, pinnedX .F4 R s 1⁆ =
        (F.map fun f => pinnedX .F4 R (f.1 • r + f.2.1 • s) (f.2.2 : R)).prod ∧
      ((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
          2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r) ∧ F = [(1, 1, -1)]) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1 ∧ F = [(1, 1, 1), (1, 2, 1)]) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1 ∧ F = [(1, 1, -1), (2, 1, 1)]) ∨
        (¬(f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
            2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∧
          ¬(f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) ∧
          ¬(f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) ∧
          (F = [] ∨ F = [(1, 1, -2)]))) := by
  obtain ⟨row, hrow, w, hwr, hws, hfr, hcomm⟩ :=
    exists_pairTable_commutatorElement_of_two_eq_zero hr hs hne hne'
  have eA := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.1)
  have eB := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.2.1) (orbitCertRoot .F4 row.2.1)
  have eC := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.2.1)
  simp only [hwr, hws] at eA eB eC
  have hcases := f4_pairTable_cases row hrow
  rw [← eA, ← eB, ← eC] at hcases
  refine ⟨row.2.2.2.map fun f => (f.1, f.2.1, f.2.2.2), fun f hf => ?_, ?_, hcases⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact hfr g hg
  · rw [hcomm R h2 1 1, List.map_map]
    simp only [one_pow, mul_one, Function.comp_def]

variable {K : Type} [Field K]

theorem f4_field_two_root_pair_relations
    (hK : Nat.card K = 2) :
    ringChar K = 2 ∧ Function.Injective f4Euclid ∧
      f4Euclid '' {v | IsRoot .F4 v} = f4LongEuclid ∪ f4ShortEuclid ∧
      (∀ x ∈ f4LongEuclid, x ⬝ᵥ x = 2) ∧ (∀ x ∈ f4ShortEuclid, x ⬝ᵥ x = 1) ∧
      f4Euclid '' {v | IsRoot .F4 v ∧ 0 < height v} = f4PosEuclid ∧
      {v : Fin Tag.F4.rank → ℤ | IsRoot .F4 v ∧ 0 < height v}.ncard = 24 ∧
      (∀ r, IsRoot .F4 r →
        pinnedX .F4 K r 1 ∈ adjointGroup .F4 K ∧ orderOf (pinnedX .F4 K r 1) = 2) ∧
      (∀ r₀, IsRoot .F4 r₀ → ∃ g ∈ adjointGroup .F4 K, ∀ r, IsRoot .F4 r → ∃ r', IsRoot .F4 r' ∧
        f4Euclid r' = euclidReflect (f4Euclid r₀) (f4Euclid r) ∧
        g * pinnedX .F4 K r 1 * g⁻¹ = pinnedX .F4 K r' 1) ∧
      (∀ (i : Fin Tag.F4.rank) (r : Fin Tag.F4.rank → ℤ), IsRoot .F4 r →
        weylElt .F4 K i 1 ∈ adjointGroup .F4 K ∧
        weylElt .F4 K i 1 * pinnedX .F4 K r 1 * (weylElt .F4 K i 1)⁻¹ =
          pinnedX .F4 K (reflect .F4 i r) 1 ∧
        f4Euclid (reflect .F4 i r) = euclidReflect (f4SimpleEuclid i) (f4Euclid r)) ∧
      (∀ r s r' s' : Fin Tag.F4.rank → ℤ, IsRoot .F4 r → IsRoot .F4 s → IsRoot .F4 r' →
        IsRoot .F4 s' → r ≠ s → r ≠ -s → r' ≠ s' → r' ≠ -s' →
        f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid r' ⬝ᵥ f4Euclid r' →
        f4Euclid s ⬝ᵥ f4Euclid s = f4Euclid s' ⬝ᵥ f4Euclid s' →
        f4Euclid r ⬝ᵥ f4Euclid s = f4Euclid r' ⬝ᵥ f4Euclid s' →
        ∃ w : WeylGroup .F4, w • r = r' ∧ w • s = s' ∧ ∃ g ∈ adjointGroup .F4 K,
          ∀ t, IsRoot .F4 t → g * pinnedX .F4 K t 1 * g⁻¹ = pinnedX .F4 K (w • t) 1) ∧
      ∀ r s : Fin Tag.F4.rank → ℤ, IsRoot .F4 r → IsRoot .F4 s → r ≠ s → r ≠ -s →
        ((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
            2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) →
          IsRoot .F4 (r + s) ∧ ⁅pinnedX .F4 K r 1, pinnedX .F4 K s 1⁆ = pinnedX .F4 K (r + s) 1) ∧
        ((f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) →
          IsRoot .F4 (r + s) ∧ IsRoot .F4 (r + 2 • s) ∧
          f4Euclid (r + s) ⬝ᵥ f4Euclid (r + s) = 1 ∧
          f4Euclid (r + 2 • s) ⬝ᵥ f4Euclid (r + 2 • s) = 2 ∧
          ⁅pinnedX .F4 K r 1, pinnedX .F4 K s 1⁆ =
            pinnedX .F4 K (r + s) 1 * pinnedX .F4 K (r + 2 • s) 1 ∧
          ⁅pinnedX .F4 K s 1, pinnedX .F4 K r 1⁆ =
            pinnedX .F4 K (r + s) 1 * pinnedX .F4 K (r + 2 • s) 1 ∧
          Commute (pinnedX .F4 K (r + s) 1) (pinnedX .F4 K (r + 2 • s) 1)) ∧
        (¬(f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
            2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) →
          ¬(f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) →
          ¬(f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) →
          Commute (pinnedX .F4 K r 1) (pinnedX .F4 K s 1)) := by
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl (by rw [hK, pow_one])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ c : K, -c = c := CharTwo.neg_eq
  have hconj : ∀ (w : WeylGroup .F4) (t : Fin Tag.F4.rank → ℤ), IsRoot .F4 t → ∀ c : K,
      canonicalRep (coxeterSystem .F4) K w * pinnedX .F4 K t c *
        (canonicalRep (coxeterSystem .F4) K w)⁻¹ = pinnedX .F4 K (w • t) c :=
    fun w t ht c => canonicalRep_mul_pinnedX_mul_inv_of_two h2 w ht c
  refine ⟨ringChar.eq K 2, f4Euclid_injective, f4Euclid_image_roots,
    fun x hx => dotProduct_self_of_mem_f4LongEuclid hx,
    fun x hx => dotProduct_self_of_mem_f4ShortEuclid hx, f4Euclid_image_posRoots,
    ncard_f4_posRoots, fun r _ => ?_, fun r₀ hr₀ => ?_, fun i r hr => ?_, ?_, ?_⟩
  ·
    refine ⟨pinnedX_mem_adjointGroup r 1, orderOf_eq_prime ?_ ?_⟩
    · rw [sq, ← pinnedX_add, one_add_one_eq_two, h2, pinnedX_zero]
    · intro h
      rw [← pinnedX_zero .F4 K r] at h
      exact one_ne_zero (pinnedX_injective .F4 K r h)
  ·
    exact ⟨canonicalRep (coxeterSystem .F4) K (rootReflection r₀),
      canonicalRep_mem_adjointGroup _ K _, fun r hr =>
        ⟨rootReflection r₀ • r, IsRoot.smul hr _, f4Euclid_rootReflection hr₀ r,
          hconj _ r hr 1⟩⟩
  ·
    refine ⟨weylElt_mem_adjointGroup i 1, ?_, f4Euclid_reflect i r⟩
    have h := hconj (simple .F4 i) r hr 1
    rwa [canonicalRep_simple, simple_smul] at h
  ·
    intro r s r' s' hr hs hr' hs' hne hne' hne₂ hne₂' hl₁ hl₂ hip
    obtain ⟨row₁, hrow₁, w₁, h₁r, h₁s, -, -⟩ :=
      exists_pairTable_commutatorElement_of_two_eq_zero.{0} hr hs hne hne'
    obtain ⟨row₂, hrow₂, w₂, h₂r, h₂s, -, -⟩ :=
      exists_pairTable_commutatorElement_of_two_eq_zero.{0} hr' hs' hne₂ hne₂'
    have a₁ := f4Euclid_smul_dotProduct w₁ (orbitCertRoot .F4 row₁.1) (orbitCertRoot .F4 row₁.1)
    have b₁ := f4Euclid_smul_dotProduct w₁ (orbitCertRoot .F4 row₁.2.1)
      (orbitCertRoot .F4 row₁.2.1)
    have c₁ := f4Euclid_smul_dotProduct w₁ (orbitCertRoot .F4 row₁.1) (orbitCertRoot .F4 row₁.2.1)
    have a₂ := f4Euclid_smul_dotProduct w₂ (orbitCertRoot .F4 row₂.1) (orbitCertRoot .F4 row₂.1)
    have b₂ := f4Euclid_smul_dotProduct w₂ (orbitCertRoot .F4 row₂.2.1)
      (orbitCertRoot .F4 row₂.2.1)
    have c₂ := f4Euclid_smul_dotProduct w₂ (orbitCertRoot .F4 row₂.1) (orbitCertRoot .F4 row₂.2.1)
    simp only [h₁r, h₁s] at a₁ b₁ c₁
    simp only [h₂r, h₂s] at a₂ b₂ c₂
    obtain ⟨e₁, e₂⟩ := f4_pairTable_invariants_injective row₁ hrow₁ row₂ hrow₂
      (a₁.symm.trans (hl₁.trans a₂)) (b₁.symm.trans (hl₂.trans b₂)) (c₁.symm.trans (hip.trans c₂))
    refine ⟨w₂ * w₁⁻¹, ?_, ?_, canonicalRep (coxeterSystem .F4) K (w₂ * w₁⁻¹),
      canonicalRep_mem_adjointGroup _ K _, fun t ht => hconj _ t ht 1⟩
    · rw [mul_smul, ← h₁r, inv_smul_smul, e₁, h₂r]
    · rw [mul_smul, ← h₁s, inv_smul_smul, e₂, h₂s]
  ·
    intro r s hr hs hne hne'
    obtain ⟨F, hF, hc, hcases⟩ := f4_exists_commutator_factors h2 hr hs hne hne'
    refine ⟨fun hA => ?_, fun hB => ?_, fun hA hB hB' => ?_⟩
    ·
      rcases hcases with ⟨-, -, rfl⟩ | ⟨h1, h2', h3, -⟩ | ⟨h1, h2', h3, -⟩ | ⟨hn, -⟩
      · refine ⟨?_, ?_⟩
        · simpa using hF _ List.mem_cons_self
        · simpa [hneg] using hc
      · exact absurd hA.1 (by rw [h1, h2']; norm_num)
      · exact absurd hA.1 (by rw [h1, h2']; norm_num)
      · exact absurd hA hn
    ·
      obtain ⟨hA, hB₁, hC⟩ := hB
      rcases hcases with ⟨h1, -, -⟩ | ⟨-, -, -, rfl⟩ | ⟨h1, -, -, -⟩ | ⟨-, hn, -⟩
      · exact absurd h1 (by rw [hA, hB₁]; norm_num)
      ·
        have hne₂ : s ≠ r := fun h => hne h.symm
        have hne₂' : s ≠ -r := fun h => hne' (by rw [h, neg_neg])
        obtain ⟨F', -, hc', hcases'⟩ := f4_exists_commutator_factors h2 hs hr hne₂ hne₂'
        have hsr : f4Euclid s ⬝ᵥ f4Euclid r = -1 := by rw [dotProduct_comm, hC]
        have hrs : IsRoot .F4 (r + s) := by simpa using hF _ List.mem_cons_self
        have hr2s : IsRoot .F4 (r + 2 • s) := by
          simpa using hF _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have l₁ : f4Euclid (r + s) ⬝ᵥ f4Euclid (r + s) = 1 := by
          simp only [f4Euclid_add, add_dotProduct, dotProduct_add, hA, hB₁, hC, hsr]
          norm_num
        have l₂ : f4Euclid (r + 2 • s) ⬝ᵥ f4Euclid (r + 2 • s) = 2 := by
          have e : (2 • s : Fin Tag.F4.rank → ℤ) = s + s := two_nsmul s
          simp only [e, f4Euclid_add, add_dotProduct, dotProduct_add, hA, hB₁, hC, hsr]
          norm_num
        have l₃ : f4Euclid (r + s) ⬝ᵥ f4Euclid (r + 2 • s) = 1 := by
          have e : (2 • s : Fin Tag.F4.rank → ℤ) = s + s := two_nsmul s
          simp only [e, f4Euclid_add, add_dotProduct, dotProduct_add, hA, hB₁, hC, hsr]
          norm_num
        have hne₃ : r + s ≠ r + 2 • s := fun h => by
          have := l₂
          rw [← h, l₁] at this
          norm_num at this
        have hne₃' : r + s ≠ -(r + 2 • s) := fun h => by
          have := l₁
          rw [h, f4Euclid_neg, neg_dotProduct, dotProduct_neg, neg_neg, l₂] at this
          norm_num at this
        obtain ⟨F'', -, hc'', hcases''⟩ := f4_exists_commutator_factors h2 hrs hr2s hne₃ hne₃'
        refine ⟨hrs, hr2s, l₁, l₂, by simpa using hc, ?_, ?_⟩
        · rcases hcases' with ⟨h1, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hn, -⟩
          · exact absurd h1 (by rw [hA, hB₁]; norm_num)
          · exact absurd h1 (by rw [hB₁]; norm_num)
          · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
              one_smul, Int.cast_neg, Int.cast_one, hneg] at hc'
            rw [hc', add_comm s r, add_comm (2 • s) r]
          · exact absurd ⟨hB₁, hA, hsr⟩ hn
        · rcases hcases'' with ⟨h1, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, -, hF''⟩
          · exact absurd h1 (by rw [l₁, l₂]; norm_num)
          · exact absurd h1 (by rw [l₁]; norm_num)
          · exact absurd h1 (by rw [l₃]; norm_num)
          · rw [← commutatorElement_eq_one_iff_commute, hc'']
            rcases hF'' with rfl | rfl
            · rfl
            · simp [h2, pinnedX_zero]
      · exact absurd h1 (by rw [hA]; norm_num)
      · exact absurd ⟨hA, hB₁, hC⟩ hn
    ·
      rcases hcases with ⟨h1, h2', -⟩ | ⟨h1, h2', h3, -⟩ | ⟨h1, h2', h3, -⟩ | ⟨-, -, -, hF'⟩
      · exact absurd ⟨h1, h2'⟩ hA
      · exact absurd ⟨h1, h2', h3⟩ hB
      · exact absurd ⟨h1, h2', h3⟩ hB'
      · rw [← commutatorElement_eq_one_iff_commute, hc]
        rcases hF' with rfl | rfl
        · rfl
        · simp [h2, pinnedX_zero]

end CFSG.LieType.Chevalley
