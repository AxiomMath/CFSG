module

public import CFSG.LieType.Chevalley.BorelCoreCenter
public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.RightBruhatMultiplication
public import CFSG.LieType.Chevalley.ConnectedDiagram

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem weylElt_mem_bruhatCell_simple
    (i : Fin τ.rank) :
    weylElt τ K i 1 ∈ bruhatCell τ K (simple τ i) := by
  rw [← canonicalRep_simple (coxeterSystem τ) K i]
  exact canonicalRep_mem_bruhatCell _

theorem canonicalRep_mem_of_bruhatCell
    {A : Subgroup (ModGL τ K)} (hB : borelGroup τ K ≤ A)
    {w : WeylGroup τ} {x : ModGL τ K} (hx : x ∈ bruhatCell τ K w) (hxA : x ∈ A) :
    canonicalRep (coxeterSystem τ) K w ∈ A := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
  have := mul_mem (mul_mem (inv_mem (hB hb)) hxA) (inv_mem (hB hb'))
  simpa [mul_assoc] using this

variable (τ K) in
theorem normal_borel_saturation
    (M : Subgroup (adjointGroup τ K)) [M.Normal] :
    M ≤ Subgroup.center (adjointGroup τ K) ∨
      ((M.map (adjointGroup τ K).subtype : Set (ModGL τ K)) * (borelGroup τ K : Set (ModGL τ K)) =
          (parabolicSubgroup τ K Set.univ : Set (ModGL τ K)) ∧
        (parabolicSubgroup τ K Set.univ : Set (ModGL τ K)) = adjointGroup τ K) := by
  obtain ⟨-, -, -, -, -, hPuniv, -⟩ := standard_parabolic_cells τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  by_cases hMZ : M ≤ Subgroup.center (adjointGroup τ K)
  · exact Or.inl hMZ
  right
  set M' := M.map (adjointGroup τ K).subtype
  have hM'C : M' ≤ adjointGroup τ K := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hnorm : ∀ g ∈ adjointGroup τ K, ∀ x ∈ M', g * x * g⁻¹ ∈ M' := by
    rintro g hg _ ⟨m, hm, rfl⟩
    exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance m hm ⟨g, hg⟩, rfl⟩
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (M' : Set (ModGL τ K)) := fun b hb =>
    Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hnorm b (hBC hb) x hx, fun hx => by
      have := hnorm b⁻¹ (inv_mem (hBC hb)) _ hx
      simpa [mul_assoc] using this⟩
  have hprod : (M' : Set (ModGL τ K)) * (borelGroup τ K : Set (ModGL τ K)) =
      ((M' ⊔ borelGroup τ K : Subgroup (ModGL τ K)) : Set (ModGL τ K)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left M' (borelGroup τ K) hBN).symm
  set A := M' ⊔ borelGroup τ K
  have hBA : borelGroup τ K ≤ A := le_sup_right
  have hAC : A ≤ adjointGroup τ K := sup_le hM'C hBC
  have hA := eq_parabolicSubgroup_of_borelGroup_le hBA hAC
  set J := {i | weylElt τ K i 1 ∈ A}
  have hM'B : ¬ M' ≤ borelGroup τ K := by
    intro h
    apply hMZ
    rw [← (borel_core_center τ K).1]
    refine Subgroup.normal_le_normalCore.2 fun m hm => ?_
    rw [Subgroup.mem_subgroupOf]
    exact h ⟨m, hm, rfl⟩
  have hJne : J.Nonempty := by
    by_contra hJ
    rw [Set.not_nonempty_iff_eq_empty] at hJ
    apply hM'B
    have h0 : A = borelGroup τ K := by
      rw [hA, hJ]
      simp [parabolicSubgroup]
    rw [← h0]
    exact le_sup_left
  have hJu : J = Set.univ := by
    by_contra hJu
    obtain ⟨i, hi, j, hj, -, hl2, hl3⟩ := (connected_weyl_diagram τ).2.2 J hJne hJu
    have hiA : weylElt τ K i 1 ∈ (M' : Set (ModGL τ K)) * (borelGroup τ K : Set (ModGL τ K)) := by
      rw [hprod]
      exact hi
    obtain ⟨m, hm, b, hb, hmb⟩ := hiA
    have hmD : m ∈ bruhatCell τ K (simple τ i) := by
      have hm' : m = weylElt τ K i 1 * b⁻¹ := by rw [← hmb, mul_inv_cancel_right]
      obtain ⟨b₁, hb₁, b₂, hb₂, h₁⟩ := mem_bruhatCell.1 (weylElt_mem_bruhatCell_simple (K := K) i)
      exact mem_bruhatCell.2 ⟨b₁, hb₁, b₂ * b⁻¹, mul_mem hb₂ (inv_mem hb), by
        rw [hm', ← h₁]
        group⟩
    have hjC : weylElt τ K j 1 ∈ adjointGroup τ K := weylElt_mem_adjointGroup j 1
    have hx : weylElt τ K j 1 * m * (weylElt τ K j 1)⁻¹ ∈ M' := hnorm _ hjC m hm
    have hjinv : (weylElt τ K j 1)⁻¹ ∈ bruhatCell τ K (simple τ j) := by
      have h := (right_bruhat_multiplication τ K).1 (simple τ j)
      rw [simple_inv] at h
      rw [← h]
      exact Set.inv_mem_inv.2 (weylElt_mem_bruhatCell_simple j)
    have hl1 : (coxeterSystem τ).length (simple τ j * simple τ i) =
        (coxeterSystem τ).length (simple τ i) + 1 := by
      rw [hl2, CoxeterSystem.length_simple]
    have hl3' : (coxeterSystem τ).length (simple τ j * simple τ i * simple τ j) =
        (coxeterSystem τ).length (simple τ j * simple τ i) + 1 := by
      rw [hl2, hl3]
    have hD : weylElt τ K j 1 * m * (weylElt τ K j 1)⁻¹ ∈
        bruhatCell τ K (simple τ j * simple τ i * simple τ j) := by
      rw [← (right_bruhat_multiplication τ K).2.1 j _ hl3',
        ← (simple_bruhat_multiplication τ K).1 j (simple τ i) hl1]
      exact Set.mul_mem_mul (Set.mul_mem_mul (weylElt_mem_bruhatCell_simple j) hmD) hjinv
    have hn : canonicalRep (coxeterSystem τ) K (simple τ j * simple τ i * simple τ j) ∈ A :=
      canonicalRep_mem_of_bruhatCell hBA hD (le_sup_left (b := borelGroup τ K) hx)
    have hω : (coxeterSystem τ).wordProd [j, i, j] = simple τ j * simple τ i * simple τ j := by
      simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_assoc]
    have hred : (coxeterSystem τ).IsReduced [j, i, j] := by
      rw [CoxeterSystem.IsReduced, hω, hl3]
      rfl
    have hconj : (borelGroup τ K).map (MulAut.conj (canonicalRep (coxeterSystem τ) K
        ((coxeterSystem τ).wordProd [j, i, j]))).toMonoidHom ≤ A := by
      rw [hω]
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hn (hBA hy)) (inv_mem hn)
    exact hj (reduced_word_borel_extraction τ K A hBA [j, i, j] hred hconj j
      List.mem_cons_self)
  refine ⟨?_, by rw [hPuniv]⟩
  rw [hprod, hA, hJu]

end CFSG.LieType.Chevalley
