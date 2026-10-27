module

public import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
public import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexOrder

open NormalInduction (conjClassFun conjClassFun_apply)

variable {L : Type*} [Group L] [Fintype L] {H : Subgroup L}

open scoped Classical in
noncomputable def NormalInduction.conjOrbit (H : Subgroup L) [H.Normal] (lam : H → ℂ) :
    Finset (H → ℂ) :=
  Finset.univ.image fun g : L => conjClassFun H g lam

theorem NormalInduction.mem_conjOrbit [H.Normal] {lam mu : H → ℂ} :
    mu ∈ NormalInduction.conjOrbit H lam ↔ ∃ g : L, conjClassFun H g lam = mu := by
  classical
  simp [NormalInduction.conjOrbit]

theorem NormalInduction.conjClassFun_mem_conjOrbit [H.Normal] (lam : H → ℂ) (g : L) :
    conjClassFun H g lam ∈ NormalInduction.conjOrbit H lam :=
  NormalInduction.mem_conjOrbit.2 ⟨g, rfl⟩

theorem NormalInduction.self_mem_conjOrbit [H.Normal] (lam : H → ℂ) :
    lam ∈ NormalInduction.conjOrbit H lam :=
  NormalInduction.mem_conjOrbit.2 ⟨1, by funext n; simp [conjClassFun_apply]⟩

theorem NormalInduction.conjOrbit_nonempty [H.Normal] (lam : H → ℂ) :
    (NormalInduction.conjOrbit H lam).Nonempty :=
  ⟨lam, NormalInduction.self_mem_conjOrbit lam⟩

theorem NormalInduction.conjOrbit_subset_Irr [H.Normal] {lam : H → ℂ} (hlam : lam ∈ Irr H) :
    ↑(NormalInduction.conjOrbit H lam) ⊆ Irr H := by
  intro mu hmu
  obtain ⟨g, rfl⟩ := NormalInduction.mem_conjOrbit.1 hmu
  exact conjClassFun_mem_Irr H g hlam

theorem cfInner_sum_eq_ite {S : Finset (L → ℂ)} (hS : ↑S ⊆ Irr L) {χ : L → ℂ}
    (hχ : χ ∈ Irr L) [Decidable (χ ∈ S)] :
    cfInner (∑ ψ ∈ S, ψ) χ = if χ ∈ S then 1 else 0 := by
  classical
  rw [cfInner_sum_left S (fun ψ => ψ) χ]
  split
  · rename_i h
    rw [Finset.sum_eq_single_of_mem χ h]
    · exact cfInner_self_of_mem_Irr hχ
    · exact fun ψ hψ hne => cfInner_eq_zero_of_mem_Irr (hS hψ) hχ hne
  · rename_i h
    exact Finset.sum_eq_zero fun ψ hψ =>
      cfInner_eq_zero_of_mem_Irr (hS hψ) hχ fun he => h (he ▸ hψ)

theorem mem_iff_cfInner_sum_ne_zero {S : Finset (L → ℂ)} (hS : ↑S ⊆ Irr L) {χ : L → ℂ}
    (hχ : χ ∈ Irr L) : χ ∈ S ↔ cfInner (∑ ψ ∈ S, ψ) χ ≠ 0 := by
  classical
  rw [cfInner_sum_eq_ite hS hχ]
  split <;> simp_all

theorem resClassFun_eq_sum_conjOrbit [H.Normal] {lam : H → ℂ} (hlam : lam ∈ Irr H)
    {S : Finset (L → ℂ)} (hS : ↑S ⊆ Irr L) (hθ : indClassFun H lam = ∑ ψ ∈ S, ψ)
    {χ : L → ℂ} (hχ : χ ∈ S) :
    resClassFun H χ = ∑ mu ∈ NormalInduction.conjOrbit H lam, mu := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hχIrr : χ ∈ Irr L := hS hχ
  have hone : cfInner (indClassFun H lam) χ = 1 := by
    rw [hθ, cfInner_sum_eq_ite hS hχIrr, if_pos hχ]
  have h1 : cfInner (resClassFun H χ) lam = 1 := by
    rw [← cfInner_indClassFun_eq_cfInner_resClassFun hχIrr hlam, hone]
  have hmem : lam ∈ resConstituents H χ :=
    mem_resConstituents.2 ⟨hlam, by rw [h1]; exact zero_lt_one⟩
  obtain ⟨e, -, hconst, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := H) hχIrr
  have he1 : (e : ℂ) = 1 := by rw [← hconst lam hmem, h1]
  have hSet : resConstituents H χ = NormalInduction.conjOrbit H lam := by
    ext mu
    rw [NormalInduction.mem_conjOrbit, mem_resConstituents_iff_exists_conjClassFun hχIrr hmem]
  rw [hres, he1, one_smul, hSet]

theorem resClassFun_eq_sum_conjOrbit_of_cfInner_ne_zero [H.Normal] {lam : H → ℂ}
    (hlam : lam ∈ Irr H) {S : Finset (L → ℂ)} (hS : ↑S ⊆ Irr L)
    (hθ : indClassFun H lam = ∑ ψ ∈ S, ψ) {χ : L → ℂ} (hχ : χ ∈ Irr L)
    (hne : cfInner (indClassFun H lam) χ ≠ 0) :
    resClassFun H χ = ∑ mu ∈ NormalInduction.conjOrbit H lam, mu :=
  resClassFun_eq_sum_conjOrbit hlam hS hθ ((mem_iff_cfInner_sum_ne_zero hS hχ).2 (hθ ▸ hne))

theorem resClassFun_eq_resClassFun_of_mem [H.Normal] {lam : H → ℂ} (hlam : lam ∈ Irr H)
    {S : Finset (L → ℂ)} (hS : ↑S ⊆ Irr L) (hθ : indClassFun H lam = ∑ ψ ∈ S, ψ)
    {χ χ' : L → ℂ} (hχ : χ ∈ S) (hχ' : χ' ∈ S) :
    resClassFun H χ = resClassFun H χ' := by
  rw [resClassFun_eq_sum_conjOrbit hlam hS hθ hχ, resClassFun_eq_sum_conjOrbit hlam hS hθ hχ']

theorem apply_one_eq_apply_one_of_mem [H.Normal] {lam : H → ℂ} (hlam : lam ∈ Irr H)
    {S : Finset (L → ℂ)} (hS : ↑S ⊆ Irr L) (hθ : indClassFun H lam = ∑ ψ ∈ S, ψ)
    {χ χ' : L → ℂ} (hχ : χ ∈ S) (hχ' : χ' ∈ S) : χ 1 = χ' 1 := by
  have h := congrFun (resClassFun_eq_resClassFun_of_mem hlam hS hθ hχ hχ') 1
  simpa using h

end

end CFSG.FeitThompson
