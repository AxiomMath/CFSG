module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DegQ0

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
open scoped commutatorElement
open AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem commutator_comap_perfect (C : AhatData.CoverSetup n K) {Q : Subgroup (Perm (Fin n))}
    (hQA : Q ≤ alternatingGroup (Fin n)) (hQ : ⁅Q, Q⁆ = Q) :
    ⁅⁅Q.comap C.ρ, Q.comap C.ρ⁆, ⁅Q.comap C.ρ, Q.comap C.ρ⁆⁆ = ⁅Q.comap C.ρ, Q.comap C.ρ⁆ ∧
      (⁅Q.comap C.ρ, Q.comap C.ρ⁆).map C.ρ = Q := by
  set E : Subgroup K := Q.comap C.ρ with hE
  have hEmap : E.map C.ρ = Q := C.map_comap_eq_of_le hQA
  have hLmap : (⁅E, E⁆).map C.ρ = Q := by rw [Subgroup.map_commutator, hEmap, hQ]
  refine ⟨?_, hLmap⟩
  have hcen : ∀ a ∈ E, ∃ l ∈ ⁅E, E⁆, l⁻¹ * a ∈ center K := by
    intro a ha
    have : C.ρ a ∈ (⁅E, E⁆).map C.ρ := by rw [hLmap]; exact ha
    obtain ⟨l, hl, hla⟩ := this
    exact ⟨l, hl, by rw [← C.ρ_eq_one_iff, map_mul, map_inv, hla, inv_mul_cancel]⟩
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact (⁅E, E⁆).mul_mem ((⁅E, E⁆).mul_mem ((⁅E, E⁆).mul_mem ha hb) ((⁅E, E⁆).inv_mem ha))
      ((⁅E, E⁆).inv_mem hb)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨l₁, hl₁, hc₁⟩ := hcen a ha
    obtain ⟨l₂, hl₂, hc₂⟩ := hcen b hb
    have e₁ : a = l₁ * (l₁⁻¹ * a) := by group
    have e₂ : b = l₂ * (l₂⁻¹ * b) := by group
    have : ⁅a, b⁆ = ⁅l₁, l₂⁆ := by
      rw [e₁, e₂]
      exact (CFSG.SectionRank.commutatorElement_mul_mem_center l₁ l₂ hc₁ hc₂).trans (by simp)
    rw [this]
    exact Subgroup.commutator_mem_commutator hl₁ hl₂

section Std

variable {k : ℕ} {h : 2 * k ≤ n}

theorem isPairLift_of_dblPair {C : AhatData.CoverSetup n K} {i l : Fin k} (hil : i ≠ l) {x : K}
    (hx : C.ρ x = dblPair n k h i l) : IsPairLift C (stdInv n k h) x := by
  have hinj := (pairEmb n k h).injective
  have hab : pairEmb n k h (i, 0) ≠ pairEmb n k h (i, 1) := fun e => by
    have := hinj e
    simp at this
  have hac : pairEmb n k h (i, 0) ≠ pairEmb n k h (l, 0) := fun e => hil (by
    have := hinj e
    simp_all)
  have had : pairEmb n k h (i, 0) ≠ pairEmb n k h (l, 1) := fun e => hil (by
    have := hinj e
    simp_all)
  have hbc : pairEmb n k h (i, 1) ≠ pairEmb n k h (l, 0) := fun e => hil (by
    have := hinj e
    simp_all)
  have hbd : pairEmb n k h (i, 1) ≠ pairEmb n k h (l, 1) := fun e => hil (by
    have := hinj e
    simp_all)
  have hcd : pairEmb n k h (l, 0) ≠ pairEmb n k h (l, 1) := fun e => by
    have := hinj e
    simp at this
  refine ⟨pairEmb n k h (i, 0), pairEmb n k h (i, 1), pairEmb n k h (l, 0),
    pairEmb n k h (l, 1), hab, hac, had, hbc, hbd, hcd, ?_, ?_, ?_, ?_, hx⟩
  · rw [stdInv_apply_pair]
    rfl
  · rw [stdInv_apply_pair]
    rfl
  · rw [stdInv_apply_pair]
    rfl
  · rw [stdInv_apply_pair]
    rfl

end Std

theorem exists_diag_std (C : AhatData.CoverSetup n K) {α : MulAut K} {k : ℕ} {hk : 2 * k ≤ n}
    (h : C.Induces α (stdInv n k hk)) (hk7 : 7 ≤ k) :
    ∃ r : K, IsPairLift C (stdInv n k hk) r ∧ ∃ Y : Subgroup K, Y ≤ fixSub α ∧
      (∀ y ∈ Y, y * r = r * y) ∧ ⁅Y, Y⁆ = Y ∧
      ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β), Nat.card β = k - 2 ∧
        ∃ θ : ↥Y →* alternatingGroup β, Function.Surjective θ := by
  classical
  let i₁ : Fin k := ⟨0, by omega⟩
  let i₂ : Fin k := ⟨1, by omega⟩
  have hi : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  obtain ⟨r, -, hr⟩ := h.exists_dblPair_mem_fixSub i₁ i₂ hi
  have hrp : IsPairLift C (stdInv n k hk) r := isPairLift_of_dblPair hi hr
  let f := otherHom n k hk i₁ i₂
  have hinj : Function.Injective f := otherHom_injective
  let Q : Subgroup (Perm (Fin n)) := (alternatingGroup (OtherPairs k i₁ i₂)).map f
  have hQeq : Q0 n k hk i₁ i₂ = Q := Subgroup.ext fun q => degQ0_mem_iff.trans Subgroup.mem_map.symm
  have hcard : Nat.card (OtherPairs k i₁ i₂) = k - 2 := by
    rw [Nat.card_eq_fintype_card]
    exact card_otherPairs hi
  have hQA : Q ≤ alternatingGroup (Fin n) := fun q hq =>
    Q0_le_alternatingGroup (by rw [hQeq]; exact hq)
  have h5 : 5 ≤ Nat.card (OtherPairs k i₁ i₂) := by omega
  have hperf : Group.IsPerfect (alternatingGroup (OtherPairs k i₁ i₂)) :=
    ⟨commutator_alternatingGroup_eq_top h5⟩
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]
  obtain ⟨hperfY, hYmap⟩ := commutator_comap_perfect C hQA hQperf
  have hcommσ : ∀ x ∈ Q.comap C.ρ, C.ρ x * stdInv n k hk = stdInv n k hk * C.ρ x := fun x hx =>
    Q0_comm_stdInv _ (by rw [hQeq]; exact hx)
  have hcommr : ∀ x ∈ Q.comap C.ρ, C.ρ x * C.ρ r = C.ρ r * C.ρ x := fun x hx => by
    rw [hr]
    exact Q0_comm_dblPair _ (by rw [hQeq]; exact hx)
  refine ⟨r, hrp, ⁅Q.comap C.ρ, Q.comap C.ρ⁆, ?_, ?_, hperfY, OtherPairs k i₁ i₂, inferInstance,
    inferInstance, hcard, ?_⟩
  · exact h.commutator_le_fixSub (Q.comap C.ρ) hcommσ
  · have hle := (C.induces_conj r).commutator_le_fixSub (Q.comap C.ρ) hcommr
    rw [fixSub_conj] at hle
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hle hy)
  · let eQ : ↥(alternatingGroup (OtherPairs k i₁ i₂)) ≃* ↥Q :=
      Subgroup.equivMapOfInjective _ f hinj
    let Y : Subgroup K := ⁅Q.comap C.ρ, Q.comap C.ρ⁆
    let ρY : ↥Y →* ↥Q := (C.ρ.comp Y.subtype).codRestrict Q (fun y => by
      have : C.ρ (y : K) ∈ Y.map C.ρ := ⟨y, y.2, rfl⟩
      rwa [hYmap] at this)
    refine ⟨eQ.symm.toMonoidHom.comp ρY, fun a => ?_⟩
    have hmem : (eQ a : Perm (Fin n)) ∈ Y.map C.ρ := by
      rw [hYmap]
      exact (eQ a).2
    obtain ⟨y, hy, hya⟩ := hmem
    refine ⟨⟨y, hy⟩, ?_⟩
    have : ρY ⟨y, hy⟩ = eQ a := Subtype.ext hya
    simp [this]

theorem exists_diag (C : AhatData.CoverSetup n K) {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (hσ : σ * σ = 1) {m : ℕ} (hm : σ.support.card = 2 * m) (hm7 : 7 ≤ m) :
    ∃ r : K, IsPairLift C σ r ∧ ∃ Y : Subgroup K, Y ≤ fixSub α ∧
      (∀ y ∈ Y, y * r = r * y) ∧ ⁅Y, Y⁆ = Y ∧
      ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β), Nat.card β = m - 2 ∧
        ∃ θ : ↥Y →* alternatingGroup β, Function.Surjective θ := by
  obtain ⟨hkn, g, hg, h'⟩ := h.exists_std hσ hm
  obtain ⟨r, hr, Y, hY1, hY2, hY3, β, i1, i2, hβ, θ, hθ⟩ := exists_diag_std (C.conjPerm g) h' hm7
  refine ⟨r, ?_, Y, hY1, hY2, hY3, β, i1, i2, hβ, θ, hθ⟩
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd, hρ⟩ := hr
  have key : ∀ x, σ (g⁻¹ x) = g⁻¹ (stdInv n m hkn x) := fun x => by
    have h1 := congrArg (fun e : Perm (Fin n) => g⁻¹ (e x)) hg
    simpa [Perm.mul_apply] using h1
  have hρr : C.ρ r = swap (g⁻¹ a) (g⁻¹ b) * swap (g⁻¹ c) (g⁻¹ d) := by
    have h1 : (C.conjPerm g).ρ r = g * C.ρ r * g⁻¹ := C.ρ_conjPerm g r
    rw [hρ] at h1
    have h2 : C.ρ r = g⁻¹ * (swap a b * swap c d) * g⁻¹⁻¹ := by
      rw [inv_inv, h1]
      group
    rw [h2, conj_swap_mul_swap]
  refine ⟨g⁻¹ a, g⁻¹ b, g⁻¹ c, g⁻¹ d, g⁻¹.injective.ne hab, g⁻¹.injective.ne hac,
    g⁻¹.injective.ne had, g⁻¹.injective.ne hbc, g⁻¹.injective.ne hbd, g⁻¹.injective.ne hcd, ?_, ?_,
    ?_, ?_, hρr⟩
  · rw [key, ha]
  · rw [key, hb]
  · rw [key, hc]
  · rw [key, hd]

end CFSG.OddStandard.Solomon75
