module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7End1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma relIndex_ne_zero_of_finite [Finite G] {H R : Subgroup G} :
    H.relIndex R ≠ 0 := by
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem sec63_pow_two_mem [Finite G] {R H : Subgroup G} (h : H.relIndex R ≤ 2) :
    ∀ r ∈ R, r ^ 2 ∈ R ⊓ H := by
  have hne : H.relIndex R ≠ 0 := relIndex_ne_zero_of_finite
  intro r hr
  have h2 : r ^ 2 ∈ H ⊓ R :=
    Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd (H := H) (K := R) hne hr
      (n := 2) (fun m hm hmle => by
        have hm2 : m ≤ 2 := hmle.trans h
        have : m = 1 ∨ m = 2 := by omega
        rcases this with rfl | rfl <;> norm_num)
  simpa [inf_comm] using h2

theorem sec63_elem_le_of_relIndex [Finite G] {R H : Subgroup G} (hU : IsCyclic ↥(R ⊓ H))
    (h : H.relIndex R ≤ 2) :
    ∀ E : Subgroup G, E ≤ R → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  intro E hER hE
  haveI : IsCyclic ↥(R ⊓ H) := hU
  have hexp : ∀ x ∈ E ⊓ H, x ^ 2 = 1 := fun x hx =>
    hE.2 x (Subgroup.mem_inf.mp hx).1
  have hEH : Nat.card ↥(E ⊓ H) ≤ 2 :=
    sec7End_card_le (H := E ⊓ H) (Q := R ⊓ H) (n := 2)
      (inf_le_inf hER le_rfl) inferInstance (by norm_num) hexp
  have hne : H.relIndex R ≠ 0 := relIndex_ne_zero_of_finite
  have hrel : H.relIndex E ≤ 2 := (Subgroup.relIndex_le_of_le_right hER hne).trans h
  have hcard := Subgroup.relIndex_mul_card (H := H) (K := E)
  calc Nat.card E = H.relIndex E * Nat.card ↥(H ⊓ E) := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hrel (by rw [inf_comm]; exact hEH)
    _ = 4 := by norm_num

theorem sec63_elem_le_of_quot_z4 [Finite G] {R H : Subgroup G} (hU : IsCyclic ↥(R ⊓ H))
    (h : QuotEquivTo R (R ⊓ H) (Multiplicative (ZMod 4))) :
    ∀ E : Subgroup G, E ≤ R → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  intro E hER hE
  obtain ⟨φ, -, hker⟩ := h
  let ψ : ↥E →* Multiplicative (ZMod 4) := φ.comp (Subgroup.inclusion hER)
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hker_le : Nat.card ψ.ker ≤ 2 := by
    haveI : IsCyclic ↥(R ⊓ H) := hU
    have hexp : ∀ x ∈ E ⊓ H, x ^ 2 = 1 := fun x hx =>
      hE.2 x (Subgroup.mem_inf.mp hx).1
    have hEH : Nat.card ↥(E ⊓ H) ≤ 2 :=
      sec7End_card_le (H := E ⊓ H) (Q := R ⊓ H) (n := 2)
        (inf_le_inf hER le_rfl) inferInstance (by norm_num) hexp
    let f : ψ.ker → ↥(E ⊓ H) := fun k =>
      ⟨((k.1 : ↥E) : G), by
        refine Subgroup.mem_inf.mpr ⟨(k.1 : ↥E).2, ?_⟩
        have hk : Subgroup.inclusion hER (k.1 : ↥E) ∈ φ.ker :=
          MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp k.2)
        rw [hker] at hk
        exact (Subgroup.mem_subgroupOf.mp hk).2⟩
    have hf : Function.Injective f := by
      intro k l hkl
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥(E ⊓ H) => (y : G)) hkl
    exact (Nat.card_le_card_of_injective f hf).trans hEH
  have hrange_le : Nat.card ψ.range ≤ 2 := by
    have hexp2 : ∀ x ∈ ψ.range, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [← map_pow]
      have he2 : e ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hE.2 (e : G) e.2
      rw [he2, map_one]
    exact sec7End_card_le (H := ψ.range) (Q := ⊤) le_top inferInstance
      (by norm_num) hexp2
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hker_le hrange_le
    _ = 4 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
