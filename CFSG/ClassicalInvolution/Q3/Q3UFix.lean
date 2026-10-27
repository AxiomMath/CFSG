module

public import CFSG.ClassicalInvolution.Q3.Q3UBasic
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Diagonal

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.LocalCores CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Fix

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem commute_of_ne_isComponent {A B : Subgroup Y} (hA : IsComponent A) (hB : IsComponent B)
    (hne : A ≠ B) {a b : Y} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((distinct_components_commute hA hB).resolve_left hne) ha) b hb).symm

omit [Finite Y] in
theorem not_forall_commute_of_isComponent {A : Subgroup Y} (hA : IsComponentOf A ⊤) :
    ¬ ∀ x ∈ A, ∀ a ∈ A, a * x = x * a := by
  intro hcomm
  have hcen : Subgroup.center A = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hcomm (a : Y) a.2 (b : Y) b.2)
  have hone : ∀ x : A ⧸ Subgroup.center A, x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a => exact (QuotientGroup.eq_one_iff a).mpr (hcen ▸ Subgroup.mem_top a)
  obtain ⟨x, y, hxy⟩ := @exists_pair_ne _ hA.2.2.2.toNontrivial
  exact hxy ((hone x).trans (hone y).symm)

theorem IsClassicalMember3.conjSub_mem_pair (h : IsClassicalMember3 L z) {A : Subgroup Y}
    (hA : IsComponentOf A ⊤) (hne : conjSub z A ≠ A) {k : Y} (hk : k ∈ L) :
    conjSub k A = A ∨ conjSub k A = conjSub z A := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.sq_eq_one
  have hAc : IsComponent A := (isComponent_iff_open A).mpr hA
  obtain ⟨Δ, hΔC, hΔcomp, hdiag⟩ :=
    CFSG.ClassicalInvolution.Balance.LocalBalance.exists_diagonal_component hAc hzz hne
  have hΔ' := (isComponent_iff_open _).mp hΔcomp
  have hLΔ := h.le_centralizer_of_isComponentOf_centralizer hΔC hΔ'
  by_contra hcon
  push Not at hcon
  obtain ⟨hB1, hB2⟩ := hcon
  have hA'c : IsComponent (conjSub z A) := isComponent_map_mulEquiv (MulAut.conj z) hAc
  have hBc : IsComponent (conjSub k A) := isComponent_map_mulEquiv (MulAut.conj k) hAc
  have hB'c : IsComponent (conjSub z (conjSub k A)) :=
    isComponent_map_mulEquiv (MulAut.conj z) hBc
  have hB'A : conjSub z (conjSub k A) ≠ A := by
    intro e
    apply hB2
    calc conjSub k A = conjSub z (conjSub z (conjSub k A)) := by
          rw [← conjSub_mul, hzz, conjSub_one]
      _ = conjSub z A := by rw [e]
  have hkz : k * z = z * k := h.commute_involution hk
  apply not_forall_commute_of_isComponent hA
  intro x hx a ha
  have hdΔ := hdiag x hx
  have hdk : (x * (z * x * z⁻¹)) * k = k * (x * (z * x * z⁻¹)) :=
    Subgroup.mem_centralizer_iff.mp (hLΔ hk) _ hdΔ
  have hconj : z * (k * x * k⁻¹) * z⁻¹ = k * (z * x * z⁻¹) * k⁻¹ := by
    calc z * (k * x * k⁻¹) * z⁻¹ = (z * k) * x * (z * k)⁻¹ := by group
      _ = (k * z) * x * (k * z)⁻¹ := by rw [hkz]
      _ = k * (z * x * z⁻¹) * k⁻¹ := by group
  have hd' : x * (z * x * z⁻¹) = k * (x * (z * x * z⁻¹)) * k⁻¹ := by
    rw [← hdk]
    group
  have hdecomp : x * (z * x * z⁻¹) = (k * x * k⁻¹) * (z * (k * x * k⁻¹) * z⁻¹) := by
    calc x * (z * x * z⁻¹) = k * (x * (z * x * z⁻¹)) * k⁻¹ := hd'
      _ = (k * x * k⁻¹) * (k * (z * x * z⁻¹) * k⁻¹) := by group
      _ = (k * x * k⁻¹) * (z * (k * x * k⁻¹) * z⁻¹) := by rw [hconj]
  have hb : k * x * k⁻¹ ∈ conjSub k A := conj_mem_conjSub hx
  have hb' : z * (k * x * k⁻¹) * z⁻¹ ∈ conjSub z (conjSub k A) := conj_mem_conjSub hb
  have hw : z * x * z⁻¹ ∈ conjSub z A := conj_mem_conjSub hx
  have h1 : a * (k * x * k⁻¹) = (k * x * k⁻¹) * a :=
    commute_of_ne_isComponent hAc hBc (fun e => hB1 e.symm) ha hb
  have h2 : a * (z * (k * x * k⁻¹) * z⁻¹) = (z * (k * x * k⁻¹) * z⁻¹) * a :=
    commute_of_ne_isComponent hAc hB'c (fun e => hB'A e.symm) ha hb'
  have h3 : a * (z * x * z⁻¹) = (z * x * z⁻¹) * a :=
    commute_of_ne_isComponent hAc hA'c (fun e => hne e.symm) ha hw
  have key : a * (x * (z * x * z⁻¹)) = (x * (z * x * z⁻¹)) * a := by
    rw [hdecomp, ← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  apply mul_right_cancel (b := z * x * z⁻¹)
  calc a * x * (z * x * z⁻¹) = a * (x * (z * x * z⁻¹)) := mul_assoc _ _ _
    _ = (x * (z * x * z⁻¹)) * a := key
    _ = x * ((z * x * z⁻¹) * a) := mul_assoc _ _ _
    _ = x * (a * (z * x * z⁻¹)) := by rw [h3]
    _ = x * a * (z * x * z⁻¹) := (mul_assoc _ _ _).symm

theorem IsClassicalMember3.conjSub_eq_of_isComponent (h : IsClassicalMember3 L z)
    {A : Subgroup Y} (hA : IsComponentOf A ⊤) : conjSub z A = A := by
  by_contra hne
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.sq_eq_one
  obtain ⟨u, huL, hu2⟩ := h.exists_sq_eq
  have huz : u * z = z * u := h.commute_involution huL
  have hzu : conjSub z A = conjSub u (conjSub u A) := by
    rw [← conjSub_mul, ← pow_two, hu2]
  have hcc : ∀ K : Subgroup Y, conjSub u (conjSub z K) = conjSub z (conjSub u K) := by
    intro K
    rw [← conjSub_mul, ← conjSub_mul, huz]
  have hzzA : conjSub z (conjSub z A) = A := by rw [← conjSub_mul, hzz, conjSub_one]
  rcases h.conjSub_mem_pair hA hne huL with hu | hu
  · apply hne
    rw [hzu, hu, hu]
  · apply hne
    calc conjSub z A = conjSub u (conjSub u A) := hzu
      _ = conjSub u (conjSub z A) := by rw [hu]
      _ = conjSub z (conjSub u A) := hcc A
      _ = conjSub z (conjSub z A) := by rw [hu]
      _ = A := hzzA

theorem IsClassicalMember3.mem_normalizer_of_isComponent (h : IsClassicalMember3 L z)
    {A : Subgroup Y} (hA : IsComponentOf A ⊤) : z ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hAeq := h.conjSub_eq_of_isComponent hA
  have e := mem_conjSub_iff (n := z) (K := A) (x := z * y * z⁻¹)
  rw [hAeq, show z⁻¹ * (z * y * z⁻¹) * z = y by group] at e
  exact e.symm

end Fix

end CFSG.ClassicalInvolution.Q3
