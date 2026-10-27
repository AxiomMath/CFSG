module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

theorem mem_conjugate_iff_conj_mem {H : Subgroup X} {g x : X} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simpa [conjugate, MulAut.conj_symm_apply] using
    (mem_map_equiv (f := MulAut.conj g⁻¹) (K := H) (x := x))

theorem inv_mul_mul_mem_centralizer_of_mem_normalizer {E : Subgroup X} {g x : X}
    (hg : g ∈ normalizer (E : Set X)) (hx : x ∈ centralizer (E : Set X)) :
    g⁻¹ * x * g ∈ centralizer (E : Set X) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro e he
  have hge : g * e * g⁻¹ ∈ E := (mem_normalizer_iff.mp hg e).mp he
  have hcomm := hx _ hge
  calc e * (g⁻¹ * x * g) = g⁻¹ * ((g * e * g⁻¹) * x) * g := by group
    _ = g⁻¹ * (x * (g * e * g⁻¹)) * g := by rw [hcomm]
    _ = g⁻¹ * x * g * e := by group

theorem abelian_p_subgroup_normalizer_preserves_sylow_power_counts [Finite X] {p : ℕ}
    [Fact p.Prime] {E P : Subgroup X} (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEp : IsPGroup p E)
    (hP : ∃ Q : Sylow p (centralizer (E : Set X)),
      (Q : Subgroup (centralizer (E : Set X))).map (centralizer (E : Set X)).subtype = P) :
    E ≤ (center P).map P.subtype ∧
    (∀ g ∈ normalizer (E : Set X), ∃ c ∈ centralizer (E : Set X),
      conjugate P (g * c) = P ∧ ∀ e ∈ E, (g * c)⁻¹ * e * (g * c) = g⁻¹ * e * g) ∧
    (∀ d : ℕ, ∀ g ∈ normalizer (E : Set X), ∀ e ∈ E,
      Nat.card {x : X // x ∈ P ∧ x ^ d = e} =
        Nat.card {x : X // x ∈ P ∧ x ^ d = g⁻¹ * e * g}) ∧
    (∀ d : ℕ, ∀ e ∈ E, ∀ e' ∈ E,
      Nat.card {x : X // x ∈ P ∧ x ^ d = e} ≠ Nat.card {x : X // x ∈ P ∧ x ^ d = e'} →
        ∀ g ∈ normalizer (E : Set X), g⁻¹ * e * g ≠ e') := by
  set C := centralizer (E : Set X) with hCdef
  obtain ⟨Q, hQP⟩ := hP
  have hPC : P ≤ C := hQP ▸ map_subtype_le _
  have hEC : E ≤ C := fun x hx => mem_centralizer_iff.mpr fun y hy => hEcomm y hy x hx
  have hEnormal : (E.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hcomm := mem_centralizer_iff.mp c.2 n hn
    have : ((c * n * c⁻¹ : C) : X) = n := by
      simp only [coe_mul, coe_inv]
      rw [← hcomm, mul_inv_cancel_right]
    rw [this]
    exact hn
  have hEpC : IsPGroup p (E.subgroupOf C) := hEp.of_equiv (subgroupOfEquivOfLe hEC).symm
  have hEQ : E.subgroupOf C ≤ Q := hEpC.le_sylow_of_normal Q
  have hEP : E ≤ P := by
    intro e he
    rw [← hQP]
    exact ⟨⟨e, hEC he⟩, hEQ he, rfl⟩
  have hcardConj : ∀ g : X, Nat.card (conjugate P g) = Nat.card P := fun g =>
    (Nat.card_congr ((MulAut.conj g⁻¹).subgroupMap P).toEquiv).symm
  have hconj : ∀ g ∈ normalizer (E : Set X), ∃ c ∈ C,
      conjugate P (g * c) = P ∧ ∀ e ∈ E, (g * c)⁻¹ * e * (g * c) = g⁻¹ * e * g := by
    intro g hg
    have hPg : conjugate P g ≤ C := by
      intro x hx
      rw [mem_conjugate_iff_conj_mem] at hx
      have h := inv_mul_mul_mem_centralizer_of_mem_normalizer hg (hPC hx)
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
    have hcardQ : Nat.card (Q : Subgroup C) = Nat.card P := by
      rw [← hQP]
      exact Nat.card_congr ((Q : Subgroup C).equivMapOfInjective _ C.subtype_injective).toEquiv
    let Q' : Sylow p C := Sylow.ofCard ((conjugate P g).subgroupOf C) (by
      rw [← Sylow.card_eq_multiplicity Q, hcardQ, ← hcardConj g]
      exact Nat.card_congr (subgroupOfEquivOfLe hPg).toEquiv)
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q' Q
    refine ⟨(c⁻¹ : C), (c⁻¹ : C).2, ?_, ?_⟩
    · apply Subgroup.eq_of_le_of_card_ge _ (hcardConj _).ge
      intro x hx
      rw [mem_conjugate_iff_conj_mem] at hx
      set y := g * ((c⁻¹ : C) : X) * x * (g * ((c⁻¹ : C) : X))⁻¹ with hydef
      have hyg : g⁻¹ * y * g ∈ conjugate P g := by
        rw [mem_conjugate_iff_conj_mem, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
        exact hx
      have hmem : (⟨g⁻¹ * y * g, hPg hyg⟩ : C) ∈ (Q' : Subgroup C) := by
        change _ ∈ (conjugate P g).subgroupOf C
        exact hyg
      have hsmul := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) (Q' : Subgroup C) hmem
      rw [← Sylow.coe_subgroup_smul, hc] at hsmul
      have hP' : ((MulAut.conj c • (⟨g⁻¹ * y * g, hPg hyg⟩ : C) : C) : X) ∈ P := by
        rw [← hQP]
        exact ⟨_, hsmul, rfl⟩
      convert hP' using 1
      simp only [hydef, MulAut.smul_def, MulAut.conj_apply, coe_mul, coe_inv]
      group
    · intro e he
      have hge : g⁻¹ * e * g ∈ E := (mem_normalizer_iff''.mp hg e).mp he
      have hcomm := mem_centralizer_iff.mp c.2 _ hge
      calc (g * ((c⁻¹ : C) : X))⁻¹ * e * (g * ((c⁻¹ : C) : X))
          = (c : X) * (g⁻¹ * e * g) * (c : X)⁻¹ := by simp only [coe_inv]; group
        _ = (g⁻¹ * e * g) * c * (c : X)⁻¹ := by rw [← hcomm]
        _ = g⁻¹ * e * g := by group
  have hcount : ∀ d : ℕ, ∀ g ∈ normalizer (E : Set X), ∀ e ∈ E,
      Nat.card {x : X // x ∈ P ∧ x ^ d = e} =
        Nat.card {x : X // x ∈ P ∧ x ^ d = g⁻¹ * e * g} := by
    intro d g hg e he
    obtain ⟨c, -, hPc, hEc⟩ := hconj g hg
    set h := g * c
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (MulAut.conj h⁻¹).toEquiv fun x => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    rw [← hEc e he]
    have hmem : x ∈ P ↔ h⁻¹ * x * h ∈ P := by
      conv_rhs => rw [← hPc, mem_conjugate_iff_conj_mem,
        show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
    have hpow : (h⁻¹ * x * h) ^ d = h⁻¹ * x ^ d * h := by
      have := map_pow (MulAut.conj h⁻¹) x d
      simpa only [MulAut.conj_apply, inv_inv] using this.symm
    rw [hpow, ← hmem]
    refine and_congr_right fun _ => ⟨fun hx => by rw [hx], fun hx => ?_⟩
    calc x ^ d = h * (h⁻¹ * x ^ d * h) * h⁻¹ := by group
      _ = h * (h⁻¹ * e * h) * h⁻¹ := by rw [hx]
      _ = e := by group
  refine ⟨?_, hconj, hcount, ?_⟩
  · intro e he
    refine ⟨⟨e, hEP he⟩, ?_, rfl⟩
    change _ ∈ center P
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hPC x.2) e he).symm
  · intro d e he e' _ hne g hg hge
    apply hne
    rw [hcount d g hg e he, hge]

end CFSG.ComponentClassification.UnbalancedGS
