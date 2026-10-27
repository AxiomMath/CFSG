module

public import CFSG.GH74.Uniqueness.Section6Defs
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Cor5

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
private theorem conjugate_centralizer_singleton_eq (s g : X) :
    conjugate (centralizer ({s} : Set X)) g = centralizer ({g⁻¹ * s * g} : Set X) := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * (g⁻¹ * s * g) = g⁻¹ * ((g * x * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * x * g⁻¹)) * g := by rw [hx]
      _ = (g⁻¹ * s * g) * x := by group
  · intro hx
    calc (g * x * g⁻¹) * s = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by rw [hx]
      _ = s * (g * x * g⁻¹) := by group

theorem IsProductDisconnected.inf_conjugate_eq_inf_centralizer (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hT4b : Theorem4bStmt Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M) :
    M ⊓ β ⊓ conjugate β z = (M ⊓ β) ⊓ centralizer ({z} : Set X) := by
  set D := M ⊓ β with hD
  set E := D ⊓ conjugate β z with hE
  have hED : E ≤ D := inf_le_left
  have hEM : E ≤ M := hED.trans inf_le_left
  have hEβ : E ≤ β := hED.trans inf_le_right
  have hCE : D ⊓ centralizer ({z} : Set X) ≤ E := by
    intro c hc
    obtain ⟨hcD, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hcD, mem_conjugate_iff.mpr ?_⟩
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have e : z * c * z⁻¹ = c := by rw [← hcz]; group
    rw [e]
    exact (Subgroup.mem_inf.mp hcD).2
  refine le_antisymm ?_ hCE
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hzE : z ∈ normalizer (E : Set X) := by
    rw [hE, hD, inf_assoc]
    exact mem_normalizer_inf (Subgroup.le_normalizer hzM)
      (mem_normalizer_inf_conjugate (M := β) hz2)
  have hzW : z ∈ normalizer (pPrimeCoreIn E : Set X) := mem_normalizer_pPrimeCoreIn hzE
  have hWE : pPrimeCoreIn E ≤ E := pPrimeCoreIn_le E
  have hcomm : ∀ w ∈ pPrimeCoreIn E, z * w = w * z := by
    rcases hT4b z hz hzM (pPrimeCoreIn E) (odd_card_pPrimeCoreIn E) (hWE.trans hEM) hzW with
      hc | hc
    · exact hc
    · exact absurd (hc β (h.mem_omegaFix_iff.mpr ⟨hβ, hWE.trans hEβ⟩)) hβM
  intro x hxE
  refine Subgroup.mem_inf.mpr ⟨hED hxE, ?_⟩
  have hxD : x ∈ ((M ⊓ β : Subgroup X) : Set X) := hED hxE
  rw [(h.prop38d hZ hz hzM hβ hβM).1] at hxD
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hxD
  have hcE : c ∈ E := hCE hc
  have haE : a ∈ E := by
    have := E.mul_mem hxE (E.inv_mem hcE)
    simpa using this
  have haW : a ∈ pPrimeCoreIn E := by
    refine le_pPrimeCoreIn (N := E ⊓ pPrimeCoreIn D) (D := E) inf_le_left ?_ ?_
      (Subgroup.mem_inf.mpr ⟨haE, ha⟩)
    · intro e he
      exact mem_normalizer_inf (Subgroup.le_normalizer he) (pPrimeCoreIn_normalizes D (hED he))
    · exact Odd.of_dvd_nat (odd_card_pPrimeCoreIn D) (Subgroup.card_dvd_of_le inf_le_right)
  have haz : z * a = a * z := hcomm a haW
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc a * c * z = a * (c * z) := by rw [mul_assoc]
    _ = a * (z * c) := by rw [hcz]
    _ = (a * z) * c := by rw [mul_assoc]
    _ = (z * a) * c := by rw [haz]
    _ = z * (a * c) := by rw [mul_assoc]

theorem ZDSetup.cor5 (S : ZDSetup X Z M) (hT4 : Theorem4Stmt Z M) (h61 : Lemma61aStmt Z M) :
    Cor5Stmt Z M := by
  refine ⟨h61 hT4.1, ?_⟩
  rintro γ δ s ⟨hγ, hδ, hs, hsγ, hγδ⟩
  have hZ := S.invariant
  have h := S.prodDisc
  obtain ⟨g, hg⟩ := exists_conjugate_eq_base hγ
  have hzZ : g⁻¹ * s * g ∈ Z := hZ.2 s hs g
  have hzM : g⁻¹ * s * g ∈ M := by
    rw [← hg, mem_conjugate_iff]
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rw [e]
    exact (h.conjugate_eq_iff_mem hγ).mp hsγ
  have hδ' : conjugate δ g ∈ omega M := conjugate_mem_omega hδ g
  have hδ'M : conjugate δ g ≠ M := fun heq => hγδ (conjugate_injective g (hg.trans heq.symm))
  have hbase := h.inf_conjugate_eq_inf_centralizer hZ hT4.2 hzZ hzM hδ' hδ'M
  have e : conjugate (conjugate δ s) g = conjugate (conjugate δ g) (g⁻¹ * s * g) := by
    rw [conjugate_conjugate, conjugate_conjugate]
    congr 1
    group
  apply conjugate_injective g
  show conjugate (γ ⊓ δ ⊓ conjugate δ s) g = conjugate ((γ ⊓ δ) ⊓ centralizer ({s} : Set X)) g
  simp only [conjugate_inf, hg, conjugate_centralizer_singleton_eq]
  rw [e]
  exact hbase

end Cor5

end CFSG.GH74.Uniqueness
