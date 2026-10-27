module

public import CFSG.Adapters.TauCetiExceptional.BigCellEndgame

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

@[expose] def DiagFieldNormalForm (τ : Tag) (E : Type) [Field E] : Prop :=
  ∀ α : MulAut (adjointGroup τ E), ∃ (g : adjointGroup τ E) (a : Fin τ.rank → Eˣ)
    (σ : E ≃+* E), ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (g : ModGL τ E) * rootDiagUnit τ a * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ E) *
        (rootDiagUnit τ a)⁻¹ * (g : ModGL τ E)⁻¹

theorem baseChangeGL_rootDiagUnit
    {K L : Type} [Field K] [Field L] (f : K →+* L)
    (a : Fin τ.rank → Kˣ) :
    baseChangeGL f (rootDiagUnit τ a) = rootDiagUnit τ fun k => Units.map f.toMonoidHom (a k) := by
  refine Units.ext ((natMat τ L).injective ?_)
  rw [natMat_rootDiagUnit, ← mapMatrix_charDiag, ← natMat_rootDiagUnit]
  exact natMat_of_baseChange (baseChange_baseChangeEnd f _)

theorem mem_adjointGroup_of_diag_entrywise
    {L : Type} [Field L] [IsAlgClosed L]
    (hτ : τ ≠ .G2) (h2 : (2 : L) ≠ 0) (E : Subfield L) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) {H : Subgroup (ModGL τ L)}
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) (g : adjointGroup τ E) (a : Fin τ.rank → Eˣ)
    (α : MulAut (adjointGroup τ E))
    (hα : ∀ x : adjointGroup τ E,
      baseChangeGL E.subtype (α x : ModGL τ E) = h * baseChangeGL E.subtype (x : ModGL τ E) * h⁻¹)
    (hgσ : ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (g : ModGL τ E) * rootDiagUnit τ a * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ E) *
        (rootDiagUnit τ a)⁻¹ * (g : ModGL τ E)⁻¹) :
    h ∈ adjointGroup τ L := by
  set g' : ModGL τ L := baseChangeGL E.subtype ((g : ModGL τ E) * rootDiagUnit τ a) with hg'
  have hgL : g' ∈ adjointGroup τ L := by
    rw [hg', map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (map_baseChangeGL_adjointGroup_le E.subtype
      (Subgroup.mem_map.2 ⟨(g : ModGL τ E), g.2, rfl⟩))
      (exceptional_Lang_adjoint_diagonal_lift τ L _).1
  have hh' : g'⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hCH hgL)) hh
  have hσ : ∀ x ∈ adjointGroup τ E, g'⁻¹ * h * baseChangeGL E.subtype x * (g'⁻¹ * h)⁻¹ =
      baseChangeGL E.subtype (Units.map (entrywiseHom σ.toRingHom) x) := by
    intro x hx
    have e : g'⁻¹ * h * baseChangeGL E.subtype x * (g'⁻¹ * h)⁻¹ =
        g'⁻¹ * (h * baseChangeGL E.subtype x * h⁻¹) * g' := by group
    rw [e, ← hα ⟨x, hx⟩, hgσ ⟨x, hx⟩, hg', ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hmem := mem_adjointGroup_of_conj_entrywise hτ h2 E σ t ht _ (hH _ hh') hσ
  have e : h = g' * (g'⁻¹ * h) := by group
  rw [e]
  exact mul_mem hgL hmem

section Endgame

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_of_diagNormalForm
    (hτ : τ ≠ .G2) (hp2 : p ≠ 2)
    (hNF : ∀ k, k ≠ 0 → DiagFieldNormalForm τ (frobeniusFixedSubfield L p k))
    (H : Subgroup (ModGL τ L)) (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0) :
    H ≤ adjointGroup τ L := by
  intro h hh
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut hp2 H hCH hH hh
  obtain ⟨g, a, σ, hgσ⟩ := hNF k hk α
  exact mem_adjointGroup_of_diag_entrywise hτ (two_ne_zero_of_charP hp2) _ σ t ht hCH hH hh g
    a α hα hgσ

end Endgame

theorem diagFieldNormalForm_E7_E8
    (hτ : τ = .E7 ∨ τ = .E8) (E : Type) [Field E] [Finite E] :
    DiagFieldNormalForm τ E := fun α => by
  obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form τ (Or.inr hτ) E).2.2 α
  refine ⟨g, a, σ, fun x => ?_⟩
  have hQ : exactQ τ E ε = 1 := by
    rcases hτ with rfl | rfl <;> rfl
  rw [hα x, hQ, mul_one, inv_one, mul_one]

section E8

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_E8
    (hp2 : p ≠ 2) (H : Subgroup (ModGL .E8 L))
    (hCH : adjointGroup .E8 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .E8 P →
      evalMat (natMat .E8 L (h : Module.End L (RootModule .E8 L))) P = 0) :
    H ≤ adjointGroup .E8 L :=
  le_adjointGroup_of_diagNormalForm (by decide) hp2 (fun k hk => by
    have := finite_frobeniusFixedSubfield L p k hk
    exact diagFieldNormalForm_E7_E8 (Or.inr rfl) _) H hCH hH

end E8

end CFSG.TauCetiBridge.BigCell
