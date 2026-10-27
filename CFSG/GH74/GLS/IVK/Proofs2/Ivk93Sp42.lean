module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open scoped MatrixGroups

theorem ivk93_psp_four2_fst {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {x : StatedProj (StatedSp 2 F)} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (StatedProj (StatedSp 2 F))}
    (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : Nonempty (SL(2, F) ≃* ↥L₁) ∧ 5 ≤ Nat.card F := by
  classical
  have h2 := CatFactsSp4.two_ne_zero_of_odd_card hodd
  obtain ⟨g, hg⟩ := CatFactsSp4.exists_conj_of_orderOf_eq_two hodd h.ord
  set φ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹ with hφ
  have hφx : φ x = g⁻¹ * x * g := by simp [hφ]
  have hC : (centralizer ({x} : Set _)).map φ.toMonoidHom = centralizer ({g⁻¹ * x * g} : Set _) :=
    by rw [map_centralizer_singleton_equiv', hφx]
  have hK1 : IsPComponent 2 ((L₁.map φ.toMonoidHom).subgroupOf (centralizer {g⁻¹ * x * g})) := by
    rw [← hC]
    exact (isPComponent_subgroupOf_map_iff' φ h.le₁).mp h.comp₁.2
  have hK2 : IsPComponent 2 ((L₂.map φ.toMonoidHom).subgroupOf (centralizer {g⁻¹ * x * g})) := by
    rw [← hC]
    exact (isPComponent_subgroupOf_map_iff' φ h.le₂).mp h.comp₂.2
  have hle1 : L₁.map φ.toMonoidHom ≤ centralizer {g⁻¹ * x * g} := hC ▸ map_mono h.le₁
  have hle2 : L₂.map φ.toMonoidHom ≤ centralizer {g⁻¹ * x * g} := hC ▸ map_mono h.le₂
  have eK : ↥L₁ ≃* ↥(L₁.map φ.toMonoidHom) := L₁.equivMapOfInjective _ φ.injective
  rcases hg with hg | hg
  · rw [hg] at hK1 hle1
    obtain ⟨hcases, h5⟩ := CatFactsSp4.pComponent_centralizer_u1 hodd hle1 hK1
    rcases hcases with h' | h'
    · exact ⟨⟨(CatFactsSp4.E1Equiv h2).trans ((MulEquiv.subgroupCongr h'.symm).trans eK.symm)⟩, h5⟩
    · exact ⟨⟨(CatFactsSp4.E2Equiv h2).trans ((MulEquiv.subgroupCongr h'.symm).trans eK.symm)⟩, h5⟩
  · exfalso
    rw [hg] at hK1 hK2 hle1 hle2
    have h1 := (CatFactsSp4.pComponent_centralizer_u2 hodd hle1 hK1).1
    have h2' := (CatFactsSp4.pComponent_centralizer_u2 hodd hle2 hK2).1
    exact h.ne (Subgroup.map_injective φ.injective (h1.trans h2'.symm))

theorem ivk93_psp_four2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {x : StatedProj (StatedSp 2 F)} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (StatedProj (StatedSp 2 F))}
    (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    Nonempty (SL(2, F) ≃* ↥L₁) ∧ Nonempty (SL(2, F) ≃* ↥L₂) ∧ 5 ≤ Nat.card F := by
  obtain ⟨e₁, h5⟩ := ivk93_psp_four2_fst hodd h
  obtain ⟨e₂, -⟩ := ivk93_psp_four2_fst hodd h.symm
  exact ⟨e₁, e₂, h5⟩

theorem ivk93_sp42 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93Eq2 (fun X _ => LieModel X .PSp 2 p f) (p ^ f) := by
  intro p f hp hp2 hf J _ _ hJ x hx q₁ q₂ L₁ L₂ h
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h' := h.of_equiv e
  obtain ⟨⟨eS₁⟩, ⟨eS₂⟩, h5⟩ := ivk93_psp_four2 hodd h'
  have e₁ := h'.q_eq_of_equiv_sl2 hodd h5 eS₁
  have e₂ := h'.q_eq_of_equiv_sl2' hodd h5 eS₂
  rw [← hF]
  exact ⟨e₁, e₂⟩

end CFSG.GH74.GLS.IVK.Proofs2
