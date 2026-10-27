module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec

theorem Ivk93Cfg2.exists_pgl {F : Type} [Field F] [Finite F] {n : ℕ}
    {x : StatedProj (StatedSL n F)} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup (StatedProj (StatedSL n F))} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    ∃ A : GL (Fin n) F, CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A ∧
      Matrix.ProjGenLinGroup.mk A ≠ 1 ∧ Matrix.ProjGenLinGroup.mk A ^ 2 = 1 ∧
      ∃ L₁' L₂' : Subgroup (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _)),
        IsPComponent 2 L₁' ∧ IsPComponent 2 L₂' ∧ L₁' ≠ L₂' := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have := projToPGL_range_normal n F
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ x)
  have hx2 : x ^ 2 = 1 := by rw [← h.ord, pow_orderOf_eq_one]
  refine ⟨A, hA.symm, ?_, ?_, ?_⟩
  · rw [hA]
    intro h1
    have h2 : x = 1 := hφ (h1.trans (map_one φ).symm)
    exact h.ne_one h2
  · rw [hA, ← map_pow, hx2, map_one]
  obtain ⟨-, hK⟩ := isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2
  obtain ⟨hK'le, hK'⟩ := isPComponent_map_of_normal φ hφ h.le₂ h.comp₂.2
  have hKle : L₁.map φ ≤ centralizer ({φ x} : Set _) :=
    (isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2).1
  rw [← hA] at hK hK' hKle hK'le
  refine ⟨_, _, hK, hK', fun heq => h.ne ?_⟩
  have h1 := subgroupOf_inj.mp heq
  rw [inf_of_le_left hKle, inf_of_le_left hK'le] at h1
  exact map_injective hφ h1

theorem ivk93_l32 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93Empty2 (fun X _ => LieModel X .PSL 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ x hx q₁ q₂ L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Finite (StatedProj (StatedSL 3 F)) := Finite.of_equiv _ e.toEquiv
  obtain ⟨A, -, hne, hinv, L₁', L₂', h₁, h₂, hL⟩ := (h.of_equiv e).exists_pgl
  obtain ⟨r, s, hr, hs, hrs⟩ := split_of_two_pComponents h2 (by norm_num) A hne hinv h₁ h₂ hL
  omega

end CFSG.GH74.GLS.IVK.Proofs2
