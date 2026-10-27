module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Sl2Fin
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4C
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4D

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X : Subgroup A}

theorem prop4_3E_core (F : E4Hyp G z k) (hOut : L34DiagClosure) {c : E4Ctx G z A a p X}
    (hN : ⁅layer A, X⁆ ≠ ⊥) : Concl43E k a p X := by
  obtain ⟨J, hJ, hJX⟩ := exists_comp_comm_ne hN
  have hX : ∀ J' : Subgroup A, IsComponent J' → X ≤ normalizer (J' : Set A) := fun J' hJ' =>
    X_le_normalizer_comp c.A4.prime c.A4.odd c.A4.pgroup hJ'
      (fun J₁ J₂ J₃ => F.two A a c.sec J₁ J₂ J₃)
  have hXJ : X ≤ normalizer (J : Set A) := hX J hJ
  have haJ : a ∈ normalizer (J : Set A) := by
    by_contra hna
    have hJ₂ : IsComponent (J.map (MulAut.conj a).toMonoidHom) := isComponent_conj hJ a
    have hne : J ≠ J.map (MulAut.conj a).toMonoidHom := fun h =>
      hna (mem_normalizer_of_map_conj_eq' h.symm)
    have hcomp2 : ∀ J₃ : Subgroup A, IsComponent J₃ →
        J₃ = J ∨ J₃ = J.map (MulAut.conj a).toMonoidHom := by
      intro J₃ h3
      by_contra hcon
      push Not at hcon
      exact F.two A a c.sec J (J.map (MulAut.conj a).toMonoidHom) J₃ hJ hJ₂ h3 hne hcon.1.symm
        hcon.2.symm
    have hlayer : layer A = J ⊔ J.map (MulAut.conj a).toMonoidHom := by
      apply le_antisymm
      · refine sSup_le fun J₃ h3 => ?_
        rcases hcomp2 J₃ h3 with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_sSup hJ) (le_sSup hJ₂)
    have hnorm : (J ⊔ J.map (MulAut.conj a).toMonoidHom).Normal := by
      have hc := CFSG.LocalCores.layer_characteristic (G := A)
      rw [← hlayer]
      infer_instance
    exact swap_false c.A4.prime c.A4.odd c.A4.pgroup c.z2 (fun g hg => c.inv g hg) c.op hJ hJ₂ hne
      hnorm hXJ (hX _ hJ₂) rfl hJX
  let d : SubData c J := ⟨hJ, hXJ, haJ, hJX⟩
  have hcompSl : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J) →
      ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J := by
    intro hsl J' hJ' hJ'K
    by_contra hne
    exact sl2_two F d hsl hJ' (Ne.symm hne) hJ'K
  rcases d.cases F with ha | hb | hc' | hd
  · rcases sl2_final F d (Or.inl ha) (hcompSl (Or.inl ha)) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases sl2_final F d (Or.inr hb) (hcompSl (Or.inr hb)) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl (case_c F d hc'))
  · exact Or.inr (Or.inr (Or.inl (case_d F hOut d hd)))

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
