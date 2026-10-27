module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlphaMain
public import CFSG.GH74.GLS.C3.Layer1.Th2P812

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

theorem false_of_exceptional_Q_le_Pa {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G}
    {K T S : Subgroup G} (hs : Th2Std x y K T S)
    (he7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {T' S' : Subgroup G} {a : G}
    (hw : IsExcA7Witness x K T' S' a)
    (hQ : T' ⊓ CxK x K ≤ (T' ⊓ K).map (MulAut.conj a).toMonoidHom) : False := by
  obtain ⟨e7⟩ := he7
  obtain ⟨z, psi, A⟩ := Th2.AlphaStep.exists_alphaSetup hG hs e7 hw hQ
  obtain ⟨g, hg⟩ := A.exists_conj_x_v hQ
  obtain ⟨hT'C, -, -, hSsyl, hTS, -, -, -, -, hS, -, -, -, -, -⟩ := hw
  have hzx : z * x = x * z := mem_centralizer_singleton_iff.1 (A.T_le_C A.z_mem.1)
  have hTv : T' ≤ centralizer ({z * x} : Set G) := by
    intro t ht
    rw [mem_centralizer_singleton_iff]
    have h1 : z * t = t * z := A.z_central t ht
    have h2 : t * x = x * t := mem_centralizer_singleton_iff.1 (A.T_le_C ht)
    calc t * (z * x) = (t * z) * x := by group
      _ = (z * t) * x := by rw [h1]
      _ = z * (t * x) := by group
      _ = z * (x * t) := by rw [h2]
      _ = (z * x) * t := by group
  have hav : a ∈ centralizer ({z * x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h : a * (z * x) * a⁻¹ = z * x := by
      calc a * (z * x) * a⁻¹ = (a * z * a⁻¹) * (a * x * a⁻¹) := by group
        _ = x * z := by rw [A.hxz, A.hxa]
        _ = z * x := hzx.symm
    calc a * (z * x) = (a * (z * x) * a⁻¹) * a := by group
      _ = (z * x) * a := by rw [h]
  have hSv : S' ≤ centralizer ({z * x} : Set G) := by
    rw [hS]
    exact sup_le hTv (Subgroup.zpowers_le.2 hav)
  exact Th2.AlphaStep.false_of_conj_x_v hT'C hSsyl hTS hg hSv

@[expose] def B_thm2_A7_exc_beta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Is2TerminalU2Triple x y K →
      Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
        ∀ (T' S' : Subgroup G) (a : G), IsExcA7Witness x K T' S' a →
          ¬ (T' ⊓ CxK x K ≤ (T' ⊓ K).map (MulAut.conj a).toMonoidHom) → False

theorem b_thm2_A7_exc_of_beta (h : B_thm2_A7_exc_beta) : B_thm2_A7_exc := by
  intro G _ _ hG x y K T S hs hex
  obtain ⟨h2t, he7, T', S', a, hw⟩ := isExceptionalA7Triple_iff.1 hex
  by_cases hQ : T' ⊓ CxK x K ≤ (T' ⊓ K).map (MulAut.conj a).toMonoidHom
  · exact false_of_exceptional_Q_le_Pa hG hs he7 hw hQ
  · exact h G hG x y K T S hs h2t he7 T' S' a hw hQ

end CFSG.GH74.GLS
