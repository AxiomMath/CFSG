module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61Wrap

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_prop64_rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B →
      ∀ (b : G) (J : Subgroup G), Th2.Obs.Obstr52 B b J →
        Nonempty (kBar J ≃* alternatingGroup (Fin 7)) → Nonempty (kBar K ≃* alternatingGroup (Fin 7))

theorem isWeakKBal_two_of_prop64
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h64 : B_prop64_rank4) {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G}
    {K T S : Subgroup G} (h : Th2Std x y K T S)
    (hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) : IsWeakKBal 2 B := by
  by_contra hweak
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  obtain ⟨b, J, hobs⟩ := Th2.Obs.exists_obstr52 hGKF hE2 hL34 hG hE hweak
  have hA7 : Nonempty (kBar J ≃* alternatingGroup (Fin 7)) :=
    hobs.nonempty_A7_of_rank_four hG.pRank_eq_four.le hE.2.1
  exact hnotA7 (h64 G hG x y K T S h B hB b J hobs hA7)

theorem b_cor67_of_prop64
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h64 : B_prop64_rank4) : B_cor67 := by
  intro G _ _ hG x y K T S h hq B hB
  exact isWeakKBal_two_of_prop64 hGKF hE2 hL34 h64 hG h (not_nonempty_A7_of_hasL2Model hq) hB

theorem b_cor614_of_prop64
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h64 : B_prop64_rank4) : B_cor614 := by
  intro G _ _ hG x y K T S h hq _ B hB
  exact isWeakKBal_two_of_prop64 hGKF hE2 hL34 h64 hG h (not_nonempty_A7_of_hasL2Model hq) hB

end CFSG.GH74.GLS
