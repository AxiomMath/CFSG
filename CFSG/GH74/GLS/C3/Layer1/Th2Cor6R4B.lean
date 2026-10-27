module

public import CFSG.GH74.GLS.C3.Layer1.Th2Cor6R4
public import CFSG.GH74.GLS.C3.Layer1.Th2L625c2

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

variable {G : Type} [Group G] [Finite G]

theorem Obstr52.exists_isUnbalancingTriple {B : Subgroup G} {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    ∃ d ∈ B, IsUnbalancingTriple b d J := by
  obtain ⟨D, hD⟩ := h.exists_D
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  have hDk : 2 ^ 2 ≤ Nat.card ↥D := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hD.D_el]
    exact Nat.pow_le_pow_right (by norm_num) hD.D_rank
  obtain ⟨d, hdD, hd1⟩ := Bal.exists_ne_one_of_two_pow_le (k := 2) (by norm_num) hDk
  have hdB : d ∈ B := hD.D_le hdD
  have hd2 : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq d hdB) hd1
  refine ⟨d, hdB, ⟨hb2, h.comp⟩, hd2, mem_centralizer_singleton_iff.2 (hBc d hdB b h.mem),
    hD.D_norm d hdD, ?_⟩
  intro hle
  obtain ⟨c, hcX, hcmove⟩ := hD.X_move
  have hcY : c ∈ AG D ⊓ centralizer ({b} : Set G) :=
    commutator_le_Y hB hD.D_le h.mem hcX
  exact hcmove (hle ⟨AG_le_pPrimeCoreOf hdD hd1 hcY.1, hcY.2⟩)

end CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_prop64_rank4_ne5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ HasL2Model (kBar K) (fun q => q = 5) →
      ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B →
        ∀ (b : G) (J : Subgroup G), Th2.Obs.Obstr52 B b J →
          Nonempty (kBar J ≃* alternatingGroup (Fin 7)) →
            Nonempty (kBar K ≃* alternatingGroup (Fin 7))

theorem b_prop64_rank4_of_ne5

        (h625c1 : B_lemma625c1) (h : B_prop64_rank4_ne5) : B_prop64_rank4 := by
  intro G _ _ hG x y K T S hs B hB b J hobs hA7
  by_cases h5 : HasL2Model (kBar K) (fun q => q = 5)
  · exfalso
    have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
    obtain ⟨d, hdB, hunb⟩ := hobs.exists_isUnbalancingTriple hE.2.1
    have hv : IsV2Triple x y K := hs.v2ss.isV2Triple
    have hL2odd : HasL2Model (kBar K) Odd :=
      C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; decide) h5
    have hup : pRank 2 ↥(CxK x K) + 2 ≤ pRank 2 G :=
      Th2.L625.pRank_CxK_add_two_le hv.1.1 hL2odd
    have hlow : 2 ≤ pRank 2 ↥(CxK x K) := by
      rcases hv.2.2.1 with h2 | hexc
      · exact h2
      · exact absurd hexc.2.1 (not_nonempty_A7_of_hasL2Model h5)
    have hCx : pRank 2 ↥(CxK x K) = 2 := by
      have := hG.pRank_eq_four
      omega
    have hE' : IsEStarUnbal b d J := ⟨hunb, B, hE, hobs.mem, hdB⟩
    have hrk : pRank 2 ↥(centralizer ({b, d} : Set G)) = 4 :=
      hE'.pRank_centralizer hG.pRank_eq_four
    have hJ := h625c1 G hG x y K hs.v2ss.isV2StarTriple h5 hCx b d J hunb.isLocallyUnbalancing hrk
    exact not_nonempty_A7_of_hasL2Model hJ hA7
  · exact h G hG x y K T S hs h5 B hB b J hobs hA7

end CFSG.GH74.GLS
