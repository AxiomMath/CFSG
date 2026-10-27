module

public import CFSG.Quasithin.H13.L32NLem14325e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14325

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem exists_comp_img_F4 (h1332 : Stmt13_3_2_F4) (h1352 : A6.Stmt13_5_2_F4) (h1381 : Stmt13_8_1_F4)
    (h36 : A36ForSQTK) (h39 : A39ForSQTK) {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hPH : P ≤ D.img (l32nH T V)) (hP1 : P ≠ ⊥) (hPp : ⁅P, P⁆ = P)
    (hnorm : ∀ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), IsSubnormal X (D.img (l32nH T V)) →
      X ≠ ⊥ → ⁅X, X⁆ = X → ¬ ∀ γ ∈ X, ∀ w ∈ D.hat V, γ w ∈ D.hat V) :
    ∃ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), IsSubnormal X (D.img (l32nH T V)) ∧ X ≠ ⊥ ∧
      ⁅X, X⁆ = X ∧ (Nat.card X ∣ 60 ∨ Nat.card X ∣ 168) := by
  obtain ⟨K, hK, hK1⟩ := C.exists_comp h39 hPH hP1 hPp
  refine ⟨D.img K, img_subnormal hK, hK1, img_perfect hK, ?_⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK

  have hKM : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
    intro hle
    apply hnorm _ (img_subnormal hK) hK1 (img_perfect hK)
    intro γ hγ w hw
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    have hkM : k ∈ l32nH T V ⊓ Subgroup.normalizer (L : Set G) := ⟨hKH hk, hle hk⟩
    rw [C.HM] at hkM
    exact C.rho_mem_hatV_of_normalizer (hKH hk) hkM.2 hw
  have hVK : ⁅vH T L V, K⁆ ≠ ⊥ := by
    intro hb
    apply hKM
    refine le_trans ?_ C.cent_le
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : ⁅w, k⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hw hk
      rwa [hb, Subgroup.mem_bot] at this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo C.hyp.fsu.sylow
  have hInH : InH (S : Subgroup G) (l32nH T V) := ⟨hS ▸ C.T_le, C.pCoreOf_ne_bot⟩
  have hTFAE := lemma_1_2_10_of_a36 C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h36 S
    hInH hK
  have h2 : ∃ W, IsTwoReducedIn (l32nH T V) W ∧ ⁅W, K⁆ ≠ ⊥ := ⟨vH T L V, C.red, hVK⟩
  have hLf : quasithinIsFaithfulLocal (S : Subgroup G) K := (hTFAE.out 1 2).mpr h2
  rw [hS] at hLf

  have hdvd := C.card_img_dvd hK
  rcases lemma1434One_of_inputs_F4 h1332 h1352 h1381 G T L C.hyp.hyp K hLf with he | h3
  · left
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hdvd
    exact hdvd
  · right
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h3
    rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two] at hdvd
    exact hdvd

end Ctx14325

end L14325

end CFSG.Quasithin.H13
