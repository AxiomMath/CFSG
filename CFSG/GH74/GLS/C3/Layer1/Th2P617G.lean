module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617C
public import CFSG.GH74.GLS.C3.Layer1.Th2P617F

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_prop617_obs_gt4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      pRank 2 ↥(T ⊓ CxK x K) ≤ 2 → 4 < Nat.card ↥(T ⊓ CxK x K) →
        ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B →
          ∀ (b : G) (J : Subgroup G), Th2.Obs.Obstr52 B b J → J ≠ K → b ≠ x → False

theorem four_le_card_Q {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) : 4 ≤ Nat.card ↥(T ⊓ CxK x K) := by
  have hcen := centerlessBar_of_A7 h7
  have hcd := hs.commDisj hcen
  have hP : RankTwoShape (T ⊓ K) := rankTwoShape_sylow_A7 hs.sylow_P h7
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hcd hP B).1 hB
  have hcardE : Nat.card ↥E₁ = 2 ^ pRank 2 ↥E₁ := C3.Layer1.Back.card_eq_two_pow_pRank hE₁S.2.1
  have h4 : 4 ≤ Nat.card ↥E₁ := by
    rw [hcardE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥E₁ := Nat.pow_le_pow_right (by norm_num) hE₁2
  exact h4.trans (Subgroup.card_le_of_le hE₁S.1)

theorem b_prop617_obs_ne_of_gt4
    (h : B_prop617_obs_gt4) : B_prop617_obs_ne := by
  intro G _ _ hG x y K T S hs h7 hQ2 hnc B hB b J hobs hJK hbx
  by_cases h4 : 4 < Nat.card ↥(T ⊓ CxK x K)
  · exact h G hG x y K T S hs h7 hQ2 h4 B hB b J hobs hJK hbx
  · have hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4 :=
      le_antisymm (not_lt.1 h4) (four_le_card_Q hs h7 hB)
    have hTS : T = S := by
      by_contra hne
      exact hnc ⟨hQ4, lt_of_le_of_ne hs.T_le_S hne⟩
    exact Th2.Obs.false_of_Q4_TS_of_smallQ hs h7 hQ4 hTS hB hobs hG.kproper.1 hG.kproper.2.1

end CFSG.GH74.GLS
