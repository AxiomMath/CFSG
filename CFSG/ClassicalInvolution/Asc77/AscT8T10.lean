module

public import CFSG.ClassicalInvolution.Asc77.AscT8T9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_AlphaNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          (∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
            z' ≠ z * t) →
            T8.H274 Ω K z ≤
              Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G)

end Residual

end T8T

section Main

variable (p f : ℕ) [Fact p.Prime]


theorem c27_alphaNorm_of_alphaConst (hD4 : Ih8D4Star p f) (h2 : C27_2 p f)
    (hA : T8T.C27_AlphaConst p f) : T8T.C27_AlphaNorm p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4 hab _
  have hN := T8T.sigmaNorm_le_normalizer_alpha hA hs hdisc hab hE4
  exact sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
    T8T.centralizer_le_normalizer_alpha_of_nbr hD4 h2 hA (T8T.hyp51Tri_proved p f) hs hdisc hab
      hE4 hN hM hs')

theorem c27_Oab_of_alphaNorm (h2 : C27_2 p f) (h4a : C27_4a p f) (hN : T8T.C27_AlphaNorm p f) :
    C27_Oab p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4 hab hE8
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨K', R', z', hF, hind⟩ := T8T.exists_triFrame_of_std8 hs hE4 hab hE8
  have hHyp : Hyp51 (Subgroup.closure ({z, t, z'} : Set G)) :=
    T8T.hyp51Tri_proved p f G Ω ![K, J, K'] ![z, t, z'] ![R, T, R'] hs.stand hnt hF hind
  have hzt : z * t = t * z := hF.comm hp hΩ 0 1
  have hz2 : z * z = 1 := hF.sq 0
  have ht2 : t * t = 1 := hF.sq 1
  have hz1 : z ≠ 1 := hF.ne_one 0
  have ht1 : t ≠ 1 := hF.ne_one 1
  have hzt' : t ≠ z := (hF.x_ne hnt (i := 0) (j := 1) (by decide)).symm
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, z'} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt' hzt.symm
  obtain ⟨hodd, -⟩ := lemma54_odd_and_eq hHyp hDB hD
  have hH274 := hN G Ω K J S R T W z t hs hdisc hE4 hab hE8
  have hcomp := h2 G Ω K J S R T W z t hs hdisc
  have htop : T8.H274 Ω K z = ⊤ := s26_H274_eq_top h4a hs hdisc hcomp
  rw [htop, top_le_iff] at hH274
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH274
  have hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
      have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  exact T8.oddCoreOf_layerJoin_le_of_alpha hs hα

theorem c27_Oab_of_alphaConst'' (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (h4a : C27_4a p f)
    (hA : T8T.C27_AlphaConst p f) : C27_Oab p f :=
  c27_Oab_of_alphaNorm p f h2 h4a (c27_alphaNorm_of_alphaConst p f hD4 h2 hA)

end Main

end CFSG.ClassicalInvolution.Asc77
