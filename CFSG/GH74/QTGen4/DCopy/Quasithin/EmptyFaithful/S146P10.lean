module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612DC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146P8
public import CFSG.Quasithin.EmptyFaithful.S146P9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

theorem stage14613LabP_of_inputs_F4 (iA : Input14613AP) (iB1 : Input14613B1P)
    (iB2 : Input14613B2P) : Stage14613LabP_F4 := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t hdec
  have hp : p = 3 ∨ p = 5 := S.p_eq_three_or_five_of_isRedCE hred
  have hH : IsHTM T M H := hred.isHTM
  have hF81 : HypF81 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) H :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).1
  obtain ⟨γ, γ', g, hsetup⟩ := F8.exists_F8Setup hF81
  by_cases hD : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) <
      F8.Uγ (VZ T M) H (g : G)
  · have hex : ∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
        F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
          F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) < F8.Uγ (VZ T M) H (g : G) :=
      ⟨γ, γ', g, hsetup, hD⟩
    rcases hdec.mIdx_uK_sup S hred hp with h4 | h8
    · rcases iB1 G T M S H PQ p hred H₀ H₁ H₂ t hdec hex h4 with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inr (Or.inl h1)
    · rcases iB2 G T M S H PQ p hred H₀ H₁ H₂ t hdec hex h8 with h2 | h2
      · exact Or.inl (Or.inr ⟨hp, h8, h2⟩)
      · exact Or.inr (Or.inr ⟨hp, h8, h2⟩)
  · have hle : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) ≤ F8.Uγ (VZ T M) H (g : G) :=
      centralizerMod_le_left _ _ _
    have hge : F8.Uγ (VZ T M) H (g : G) ≤ F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) := by
      by_contra hn
      exact hD (lt_of_le_not_ge hle hn)
    have hDU : F8.Uγ (VZ T M) H (g : G) = F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) :=
      le_antisymm hge hle
    rcases iA G T M S H PQ p hred H₀ H₁ H₂ t hdec γ γ' g hsetup hDU with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inr (Or.inl h1)

section Final

theorem stage14617_of_four_five_PM_F4 (h5 : Stage1461Five) (h12 : Stage14612PartP_F4)
    (h13 : Stage14613Lab_F4)
    (h14 : Stage14614_F4) (h15 : Stage14615_F4) (h16 : Stage14616_F4) (h4 : Stage1463Four)
    (iMod : Input14617Mod) (iF : Input14617Fstar) (iγ : Input14617Gamma) (iOrb : Input14617Orbit)
    (iFour : Input14617Four_F4) (iFive : Input14617Five) : Stage14617_F4 := by
  intro G _ _ T M S H PQ p hred hmax
  have hp3 : p = 3 := h15 G T M S H PQ p hred hmax
  have hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T) :=
    iF G T M S H PQ p hred hmax (stage14614At_of_F4 h14 S hred hmax)

  have hnot2 : ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
      ¬ Case13Two T M H p H₁ := fun H₀ H₁ H₂ t h hc =>
    h.not_case13Two_F4 S h5 h16 h4 hred hmax (iMod G T M S H PQ p hred H₀ H₁ H₂ t h) hF
      (iγ G T M S H PQ p hred hp3 H₀ H₁ H₂ t h) hc

  have hOne : ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
      Case13One T M H p H₁ ∨ Case13One T M H p H₂ := fun H₀ H₁ H₂ t hdec => by
    rcases h13 G T M S H PQ p hred H₀ H₁ H₂ t hdec with (h1 | h1) | (h1 | h1)
    · exact Or.inl h1
    · exact absurd h1 (hnot2 _ _ _ _ hdec)
    · exact Or.inr h1
    · exact absurd h1 (hnot2 _ _ _ _ hdec.swap)

  have hOF : IsOFourPlusOn T M H := by
    obtain ⟨-, H₀, H₁, H₂, t, hdecP⟩ := h12 G T M S H PQ p hred hmax
    have hdec : IsDec12 T M H p H₀ H₁ H₂ t :=
      hdecP.toIsDec12 (indexThreeP_proved G T M S H PQ p hred hp3 H₀ H₁ H₂ t hdecP)
    rcases hOne H₀ H₁ H₂ t hdec with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  refine ⟨hOF, fun H₀ H₁ H₂ t hdec => ⟨?_, ?_, ?_, ?_⟩⟩
  ·
    intro γ γ' g hsetup
    exact hdec.not_A₁_le_uHi_F4 S h5 h16 h4 hred hmax (iMod G T M S H PQ p hred H₀ H₁ H₂ t hdec) hF
      (fun w hw hwZ => iOrb G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec w hw hwZ) hsetup
  ·
    intro u _ hu huZ huT
    exact hdec.isInvU_of_mem_F4 S h5 h16 hred hmax iMod hF hu huZ huT
  ·
    intro u huK hu huZ huT
    exact iFour G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec (hOne H₀ H₁ H₂ t hdec) u huK hu huZ huT
      (hdec.isInvU_of_mem_F4 S h5 h16 hred hmax iMod hF hu huZ huT)
  ·
    exact iFive G T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec

end Final

theorem stage14617_of_named_inputs_PM_F4 (h2 : Stage1461Two) (h5 : Stage1461Five)
    (h12 : Stage14612PartP_F4) (h13 : Stage14613Lab_F4) (h14 : Stage14614_F4)
    (h15 : Stage14615_F4) (h16 : Stage14616_F4) (h4 : Stage1463Four) (iMod : Input14617Mod)
    (iF : Input14617Fstar) (iUK : Input14617UK_F4) : Stage14617_F4 :=
  stage14617_of_four_five_PM_F4 h5 h12 h13 h14 h15 h16 h4 iMod iF input14617Gamma_proved
    input14617Orbit_proved (input14617Four_of_F4 h2 h4 input14617Trans_proved
      input14617Singular_proved iUK) (input14617Five_of input14617V_proved)

end CFSG.Quasithin
