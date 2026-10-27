module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Frame
public import CFSG.ClassicalInvolution.SmallCases.EvenLie
public import CFSG.ClassicalInvolution.SmallCases.Sporadic
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.ClassicalInvolution Subgroup

theorem noTwoA7Classical_of_noNonsolvable {F : Type*} [Group F] (h : NoNonsolvableClassical F) :
    NoTwoA7Classical F :=
  fun z hz J hzJ hJ hW hns => h z hz J hzJ hJ hW.classical hns

section Ly


theorem noNonsolvableClassical_Ly_local :
    NoNonsolvableClassical (NativeSporadic.Carrier .Ly) :=
  LyProof.noNonsolvableClassical_Ly_centralizer

end Ly

section M11


theorem noTwoA7Classical_of_M11 {X : Type} [Group X] [Finite X]
    (h : NativeSporadic.IsSporadic X .M11) : NoTwoA7Classical X := by
  obtain ⟨e⟩ := h
  have hX : Nat.card X = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  intro z hz J hzJ hJ hW hns
  obtain ⟨-, hcen, ⟨eA⟩⟩ := hW
  have h1 : Nat.card (↥J ⧸ CFSG.Open.classicalInvolutionOddCore ↥J) = 5040 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥J ⧸ CFSG.Open.classicalInvolutionOddCore ↥J))
    rw [hcen, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at this
    simpa [Nat.factorial] using this
  have h2 : 5040 ∣ 7920 := by
    rw [← h1, ← hX]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)
  omega

end M11

theorem center_quotient_eq_bot {G : Type} [Group G] (hG : IsQuasisimple G) :
    Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hG.2.1
  rcases (inferInstance : (Subgroup.center (G ⧸ Subgroup.center G)).Normal).eq_bot_or_eq_top with
    h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hG
    apply hab
    have ha : a ∈ Subgroup.center (G ⧸ Subgroup.center G) := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

section Cells

theorem noTwoA7Classical_of_ghList (hOdd : TwoA7OddLie) {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hGH : GHList X) : NoTwoA7Classical X := by
  rcases hGH with ⟨n, -, -, ⟨e⟩⟩ | hspor | ⟨p, f, hp, hf, h⟩
  · exact noTwoA7Classical_of_noNonsolvable
      (NoNonsolvableClassical.of_mulEquiv e (noNonsolvableClassical_alternating n))
  · rcases hspor with h | h
    · exact noTwoA7Classical_of_M11 h
    · exact noTwoA7Classical_of_noNonsolvable
        (noNonsolvableClassical_of_gh74_models noNonsolvableClassical_Ly_local h)
  · rcases h with h | h | h | h | h | h | ⟨rfl, h⟩
    · exact hOdd X hZ ⟨p, f, hp, hf, Or.inl h⟩
    · exact hOdd X hZ ⟨p, f, hp, hf, Or.inr (Or.inl h)⟩
    · exact hOdd X hZ ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inl h))⟩
    · exact hOdd X hZ ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact hOdd X hZ ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact hOdd X hZ ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    · refine noTwoA7Classical_of_noNonsolvable ?_
      rcases h with h | h | h | h | h
      · exact noNonsolvableClassical_of_lieModel_two h (by decide) (by decide)
      · exact noNonsolvableClassical_of_lieModel_two h (by decide) (by decide)
      · exact noNonsolvableClassical_of_lieModel_two h (by decide) (by decide)
      · exact noNonsolvableClassical_of_lieModel_two h (by decide) (by decide)
      · exact noNonsolvableClassical_of_lieModel_two h (by decide) (by decide)

theorem pumpupTwoA7_of_ghList_of_oddLie (hOdd : TwoA7OddLie) {H : Type} [Group H] [Finite H]
    (L I : Subgroup H) (s : H) {K₀ : Type} [Group K₀] (hGH : GHList (↥L ⧸ Subgroup.center ↥L))
    (hL : IsComponent L) (hs : orderOf s = 2) (hsI : s ∈ I) (hIL : I ≤ L)
    (hIc : IsPCompIn 2 (Subgroup.centralizer ({s} : Set H)) I) (hK₀ : IsDoubleCoverOfAlt K₀ 7)
    (hφ : ∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) : I = L :=
  pumpupTwoA7_of_noTwoA7 L I s
    (noTwoA7Classical_of_ghList hOdd (center_quotient_eq_bot hL.1) hGH) hL hs hsI hIL hIc hK₀ hφ

end Cells

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
