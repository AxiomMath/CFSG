module

import CFSG.ClassicalInvolution.Asc77.AscT8W3Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8S26ULift
public import CFSG.ClassicalInvolution.Asc77.AscT8W1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8W

section Sylow

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_sylow_RT (hs : Std8 p f Ω K J S R T W z t) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧ T ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  exact exists_sylow_RTE (s26_conjSub_omegaNbrGen hΩ) hs.hJ hs.hR.2.1 hs.hR.2.2 hs.hT.2.1 hs.hT.2.2

theorem eq_J_of_mem_X (hs : Std8 p f Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) {L : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ omegaNbrGen Ω K)
    (hcard : 2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G))) : L = J := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hP : PartIHyp p f Ω := T8.partIHyp_of_std8 hs
  obtain ⟨η₂, hη₂, hinv₂⟩ := exists_invariant_mem_etaSet hp hq hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup G), s ∈ Subgroup.normalizer (W₂ : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Ctx p f Ω W₂ := MuTab.muTabCtx hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    obtain ⟨e⟩ := l7_5_2_proved p f hp hq G Ω hΩ W₂ hW₂ W hs.hW.1
    exact ⟨e.trans φ⟩
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hs.hT.1 hs.hT.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  have hTD : T ∈ DSet Ω W₂ := ⟨hs.hT.1, fun x hx => hSN x (hTS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₂ hRD
  obtain ⟨t₀, ht₀T, ht₀W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₂ hTD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  let ρJ : Rep Ω W₂ := ⟨J, T, t₀, hJΩ, hTD, hTsyl, ht₀T, ht₀W⟩
  have h611 : L ⊓ W₂ ∈ η₂ := l6_11_proved p f hp hq G Ω hΩ S₂ η₂ hη₂G hηS L hL hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hp hq hL
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := hΩ.isPGroup_of_mem_USet hp hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := c₂.exists_rep_of_involution_mem hL hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  by_cases hLK : L = K
  · exact absurd (hLK ▸ hLX) hKX
  by_contra hLJ
  exact no_three_reps_E4 hP hW₂ hE₂ ρK ρJ ρL (Ne.symm hs.hJ.2.1)
    (by show K ≠ ρL.K; rw [hρLL]; exact Ne.symm hLK)
    (by show J ≠ ρL.K; rw [hρLL]; exact Ne.symm hLJ)

theorem sX_normalizes_J (hs : Std8 p f Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) {s : G} (hsS : s ∈ (S₂ : Subgroup G))
    (hsX : s ∈ omegaNbrGen Ω K) : conjSub s J = J := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  exact sX_normalizes_JE hΩ.conjInvariant (fun hR => hΩ.eight_le_of_mem_RSet hp hR) hs.hJ hs.hT.1
    hs.hT.2.1 hTS₂ (fun hL hLX hcard => eq_J_of_mem_X hs hE hRS₂ hTS₂ hKX hL hLX hcard) hsS hsX

theorem sX_centralizes_t (hs : Std8 p f Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hKX : ¬ K ≤ omegaNbrGen Ω K) {s : G} (hsS : s ∈ (S₂ : Subgroup G))
    (hsX : s ∈ omegaNbrGen Ω K) : s * t * s⁻¹ = t :=
  hs.ht.conj_eq (sX_normalizes_J hs hE hRS₂ hTS₂ hKX hsS hsX)

end Sylow

end T8W

end CFSG.ClassicalInvolution.Asc77
