module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBig
import CFSG.ClassicalInvolution.Asc77.AscT8W1Eng
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75
public import CFSG.ClassicalInvolution.Asc77.AscT7FC
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8W

section Reps

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem no_three_reps_E4 (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h12 : ρ₁.K ≠ ρ₂.K) (h13 : ρ₁.K ≠ ρ₃.K) (h23 : ρ₂.K ≠ ρ₃.K) :
    False := by
  exact no_three_reps_E4E
    (fun ρ => muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (MuTab.muTabElt_mem ρ))
    (MuTab.muTabElt_eq_iff hP hW) (MuTab.muTab_commute_iff hP hW) (MuTab.muTabElt_ne_mul hP hW)
    hW hE ρ₁ ρ₂ ρ₃ h12 h13 h23

theorem exists_rep_ne_E4 (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (hE : MuIsoE4 Ω W)
    (ρ : Rep Ω W) : ∃ σ : Rep Ω W, σ.K ≠ ρ.K := by
  exact exists_rep_ne_E4E (MuTab.muTabElt_eq_iff hP hW)
    (fun ρ => muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (MuTab.muTabElt_mem ρ)) hE ρ

end Reps

section Key

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_unique_member_E4 (hs : Std8 p f Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hKX : ¬ K ≤ omegaNbrGen Ω K) :
    ∃ J₂ ∈ omegaNbr Ω K, ∀ L ∈ Ω, L ≤ omegaNbrGen Ω K →
      2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G)) → L = J₂ := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
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
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₂ hRD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  have hρKK : ρK.K = K := rfl
  obtain ⟨σ, hσ⟩ := exists_rep_ne_E4 hP hW₂ hE₂ ρK
  have hcomm : ∀ x y : ↥(muGroup Ω W₂), x * y = y * x := by
    obtain ⟨φ⟩ := hE₂
    intro x y
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hnbr : σ.K ∈ omegaNbr Ω K :=
    c₂.omega_of_comm ρK σ (Ne.symm hσ) (by have := congrArg Subtype.val (hcomm
      (MuTab.muTabElt ρK) (MuTab.muTabElt σ)); exact this)
  refine ⟨σ.K, hnbr, fun L hL hLX hcard => ?_⟩
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
  by_contra hLσ
  exact no_three_reps_E4 hP hW₂ hE₂ ρK σ ρL (Ne.symm hσ) (by rw [hρKK, hρLL]; exact Ne.symm hLK)
    (by rw [hρLL]; exact Ne.symm hLσ)

end Key

end T8W

end CFSG.ClassicalInvolution.Asc77
