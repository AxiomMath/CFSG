module

public import CFSG.ClassicalInvolution.AschTight.Sec7L76C
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.AschTight.Sec7L612B

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Family

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem l7_6_on (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hex : EtaExists Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) (h610 : EtaActsR Ω) (h67 : RCommute Ω)
    (hkey : KeyOn Ω) (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hmu : ¬ IsMulCommutative ↥(muGroup Ω W)) :
    (∀ x ∈ Subgroup.centralizer (W : Set G), ∀ g : G,
        g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set G) →
          ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = g * x * g⁻¹) ∧
      ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ g : G, conjSub g R = T →
        ∃ n ∈ Subgroup.normalizer (W : Set G), conjSub n R = T := by
  have hW2 := isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S, hηS, hinv⟩ := id hη
  have h612 := l6_12_on hp hq hΩ hex habel h611 htr S
  dsimp only at h612
  have hMS : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S : Subgroup G)}, U) ≤
      (S : Subgroup G) := iSup₂_le fun U hU => hU.2
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  · have heq : η = η₀ := huniq η hη fun m hm U hU => hinv m (hMS hm) U hU
    subst heq
    have hWC : WeaklyClosedIn W S := by
      intro g hg
      rw [hWη] at hg ⊢
      refine conjSub_iSup_eq_of_forall_mem (hwc g fun U hU => ?_)
      exact (conjSub_mono (le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl)).trans hg
    exact ⟨fun x hx g hg => control_centralizer_of_weaklyClosed hW2 hWC hx hg,
      fun R hR T hT g hg => control_DSet_of_weaklyClosed hp hq hΩ habel h611 hW hWC hR hT hg⟩
  · exact absurd (isMulCommutative_muGroup_of_two hp hΩ h611 h610 h67 hkey h2 hW) hmu

end Family

variable (p f : ℕ) [Fact p.Prime]

theorem l6_12_mod : L6_12ModTmp p f :=
  l6_12ModTmp_of p f
    (fun G _ _ Ω hΩ S => (l6_9_proved p f hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1 S).1)
    (fun G _ _ Ω hΩ η ⟨S, hS, hinv⟩ =>
      ((l6_9_proved p f hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1 S).2 η hS hinv).1)
    (fun G _ _ Ω hΩ => l6_11_proved p f hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1)

theorem l7_6ModTmp_of_key (hkey : L7_1Key p f) : L7_6ModTmp p f := by
  intro G _ _ Ω hΩ htr W hW hmu
  have hp := hΩ.1
  have hq := hΩ.2.1
  have hmod := hΩ.2.2.1
  exact l7_6_on hp hq hmod (fun S => (l6_9_proved p f hp hq G Ω hmod S).1)
    (fun η ⟨S, hS, hinv⟩ => ((l6_9_proved p f hp hq G Ω hmod S).2 η hS hinv).1)
    (l6_11_proved p f hp hq G Ω hmod)
    (fun S η hη hηS => (l6_10_proved p f hp hq G Ω hmod S η hη hηS).1)
    (l6_7_proved p f hp hq G Ω hmod) (hkey G Ω hΩ) htr hW hmu

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
