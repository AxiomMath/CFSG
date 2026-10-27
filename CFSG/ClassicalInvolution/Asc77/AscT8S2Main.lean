module

public import CFSG.ClassicalInvolution.Asc77.AscT8S2Key
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Q
public import CFSG.ClassicalInvolution.Asc77.AscT8S26VProper
import CFSG.ClassicalInvolution.Asc77.AscT8S2MainEng
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement


section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_sylow_meeting_X (hs : Std8 p f Ω K J S R T W z t) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  exact exists_sylow_meeting_XE hs.hR.2.1
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1) (s26_conjSub_omegaNbrGen hΩ)

theorem s26XMuZ2_of_data (hs : Std8 p f Ω K J S R T W z t)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (hX : omegaNbrGen Ω K ≠ ⊤) :
    ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
      MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W' := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  obtain ⟨S₂, hRS₂, hS₂X⟩ := exists_sylow_meeting_X hs
  obtain ⟨J₂, hJ₂, hK1⟩ :=
    T8S2.exists_unique_member hs φ hRS₂ (T8S2.not_le_omegaNbrGen hs hX)
  have hGen := s26_genSection_omegaNbrGen (K := K) hp hq hΩ hs.stand.aEmpty
  have hJ₂X : J₂ ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J₂ hJ₂
  refine T8S2.exists_muIsoZ2_of_sylow hp hq (Λ := restrictFamily Ω X) (hΩ.restrict X)
    hGen.hyp hGen.aEmpty (AscP1Nine3.sylowOfIsSylow2In₉ hS₂X) (J₀ := J₂.subgroupOf X)
    ⟨J₂, hJ₂.1, hJ₂X, rfl⟩ ?_
  rintro _ ⟨L, hL, hLX, rfl⟩ hcard
  have hSH : ((AscP1Nine3.sylowOfIsSylow2In₉ hS₂X : Sylow 2 ↥X) : Subgroup ↥X) =
      ((S₂ : Subgroup G) ⊓ X).subgroupOf X := rfl
  have hLS : L ⊓ (S₂ : Subgroup G) ≤ X := inf_le_left.trans hLX
  have hinf : L.subgroupOf X ⊓ ((S₂ : Subgroup G) ⊓ X).subgroupOf X =
      (L ⊓ (S₂ : Subgroup G)).subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hSH, hinf] at hcard
  have hc2 : Nat.card ↥((L ⊓ (S₂ : Subgroup G)).subgroupOf X) =
      Nat.card ↥(L ⊓ (S₂ : Subgroup G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv
  rw [hc2] at hcard
  rw [hK1 L hL hLX hcard]

theorem s26XMuZ2_proved : S26XMuZ2 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  obtain ⟨φ⟩ := hS4
  exact s26XMuZ2_of_data hs φ (s26XProper_proved G Ω K J S R T W z t hs hdisc ⟨φ⟩)

end Main

end CFSG.ClassicalInvolution.Asc77
