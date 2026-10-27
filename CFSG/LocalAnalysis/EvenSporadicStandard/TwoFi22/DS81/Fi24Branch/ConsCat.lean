module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotKc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem Cz_ne_top (hs : StdHyp G L) {z : G} (hz : z ≠ 1) : Cz z ≠ ⊤ := by
  intro htop
  have hzcenter : z ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Cz z := htop ▸ Subgroup.mem_top g
    rw [mem_Cz] at hg
    exact hg
  have hne : center G ≠ ⊥ := by
    intro hbot
    rw [hbot] at hzcenter
    exact hz (Subgroup.mem_bot.mp hzcenter)
  have htopc : center G = ⊤ := by
    rcases hs.simple.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact absurd h hne
    · exact h
  letI : CommGroup G := Group.commGroupOfCenterEqTop htopc
  obtain ⟨a, b, hab⟩ := hs.nonabelian
  exact hab (mul_comm a b)

theorem catSections (hs : StdHyp G L) {z : G} (hz : z ≠ 1) : CatSections ↥(Cz z) := by
  intro A S _ _ hnonab φ hφ
  let A' : Subgroup G := A.map (Cz z).subtype
  have hA'le : A' ≤ Cz z := Subgroup.map_subtype_le A
  have hA'top : A' ≠ ⊤ := ne_top_of_le_ne_top (Cz_ne_top hs hz) hA'le
  let e : ↥A ≃* ↥A' :=
    Subgroup.equivMapOfInjective A (Cz z).subtype (Cz z).subtype_injective
  let φ' : ↥A' →* S := φ.comp e.symm.toMonoidHom
  have hφ' : Function.Surjective φ' := hφ.comp e.symm.surjective
  exact CFSG.EvenSporadicStandard.Induction.Hyp.catalog_of_kProper_of_surjective
    hs.kProper A' hA'top S hnonab φ' hφ'

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
