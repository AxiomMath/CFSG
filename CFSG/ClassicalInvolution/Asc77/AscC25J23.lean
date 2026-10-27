module

public import CFSG.ClassicalInvolution.Asc77.AscC25J22
public import CFSG.ClassicalInvolution.Asc77.AscC25J16
public import CFSG.ClassicalInvolution.Asc77.AscC25J6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.C25V
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911 CFSG.ClassicalInvolution.Asc77.T3CII
open scoped MatrixGroups commutatorElement

section Weak

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem weak_member_data9 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f = 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a) :
    ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
      IsClassicalMemberU (.sl2 3 1) (crossIn K' a) ⟨z, hzA⟩ := by
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have hfix := fix_of_isFAut h haS hF
  have haK' : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.2
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK'
  have hσ1 : fieldChar hp hq e ⟨a, haK'⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hR'syl.1 h.hqR' h.hzR' hF ha2 haK'
  have hzb : z ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hyp.hzS a haS).symm
  have d' := twinCtx'_of_hyp25 h
  have hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K' = K' →
        conjSub (y * x * y⁻¹) K' = K' := fun y x hy hx hxK =>
    d'.conj_normalizer (Subgroup.mem_centralizer_singleton_iff.mp hy)
      (Subgroup.mem_centralizer_singleton_iff.mp hx) hxK
  have hiso := crossIn_fix9 hp hq h9 e haK' ha2 hσ1
  exact ⟨hzb, crossIn_isClassicalMember h.hz' (isUniqueInvolution_le_centralizer h.hz') hconj hzb
    hiso⟩

end Weak

section S4Tag

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)}


theorem false_of_s4_tag (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hne : Φ.Nonempty)
    (D : LieSystemDataU 3 1 (Fin 1) E Φ) {t : StatedLieTag} {k : ℕ}
    (hCI : CompIs 3 1 (D.kind 0) t k)
    (hS4 : (t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨
      (t = .POmegaMinus ∧ k = 4))
    (hnc4 : ∀ {J₁ J₂ : Subgroup E}, J₁ ∈ Φ → J₂ ∈ Φ → ∀ {y z₂ : E}, y ∈ J₁ →
      y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 → z₂ ≠ y * y →
      z₂ * y = y * z₂ → False) : False := by
  obtain ⟨e, he, hfund, hadm, hc⟩ := hCI
  have hD4 : t ≠ .trialityD4 := by
    rcases hS4 with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have he1 : e = 1 := he.resolve_right fun h => hD4 h.1
  subst he1
  have hsurj : Function.Surjective (D.hom 0) := by
    apply MonoidHom.range_eq_top.mp
    have h1 : (⨆ j, (D.hom j).range) = (D.hom 0).range :=
      le_antisymm (iSup_le fun j => by rw [Subsingleton.elim j 0])
        (le_iSup (fun j => (D.hom j).range) 0)
    rw [← h1, D.generate]
  have hfund' : ∀ L ∈ Φ, ∃ R ∈ (D.kind 0).fund, L = R.map (D.hom 0) := by
    intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ⟨R, hR, hLR⟩
  obtain ⟨M⟩ := ih8Model_of_comp hΦ.conjInvariant hfund hadm he hc (D.hom 0)
    (D.ker_le_center 0) hsurj hfund'
  obtain ⟨J₁, hJ₁, J₂, hJ₂, y, hy, z₂, hz₂, h1, h2, h3, h4, h5, h6⟩ := s4_excl3 M hne hS4
  exact hnc4 hJ₁ hJ₂ hy h1 h2 hz₂ h3 h4 h5 h6

end S4Tag

end CFSG.ClassicalInvolution.Asc77.C25J
