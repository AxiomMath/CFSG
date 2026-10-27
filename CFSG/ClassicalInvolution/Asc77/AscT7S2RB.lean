module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectD
public import CFSG.ClassicalInvolution.ModelFacts.Orth15LieTwin


public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected

namespace T7S2R

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Ih8S4Star : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (e : ℕ),
    HypOmegaMod p f Ω →
      (Nonempty (Ih8Model p f Ω .POmegaOdd 3 e) ∨ Nonempty (Ih8Model p f Ω .POmegaMinus 4 e)) →
        T3.DStarConnected Ω

variable {p f}

section Tag

omit [Fact p.Prime] in
theorem smallModel_odd {k : ℕ} (h : SmallModel .POmegaOdd k) : k = 3 := by
  rcases h with h | h | h | h | h | h <;> simp_all

omit [Fact p.Prime] in
theorem smallModel_plus {k : ℕ} (h : SmallModel .POmegaPlus k) : k = 4 := by
  rcases h with h | h | h | h | h | h <;> simp_all

omit [Fact p.Prime] in
theorem smallModel_minus {k : ℕ} (h : SmallModel .POmegaMinus k) : k = 4 := by
  rcases h with h | h | h | h | h | h <;> simp_all


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}


theorem tag_of_twinShape_disc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hD4s : Ih8D4Star p f)
    (hS4 : Ih8S4Star p f) (hΦ : HypOmegaMod p f Φ) (hne : Φ.Nonempty) {t : StatedLieTag}
    {k e : ℕ} (M : Ih8Model p f Φ t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hshape : TwinShape t k) (hdisc : ¬ T3.DStarConnected Φ) :
    (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) := by
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4 with hc | hsmall
  · exact absurd (fun K₁ hK₁ L hL => T7A.mem_dstarComp_of_mem_dComp hp2 hΦ
      (M.dConnected_of_connected hp2 hq hne hG2 hD4 hc K₁ hK₁ L hL)) hdisc
  rcases hshape with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk : k = 3 := smallModel_odd hsmall
    subst hk
    exact absurd (hS4 hp2 hq X Φ e hΦ (Or.inl ⟨M⟩)) hdisc
  · have hk : k = 4 := smallModel_plus hsmall
    subst hk
    exact absurd (hD4s hp2 hq X Φ e hΦ ⟨M⟩) hdisc
  · have hk : k = 4 := smallModel_minus hsmall
    subst hk
    exact absurd (hS4 hp2 hq X Φ e hΦ (Or.inr ⟨M⟩)) hdisc
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)


theorem tag_of_disc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hG2D4 : Ih8G2D4 p f) (hD4s : Ih8D4Star p f)
    (hS4 : Ih8S4Star p f) (hS : TransSection p f Φ) (D : OmegaLie p f Φ) (hne : Φ.Nonempty)
    {K₀ K₁ : Subgroup X} (hK₀ : K₀ ∈ Φ) (hK₁ : K₁ ∈ twinSet Φ K₀) (hne' : K₁ ≠ K₀)
    (hdisc : ¬ T3.DStarConnected Φ) (i : Fin D.card) :
    (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
      (D.tag i = .PSU ∧ D.rank i = 4) := by
  have hcard : D.card = 1 := D.card_eq_one_of_transitive hS.hyp hS.gen hS.trans hne
  let M : Ih8Model p f Φ (D.tag i) (D.rank i) (D.exp i) :=
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := D.hom_surjective_of_gen hcard hS.gen i
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => D.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => D.cls_conj hS.hyp.conjInvariant i hR g }
  by_cases hG2d4 : D.tag i = .G2 ∨ D.tag i = .trialityD4
  · exfalso
    have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
    exact hne' ((hG2D4 hp2 hq X Φ hS.hyp hS.aEmpty hS.trans (D.tag i) (D.rank i) (D.exp i) ⟨M⟩
      hG2d4).1 K₀ hK₀ K₁ hK₁)
  have hG2 : D.tag i ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4' : D.tag i ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K₀).mp hK₀
  obtain ⟨R', hR', hK₁eq⟩ := (M.mem_iff K₁).mp hK₁.1
  obtain ⟨z, hzK, hzK'⟩ := hK₁.2
  have hexact : HypOmega p f Φ := hS.hyp.toExact (D.exactMembers hp2 hq hS.hyp)
  have hK₁Φ : R'.map (D.hom i) ∈ Φ := hK₁eq ▸ hK₁.1
  rw [hK₁eq] at hzK' hne'
  have hshape := (twinShape_of_twin hp2 hq hexact D i hG2 hD4' (M.cls_sub hR) (M.cls_sub hR') hK₀
    hK₁Φ hzK hzK' hne'.symm).1
  exact tag_of_twinShape_disc hp2 hq hD4s hS4 hS.hyp hne M hG2 hD4' hshape hdisc

end Tag

end T7S2R

end CFSG.ClassicalInvolution.Asc77
