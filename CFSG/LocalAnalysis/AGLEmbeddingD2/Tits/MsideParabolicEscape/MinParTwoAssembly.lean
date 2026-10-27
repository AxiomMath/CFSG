module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

theorem TwoParLat.toTwoPar {S : Type} [Group S] {T P₁ P₂ : Subgroup S} (h : TwoParLat S T P₁ P₂) :
    TwoPar S T P₁ P₂ where
  sylow := h.sylow
  lt₁ := by rw [h.normT]; exact h.lt₁
  lt₂ := by rw [h.normT]; exact h.lt₂
  atom₁ := by rw [h.normT]; exact h.atom₁
  atom₂ := by rw [h.normT]; exact h.atom₂
  ne := h.ne
  top₁ := h.top₁
  top₂ := h.top₂
  hover := by rw [h.normT]; exact h.hover
  cover := fun X hTX hX => by
    rcases h.hover X hTX with e | e | e | e
    · exact Or.inl (e ▸ h.lt₁.le)
    · exact Or.inl e.le
    · exact Or.inr e.le
    · exact absurd e hX
  ov₁ := fun X hTX hXP hXn => by
    rw [h.normT] at hXn
    rcases h.atom₁ X hTX hXP with e | e
    · exact absurd e.le hXn
    · exact (pElementSubgroup_le _).trans e.ge
  ov₂ := fun X hTX hXP hXn => by
    rw [h.normT] at hXn
    rcases h.atom₂ X hTX hXP with e | e
    · exact absurd e.le hXn
    · exact (pElementSubgroup_le _).trans e.ge
  gen₁ := h.gen₁.trans le_sup_right
  gen₂ := h.gen₂.trans le_sup_right
  ct₁ := h.ct₁
  ct₂ := h.ct₂

section

variable {S : Type} [Group S] [Finite S] {T P₁ P₂ : Subgroup S}

theorem TwoPar.sup_eq_top (h : TwoPar S T P₁ P₂) : P₁ ⊔ P₂ = ⊤ := by
  rcases h.hover (P₁ ⊔ P₂) (h.lt₁.le.trans le_sup_left) with e | e | e | e
  · exact absurd (e ▸ le_sup_left : P₁ ≤ _) h.lt₁.not_ge
  · rcases h.atom₁ P₂ h.lt₂.le (e ▸ le_sup_right) with e1 | e1
    · exact absurd e1 h.lt₂.ne'
    · exact absurd e1.symm h.ne
  · rcases h.atom₂ P₁ h.lt₁.le (e ▸ le_sup_left) with e1 | e1
    · exact absurd e1 h.lt₁.ne'
    · exact absurd e1 h.ne
  · exact e

theorem TwoPar.oddWitness (h : TwoPar S T P₁ P₂) (J : Set Bool) (hJ : J.Nonempty)
    (hne : (⨆ j ∈ J, h.node j) ≠ ⊤) : OddWitness (⨆ j ∈ J, h.node j) := by
  obtain ⟨j, hj⟩ := hJ
  have hall : ¬ ∀ b, b ∈ J := by
    intro hall
    apply hne
    have : P₁ ⊔ P₂ ≤ ⨆ j ∈ J, h.node j :=
      sup_le (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => h.node j) true (hall true) le_rfl)
        (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => h.node j) false (hall false) le_rfl)
    rw [h.sup_eq_top] at this
    exact top_le_iff.1 this
  push Not at hall
  obtain ⟨b0, hb0⟩ := hall
  have hJb : ∀ j' ∈ J, j' = j := by
    intro j' hj'
    by_contra hne'
    apply hb0
    cases j' <;> cases j <;> cases b0 <;> simp_all
  have hsup : (⨆ j' ∈ J, h.node j') = h.node j :=
    le_antisymm (iSup₂_le fun j' hj' => (hJb j' hj') ▸ le_rfl)
      (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => h.node j) j hj le_rfl)
  rw [hsup]
  exact oddWitness_of_charTwo h.sylow (Subgroup.le_normalizer.trans (h.le_node j).le) (h.ct j)
    (fun hle => h.nonnorm j (hle.trans Subgroup.le_normalizer))

end

theorem kFact_of_twoPar {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y))
    (hR2 : IsPGroup 2 R) (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    {P₁ P₂ : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (h : TwoPar (↥L ⧸ Subgroup.center ↥L)
      (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) P₁ P₂) :
    (∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
      (conjClosure P R ≠ L →
        ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
          twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥) := by
  let D0 := minParData_of_twoPar h
  refine ⟨minParabolic_of_minParData hR hR2 hS hP (minParData_of_center D0 hS), ?_⟩
  exact clause_four_of_witness hR hS hP D0 (fun J hJ hne => h.oddWitness J hJ hne)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
