module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamental

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Abstract

variable {X : Type*} [Group X]

@[expose] def CommutingGeneration (𝓕 : Set (Subgroup X)) : Prop :=
  ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) →
    (∀ r ∈ R₂, c₂ * r = r * c₂) → (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) →
      (⊤ : Subgroup X) ≤ ⨆ R ∈ 𝓕,
        ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set X) ∨
          R ≤ Subgroup.centralizer ({c₂} : Set X) ∨
          R ≤ Subgroup.centralizer ({c₁ * c₂} : Set X)), R

theorem CommutingGeneration.of_mulEquiv {Y : Type*} [Group Y] (φ : X ≃* Y) {𝓕 : Set (Subgroup X)}
    {𝓕' : Set (Subgroup Y)} (hfund : ∀ R : Subgroup X, R ∈ 𝓕 ↔ R.map φ.toMonoidHom ∈ 𝓕')
    (h : CommutingGeneration 𝓕') : CommutingGeneration 𝓕 := by
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  have hmem : ∀ (R : Subgroup X) (c : X), c ∈ R → φ c ∈ R.map φ.toMonoidHom :=
    fun R c hc => ⟨c, hc, rfl⟩
  have hcomm : ∀ (R : Subgroup X) (c : X), (∀ r ∈ R, c * r = r * c) →
      ∀ r ∈ R.map φ.toMonoidHom, φ c * r = r * φ c := by
    rintro R c hcR _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg φ (hcR r hr)
  have key := h (R₁.map φ.toMonoidHom) ((hfund R₁).1 hR₁) (R₂.map φ.toMonoidHom)
    ((hfund R₂).1 hR₂) (φ c₁) (hmem R₁ c₁ hc₁) (φ c₂) (hmem R₂ c₂ hc₂) (hcomm R₁ c₁ hz₁)
    (hcomm R₂ c₂ hz₂) (hcomm R₁ c₂ hx₂₁) (hcomm R₂ c₁ hx₁₂)
  intro x _
  have hx : φ x ∈ ⨆ R' ∈ 𝓕', ⨆ (_ : R' ≤ Subgroup.centralizer ({φ c₁} : Set Y) ∨
      R' ≤ Subgroup.centralizer ({φ c₂} : Set Y) ∨
      R' ≤ Subgroup.centralizer ({φ c₁ * φ c₂} : Set Y)), R' := key (Subgroup.mem_top _)
  have hpre : (⨆ R' ∈ 𝓕', ⨆ (_ : R' ≤ Subgroup.centralizer ({φ c₁} : Set Y) ∨
      R' ≤ Subgroup.centralizer ({φ c₂} : Set Y) ∨
      R' ≤ Subgroup.centralizer ({φ c₁ * φ c₂} : Set Y)), R').map φ.symm.toMonoidHom ≤
      ⨆ R ∈ 𝓕, ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set X) ∨
        R ≤ Subgroup.centralizer ({c₂} : Set X) ∨
        R ≤ Subgroup.centralizer ({c₁ * c₂} : Set X)), R := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun R' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hcond => ?_
    have hR : R'.map φ.symm.toMonoidHom ∈ 𝓕 := by
      rw [hfund, Subgroup.map_map]
      have : (φ.toMonoidHom.comp φ.symm.toMonoidHom) = MonoidHom.id Y := by
        ext y
        simp
      rw [this, Subgroup.map_id]
      exact hR'
    have hcen : ∀ c : X, R' ≤ Subgroup.centralizer ({φ c} : Set Y) →
        R'.map φ.symm.toMonoidHom ≤ Subgroup.centralizer ({c} : Set X) := by
      intro c hc
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hc hy)
      apply φ.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
      exact this
    refine le_iSup₂_of_le _ hR (le_iSup_of_le ?_ le_rfl)
    rcases hcond with h1 | h1 | h1
    · exact Or.inl (hcen c₁ h1)
    · exact Or.inr (Or.inl (hcen c₂ h1))
    · refine Or.inr (Or.inr (hcen (c₁ * c₂) ?_))
      rwa [map_mul]
  exact hpre ⟨φ x, hx, by simp⟩

theorem commutingFundamentalGeneration_iff (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) :
    CommutingFundamentalGeneration p t n e ↔
      CommutingGeneration (CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).D) :=
  Iff.rfl

end Abstract

section Center

theorem eq_one_or_eq_of_isClassicalSL2_center {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {G : Type*} [Group G] {J : Subgroup G} {d : G}
    (h : CFSG.ClassicalInvolution.IsClassicalSL2 F J d) {c : G} (hc : c ∈ J)
    (hcc : ∀ r ∈ J, c * r = r * c) : c = 1 ∨ c = d := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  have hz : e ⟨c, hc⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨y, rfl⟩ := e.surjective B
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hcc y y.2).symm)
  have hd : e ⟨d, h.mem⟩ = -1 :=
    (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2 (e ⟨d, h.mem⟩)).mp
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact h.orderOf_eq_two)
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).1 hz with h1 | h1
  · left
    have : (⟨c, hc⟩ : J) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨c, hc⟩ : J) = ⟨d, h.mem⟩ := e.injective (by rw [h1, hd])
    exact congrArg Subtype.val this

end Center

end CFSG.ClassicalInvolution.ModelFacts
