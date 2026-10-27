module

public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.Q3NMInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups


section Conj

theorem natCard_conjSub' {G : Type} [Group G] (n : G) (K : Subgroup G) :
    Nat.card ↥(conjSub n K) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj n).injective

theorem conjSub_mem_fund_of_not_a1 {c : CompData}
    (hc : (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), c = CompData.model t n) ∨
      c = CompData.m11)
    {R : Subgroup c.G} (hR : R ∈ c.fund) (g : c.G) : conjSub g R ∈ c.fund := by
  rcases hc with ⟨t, n, rfl⟩ | rfl
  · obtain ⟨g₀, γ, hγ, rfl⟩ := hR
    exact ⟨g * g₀, γ, hγ, by rw [conjSub_mul]⟩
  · obtain ⟨w, hw⟩ := hR
    exact ⟨g * w * g⁻¹, hw.conj g⟩

end Conj

section Component

variable {Y : Type} [Group Y] {ι : Type} {Λ : Set (Subgroup Y)}

@[expose] def centerQuotHom (D : LieSystemData3 ι Y Λ) (j : ι) :
    (D.kind j).G →* (D.hom j).range ⧸ Subgroup.center (D.hom j).range :=
  (QuotientGroup.mk' (Subgroup.center (D.hom j).range)).comp (D.hom j).rangeRestrict

theorem centerQuotHom_surjective (D : LieSystemData3 ι Y Λ) (j : ι) :
    Function.Surjective (centerQuotHom D j) :=
  (QuotientGroup.mk'_surjective _).comp (D.hom j).rangeRestrict_surjective

theorem centerQuotHom_apply (D : LieSystemData3 ι Y Λ) (j : ι) (g : (D.kind j).G) :
    centerQuotHom D j g = QuotientGroup.mk' (Subgroup.center (D.hom j).range)
      ((D.hom j).rangeRestrict g) := rfl

theorem centerQuotHom_ker_le_center (D : LieSystemData3 ι Y Λ) (j : ι)
    (hq : CFSG.Open.IsQuasisimple (D.kind j).G) :
    (centerQuotHom D j).ker ≤ Subgroup.center (D.kind j).G := by
  have : Group.IsPerfect (D.kind j).G := ⟨hq.1⟩
  have hψ : Function.Surjective (D.hom j).rangeRestrict := (D.hom j).rangeRestrict_surjective
  have hker : (D.hom j).rangeRestrict.ker ≤ Subgroup.center (D.kind j).G := by
    rw [MonoidHom.ker_rangeRestrict]
    exact D.ker_le_center j
  intro g hg
  have h1 : (D.hom j).rangeRestrict g ∈ Subgroup.center (D.hom j).range :=
    (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨c, hc, hcg⟩ := center_le_map_center_of_perfect (D.hom j).rangeRestrict hψ hker h1
  have h2 : c⁻¹ * g ∈ (D.hom j).rangeRestrict.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
  have h3 : g = c * (c⁻¹ * g) := by group
  rw [h3]
  exact Subgroup.mul_mem _ hc (hker h2)

@[expose] def _root_.CFSG.ClassicalInvolution.Q3.LieSystemData3.ofComponent {X : Type} [Group X]
    (c : CompData) (hv : c.Valid) (ψ : c.G →* X) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center c.G) (Φ : Set (Subgroup X))
    (hfund : ∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map ψ) (hmeets : ∃ R ∈ c.fund, R.map ψ ∈ Φ)
    (hcard : ∀ L ∈ Φ, Nat.card L = 24) : LieSystemData3 PUnit X Φ where
  kind _ := c
  valid _ := hv
  hom _ := ψ
  ker_le_center _ := hker
  commute i j h _ _ := absurd (Subsingleton.elim i j) h
  generate := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := hsurj x
    exact Subgroup.mem_iSup_of_mem PUnit.unit ⟨g, rfl⟩
  fundamental L hL := ⟨PUnit.unit, hfund L hL⟩
  meets _ := hmeets
  card_eq := hcard

end Component

section Quotient

variable {Y : Type} [Group Y] [Finite Y] {ι : Type} {Λ : Set (Subgroup Y)}

theorem exists_centerQuotient_system (D : LieSystemData3 ι Y Λ) (j : ι)
    (hq : CFSG.Open.IsQuasisimple (D.kind j).G)
    (hfc : ∀ R ∈ (D.kind j).fund, ∀ g : (D.kind j).G, conjSub g R ∈ (D.kind j).fund)
    {R : Subgroup (D.kind j).G} (hR : R ∈ (D.kind j).fund) (hRΛ : R.map (D.hom j) ∈ Λ)
    {z : Y} (hz : IsClassicalMember3 (R.map (D.hom j)) z)
    (hzQ : z ∈ (D.hom j).range) :
    ∃ (Λ' : Set (Subgroup ((D.hom j).range ⧸ Subgroup.center (D.hom j).range)))
      (K' : Subgroup ((D.hom j).range ⧸ Subgroup.center (D.hom j).range)),
      InClass3 Λ' ∧ LieSystemMod3 Λ' ∧ K' ∈ Λ' ∧
        IsClassicalMember3 K'
          (QuotientGroup.mk' (Subgroup.center (D.hom j).range) ⟨z, hzQ⟩) := by
  set Q : Subgroup Y := (D.hom j).range with hQ
  set ψ : (D.kind j).G →* Q := (D.hom j).rangeRestrict with hψ
  set φ : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hφ
  have hQq : CFSG.Open.IsQuasisimple Q := isQuasisimple_range3 D j hq
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQq.2
  have hXq : CFSG.Open.IsQuasisimple (Q ⧸ Subgroup.center Q) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hQq (Subgroup.center Q) le_rfl
  have hXZ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ :=
    Q3NM.center_quotient_center_eq_bot_of_isQuasisimple hQq
  have hKQ : R.map (D.hom j) ≤ Q := Subgroup.map_le_range _ _
  have hRψ : (R.map (D.hom j)).subgroupOf Q = R.map ψ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, hrx⟩
      exact ⟨r, hr, Subtype.ext hrx⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, rfl⟩
  have hclQ : IsClassicalMember3 (R.map ψ) (⟨z, hzQ⟩ : Q) := by
    rw [← hRψ]
    exact hz.subgroupOf hKQ
  have hzc : (⟨z, hzQ⟩ : Q) ∉ Subgroup.center Q := hclQ.not_mem_center_of_quasisimple hQq
  have hz1 : φ ⟨z, hzQ⟩ ≠ 1 := fun h => hzc ((QuotientGroup.eq_one_iff _).mp h)
  have hker : φ.ker ≤ Subgroup.center Q := by
    rw [hφ, QuotientGroup.ker_mk']
  have hcl : IsClassicalMember3 ((R.map ψ).map φ) (φ ⟨z, hzQ⟩) :=
    hclQ.map_central φ (QuotientGroup.mk'_surjective _) hker hz1
  have hθ : centerQuotHom D j = φ.comp ψ := rfl
  have hK'eq : R.map (centerQuotHom D j) = (R.map ψ).map φ := by
    rw [hθ, Subgroup.map_map]
  have hcl' : IsClassicalMember3 (R.map (centerQuotHom D j)) (φ ⟨z, hzQ⟩) := by
    rw [hK'eq]
    exact hcl
  have hΛ' : InClass3 (Set.range fun x : Q ⧸ Subgroup.center Q =>
      conjSub x (R.map (centerQuotHom D j))) := inClass3_conjugates hcl'
  have hOX : classicalInvolutionOddCore (Q ⧸ Subgroup.center Q) = ⊥ :=
    Q3T.oddCore_eq_bot_of_quasisimple hXq hXZ hcl'.orderOf_eq_two
  have hcard : ∀ L ∈ Set.range (fun x : Q ⧸ Subgroup.center Q =>
      conjSub x (R.map (centerQuotHom D j))), Nat.card L = 24 := by
    rintro _ ⟨x, rfl⟩
    rw [natCard_conjSub']
    have h1 : Nat.card (R.map (centerQuotHom D j)) ≥ 24 := hcl'.card_ge
    have h2 : Nat.card (R.map (centerQuotHom D j)) ∣ Nat.card (R.map ψ) := by
      rw [hK'eq]
      exact Subgroup.card_map_dvd _ _
    have h3 : Nat.card (R.map ψ) = 24 := by
      rw [← hRψ, ← D.card_eq _ hRΛ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKQ).toEquiv
    rw [h3] at h2
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) h1
  have hfund : ∀ L ∈ Set.range (fun x : Q ⧸ Subgroup.center Q =>
      conjSub x (R.map (centerQuotHom D j))), ∃ R' ∈ (D.kind j).fund,
        L = R'.map (centerQuotHom D j) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := centerQuotHom_surjective D j x
    exact ⟨conjSub g R, hfc R hR g, conjSub_map (centerQuotHom D j) g R⟩
  have hmeets : ∃ R' ∈ (D.kind j).fund, R'.map (centerQuotHom D j) ∈ Set.range
      (fun x : Q ⧸ Subgroup.center Q => conjSub x (R.map (centerQuotHom D j))) :=
    ⟨R, hR, 1, conjSub_one _⟩
  have hLie3 : LieSystem3 (Q ⧸ Subgroup.center Q) (Set.range fun x : Q ⧸ Subgroup.center Q =>
      conjSub x (R.map (centerQuotHom D j))) :=
    ⟨PUnit, inferInstance, ⟨LieSystemData3.ofComponent (D.kind j) (D.valid j) (centerQuotHom D j)
      (centerQuotHom_surjective D j) (centerQuotHom_ker_le_center D j hq) _ hfund hmeets hcard⟩⟩
  exact ⟨_, R.map (centerQuotHom D j), hΛ', lieSystemMod3_of_lieSystem3_corefree hOX hLie3,
    ⟨1, conjSub_one _⟩, hcl'⟩

end Quotient

end CFSG.ClassicalInvolution.Q3.Q3TIY
