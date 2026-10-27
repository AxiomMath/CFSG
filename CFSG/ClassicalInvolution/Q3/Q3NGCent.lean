module

public import CFSG.ClassicalInvolution.AschTight.S19GC3
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]


theorem nonempty_centralizer_equiv_d4' (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {E : Type*} [Group E]
    (f : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) →* E)
    (hf : Function.Bijective f)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e))) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), (2 : F) ≠ 0 ∧
      Nonempty (↥(Subgroup.centralizer ((R.map f : Subgroup E) : Set E)) ≃* SL(2, F)) := by
  obtain ⟨hσ3, hK1, hC₀, hgF, hoddK, hoddF⟩ := d4_model_data hp2 he
  obtain ⟨i, g₀, hRg⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨g, hg⟩ : ∃ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), g = g₀ :=
    ⟨g₀, rfl⟩
  have hR' : R = conjSub g (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    rw [hg]
    exact hRg
  subst hR'
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3]
    exact ⟨GaloisField p (3 * e), inferInstance, Fintype.ofFinite _,
      CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hoddK,
      nonempty_centralizer_equiv f hf _ g (slB _ hσ3) (slB_injective hσ3)
        (centralizer_range_slLong hσ3 hK1 hC₀ hgF)⟩
  · have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3]
    exact ⟨↥(fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)), inferInstance,
      Fintype.ofFinite _, CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hoddF,
      nonempty_centralizer_equiv f hf _ g _
        ((MulAut.conj _).injective.comp (slLong_injective hσ3))
        (centralizer_range_slShort hσ3 hK1 hC₀ hgF)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups


section Involutions

theorem eq_of_involutions_in_centralizer {M X : Type} [Group M] [Group X] (φ : M →* X)
    {R : Subgroup M} {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (ε : ↥(Subgroup.centralizer ((R.map φ.rangeRestrict : Subgroup φ.range) : Set φ.range)) ≃*
      SL(2, F))
    {y₁ y₂ : X} (h₁ : y₁ ∈ φ.range) (h₂ : y₂ ∈ φ.range) (sq₁ : y₁ * y₁ = 1) (sq₂ : y₂ * y₂ = 1)
    (ne₁ : y₁ ≠ 1) (ne₂ : y₂ ≠ 1) (c₁ : ∀ r ∈ R, φ r * y₁ = y₁ * φ r)
    (c₂ : ∀ r ∈ R, φ r * y₂ = y₂ * φ r) : y₁ = y₂ := by
  have each : ∀ (y : X) (hy : y ∈ φ.range), y * y = 1 → y ≠ 1 → (∀ r ∈ R, φ r * y = y * φ r) →
      ∃ hyC : (⟨y, hy⟩ : φ.range) ∈ Subgroup.centralizer
        ((R.map φ.rangeRestrict : Subgroup φ.range) : Set φ.range), ε ⟨⟨y, hy⟩, hyC⟩ = -1 := by
    intro y hy hsq hne hc
    have hyC : (⟨y, hy⟩ : φ.range) ∈ Subgroup.centralizer
        ((R.map φ.rangeRestrict : Subgroup φ.range) : Set φ.range) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      exact Subtype.ext (hc r hr)
    refine ⟨hyC, ?_⟩
    have hA : ε ⟨⟨y, hy⟩, hyC⟩ * ε ⟨⟨y, hy⟩, hyC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨⟨y, hy⟩, hyC⟩ : ↥(Subgroup.centralizer
          ((R.map φ.rangeRestrict : Subgroup φ.range) : Set φ.range))) * ⟨⟨y, hy⟩, hyC⟩ = 1 :=
        Subtype.ext (Subtype.ext hsq)
      rw [this, map_one]
    rcases CFSG.ClassicalInvolution.G2D4Models.sl2_sq_eq_one_of_two_ne_zero h2 _ hA with h | h
    · exfalso
      apply hne
      have : (⟨⟨y, hy⟩, hyC⟩ : ↥(Subgroup.centralizer
          ((R.map φ.rangeRestrict : Subgroup φ.range) : Set φ.range))) = 1 :=
        ε.injective (by rw [h, map_one])
      exact congrArg Subtype.val (congrArg Subtype.val this)
    · exact h
  obtain ⟨hy₁C, e₁⟩ := each y₁ h₁ sq₁ ne₁ c₁
  obtain ⟨hy₂C, e₂⟩ := each y₂ h₂ sq₂ ne₂ c₂
  have := ε.injective (e₁.trans e₂.symm)
  exact congrArg Subtype.val (congrArg Subtype.val this)

theorem eq_of_involutions_centralizing3 {t : StatedLieTag} {n : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hadm : StatedLieAdmissible t n 3 1) {X : Type} [Group X]
    (φ : (CompData.model t n).G →* X) (hφ : Function.Injective φ)
    {R : Subgroup (CompData.model t n).G} (hR : R ∈ (CompData.model t n).fund) {y₁ y₂ : X}
    (h₁ : y₁ ∈ φ.range) (h₂ : y₂ ∈ φ.range) (sq₁ : y₁ * y₁ = 1) (sq₂ : y₂ * y₂ = 1)
    (ne₁ : y₁ ≠ 1) (ne₂ : y₂ ≠ 1) (c₁ : ∀ r ∈ R, φ r * y₁ = y₁ * φ r)
    (c₂ : ∀ r ∈ R, φ r * y₂ = y₂ * φ r) : y₁ = y₂ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hbij : Function.Bijective φ.rangeRestrict :=
    ⟨fun a b h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  rcases ht with rfl | rfl
  · obtain ⟨hn, -⟩ := hadm.2.2
    subst hn
    obtain ⟨ε⟩ := CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.nonempty_centralizer_equiv_g2
      (p := 3) hp2 (e := 1) le_rfl φ.rangeRestrict hbij hR
    exact eq_of_involutions_in_centralizer φ two_ne_zero_gf3 ε h₁ h₂ sq₁ sq₂ ne₁ ne₂ c₁ c₂
  · have hn : n = 0 := hadm.2.2
    subst hn
    obtain ⟨F, _, _, h2, ⟨ε⟩⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.nonempty_centralizer_equiv_d4'
        (p := 3) hp2 (e := 1) le_rfl φ.rangeRestrict hbij hR
    exact eq_of_involutions_in_centralizer φ h2 ε h₁ h₂ sq₁ sq₂ ne₁ ne₂ c₁ c₂

end Involutions

end CFSG.ClassicalInvolution.Q3.Q3W
