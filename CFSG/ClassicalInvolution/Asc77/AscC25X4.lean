module

public import CFSG.ClassicalInvolution.Asc77.AscC25X3
public import CFSG.ClassicalInvolution.Asc77.AscC25X2
public import CFSG.ClassicalInvolution.Asc77.AscT7L6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace C25X

section Model

variable (p : ℕ) [Fact p.Prime]

@[expose] def NC4At (t : StatedLieTag) (k e : ℕ) : Prop :=
  ∃ R₁ ∈ ModelFund p t k e, ∃ R₂ ∈ ModelFund p t k e, ∃ y ∈ R₁, ∃ x₂ ∈ R₂,
    y * y * y * y = 1 ∧ y * y ≠ 1 ∧ x₂ * x₂ = 1 ∧ x₂ ≠ 1 ∧ x₂ * y = y * x₂ ∧
      (y * y) * x₂ ∉ Subgroup.center (modelUniv t k p e Fact.out).K

@[expose] def NC4Fact : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k p e → p ≠ 2 → 5 ≤ p ^ e →
    ((t = .PSL ∧ k = 4 ∧ p ^ e % 4 = 1) ∨ (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 3) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) →
    NC4At p t k e

end Model

section Section

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}


theorem s4_excl (hmf : NC4Fact p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {tg : StatedLieTag} {k ee : ℕ}
    (M : Ih8Model p f Φ tg k ee) (hne' : Φ.Nonempty)
    (hS4 : (tg = .PSL ∧ k = 4 ∧ p ^ f % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ p ^ f % 4 = 3) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4)) :
    ∃ J₁ ∈ Φ, ∃ J₂ ∈ Φ, ∃ y ∈ J₁, ∃ z₂ ∈ J₂, y * y * y * y = 1 ∧ y * y ≠ 1 ∧
      z₂ * z₂ = 1 ∧ z₂ ≠ 1 ∧ z₂ ≠ y * y ∧ z₂ * y = y * z₂ := by
  classical
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hS4 with h | h | h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hS4 with h | h | h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hS4 with h | h | h | h | h <;> simp at h
  have hee : ee = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ ee := by rw [hee]; exact hq
  obtain ⟨R₁, hR₁, R₂, hR₂, y, hy, x₂, hx₂, hy4, hy2, hx₂2, hx₂1, hcomm, hnc⟩ :=
    hmf tg k ee M.admissible hp2 hq' (by rw [hee]; exact hS4)
  have hR₁cls : R₁ ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR₁
  have hR₂cls : R₂ ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR₂
  have hinj₁ := M.injOn_fund hnpsl hR₁
  have hinj₂ := M.injOn_fund hnpsl hR₂
  have hyy : y * y ∈ R₁ := R₁.mul_mem hy hy
  refine ⟨R₁.map M.ψ, M.map_mem hR₁cls, R₂.map M.ψ, M.map_mem hR₂cls, M.ψ y,
    Subgroup.mem_map_of_mem _ hy, M.ψ x₂, Subgroup.mem_map_of_mem _ hx₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_mul, hy4, map_one]
  · intro h
    rw [← map_mul] at h
    exact hy2 (hinj₁ (y * y) hyy h)
  · rw [← map_mul, hx₂2, map_one]
  · intro h
    exact hx₂1 (hinj₂ x₂ hx₂ h)
  · intro h
    apply hnc
    rw [← map_mul] at h
    have hker : x₂ * (y * y)⁻¹ ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K := by
      apply M.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have hxinv : (y * y)⁻¹ = y * y := by
      apply inv_eq_of_mul_eq_one_right
      calc y * y * (y * y) = y * y * y * y := by simp only [mul_assoc]
        _ = 1 := hy4
    rw [hxinv] at hker
    have hc : (y * y) * x₂ = x₂ * (y * y) := by
      calc y * y * x₂ = y * (y * x₂) := by simp only [mul_assoc]
        _ = y * (x₂ * y) := by rw [hcomm]
        _ = (y * x₂) * y := by simp only [mul_assoc]
        _ = (x₂ * y) * y := by rw [hcomm]
        _ = x₂ * (y * y) := by simp only [mul_assoc]
    rw [hc]
    exact hker
  · rw [← map_mul, ← map_mul, hcomm]

end Section

section Layer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G}


theorem layer_a_tag (hmf : NC4Fact p) {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    (∀ L ∈ oddQuotientFamily (exactPair Ω a),
        L = T7H.exactImg Ω a K ∨ L = T7H.exactImg Ω a K') ∨
      LayerOrthType p f Ω a 5 true ∨ LayerOrthType p f Ω a 6 (!piSign p f) := by
  classical
  obtain ⟨_hzY, _hu₁Y, _hu₂Y, -, -, hS, hlt, T⟩ := layer_a_frame hyp ha2 ha1 haR haR'
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hBelow : CITBelowU p f (Nat.card G) := hst.below f hq
  rcases twinSection_cases0 hp hq hBelow hlt hS T with hconn | ⟨D, hcard, i, hsix⟩
  · left
    exact hconn
  · right
    let M := T7L.toModelOfGen hS.hyp D hcard hS.gen i
    have hodd : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp).pow
    have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
      obtain ⟨j, hj⟩ := hodd
      omega
    have key : ((D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ f % 4 = 1) ∨
        (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ f % 4 = 3) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) →
        False := by
      intro hS4
      obtain ⟨J₁, hJ₁, J₂, hJ₂, y, hy, z₂, hz₂, hy4, hy2, hz₂2, hz₂1, hne, hcomm⟩ :=
        s4_excl hmf hp hq M ⟨_, T.hA⟩ hS4
      exact nc4_layer_excl hyp ha2 hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
    rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inl ⟨rfl, h1, h2⟩, D, hcard, i, rfl, rfl⟩
    · rcases hmod with h3 | h3
      · exact (key (Or.inl ⟨h1, h2, h3⟩)).elim
      · right
        have hπ : piSign p f = false := by
          unfold piSign
          simp [h3]
        rw [hπ]
        exact sectionOrthType_of_hasOrthType hS.gen
          ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩), D, hcard, i, rfl, rfl⟩
    · rcases hmod with h3 | h3
      · right
        have hπ : piSign p f = true := by
          unfold piSign
          simp [h3]
        rw [hπ]
        exact sectionOrthType_of_hasOrthType hS.gen
          ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)), D, hcard, i, rfl, rfl⟩
      · exact (key (Or.inr (Or.inl ⟨h1, h2, h3⟩))).elim
    · exact (key (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
    · exact (key (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))).elim
    · exact (key (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))).elim

end Layer

end C25X

end CFSG.ClassicalInvolution.Asc77
