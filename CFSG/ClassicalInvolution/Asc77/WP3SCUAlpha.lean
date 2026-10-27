module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha
public import CFSG.ClassicalInvolution.Asc77.WP3SCUGL
public import CFSG.ClassicalInvolution.Asc77.WP3SCUGU
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open scoped commutatorElement MatrixGroups

section Abstract

variable {X : Type} [Group X]

theorem alphaOf_eq_bot_of_strongConclusion {L F : Subgroup X}
    (hfaith : ∀ x : X, (∀ y ∈ L, x * y = y * x) → x = 1) (hSC : StrongConclusion L F) :
    alphaOf F = ⊥ := by
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd g hg
    have hc := hSC.2 a ha ha1 d hd g hg
    have hu : ((g * d)⁻¹ * (d * g)) = 1 := by
      apply hfaith
      intro y hy
      have h1 := hc y hy
      calc (g * d)⁻¹ * (d * g) * y = (g * d)⁻¹ * ((d * g) * y * (d * g)⁻¹) * (d * g) := by group
        _ = (g * d)⁻¹ * ((g * d) * y * (g * d)⁻¹) * (d * g) := by
          rw [show (d * g) * y * (d * g)⁻¹ = d * g * y * (d * g)⁻¹ from rfl, h1]
        _ = y * ((g * d)⁻¹ * (d * g)) := by group
    have hdg : d * g = g * d := by
      have := congrArg (fun w => (g * d) * w) hu
      simpa [mul_assoc] using this
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc d * g * d⁻¹ * g⁻¹ = (g * d) * d⁻¹ * g⁻¹ := by rw [hdg]
      _ = 1 := by group
  · rw [eq_bot_iff]
    intro d hd
    have hd' : d ∈ deltaCore F := hd
    rw [Subgroup.mem_bot]
    exact hfaith d fun y hy => hSC.1 d hd' y hy

end Abstract

section Models

variable {p e n : ℕ}

theorem conj_innerHom {S Q : Type} [Group S] [Group Q] (ψ : S →* Q) {b : Q}
    (hb : b ∈ Subgroup.normalizer (ψ.range : Set Q)) {s s' : S} (h : b * ψ s * b⁻¹ = ψ s') :
    toInducedAutOn ψ.range ⟨b, hb⟩ * FrameVertex.innerHom ψ s *
        (toInducedAutOn ψ.range ⟨b, hb⟩)⁻¹ = FrameVertex.innerHom ψ s' := by
  rw [FrameVertex.innerHom_apply, FrameVertex.innerHom_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact h

theorem strongConclusion_of_toralActionDiag {t : StatedLieTag} (hp : p.Prime)
    (htag : t = .PSL ∨ t = .PSU) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) {X : Type} [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hdiag : ToralActionDiag 2 t n p e hp ψ F) : StrongConclusion ψ.range F := by
  have : Fact p.Prime := ⟨hp⟩
  rcases htag with rfl | rfl
  · obtain ⟨ε, hε⟩ := hdiag.1 rfl
    have hrange := BootRank3.range_comp_symm ε ψ
    have hker' := BootRank3.ker_comp_symm_le_center ε ψ hker
    by_cases h3 : 3 ≤ n
    · have := strongConclusion_gf_diag h3 hp2 h5 (ψ.comp ε.symm.toMonoidHom) hker'
        (by rw [hrange]; exact hnorm) hcard hF2 hε
      rwa [hrange] at this
    · obtain rfl : n = 2 := by have := hadm.2.2.1; omega
      exact (Linear.false_of_toralDiagGL_two
        (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2)
        (ψ.comp ε.symm.toMonoidHom) hcard hF2
        (fun f hf hf1 h => hfaith f hf hf1 (by rwa [hrange] at h)) hε).elim
  · obtain ⟨ε, hε⟩ := hdiag.2.1 rfl
    have hrange := BootRank3.range_comp_symm ε ψ
    have hker' := BootRank3.ker_comp_symm_le_center ε ψ hker
    have h3 : 3 ≤ n := hadm.2.2.1
    have := strongConclusion_su_gf hp2 h5 h3 (ψ.comp ε.symm.toMonoidHom) hker'
      (by rw [hrange]; exact hnorm) hcard hF2 hε
    rwa [hrange] at this

end Models

namespace FrameVertex

section Alpha

variable {p e n : ℕ} {Q : Type} [Group Q] [Finite Q]

theorem alphaOf_inducedImage_eq_bot_of_toralDiag {t : StatedLieTag} {hp : p.Prime}
    (htag : t = .PSL ∨ t = .PSU) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) [Group.IsPerfect (modelUniv t n p e hp).K]
    (ψ : (modelUniv t n p e hp).K →* Q)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {B : Subgroup Q}
    (hB2 : ∀ x ∈ B, x * x = 1) (hBcard : Nat.card B = 8)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set Q)) {Z : Subgroup Q} (hZcard : Nat.card Z = 2)
    (hZB : Z ≤ B) (hZ : ∀ z ∈ Z, ∀ y ∈ ψ.range, z * y = y * z)
    (hZ' : ∀ b ∈ B, (∀ y ∈ ψ.range, b * y = y * b) → b ∈ Z)
    (hdiag : ToralActionDiag 2 t n p e hp ψ B) :
    alphaOf (inducedImage ψ.range B) = ⊥ := by
  classical
  obtain ⟨hcen, hnorm, hfaith⟩ := innerHom_spec ψ hker
  set L : Subgroup Q := ψ.range with hL
  set πB : ↥B →* ↥(inducedAutOn L) := (toInducedAutOn L).comp (Subgroup.inclusion hBN) with hπB
  have hπB_apply : ∀ b : ↥B, πB b = toInducedAutOn L ⟨b, hBN b.2⟩ := fun b => rfl
  have hF : inducedImage L B = πB.range := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hBN b.2⟩, b.2, rfl⟩
  have hker_iff : ∀ b : ↥B, πB b = 1 ↔ (b : Q) ∈ Z := by
    intro b
    rw [hπB_apply]
    constructor
    · intro h1
      exact hZ' b b.2 (Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hBN b.2) h1)
    · intro h1
      exact Lemma52Proof.toInducedAutOn_eq_one_of_commute L (hBN b.2) (hZ _ h1)
  have hkerEq : πB.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker_iff]
  have hcardker : Nat.card πB.ker = 2 := by
    rw [hkerEq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv).trans hZcard
  have hcardF : Nat.card (inducedImage L B) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup πB.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange πB).toEquiv, hcardker, hBcard] at h1
    rw [hF]
    omega
  have hFsq : ∀ f ∈ inducedImage L B, f * f = 1 := by
    intro f hf
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hB2 b b.2)
    rw [this, map_one]
  have hFfaith : ∀ f ∈ inducedImage L B, f ≠ 1 → ¬ ∀ x ∈ (innerHom ψ).range, f * x = x * f :=
    fun f _ hf1 hall => hf1 (hfaith f hall)
  have hdiagX : ToralActionDiag 2 t n p e hp (innerHom ψ) (inducedImage L B) := by
    rcases htag with rfl | rfl
    · obtain ⟨ε, P, hP, hact⟩ := hdiag.1 rfl
      refine ⟨fun _ => ⟨ε, P, hP, fun f hf => ?_⟩, (fun h => by cases h),
        (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
        (fun h => by cases h), (fun h => absurd rfl h)⟩
      rw [hF] at hf
      obtain ⟨b, rfl⟩ := hf
      obtain ⟨x, hxP, hx2, hxact⟩ := hact b b.2
      refine ⟨x, hxP, hx2, fun y => ?_⟩
      rw [hπB_apply]
      exact conj_innerHom ψ (hBN b.2) (hxact y)
    · obtain ⟨ε, P, hP, hact⟩ := hdiag.2.1 rfl
      refine ⟨(fun h => by cases h), fun _ => ⟨ε, P, hP, fun f hf => ?_⟩,
        (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
        (fun h => by cases h), (fun _ h => absurd rfl h)⟩
      rw [hF] at hf
      obtain ⟨b, rfl⟩ := hf
      obtain ⟨x, hxP, hx2, hxact⟩ := hact b b.2
      refine ⟨x, hxP, hx2, fun y => ?_⟩
      rw [hπB_apply]
      exact conj_innerHom ψ (hBN b.2) (hxact y)
  have hSC := strongConclusion_of_toralActionDiag hp htag hadm hp2 h5 (innerHom ψ)
    (fun g hg => hcen g (MonoidHom.mem_ker.mp hg)) hnorm hcardF hFsq hFfaith hdiagX
  exact alphaOf_eq_bot_of_strongConclusion hfaith hSC

end Alpha

end FrameVertex

end CFSG.ClassicalInvolution.Asc77
