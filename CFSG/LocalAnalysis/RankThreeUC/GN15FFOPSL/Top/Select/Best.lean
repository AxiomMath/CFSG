module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.RankThree.FFModules

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

noncomputable abbrev tautGL :
    Representation (ZMod 2) (W ≃ₗ[ZMod 2] W) W :=
  { toFun := fun g => (g : W →ₗ[ZMod 2] W)
    map_one' := by ext; rfl
    map_mul' := by intro a b; ext; rfl }

noncomputable abbrev tautRep (D : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Representation (ZMod 2) ↥D W :=
  { toFun := fun d => (d : W ≃ₗ[ZMod 2] W)
    map_one' := by ext; rfl
    map_mul' := by intro a b; ext; rfl }

omit [Finite W] in
@[simp] theorem tautRep_apply (D : Subgroup (W ≃ₗ[ZMod 2] W)) (d : ↥D) (w : W) :
    tautRep D d w = (d : W ≃ₗ[ZMod 2] W) w :=
  rfl

omit [Finite W] in
theorem fixOn_tautRep_top (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (Z : Submodule (ZMod 2) W) :
    fixOn (tautRep D) ⊤ Z = fixOn tautGL D Z := by
  ext w
  simp [fixOn, fixSub]

omit [Finite W] in
theorem cenOn_tautRep_top_map (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (Z : Submodule (ZMod 2) W) :
    (cenOn (tautRep D) ⊤ Z).map D.subtype = cenOn tautGL D Z := by
  ext g
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d.2, fun z hz => by simpa [tautRep_apply] using hd.2 z hz⟩
  · rintro ⟨hgD, hgZ⟩
    exact ⟨⟨g, hgD⟩, ⟨Subgroup.mem_top _, fun z hz => by
      simpa [tautRep_apply] using hgZ z hz⟩, rfl⟩

omit [Finite W] in
theorem card_cenOn_tautRep_top (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (Z : Submodule (ZMod 2) W) :
    Nat.card (cenOn (tautRep D) ⊤ Z) = Nat.card (cenOn tautGL D Z) := by
  have h := Subgroup.card_map_of_injective
    (K := cenOn (tautRep D) ⊤ Z) (f := D.subtype) D.subtype_injective
  rw [cenOn_tautRep_top_map] at h
  exact h.symm

omit [Finite W] in
theorem isOffenderOn_tautRep_iff (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (Z : Submodule (ZMod 2) W) :
    IsOffenderOn (tautRep D) ⊤ Z ↔ IsOffenderOn tautGL D Z := by
  constructor
  · rintro ⟨hel, hoff⟩
    refine ⟨fun a ha b hb => ?_, ?_⟩
    · simpa [tautRep_apply] using
        hel ⟨a, ha⟩ (Subgroup.mem_top _) ⟨b, hb⟩ (Subgroup.mem_top _)
    · rw [fixOn_tautRep_top, card_cenOn_tautRep_top, Subgroup.card_top] at hoff
      exact hoff
  · rintro ⟨hel, hoff⟩
    refine ⟨fun a _ b _ => ?_, ?_⟩
    · simpa [tautRep_apply] using hel a.1 a.2 b.1 b.2
    · rw [fixOn_tautRep_top, card_cenOn_tautRep_top, Subgroup.card_top]
      exact hoff

theorem exists_best_le {A : Subgroup (W ≃ₗ[ZMod 2] W)} (hA1 : A ≠ ⊥)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hoff : Nat.card W ≤ Nat.card ↥A * Nat.card {w : W // ∀ a ∈ A, a w = w}) :
    ∃ D : Subgroup (W ≃ₗ[ZMod 2] W), D ≤ A ∧ D ≠ ⊥ ∧
      Nat.card W ≤ Nat.card ↥D * Nat.card {w : W // ∀ d ∈ D, d w = w} ∧
      (∀ B : Subgroup (W ≃ₗ[ZMod 2] W), B ≤ D →
        Nat.card ↥B * Nat.card {w : W // ∀ b ∈ B, b w = w} ≤
          Nat.card ↥D * Nat.card {w : W // ∀ d ∈ D, d w = w}) ∧
      ∀ Z : Submodule (ZMod 2) W,
        (∀ d : ↥D, ∀ z ∈ Z, (d : W ≃ₗ[ZMod 2] W) z ∈ Z) →
          IsOffenderOn (tautRep D) ⊤ Z := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hfixB : ∀ B : Subgroup (W ≃ₗ[ZMod 2] W), Nat.card (fixOn tautGL B ⊤) =
      Nat.card {w : W // ∀ b ∈ B, b w = w} := by
    intro B
    refine Nat.card_congr ?_
    exact Equiv.subtypeEquivRight (fun w => by simp [fixOn, fixSub])
  have hcenB : ∀ B : Subgroup (W ≃ₗ[ZMod 2] W), cenOn tautGL B ⊤ = ⊥ := by
    intro B
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    exact LinearEquiv.ext (fun v => ha.2 v (Submodule.mem_top))
  have htop : Nat.card (⊤ : Submodule (ZMod 2) W) = Nat.card W :=
    Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := W)).toEquiv
  have hoffA : IsOffenderOn tautGL A ⊤ := by
    refine ⟨(isElemAbelianOn_top_iff (ρ := tautGL) (A := A)
      (fun a _ h => LinearEquiv.ext h)).mp hAel, ?_⟩
    rw [hfixB, hcenB, Subgroup.card_bot, htop, mul_one]
    exact hoff
  obtain ⟨D, hDA, hDbest, -, hcrit⟩ :=
    exists_bestOffender_le (ρ := tautGL) (B := A) hoffA
  refine ⟨D, hDA, ?_, ?_, ?_, ?_⟩
  · rcases hcrit with hne | hDA'
    · intro hbot
      rw [hbot] at hne
      refine hne ?_
      rw [eq_bot_iff, commOn, Submodule.span_le]
      rintro w ⟨a, ha, u, -, rfl⟩
      rw [Subgroup.mem_bot.mp ha]
      simp
    · rw [hDA']
      exact hA1
  · have h := (hDbest.forall_isInvariant_isOffenderOn ⊤
      (fun d _ z _ => Submodule.mem_top)).2
    rwa [hfixB, hcenB, Subgroup.card_bot, htop, mul_one] at h
  · intro B hB
    have h := hDbest.2 B hB
    rwa [hfixB, hfixB] at h
  · intro Z hZ
    exact (isOffenderOn_tautRep_iff D Z).mpr
      (hDbest.forall_isInvariant_isOffenderOn Z
        (fun d hd z hz => hZ ⟨d, hd⟩ z hz))

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
