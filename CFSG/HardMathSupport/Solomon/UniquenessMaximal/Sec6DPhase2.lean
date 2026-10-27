module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DPhase1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X2

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_barCenterX_iff {p : ℕ} {X K : Subgroup G} {ζ : ↥X ⧸ GLAPPrimeCore p ↥X} :
    ζ ∈ barCenterX p X K ↔ ζ ∈ barX p X K ∧ ∀ u ∈ barX p X K, ζ * u = u * ζ := by
  unfold barCenterX
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨c, hc⟩, hcen, rfl⟩
    refine ⟨hc, fun u hu => ?_⟩
    have := Subgroup.mem_center_iff.1 hcen ⟨u, hu⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hζ, h⟩
    refine ⟨⟨ζ, hζ⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (h g g.2).symm

theorem commutes_sup3 {Q : Type*} [Group Q] {A C D : Subgroup Q} {ζ : Q}
    (hA : ∀ u ∈ A, ζ * u = u * ζ) (hC : ∀ u ∈ C, ζ * u = u * ζ) (hD : ∀ u ∈ D, ζ * u = u * ζ) :
    ∀ u ∈ A ⊔ C ⊔ D, ζ * u = u * ζ := by
  have : A ⊔ C ⊔ D ≤ Subgroup.centralizer ({ζ} : Set Q) := by
    refine sup_le (sup_le (fun u hu => ?_) (fun u hu => ?_)) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hA u hu).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hC u hu).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hD u hu).symm
  intro u hu
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this hu)).symm

theorem barCenterX_le_of_comps {X K₁ K₂ K₃ : Subgroup G} (h₁ : GLAPComponent 3 X K₁)
    (h₂ : GLAPComponent 3 X K₂) (h₃ : GLAPComponent 3 X K₃) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃)
    (h23 : K₂ ≠ K₃) :
    barCenterX 3 X K₁ ≤ barCenterX 3 X (K₁ ⊔ K₂ ⊔ K₃) ∧
    barCenterX 3 X K₂ ≤ barCenterX 3 X (K₁ ⊔ K₂ ⊔ K₃) ∧
    barCenterX 3 X K₃ ≤ barCenterX 3 X (K₁ ⊔ K₂ ⊔ K₃) := by
  have hbar : ∀ {A C : Subgroup G}, GLAPComponent 3 X A → GLAPComponent 3 X C → A ≠ C →
      ∀ ζ ∈ barX 3 X A, ∀ u ∈ barX 3 X C, ζ * u = u * ζ := by
    intro A C hA hC hne ζ hζ u hu
    have hb : barX 3 X A ≠ barX 3 X C := fun h => hne (glaPComponent_unique hA hC h)
    have hcomm : ⁅barX 3 X A, barX 3 X C⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA.2.2.1 hC.2.2.1 hb
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hcen hζ) u hu).symm
  have hsup : barX 3 X (K₁ ⊔ K₂ ⊔ K₃) = barX 3 X K₁ ⊔ barX 3 X K₂ ⊔ barX 3 X K₃ := by
    rw [barX_sup (sup_le h₁.1 h₂.1) h₃.1, barX_sup h₁.1 h₂.1]
  refine ⟨fun ζ hζ => ?_, fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · rw [mem_barCenterX_iff] at hζ ⊢
    rw [hsup]
    refine ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left hζ.1), commutes_sup3 hζ.2
      (fun u hu => hbar h₁ h₂ h12 ζ hζ.1 u hu) (fun u hu => hbar h₁ h₃ h13 ζ hζ.1 u hu)⟩
  · rw [mem_barCenterX_iff] at hζ ⊢
    rw [hsup]
    refine ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right hζ.1), commutes_sup3
      (fun u hu => hbar h₂ h₁ h12.symm ζ hζ.1 u hu) hζ.2
      (fun u hu => hbar h₂ h₃ h23 ζ hζ.1 u hu)⟩
  · rw [mem_barCenterX_iff] at hζ ⊢
    rw [hsup]
    refine ⟨Subgroup.mem_sup_right hζ.1, commutes_sup3
      (fun u hu => hbar h₃ h₁ h13.symm ζ hζ.1 u hu)
      (fun u hu => hbar h₃ h₂ h23.symm ζ hζ.1 u hu) hζ.2⟩


theorem barX_Zc_le_barCenterX {X S : Subgroup G} (hS : S ≤ X) :
    barX 3 X (Zc S) ≤ barCenterX 3 X S := by
  intro ζ hζ
  rw [mem_barCenterX_iff]
  obtain ⟨z, hz, rfl⟩ := mem_barX_iff.1 hζ
  have hzZ := mem_Zc.1 hz
  refine ⟨mem_barX_iff.2 ⟨z, hzZ.1, rfl⟩, fun u hu => ?_⟩
  obtain ⟨r, hr, rfl⟩ := mem_barX_iff.1 hu
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hzZ.2 r hr)

section W9

variable {X B K : Subgroup G} {y : G}

theorem barX_W_le_center (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3)
    {R : Subgroup G} (hRle : R ≤ bClosure B K) (hRp : IsPGroup 3 ↥R)
    (hc1 : barCenterX 3 X (R ⊓ K) = barCenterX 3 X K)
    (hc2 : barCenterX 3 X (R ⊓ GLBConj y K) = barCenterX 3 X (GLBConj y K))
    (hc3 : barCenterX 3 X (R ⊓ GLBConj y (GLBConj y K)) =
      barCenterX 3 X (GLBConj y (GLBConj y K))) :
    barX 3 X (Zc (R ⊓ K) ⊔ Zc (R ⊓ GLBConj y K) ⊔ Zc (R ⊓ GLBConj y (GLBConj y K))) ≤
      barCenterX 3 X (bClosure B K) := by
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates hB hy hyN h3
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  have hcl := bClosure_eq_three hB hy hyN h3
  obtain ⟨b1, b2, b3⟩ := barCenterX_le_of_comps hK hK2 hK3 hne1 hne2 hne3
  rw [← hcl] at b1 b2 b3
  have hz1 : Zc (R ⊓ K) ≤ X := (Zc_le _).trans (inf_le_right.trans hK.1)
  have hz2 : Zc (R ⊓ GLBConj y K) ≤ X := (Zc_le _).trans (inf_le_right.trans hK2.1)
  have hz3 : Zc (R ⊓ GLBConj y (GLBConj y K)) ≤ X := (Zc_le _).trans (inf_le_right.trans hK3.1)
  rw [barX_sup (sup_le hz1 hz2) hz3, barX_sup hz1 hz2]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (barX_Zc_le_barCenterX (inf_le_right.trans hK.1)).trans (hc1 ▸ b1)
  · exact (barX_Zc_le_barCenterX (inf_le_right.trans hK2.1)).trans (hc2 ▸ b2)
  · exact (barX_Zc_le_barCenterX (inf_le_right.trans hK3.1)).trans (hc3 ▸ b3)

theorem card_W_le (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hK : GLAPComponent 3 X K)
    (hy : y ∈ B) (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3)
    {R : Subgroup G} (hRle : R ≤ bClosure B K) (hRp : IsPGroup 3 ↥R)
    (hc1 : barCenterX 3 X (R ⊓ K) = barCenterX 3 X K)
    (hc2 : barCenterX 3 X (R ⊓ GLBConj y K) = barCenterX 3 X (GLBConj y K))
    (hc3 : barCenterX 3 X (R ⊓ GLBConj y (GLBConj y K)) =
      barCenterX 3 X (GLBConj y (GLBConj y K)))
    (hZ : Nat.card (barCenterX 3 X (bClosure B K)) ≤ 9) :
    Nat.card ↥(Zc (R ⊓ K) ⊔ Zc (R ⊓ GLBConj y K) ⊔ Zc (R ⊓ GLBConj y (GLBConj y K))) ≤ 9 := by
  obtain ⟨hne1, hne2, hne3, -⟩ := three_conjugates hB hy hyN h3
  obtain ⟨hK2, hK3⟩ := phase1_comps hK hBX hy
  have hbar := barX_W_le_center hB hBX hK hy hyN h3 hRle hRp hc1 hc2 hc3
  set W₀ := Zc (R ⊓ K) ⊔ Zc (R ⊓ GLBConj y K) ⊔ Zc (R ⊓ GLBConj y (GLBConj y K)) with hW₀
  have hz1 : Zc (R ⊓ K) ≤ X := (Zc_le _).trans (inf_le_right.trans hK.1)
  have hz2 : Zc (R ⊓ GLBConj y K) ≤ X := (Zc_le _).trans (inf_le_right.trans hK2.1)
  have hz3 : Zc (R ⊓ GLBConj y (GLBConj y K)) ≤ X := (Zc_le _).trans (inf_le_right.trans hK3.1)
  have hW₀X : W₀ ≤ X := sup_le (sup_le hz1 hz2) hz3
  have hW₀R : W₀ ≤ R := sup_le (sup_le ((Zc_le _).trans inf_le_left) ((Zc_le _).trans inf_le_left))
    ((Zc_le _).trans inf_le_left)
  have hW₀p : IsPGroup 3 ↥W₀ := hRp.to_le hW₀R
  rw [← card_barX_of_isPGroup Nat.prime_three hW₀X hW₀p]
  exact (Subgroup.card_le_of_le hbar).trans hZ

end W9

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
