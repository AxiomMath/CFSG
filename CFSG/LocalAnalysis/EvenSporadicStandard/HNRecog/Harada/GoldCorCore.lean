module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.GoldCor93
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.GoldCorHom
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {T : Sylow 2 X} {A : Subgroup X}

private def goldD (A : Subgroup X) (g : X) : Subgroup X :=
  A ⊓ A.comap (MulAut.conj g).toMonoidHom

@[simp] private theorem mem_goldD {A : Subgroup X} {g a : X} :
    a ∈ goldD A g ↔ a ∈ A ∧ g * a * g⁻¹ ∈ A := by
  simp only [goldD, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

theorem goldschmidt_cor_four (h : GoldHyp T A) {t g : X} (ht : t ∈ (T : Subgroup X))
    (ht2 : t * t = 1) (hg : g * t * g⁻¹ ∈ A) :
    ∃ B : Subgroup X, B ≤ (T : Subgroup X) ∧ IsElemAbelian 2 B ∧
      Nat.card A * Nat.card ↥(B ⊓ A) ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set X)) * Nat.card B := by
  classical
  haveI : Nonempty {g : X // g * t * g⁻¹ ∈ A} := ⟨⟨g, hg⟩⟩
  obtain ⟨x₀, hx₀max⟩ := Finite.exists_max
    (fun x : {g : X // g * t * g⁻¹ ∈ A} => Nat.card (goldD A x))
  let g₀ : X := x₀.1
  have hg₀ : g₀ * t * g₀⁻¹ ∈ A := x₀.2
  let B₁ : Subgroup X := goldD A g₀
  have hB₁A : B₁ ≤ A := inf_le_left
  have hB₁t : ∀ b ∈ B₁, t * b = b * t := by
    intro b hb
    obtain ⟨_, hgbA⟩ := mem_goldD.mp hb
    have hcommA := h.elemAb.comm hg₀ hgbA
    have h2 : (MulAut.conj g₀) (t * b) = (MulAut.conj g₀) (b * t) := by
      simpa only [map_mul, MulAut.conj_apply] using hcommA
    exact (MulAut.conj g₀).injective h2
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => h.normal_of_mem ht ha
  obtain ⟨B₂, hB₂A, hB₁B₂, hB₂, hcount⟩ :=
    gold_commutator_step h.elemAb ht2 htA hB₁A hB₁t
  let H : Subgroup X := B₁ ⊔ zpowers t
  have hB₁H : B₁ ≤ H := le_sup_left
  have hnorm : B₂ ≤ normalizer (H : Set X) :=
    gold_H1_normalizes h.elemAb hB₁A hB₂A hB₂
  have hB₂T : B₂ ≤ (T : Subgroup X) := fun b hb => h.le (hB₂A hb)
  have hHle : H ≤ A.comap (MulAut.conj g₀).toMonoidHom := by
    change B₁ ⊔ zpowers t ≤ A.comap (MulAut.conj g₀).toMonoidHom
    refine sup_le inf_le_right ?_
    rw [Subgroup.zpowers_le]
    exact hg₀
  have hg₀H : ∀ x ∈ H, g₀ * x * g₀⁻¹ ∈ A := fun x hx => hHle hx
  obtain ⟨g₁, hg₁H, hg₁T⟩ := goldschmidt_9_3_two h (B := H) ⟨g₀, hg₀H⟩
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hg₁tA : g₁ * t * g₁⁻¹ ∈ A := hg₁H t htH
  have hB₁Dg₁ : B₁ ≤ goldD A g₁ := by
    intro b hb
    exact mem_goldD.mpr ⟨hB₁A hb, hg₁H b (hB₁H hb)⟩
  have hcardmax : Nat.card (goldD A g₁) ≤ Nat.card B₁ :=
    hx₀max ⟨g₁, hg₁tA⟩
  have hDg₁ : goldD A g₁ = B₁ :=
    (Subgroup.eq_of_le_of_card_ge hB₁Dg₁ hcardmax).symm
  refine ⟨B₂.map (MulAut.conj g₁).toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hg₁T b ⟨hB₂T hb, hnorm hb⟩
  · exact (h.elemAb.mono hB₂A).map (MulAut.conj g₁).toMonoidHom
  · have hinter : (B₂.map (MulAut.conj g₁).toMonoidHom) ⊓ A =
        B₁.map (MulAut.conj g₁).toMonoidHom := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxB, hxA⟩ := Subgroup.mem_inf.mp hx
        rw [Subgroup.mem_map] at hxB
        obtain ⟨b, hb, rfl⟩ := hxB
        refine Subgroup.mem_map.mpr ⟨b, ?_, rfl⟩
        have hbD : b ∈ goldD A g₁ := mem_goldD.mpr ⟨hB₂A hb, hxA⟩
        rwa [hDg₁] at hbD
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨b, hb, rfl⟩ := hx
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨b, hB₁B₂ hb, rfl⟩
        · exact (mem_goldD.mp (hB₁Dg₁ hb)).2
    rw [hinter,
      Subgroup.card_map_of_injective (K := B₁) (f := (MulAut.conj g₁).toMonoidHom)
        (MulAut.conj g₁).injective,
      Subgroup.card_map_of_injective (K := B₂) (f := (MulAut.conj g₁).toMonoidHom)
        (MulAut.conj g₁).injective]
    exact hcount

end CFSG.EvenSporadicStandard.HNRecog.Harada
