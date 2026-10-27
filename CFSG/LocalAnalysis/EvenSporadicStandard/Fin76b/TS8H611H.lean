module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611G

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem mem_W1_iff {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {q : G} :
    q ∈ Wsub h hα (zpowers α) ↔ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
      ∀ q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
        q * q' * q⁻¹ * q'⁻¹ = 1 ∨ q * q' * q⁻¹ * q'⁻¹ = α := by
  refine ⟨fun hq => ⟨hq.1, fun q' hq' => h.cmt_W1_Q hα hF hM hp hq hq'⟩, fun ⟨hq, hc⟩ => ?_⟩
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.Qs_eq_W1_W2 hα hF hM hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, -, -, hd2, -, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hαt1 : α * t ≠ 1 := fun e => hα.ne_t (by rw [eq_inv_of_mul_eq_one_left e, hti])
  have hαt3 : α * t ≠ α := fun e => h.t_ne (by simpa using e)
  have c12 : Commute a₁ a₂ := hcomm a₁ ha₁ a₂ ha₂
  have h2 : a₂ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine h.center_W2 hα hF hM hp ha₂ fun w' hw' => ?_
    have c1w : Commute a₁ w' := hcomm a₁ ha₁ w' hw'
    have cy : Commute a₁ (a₂ * w' * a₂⁻¹) := (c12.mul_right c1w).mul_right c12.inv_right
    have e1 : a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₂ * w' * a₂⁻¹ * w'⁻¹ := by
      calc a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₁ * (a₂ * w' * a₂⁻¹) * a₁⁻¹ * w'⁻¹ := by group
        _ = (a₂ * w' * a₂⁻¹) * a₁ * a₁⁻¹ * w'⁻¹ := by rw [cy.eq]
        _ = a₂ * w' * a₂⁻¹ * w'⁻¹ := by group
    rcases hd2 a₂ ha₂ w' hw' with e | e
    · exact e
    · exfalso
      rcases hc w' hw'.1 with e' | e'
      · rw [e1, e] at e'; exact hαt1 e'
      · rw [e1, e] at e'; exact hαt3 e'
  exact mul_mem ha₁ (h.Zg_mem_Wsub hα _ h2)

theorem mem_W2_iff {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {q : G} :
    q ∈ Wsub h hα (zpowers (α * t)) ↔ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
      ∀ q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
        q * q' * q⁻¹ * q'⁻¹ = 1 ∨ q * q' * q⁻¹ * q'⁻¹ = α * t := by
  refine ⟨fun hq => ⟨hq.1, fun q' hq' => h.cmt_W2_Q hα hF hM hp hq hq'⟩, fun ⟨hq, hc⟩ => ?_⟩
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.Qs_eq_W1_W2 hα hF hM hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, hd1, -, -, -, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  have hαt3 : α * t ≠ α := fun e => h.t_ne (by simpa using e)
  have h1 : a₁ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine h.center_W1 hα hF hM hp ha₁ fun w' hw' => ?_
    have c2w : Commute a₂ w' := (hcomm w' hw' a₂ ha₂).symm
    have e1 : a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₁ * w' * a₁⁻¹ * w'⁻¹ := by
      have : a₂ * w' * a₂⁻¹ = w' := by rw [c2w.eq]; group
      calc a₁ * a₂ * w' * (a₁ * a₂)⁻¹ * w'⁻¹ = a₁ * (a₂ * w' * a₂⁻¹) * a₁⁻¹ * w'⁻¹ := by group
        _ = a₁ * w' * a₁⁻¹ * w'⁻¹ := by rw [this]
    rcases hd1 a₁ ha₁ w' hw' with e | e
    · exact e
    · exfalso
      rcases hc w' hw'.1 with e' | e'
      · rw [e1, e] at e'; exact hα.ne_one e'
      · rw [e1, e] at e'; exact hαt3 e'.symm
  exact mul_mem (h.Zg_mem_Wsub hα _ h1) ha₂

theorem normalizer_Q_perm_W {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {g : G}
    (hg : ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    g * t * g⁻¹ = t ∧
    ((g * α * g⁻¹ = α ∧
      (∀ w ∈ Wsub h hα (zpowers α), g * w * g⁻¹ ∈ Wsub h hα (zpowers α)) ∧
      ∀ w ∈ Wsub h hα (zpowers (α * t)), g * w * g⁻¹ ∈ Wsub h hα (zpowers (α * t))) ∨
    (g * α * g⁻¹ = α * t ∧
      (∀ w ∈ Wsub h hα (zpowers α), g * w * g⁻¹ ∈ Wsub h hα (zpowers (α * t))) ∧
      ∀ w ∈ Wsub h hα (zpowers (α * t)), g * w * g⁻¹ ∈ Wsub h hα (zpowers α))) := by
  have hgt := h.normalizer_Q_fixes_t hα hF hM hp hg
  have hgq : ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := fun q hq => (hg q).1 hq
  have hgi : ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      g⁻¹ * q * g ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := fun q hq => by
    rw [hg, show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
    exact hq
  have hZ : g * α * g⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    have hαZ := h.alpha_mem_Zg hα
    refine (h.mem_Zg hα).2 ((h.center_QF hα).1 ⟨hgq α (h.Zg_cent_Q hα hαZ).1, fun q hq => ?_⟩)
    have e := (h.Zg_cent_Q hα hαZ).2 (g⁻¹ * q * g) (hgi q hq)
    calc g * α * g⁻¹ * q = g * (α * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * α) * g⁻¹ := by rw [e]
      _ = q * (g * α * g⁻¹) := by group
  have hgαt : g * (α * t) * g⁻¹ = (g * α * g⁻¹) * t := by
    calc g * (α * t) * g⁻¹ = (g * α * g⁻¹) * (g * t * g⁻¹) := by group
      _ = (g * α * g⁻¹) * t := by rw [hgt]
  have key : ∀ (c c' : G) (A : Subgroup G),
      (∀ w ∈ Wsub h hα A, ∀ q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
        w * q' * w⁻¹ * q'⁻¹ = 1 ∨ w * q' * w⁻¹ * q'⁻¹ = c) →
      g * c * g⁻¹ = c' → ∀ w ∈ Wsub h hα A, ∀ q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
        (g * w * g⁻¹) * q' * (g * w * g⁻¹)⁻¹ * q'⁻¹ = 1 ∨
          (g * w * g⁻¹) * q' * (g * w * g⁻¹)⁻¹ * q'⁻¹ = c' := by
    intro c c' A hA hcc' w hw q' hq'
    have e2 : (g * w * g⁻¹) * q' * (g * w * g⁻¹)⁻¹ * q'⁻¹ =
        g * (w * (g⁻¹ * q' * g) * w⁻¹ * (g⁻¹ * q' * g)⁻¹) * g⁻¹ := by group
    rw [e2]
    rcases hA w hw _ (hgi q' hq') with e3 | e3
    · left; rw [e3]; group
    · right; rw [e3, hcc']
  have hr1 : ∀ w ∈ Wsub h hα (zpowers α), ∀ q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      w * q' * w⁻¹ * q'⁻¹ = 1 ∨ w * q' * w⁻¹ * q'⁻¹ = α := fun w hw q' hq' =>
    h.cmt_W1_Q hα hF hM hp hw hq'
  have hr2 : ∀ w ∈ Wsub h hα (zpowers (α * t)), ∀ q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G),
      w * q' * w⁻¹ * q'⁻¹ = 1 ∨ w * q' * w⁻¹ * q'⁻¹ = α * t := fun w hw q' hq' =>
    h.cmt_W2_Q hα hF hM hp hw hq'
  refine ⟨hgt, ?_⟩
  rcases (h.mem_Zg hα).1 hZ with e | e | e | e
  · exact absurd (by simpa using e) hα.ne_one
  · exact absurd (mul_left_cancel (mul_right_cancel (e.trans hgt.symm))) hα.ne_t
  · left
    refine ⟨e, fun w hw => ?_, fun w hw => ?_⟩
    · exact (h.mem_W1_iff hα hF hM hp).2 ⟨hgq w hw.1, key α α _ hr1 e w hw⟩
    · refine (h.mem_W2_iff hα hF hM hp).2 ⟨hgq w hw.1, key (α * t) (α * t) _ hr2 ?_ w hw⟩
      rw [hgαt, e]
  · right
    refine ⟨e, fun w hw => ?_, fun w hw => ?_⟩
    · exact (h.mem_W2_iff hα hF hM hp).2 ⟨hgq w hw.1, key α (α * t) _ hr1 e w hw⟩
    · refine (h.mem_W1_iff hα hF hM hp).2 ⟨hgq w hw.1, key (α * t) α _ hr2 ?_ w hw⟩
      rw [hgαt, e, mul_assoc, h.t_sq, mul_one]

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
