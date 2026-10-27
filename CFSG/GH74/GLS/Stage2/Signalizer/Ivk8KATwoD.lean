module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBFix
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gGraph
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.Quasithin.H13.J4Core

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.PSL3Four
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

local notation "Perm42" => Equiv.Perm (Fin 42)

theorem mem_normalizer_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    {P : Subgroup A} {g : A} (hg : g ∈ normalizer (P : Set A)) :
    f g ∈ normalizer ((P.map f : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨g * e * g⁻¹, (hg e).1 he, by simp⟩
  · rintro ⟨e', he', hx⟩
    refine ⟨g⁻¹ * e' * g, ?_, ?_⟩
    · apply (hg (g⁻¹ * e' * g)).2
      have e : g * (g⁻¹ * e' * g) * g⁻¹ = e' := by group
      rw [e]
      exact he'
    · have hx' : f g * x * (f g)⁻¹ = f e' := hx.symm
      simp only [map_mul, map_inv]
      rw [← hx']
      group

section Model


@[expose] noncomputable def toPerm {Y : Type} [Group Y] (χ : Y ≃* ↥S) : MulAut Y →* Perm42 :=
  R.subtype.comp (toR χ).toMonoidHom

theorem toPerm_apply {Y : Type} [Group Y] (χ : Y ≃* ↥S) (z : MulAut Y) :
    toPerm χ z = ((toR χ z : ↥R) : Perm42) := rfl

theorem toPerm_injective {Y : Type} [Group Y] (χ : Y ≃* ↥S) : Function.Injective (toPerm χ) :=
  R.subtype_injective.comp (toR χ).injective

theorem toPerm_mem_R {Y : Type} [Group Y] (χ : Y ≃* ↥S) (z : MulAut Y) : toPerm χ z ∈ R :=
  (toR χ z).2

theorem toPerm_conj {Y : Type} [Group Y] (χ : Y ≃* ↥S) (y : Y) :
    toPerm χ (MulAut.conj y) = (χ y : Perm42) := by
  rw [toPerm_apply, toR_conj]
  rfl

theorem toPerm_eq_rr {Y : Type} [Group Y] {i : Fin 4} (χ : Y ≃* ↥S) {α : MulAut Y}
    (hχ : MulAut.congr χ α = Cls3.conjIso (rrR i)) : toPerm χ α = rr i := by
  have hTα : toR χ α = rrR i := by
    show Cls3.conjIso.symm (MulAut.congr χ α) = rrR i
    rw [hχ, MulEquiv.symm_apply_apply]
  rw [toPerm_apply, hTα, coe_rrR]

theorem mem_innSub_of_toPerm {Y : Type} [Group Y] (χ : Y ≃* ↥S) {z : MulAut Y}
    (hz : toPerm χ z ∈ S) : z ∈ innSub Y := by
  refine ⟨χ.symm ⟨toPerm χ z, hz⟩, ?_⟩
  apply toPerm_injective χ
  show toPerm χ (MulAut.conj (χ.symm ⟨toPerm χ z, hz⟩)) = toPerm χ z
  rw [toPerm_conj, MulEquiv.apply_symm_apply]

theorem pcfg_map {Y : Type} [Group Y] {i : Fin 4} (χ : Y ≃* ↥S) {α : MulAut Y}
    (hχ : MulAut.congr χ α = Cls3.conjIso (rrR i)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut Y)} (hP : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ e ∈ P, e * α = α * e)
    (hnorm : ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) :
    PCfg (rr i) p (P.map (toPerm χ)) := by
  have hι := toPerm_injective χ
  have hια := toPerm_eq_rr χ hχ
  refine ⟨hp, hp2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, _, rfl⟩
    exact toPerm_mem_R χ e
  · exact hP.of_equiv (P.equivMapOfInjective _ hι)
  · exact fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 h)
  · rintro _ ⟨e, he, rfl⟩
    rw [← hια, ← map_mul, ← map_mul, hcomm e he]
  · intro s hs hsr hso
    have hmem : (⟨s, hs⟩ : ↥S) ∈ (CC i).subgroupOf S :=
      Subgroup.mem_subgroupOf.2 (mem_CC.2 ⟨hsr, hs⟩)
    have hfix : (⟨s, hs⟩ : ↥S) ∈ fixSub (MulAut.congr χ α) := by
      have h1 : (⟨s, hs⟩ : ↥S) ∈ P85.fixSub (Cls3.conjIso (rrR i)) := by
        rw [P85.fixSub_conjIso]
        exact hmem
      rw [hχ]
      exact h1
    rw [← fixSub_congr] at hfix
    obtain ⟨y, hyfix, hyχ⟩ := hfix
    have hyodd : Odd (orderOf y) := by
      have h1 : orderOf (χ y) = orderOf y := MulEquiv.orderOf_eq χ y
      have h2 : orderOf (χ y) = orderOf s := by
        have h3 : χ y = ⟨s, hs⟩ := hyχ
        rw [h3]
        exact Subgroup.orderOf_mk s hs
      rw [← h1, h2]
      exact hso
    have hn := mem_normalizer_map (toPerm χ) (hnorm y hyfix hyodd)
    rw [toPerm_conj] at hn
    have hy : (χ y : Perm42) = s := congrArg Subtype.val hyχ
    rw [hy] at hn
    exact hn

theorem ka34_of_model {Y : Type} [Group Y] (hF : LieModel Y .PSL 3 2 2) {α : MulAut Y}
    (hα2 : α * α = 1) (hα1 : α ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut Y)} (hP : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ e ∈ P, e * α = α * e)
    (hnorm : ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) :
    (∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) ∧
      (IsCyclic ↥P ∨ (p = 3 ∧ α ∉ innSub Y ∧ Nat.card ↥(fixSub α) = 72)) := by
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hF
  have h2' : MulAut.congr ψ α * MulAut.congr ψ α = 1 := by rw [← map_mul, hα2, map_one]
  have h1' : MulAut.congr ψ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
  obtain ⟨i, β, hβ⟩ := exists_class_rep h2' h1'
  have hχ : MulAut.congr (ψ.trans β) α = Cls3.conjIso (rrR i) := by
    rw [congr_trans]
    exact hβ
  set χ : Y ≃* ↥S := ψ.trans β with hχdef
  have hcfg := pcfg_map χ hχ hp hp2 hP hP1 hcomm hnorm
  have hια := toPerm_eq_rr χ hχ
  have hcommutator : ∀ x : MulAut Y, toPerm χ ⁅x, α⁆ =
      toPerm χ x * rr i * (toPerm χ x)⁻¹ * (rr i)⁻¹ := fun x => by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hια]
  rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) i with rfl | rfl | rfl | rfl
  · refine ⟨fun x => mem_innSub_of_toPerm χ ?_, Or.inl ?_⟩
    · rw [hcommutator]
      exact comm_r₁ _ (toPerm_mem_R χ x)
    · have hc := cyclic_of_r₁ hcfg
      exact isCyclic_of_surjective (P.equivMapOfInjective _ (toPerm_injective χ)).symm.toMonoidHom
        (P.equivMapOfInjective _ (toPerm_injective χ)).symm.surjective
  · exact (false_of_r₂ hcfg).elim
  · exact (false_of_r₃ hcfg).elim
  · refine ⟨fun x => mem_innSub_of_toPerm χ ?_, Or.inr ⟨prime_eq_three_of_r₄ hcfg, ?_, ?_⟩⟩
    · rw [hcommutator]
      exact comm_r₄ _ (toPerm_mem_R χ x)
    · rintro ⟨y, hy⟩
      have h1 : toPerm χ α = (χ y : Perm42) := by rw [← hy, toPerm_conj]
      rw [hια] at h1
      have h2 : (χ y : Perm42) ∈ S := (χ y).2
      rw [← h1] at h2
      exact not_mem_S_r₄ h2
    · have h1 := P85.card_fixSub_congr χ α
      have h2 := P85.card_fixSub_conjIso 3
      rw [hχ] at h1
      have h3 : Nat.card ↥(fixSub α) = Nat.card ↥(P85.fixSub α) := rfl
      rw [h3, ← h1, h2]
      exact card_C₄

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
