module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAStarCert
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoD
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KATwoE
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.PSL3Four
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

local notation "Perm42" => Equiv.Perm (Fin 42)

section Model

theorem pcfg_star_map {Y : Type} [Group Y] {i : Fin 4} (χ : Y ≃* ↥S) {α : MulAut Y}
    (hχ : MulAut.congr χ α = Cls3.conjIso (rrR i)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut Y)} (hP : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ e ∈ P, e * α = α * e)
    (hnorm : ∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) :
    PCfgStar (rr i) p (P.map (toPerm χ)) := by
  have hι := toPerm_injective χ
  have hια := toPerm_eq_rr χ hχ
  refine ⟨hp, hp2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, _, rfl⟩
    exact toPerm_mem_R χ e
  · exact hP.of_equiv (P.equivMapOfInjective _ hι)
  · exact fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 h)
  · rintro _ ⟨e, he, rfl⟩
    rw [← hια, ← map_mul, ← map_mul, hcomm e he]
  · intro s hs hsr
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
    have hn := mem_normalizer_map (toPerm χ) (hnorm y hyfix)
    rw [toPerm_conj] at hn
    have hy : (χ y : Perm42) = s := congrArg Subtype.val hyχ
    rw [hy] at hn
    exact hn

theorem kay_star_L34_full
    {Y : Type} [Group Y] (hF : LieModel Y .PSL 3 2 2) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup (MulAut Y)}
    (hP : IsPGroup p ↥P) (hP1 : P ≠ ⊥) (hcomm : ∀ e ∈ P, e * α = α * e)
    (hnorm : ∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) :
    p = 3 ∧ UnitaryFix α ∧ Nat.card ↥P = 9 ∧ α ∉ innSub Y := by
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hF
  have h2' : MulAut.congr ψ α * MulAut.congr ψ α = 1 := by rw [← map_mul, hα2, map_one]
  have h1' : MulAut.congr ψ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
  obtain ⟨i, β, hβ⟩ := exists_class_rep h2' h1'
  obtain ⟨χ, hχ⟩ : ∃ χ : Y ≃* ↥S, MulAut.congr χ α = Cls3.conjIso (rrR i) :=
    ⟨ψ.trans β, by rw [congr_trans]; exact hβ⟩
  have hcfg := pcfg_star_map χ hχ hp hp2 hP hP1 hcomm hnorm
  obtain ⟨hi3, hp3, hcard⟩ := star_model_of starModel_thm hcfg
  subst hi3
  have hια := toPerm_eq_rr χ hχ
  have hout : α ∉ innSub Y := by
    rintro ⟨y, hy⟩
    have h1 : toPerm χ α = (χ y : Perm42) := by rw [← hy, toPerm_conj]
    rw [hια] at h1
    have h2 : (χ y : Perm42) ∈ S := (χ y).2
    rw [← h1] at h2
    exact not_mem_S_r₄ h2
  have hfix72 : Nat.card ↥(fixSub α) = 72 := by
    have h1 := P85.card_fixSub_congr χ α
    have h2 := P85.card_fixSub_conjIso 3
    rw [hχ] at h1
    have h3 : Nat.card ↥(fixSub α) = Nat.card ↥(P85.fixSub α) := rfl
    rw [h3, ← h1, h2]
    exact card_C₄
  exact ⟨hp3, unitaryFix_of_card_seventytwo hF hα2 hout hfix72,
    (Nat.card_congr (P.equivMapOfInjective _ (toPerm_injective χ)).toEquiv).trans hcard, hout⟩

theorem invol_not_comm_order_three {Y : Type} [Group Y] [Finite Y] (hF : LieModel Y .PSL 3 2 2)
    (_hs : IsSimpleGroup Y) {t b : Y} (ht2 : t * t = 1) (ht1 : t ≠ 1) (hb : orderOf b = 3) :
    t * b ≠ b * t := by
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hF
  intro hcomm
  have ht : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have ht'S : (ψ t : Perm42) ∈ S := (ψ t).2
  have hb'S : (ψ b : Perm42) ∈ S := (ψ b).2
  have hcomm' : (ψ t : Perm42) * (ψ b : Perm42) = (ψ b : Perm42) * (ψ t : Perm42) := by
    have := congrArg (fun y => ((ψ y : ↥S) : Perm42)) hcomm
    simpa using this
  have hb3 : orderOf (ψ b : Perm42) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hb
  have hx2 : orderOf (⟨(ψ t : Perm42), S_le_R ht'S⟩ : ↥R) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  rcases (orderOf_eq_two_iff _).1 hx2 with h | h | h | h
  · obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
    have hci : c⁻¹ ∈ R := Subgroup.inv_mem _ hc
    have hb'' : c⁻¹ * (ψ b : Perm42) * c⁻¹⁻¹ ∈ S := conj_mem_S hci hb'S
    have he' : (ψ t : Perm42) = c * r₁ * c⁻¹ := he
    rw [he'] at hcomm'
    have hr : r₁ * (c⁻¹ * (ψ b : Perm42) * c) = (c⁻¹ * (ψ b : Perm42) * c) * r₁ := by
      calc r₁ * (c⁻¹ * (ψ b : Perm42) * c)
          = c⁻¹ * ((c * r₁ * c⁻¹) * (ψ b : Perm42)) * c := by group
        _ = c⁻¹ * ((ψ b : Perm42) * (c * r₁ * c⁻¹)) * c := by rw [hcomm']
        _ = (c⁻¹ * (ψ b : Perm42) * c) * r₁ := by group
    rw [inv_inv] at hb''
    have hC : c⁻¹ * (ψ b : Perm42) * c ∈ C₁ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hr.symm, hb''⟩
    have hord : orderOf (c⁻¹ * (ψ b : Perm42) * c) = 3 := by
      have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) (ψ b : Perm42)
      simp only [MulAut.conj_apply, inv_inv] at this
      rw [this]
      exact hb3
    have hd : orderOf (c⁻¹ * (ψ b : Perm42) * c) ∣ 64 := by
      have := orderOf_dvd_natCard (⟨c⁻¹ * (ψ b : Perm42) * c, hC⟩ : ↥C₁)
      rwa [Subgroup.orderOf_mk, card_C₁] at this
    rw [hord] at hd
    omega
  · exact absurd ht'S (not_mem_S_of_isConj h not_mem_S_r₂)
  · exact absurd ht'S (not_mem_S_of_isConj h not_mem_S_r₃)
  · exact absurd ht'S (not_mem_S_of_isConj h not_mem_S_r₄)

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
