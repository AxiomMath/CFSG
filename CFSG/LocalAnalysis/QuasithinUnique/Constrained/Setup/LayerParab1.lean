module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3A

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

@[expose] def IsMinOffender (H A : Subgroup (V ≃ₗ[k] V)) : Prop :=
  A ≤ H ∧ A ≠ ⊥ ∧ CFSG.IsElementaryAbelian 2 A ∧
    Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A ∧
    ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A

@[expose] def offenderJ (H : Subgroup (V ≃ₗ[k] V)) : Subgroup (V ≃ₗ[k] V) :=
  ⨆ (A : Subgroup (V ≃ₗ[k] V)) (_ : IsMinOffender H A), A

@[expose] def oddGen (H : Subgroup (V ≃ₗ[k] V)) : Subgroup (V ≃ₗ[k] V) :=
  Subgroup.closure {h | h ∈ H ∧ Odd (orderOf h)}

theorem IsMinOffender.le {H A : Subgroup (V ≃ₗ[k] V)} (h : IsMinOffender H A) : A ≤ H := h.1

theorem le_offenderJ {H A : Subgroup (V ≃ₗ[k] V)} (h : IsMinOffender H A) : A ≤ offenderJ H :=
  le_iSup₂_of_le A h le_rfl

theorem offenderJ_le {H : Subgroup (V ≃ₗ[k] V)} : offenderJ H ≤ H :=
  iSup₂_le fun _ h => h.1

theorem IsMinOffender.conj {H A : Subgroup (V ≃ₗ[k] V)} (h : IsMinOffender H A)
    {x : V ≃ₗ[k] V} (hx : x ∈ H) : IsMinOffender H (conjSub x A) := by
  refine ⟨conjSub_le_of_mem hx h.1, ?_, ?_, ?_, ?_⟩
  · intro hA
    apply h.2.1
    apply (conjSub x).injective
    rw [hA]
    exact (conjSub x).map_bot.symm
  · exact isElementaryAbelian_of_mulEquiv
      (show ↥(conjSub x A) ≃* ↥A from
        (A.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).symm)
      h.2.2.1
  · rw [weight_conjSub]
    exact h.2.2.2.1
  · intro B hB0 hBA
    have h1 : ⊥ < conjSub x⁻¹ B := by
      have := (conjSub x⁻¹).lt_iff_lt.2 hB0
      rwa [(conjSub x⁻¹).map_bot] at this
    have h2 : conjSub x⁻¹ B < A := by
      have := (conjSub x⁻¹).lt_iff_lt.2 hBA
      rwa [conjSub_inv_conjSub] at this
    have h3 := h.2.2.2.2 _ h1 h2
    have h4 : weight (MonoidHom.id (V ≃ₗ[k] V)) B =
        weight (MonoidHom.id (V ≃ₗ[k] V)) (conjSub x⁻¹ B) := by
      have := weight_conjSub x (conjSub x⁻¹ B)
      rwa [conjSub_conjSub_inv] at this
    rw [h4, weight_conjSub x A]
    exact h3

theorem conjSub_offenderJ_le {H : Subgroup (V ≃ₗ[k] V)} {x : V ≃ₗ[k] V} (hx : x ∈ H) :
    conjSub x (offenderJ H) ≤ offenderJ H := by
  have e : conjSub x (offenderJ H) = ⨆ (A : Subgroup (V ≃ₗ[k] V)) (_ : IsMinOffender H A),
      conjSub x A := by
    simp only [offenderJ, OrderIso.map_iSup]
  rw [e]
  exact iSup₂_le fun A hA => le_offenderJ (hA.conj hx)

theorem offenderJ_normal {H : Subgroup (V ≃ₗ[k] V)} : ((offenderJ H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer offenderJ_le]
  intro y hy
  exact mem_normalizer_of_conjSub_le (conjSub_offenderJ_le hy) (conjSub_offenderJ_le (H.inv_mem hy))

theorem exists_minOffender [CharP k 2] [Finite V] {H E : Subgroup (V ≃ₗ[k] V)} (hEH : E ≤ H)
    (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) : ∃ A, IsMinOffender H A := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  let ρ : ↥E →* (V ≃ₗ[k] V) := (MonoidHom.id (V ≃ₗ[k] V)).comp E.subtype
  have hρ : Nat.card V ≤ weight ρ ⊤ := by
    have := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) E ⊤
    rw [map_subtype_top] at this
    rw [this]
    exact hEoff
  obtain ⟨B, hBbot, hwB, -, hstrict, hel⟩ := exists_maxWeight_minimalSubgroup ρ hρ
  refine ⟨B.map E.subtype, (Subgroup.map_subtype_le B).trans hEH, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective B E.subtype_injective]
    exact hBbot
  · exact isElementaryAbelian_of_mulEquiv
      (show ↥(B.map E.subtype) ≃* ↥B from
        (B.equivMapOfInjective E.subtype E.subtype_injective).symm)
      (hel 2 hEel)
  · have e1 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) E B
    have e2 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) E ⊤
    rw [map_subtype_top] at e2
    have h1 : Nat.card V ≤ weight ρ B := hρ.trans hwB
    rw [← e1]
    exact h1
  · intro D hD0 hDlt
    have hDE : D ≤ E := hDlt.le.trans (Subgroup.map_subtype_le B)
    have hDeq : (D.subgroupOf E).map E.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDE
    have hD1 : ⊥ < D.subgroupOf E := by
      rw [bot_lt_iff_ne_bot]
      intro h0
      have : D = ⊥ := by rw [← hDeq, h0, Subgroup.map_bot]
      exact (bot_lt_iff_ne_bot.1 hD0) this
    have hD2 : D.subgroupOf E < B := by
      rw [← Subgroup.map_lt_map_iff_of_injective E.subtype_injective, hDeq]
      exact hDlt
    have h3 := hstrict _ hD1 hD2
    have e1 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) E (D.subgroupOf E)
    have e2 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) E B
    rw [hDeq] at e1
    have h4 : weight ρ (D.subgroupOf E) = weight (MonoidHom.id (V ≃ₗ[k] V)) D := e1
    have h5 : weight ρ B = weight (MonoidHom.id (V ≃ₗ[k] V)) (B.map E.subtype) := e2
    rw [h4, h5] at h3
    exact h3

end CFSG.QuasithinUnique.Setup.Layer
