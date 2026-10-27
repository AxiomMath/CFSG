module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms


theorem forall_mem_range_conj_E7_E8_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    (hK : Nat.card K = 2) (α : MulAut (adjointGroup τ K)) :
    α ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form (f := 1) le_rfl K
      (by rw [pow_one]; exact hK) τ hτ
  rw [← hker, MonoidHom.mem_ker]
  refine RingEquiv.ext fun c => ?_
  rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [map_one, map_one]

theorem forall_mem_range_conj_of_mulEquiv_E8_two {G : Type*} [Group G] {L : Subgroup G}
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E8 K) (β : MulAut L) :
    β ∈ (MulAut.conj : L →* MulAut L).range :=
  (F4Pilot.conj_mem_range_conj_iff e β).1 (forall_mem_range_conj_E7_E8_two (Or.inr rfl) hK _)

theorem isCyclic_outer_of_mulEquiv_E8_two {G : Type*} [Group G] {L : Subgroup G} {K : Type}
    [Field K] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E8 K) : IsCyclic (Outer L) := by
  have : Subsingleton (Outer L) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H α =>
      induction b using QuotientGroup.induction_on with
      | H β =>
        rw [QuotientGroup.eq]
        exact forall_mem_range_conj_of_mulEquiv_E8_two hK e _
  exact isCyclic_of_subsingleton

theorem commutator_centralizer_of_mem_centralizer_sylow_E8 {K : Type} [Field K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (U : Sylow 2 (adjointGroup .E8 K))
    {w : adjointGroup .E8 K}
    (hw : w ∈ centralizer ((U : Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)))
    (hw1 : w ≠ 1) :
    ⁅centralizer ({w} : Set (adjointGroup .E8 K)), centralizer ({w} : Set (adjointGroup .E8 K))⁆ =
      centralizer ({w} : Set (adjointGroup .E8 K)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  obtain ⟨c, hc⟩ :=
    exists_conj_eq_pinnedElt_highRoot_of_mem_centralizer_sylow (Or.inr (Or.inr rfl)) U hw hw1
  have hwc : w = c⁻¹ * EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) * c⁻¹⁻¹ := by
    rw [← hc]
    group
  rw [hwc, ← map_conj_centralizer_singleton, ← map_commutator,
    commutator_centralizer_pinnedElt_highRoot_E8_of_one_le hf hK]

theorem not_forall_commute_sylow_conj_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hwL hwU
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  set w := g⁻¹ * t * g with hwdef
  set φ : adjointGroup .E8 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  set wC : adjointGroup .E8 K := e ⟨w, hwL⟩ with hwCdef
  have hφw : φ wC = w := by simp [hφdef, hwCdef]
  have hw1 : w ≠ 1 := by
    intro h
    have h1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [← hwdef, h]; group
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hwC1 : wC ≠ 1 := by
    intro h
    apply hw1
    rw [← hφw, h, map_one]
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (adjointGroup .E8 K) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (adjointGroup .E8 K)) ↔ e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hwCU : wC ∈ centralizer ((UC : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hwU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφw]
    exact h
  have hPC := commutator_centralizer_of_mem_centralizer_sylow_E8 hf hK UC hwCU hwC1
  set P := (centralizer ({wC} : Set (adjointGroup .E8 K))).map φ with hPdef
  have hPeq : P = L ⊓ centralizer ({w} : Set G) := by
    rw [hPdef, F4Pilot.map_centralizer_singleton hφ, hφr, hφw]
  have hP : ⁅P, P⁆ = P := by rw [hPdef, ← map_commutator, hPC]
  have hPL : P ≤ L := hPeq ▸ inf_le_left
  have hPw : P ≤ centralizer ({g⁻¹ * t * g} : Set G) := hPeq ▸ inf_le_right
  have hwP : g⁻¹ * t * g ∈ P := hPeq ▸ ⟨hwL, mem_centralizer_singleton_iff.2 rfl⟩
  exact LinearPilot.conj_not_mem_perfect hset (isSolvable_outer_of_mulEquiv_E8 e)
    (by rw [← map_center_eq e.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]) htC ht g hP hPL
    hPw hwP

theorem exists_conj_eq_mul_twoSided_E8_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  exact exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2
    (SeitzQ2.commutator_eq_top_of_standardSetting hset) ht hLt hCN hKt
    (not_forall_commute_sylow_conj_E8 hset le_rfl (by rw [pow_one]; exact hK) e htC ht)
    (fun _ β _ _ => forall_mem_range_conj_of_mulEquiv_E8_two hK e β)
    (fun _ hSt y hy z hz => SeitzQ2.commutator_mem_of_isCyclic_outer htC ht hCN hKt
      (isCyclic_outer_of_mulEquiv_E8_two hK e) y (hSt hy) z (hSt hz))

theorem exists_conj_eq_mul_twoCentral_E8_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  obtain ⟨x, z, hz, hxz, hz1, hU, -, -⟩ := exists_conj_eq_mul_twoSided_E8_two hset hK e ht hKt
  exact ⟨x, z, hz.1, hxz, hz1, hU⟩

end CFSG.SeitzReduction.E8Pilot
