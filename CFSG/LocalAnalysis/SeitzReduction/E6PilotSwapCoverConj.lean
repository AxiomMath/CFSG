module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCover

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (F4Work)

section General

variable {G : Type*} [Group G]

theorem map_conj_map_conj_comm {t n : G} (htn : Commute t n) (H : Subgroup G) :
    (H.map (MulAut.conj n).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj n).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : t * n = n * t := htn.eq
  have h2 : n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, h1]
  calc t * (n * x * n⁻¹) * t⁻¹ = (t * n) * x * (n⁻¹ * t⁻¹) := by group
    _ = (n * t) * x * (t⁻¹ * n⁻¹) := by rw [h1, h2]
    _ = n * (t * x * t⁻¹) * n⁻¹ := by group

theorem swapConj_injective (n : G) : Function.Injective (MulAut.conj n).toMonoidHom :=
  (MulAut.conj n).injective

theorem conj_mem_normalizer_map_conj {H : Subgroup G} {s : G} (n : G)
    (hs : s ∈ normalizer (H : Set G)) :
    n * s * n⁻¹ ∈ normalizer ((H.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hs ⊢
  intro g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    MulAut.conj_symm_apply]
  have e1 : n⁻¹ * (n * s * n⁻¹ * g * (n * s * n⁻¹)⁻¹) * n = s * (n⁻¹ * g * n) * s⁻¹ := by group
  rw [e1]
  exact hs _

theorem conj_inv_mem_centralizer_of_mem_centralizer_map_conj {X : Subgroup G} {s n : G}
    (hs : s ∈ centralizer ((X.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) :
    n⁻¹ * s * n ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff] at hs ⊢
  intro x hx
  have h := hs (n * x * n⁻¹) ⟨x, hx, rfl⟩
  calc x * (n⁻¹ * s * n) = n⁻¹ * ((n * x * n⁻¹) * s) * n := by group
    _ = n⁻¹ * (s * (n * x * n⁻¹)) * n := by rw [h]
    _ = n⁻¹ * s * n * x := by group

end General

section Neighbour


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  {e : L ≃* adjointGroup .E6 K} {t : G}

@[expose] noncomputable def SwapFactorCover.toNeighbour (h : SwapFactorCover e t .high)
    (N : E6Neighbour) (htn : Commute t ((e.symm (N.rep K) : L) : G)) : SwapFactorCover e t N where
  Kc := h.Kc.map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom
  perfect := by rw [← map_commutator, h.perfect]
  le_centralizer := by
    rw [map_conj_map_conj_comm htn]
    exact F4Pilot.map_le_centralizer_map _ h.le_centralizer
  sup_eq := by
    rw [map_conj_map_conj_comm htn, ← Subgroup.map_sup, h.sup_eq, neighbourCore_eq_map_conj e N]
  odd_card_inf := by
    rw [map_conj_map_conj_comm htn, ← Subgroup.map_inf_eq _ _ _ (swapConj_injective _),
      card_map_of_injective (swapConj_injective _)]
    exact h.odd_card_inf
  normalizer_le := by
    intro s hs hso
    set n : G := ((e.symm (N.rep K) : L) : G) with hn
    rw [← E6Neighbour.map_conj_rep_torus_high, modelToG_map_conj] at hs
    have hs' := conj_inv_mem_centralizer_of_mem_centralizer_map_conj hs
    have hso' : Odd (orderOf (n⁻¹ * s * n)) := by
      have h1 := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) s
      rw [MulAut.conj_apply, inv_inv] at h1
      rw [h1]
      exact hso
    have h1 := conj_mem_normalizer_map_conj n (h.normalizer_le _ hs' hso')
    have h2 : n * (n⁻¹ * s * n) * n⁻¹ = s := by group
    rwa [h2] at h1
  ε := (highLeviConjEquiv K N).toMonoidHom.comp (h.ε.comp
    (h.Kc.equivMapOfInjective _ (swapConj_injective ((e.symm (N.rep K) : L) : G))).symm.toMonoidHom)
  surjective := (highLeviConjEquiv K N).surjective.comp (h.surjective.comp (MulEquiv.surjective _))
  eq_one_iff := by
    intro k
    obtain ⟨k₀, rfl⟩ := (h.Kc.equivMapOfInjective _
      (swapConj_injective ((e.symm (N.rep K) : L) : G))).surjective k
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff]
    rw [h.eq_one_iff, coe_equivMapOfInjective_apply, map_conj_map_conj_comm htn]
    exact (Subgroup.mem_map_iff_mem (swapConj_injective _)).symm
  diag := by
    intro k
    obtain ⟨k₀, rfl⟩ := (h.Kc.equivMapOfInjective _
      (swapConj_injective ((e.symm (N.rep K) : L) : G))).surjective k
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    set n : G := ((e.symm (N.rep K) : L) : G) with hn
    have hk : ((h.Kc.equivMapOfInjective (MulAut.conj n).toMonoidHom (swapConj_injective n) k₀ :
        h.Kc.map (MulAut.conj n).toMonoidHom) : G) = n * k₀ * n⁻¹ := rfl
    rw [hk]
    have hrep : ((highLeviConjEquiv K N (h.ε k₀) : N.levi K) : adjointGroup .E6 K) =
        N.rep K * (h.ε k₀ : adjointGroup .E6 K) * (N.rep K)⁻¹ :=
      Subtype.ext (coe_highLeviConjEquiv N (h.ε k₀))
    rw [hrep, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv, ← hn, ← h.diag k₀]
    have h1 : t * n = n * t := htn.eq
    have h2 : n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, h1]
    calc n * k₀ * n⁻¹ * (t * (n * k₀ * n⁻¹) * t⁻¹) =
        n * k₀ * n⁻¹ * ((t * n) * k₀ * (n⁻¹ * t⁻¹)) := by group
      _ = n * k₀ * n⁻¹ * ((n * t) * k₀ * (t⁻¹ * n⁻¹)) := by rw [h1, h2]
      _ = n * (k₀ * (t * k₀ * t⁻¹)) * n⁻¹ := by group

theorem commute_symm_rep_of_mem_centralizer (ht : t ∈ centralizer (L : Set G))
    (N : E6Neighbour) : Commute t ((e.symm (N.rep K) : L) : G) :=
  (mem_centralizer_iff.1 ht _ (e.symm (N.rep K)).2).symm

end Neighbour

section All


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nonempty_forall_swapFactorCover {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E6 K) (hk : RootSwapKind e t) (N : E6Neighbour) :
    Nonempty (SwapFactorCover e t N) := by
  obtain ⟨h⟩ := nonempty_swapFactorCover_high hw hf e hk
  exact ⟨h.toNeighbour N (commute_symm_rep_of_mem_centralizer hw.mem_centralizer N)⟩

end All

end CFSG.SeitzReduction.E6Pilot
