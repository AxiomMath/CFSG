module

public import CFSG.LargeExtraspecial.S4CESpLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.Pres
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (exists_symplectic_basis_prescribed_pair)
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}
  {n : ℕ} {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}

@[expose] noncomputable def spY (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K) (a : V)
    (c : Basis (Fin n ⊕ Fin n) (ZMod 2) V) (p q : Fin n ⊕ Fin n) (t : ZMod 2) : K :=
  open Classical in
  if q = Sum.swap p then 1 else liftPt π E a (c p) (spIota c (spElt p q t))

theorem spY_of_ne (c : Basis (Fin n ⊕ Fin n) (ZMod 2) V) {p q : Fin n ⊕ Fin n}
    (hq : q ≠ Sum.swap p) (t : ZMod 2) :
    spY π E a c p q t = liftPt π E a (c p) (spIota c (spElt p q t)) := by
  simp [spY, hq]

section Rels

variable [FiniteDimensional (ZMod 2) V]
  (h : CEHyp π E a (TauCeti.BilinForm.isometryGroup β) (spPointRadical β a))
  (hβ : β.IsAlt) (hnd : β.Nondegenerate) (ha : a ≠ 0) {c : Basis (Fin n ⊕ Fin n) (ZMod 2) V}
  (hc : IsSpBasis β c)
include h hβ hnd ha hc

omit hc in
theorem exists_apply_eq_spBasis (p : Fin n ⊕ Fin n) : ∃ k, π k a = c p :=
  h.exists_apply_eq_of_sp hβ hnd ha (c.ne_zero p)

theorem spIota_mem_map_Ept {p q : Fin n ⊕ Fin n} (hq : q ≠ Sum.swap p) (t : ZMod 2) :
    spIota c (spElt p q t) ∈ (Ept π E a (c p)).map π := by
  obtain ⟨k, hk⟩ := exists_apply_eq_spBasis h hβ hnd ha p
  rw [h.map_Ept_sp hk]
  exact hc.spIota_spElt_mem hβ hq t

theorem spY_mem {p q : Fin n ⊕ Fin n} (hq : q ≠ Sum.swap p) (t : ZMod 2) :
    spY π E a c p q t ∈ Ept π E a (c p) := by
  rw [spY_of_ne c hq]
  exact liftPt_mem (spIota_mem_map_Ept h hβ hnd ha hc hq t)

theorem apply_spY {p q : Fin n ⊕ Fin n} (hq : q ≠ Sum.swap p) (t : ZMod 2) :
    π (spY π E a c p q t) = spIota c (spElt p q t) := by
  rw [spY_of_ne c hq]
  exact apply_liftPt (spIota_mem_map_Ept h hβ hnd ha hc hq t)

theorem spY_comm_of_fix {p q r s : Fin n ⊕ Fin n} (hq : q ≠ Sum.swap p) (hs : s ≠ Sum.swap r)
    (t u : ZMod 2) (hfix : spIota c (spElt r s u) (c p) = c p) :
    ⁅spY π E a c p q t, spY π E a c r s u⁆ =
      liftPt π E a (c p) (spIota c ⁅spElt p q t, spElt r s u⁆) := by
  rw [spY_of_ne c hq, h.commutatorElement_liftPt (exists_apply_eq_spBasis h hβ hnd ha p)
    (spIota_mem_map_Ept h hβ hnd ha hc hq t) (by rw [apply_spY h hβ hnd ha hc hs]; exact hfix),
    apply_spY h hβ hnd ha hc hs, ← map_commutatorElement]

theorem spY_symm {p q : Fin n ⊕ Fin n} (hq : q ≠ Sum.swap p) (t : ZMod 2) :
    spY π E a c q p t = spY π E a c p q t := by
  by_cases hqp : q = p
  · subst hqp
    rfl
  rw [spY_of_ne c (ofPos_ne hq), spY_of_ne c hq, spElt_comm hq t]
  rcases OrthoF2.zmod2_eq_zero_or_eq_one t with rfl | rfl
  · rw [spElt_zero, map_one, h.liftPt_one (exists_apply_eq_spBasis h hβ hnd ha q),
      h.liftPt_one (exists_apply_eq_spBasis h hβ hnd ha p)]
  have hsw : ∀ {x y : Fin n ⊕ Fin n}, x ≠ y → Sum.swap x ≠ Sum.swap y := fun hxy e =>
    hxy (by simpa using congrArg Sum.swap e)
  rw [hc.spIota_spElt_one hβ hqp hq]
  exact h.liftPt_spRho_symm hβ hnd ha (u' := c (Sum.swap p)) (w' := c (Sum.swap q)) _
    (by rw [hc, ite_eq_left rfl]) (by rw [hc, ite_eq_left rfl])
    (hc.apply_eq_zero (hsw hqp)) (hc.apply_eq_zero (hsw (Ne.symm hqp)))

@[expose] noncomputable def spRels : SpRelations n (ZMod 2) K where
  ξ := spY π E a c
  symm p q hq t := spY_symm h hβ hnd ha hc hq t
  add p q hq s t := by
    rw [spY_of_ne c hq, spY_of_ne c hq, spY_of_ne c hq, spElt_add, map_mul,
      h.liftPt_mul (exists_apply_eq_spBasis h hβ hnd ha p)
        (spIota_mem_map_Ept h hβ hnd ha hc hq s) (spIota_mem_map_Ept h hβ hnd ha hc hq t)]
  short p q r hpq hqr hpr s t := by
    have v1 : q ≠ Sum.swap p := ne_swap_of_idx_ne hpq
    have v2 : r ≠ Sum.swap (Sum.swap q) := by rw [Sum.swap_swap]; exact ne_of_idx_ne hqr
    have v3 : r ≠ Sum.swap p := ne_swap_of_idx_ne hpr
    have v4 : Sum.swap q ≠ Sum.swap p := fun e =>
      ne_of_idx_ne hpq (by simpa using congrArg Sum.swap e)
    have hmod := (spRelationsModel (n := n) (K := ZMod 2)).short p q r hpq hqr hpr s t
    rw [spRelationsModel_ξ] at hmod
    rw [spY_comm_of_fix h hβ hnd ha hc v1 v2 s t (hc.spIota_spElt_apply_basis v2 v4 v3 t), hmod,
      spY_of_ne c v3]
  shortLong p q hpq s t := by
    have v1 : q ≠ Sum.swap p := ne_swap_of_idx_ne hpq
    have v2 : Sum.swap q ≠ Sum.swap (Sum.swap q) := (swap_ne_self (Sum.swap q)).symm
    have v3 : Sum.swap q ≠ Sum.swap p := fun e =>
      ne_of_idx_ne hpq (by simpa using congrArg Sum.swap e)
    have v4 : p ≠ Sum.swap p := (swap_ne_self p).symm
    have hmod := (spRelationsModel (n := n) (K := ZMod 2)).shortLong p q hpq s t
    rw [spRelationsModel_ξ] at hmod
    rw [spY_comm_of_fix h hβ hnd ha hc v1 v2 s t (hc.spIota_spElt_apply_basis v2 v3 v3 t), hmod,
      map_mul, h.liftPt_mul (exists_apply_eq_spBasis h hβ hnd ha p)
        (spIota_mem_map_Ept h hβ hnd ha hc v3 _) (spIota_mem_map_Ept h hβ hnd ha hc v4 _),
      spY_of_ne c v3, spY_of_ne c v4]
  commLong p q hpq s t := by
    have v1 : q ≠ Sum.swap p := ne_swap_of_idx_ne hpq
    have v3 : Sum.swap q ≠ Sum.swap p := fun e =>
      ne_of_idx_ne hpq (by simpa using congrArg Sum.swap e)
    have v4 : p ≠ Sum.swap p := (swap_ne_self p).symm
    have hmod := (spRelationsModel (n := n) (K := ZMod 2)).commLong p q hpq s t
    rw [spRelationsModel_ξ] at hmod
    rw [spY_comm_of_fix h hβ hnd ha hc v1 v3 s t (hc.spIota_spElt_apply_basis v3 v4 v3 t), hmod,
      map_one, h.liftPt_one (exists_apply_eq_spBasis h hβ hnd ha p)]
  comm p q r s hpq hrs hrp hrq hsp hsq u t := by
    have hmod := (spRelationsModel (n := n) (K := ZMod 2)).comm p q r s hpq hrs hrp hrq hsp hsq u t
    rw [spRelationsModel_ξ] at hmod
    rw [spY_comm_of_fix h hβ hnd ha hc hpq hrs u t (hc.spIota_spElt_apply_basis hrs hrp hsp t),
      hmod, map_one, h.liftPt_one (exists_apply_eq_spBasis h hβ hnd ha p)]

end Rels

theorem ker_eq_bot_of_spPair
    [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt) (hnd : β.Nondegenerate) (ha : a ≠ 0)
    (hdim : 4 ≤ finrank (ZMod 2) V)
    (h : CEHyp π E a (TauCeti.BilinForm.isometryGroup β) (spPointRadical β a)) :
    π.ker = ⊥ := by
  obtain ⟨b, hb⟩ : ∃ b, β a b ≠ 0 := by
    by_contra! h'
    exact ha (hnd.1 a h')
  obtain ⟨m, c, hm, h1, h2, h3, hca, -⟩ := exists_symplectic_basis_prescribed_pair
    β hβ hnd a b (OrthoF2.zmod2_eq_one_of_ne_zero hb)
  have hc : IsSpBasis β c := IsSpBasis.of_pairs hβ h1 h2 h3
  have hn : 2 ≤ m + 1 := by omega
  set R := spRels h hβ hnd ha hc
  set σ := R.toHom hn
  have hσ : ∀ p q, q ≠ Sum.swap p → ∀ t, σ (spElt p q t) = spY π E a c p q t :=
    fun p q hq t => R.toHom_spElt hn hq t
  have hcomp : π.comp σ = spIota c := hom_ext_spElt fun p q hq t => by
    rw [MonoidHom.comp_apply, hσ p q hq t, apply_spY h hβ hnd ha hc hq t]
  have hpa : ∃ k, π k a = a := ⟨1, by rw [map_one]; rfl⟩
  refine h.ker_eq_bot_of_hom σ (by rw [hcomp]; exact spIota_injective)
    (by rw [hcomp]; exact hc.le_range_spIota) hpa ?_
  refine h.Ept_le_range hpa σ
    (S := {g | ∃ q, q ≠ Sum.swap (Sum.inl 0) ∧ g = spIota c (spElt (Sum.inl 0) q (1 : ZMod 2))})
    ?_ ?_
  · rw [h.Ept_self, h.map_eq, ← hca]
    exact hc.spPointRadical_le_closure hβ hnd _
  · rintro g ⟨q, hq, rfl⟩
    refine ⟨σ (spElt (Sum.inl 0) q 1), ⟨_, rfl⟩, ?_, ?_⟩
    · have hmem := spY_mem h hβ hnd ha hc hq 1
      rw [hca] at hmem
      rw [hσ _ _ hq]
      exact hmem
    · rw [← MonoidHom.comp_apply, hcomp]

end CFSG.LargeExtraspecial.S4
