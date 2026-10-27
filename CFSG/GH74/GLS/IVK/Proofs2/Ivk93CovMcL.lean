module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4McL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem ivk93cov_mcl :
    Ivk93CovEq (fun X _ => NativeSporadic.IsSporadic X .McL) 8 := by
  intro J _ _ hJ x _ n B hc
  obtain ⟨e⟩ := hJ
  let e' : J ≃* ↥mclP := e.trans mclPermEquiv
  have hord : orderOf ((e' x : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hc.ord
  obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' x).2 hord
  let φ := GHInv.centralizerEquivConj mclP e' x hg hgt
  obtain ⟨hrange, -⟩ := mclRho_range
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hs' : IsSimpleGroup ↥mclRho.range := by
    rw [hrange]
    exact hs
  have hnab' : ∃ a b : ↥mclRho.range, a * b ≠ b * a := by
    rw [hrange]
    exact hnab
  have hperf : Group.IsPerfect ↥mclCt := Subgroup.isPerfect_iff.2 mclCt_perfect
  have hqs : IsQuasisimple ↥mclCt :=
    GHInv.isQuasisimple_of_perfect_cover hperf mclRho.rangeRestrict mclRho.rangeRestrict_surjective hs'
      (by
        obtain ⟨a, b, hab⟩ := hnab'
        exact ⟨a, b, hab⟩)
      (by rw [MonoidHom.ker_rangeRestrict]; exact mclRho_ker_le_center)
  have hq : IsQuasisimple ↥(centralizer ({x} : Set J)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqs
  have hBeq := hc.eq_centralizer_of_quasisimple hq
  have hcard : Nat.card ↥(centralizer ({x} : Set J)) = 40320 := by
    rw [Nat.card_congr φ.toEquiv]
    exact (mclT0_facts).2.2.2.1
  have h1 := hc.card_ge
  rw [hBeq, hcard] at h1
  have h8 : Nat.factorial 8 = 40320 := by decide
  by_contra hne
  have h9 : 9 ≤ n := by
    have := hc.eight
    omega
  have h2 := Nat.factorial_le h9
  have h9f : Nat.factorial 9 = 362880 := by decide
  omega

theorem ivk93cov_mcl_oneClass
    {J : Type} [Group J] [Finite J]
    (hJ : NativeSporadic.IsSporadic J .McL) (u v : J) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  obtain ⟨e⟩ := hJ
  let e' : J ≃* ↥mclP := e.trans mclPermEquiv
  have hord : ∀ w : J, orderOf w = 2 → orderOf ((e' w : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    intro w hw
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hw
  obtain ⟨g₁, hg₁, h₁⟩ := (mclT0_facts).2.2.2.2 _ (e' u).2 (hord u hu)
  obtain ⟨g₂, hg₂, h₂⟩ := (mclT0_facts).2.2.2.2 _ (e' v).2 (hord v hv)
  refine isConj_iff.2 ⟨e'.symm ⟨g₂ * g₁⁻¹, mclP.mul_mem hg₂ (mclP.inv_mem hg₁)⟩, ?_⟩
  apply e'.injective
  apply Subtype.ext
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h₁, h₂]
  group

end CFSG.GH74.GLS.IVK.Proofs2
