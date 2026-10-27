module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.BridgeNat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

variable {Y : Type} [Group Y] {M : Subgroup Y}

@[expose] def centEquiv (t0 : M) :
    centralizer ({t0} : Set M) ≃* ↥(M ⊓ centralizer ({(t0 : Y)} : Set Y)) where
  toFun c := ⟨((c : M) : Y), Subgroup.mem_inf.mpr ⟨(c : M).2, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2))⟩⟩
  invFun x := ⟨⟨x, (Subgroup.mem_inf.mp x.2).1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem map_fstar_centEquiv (t0 : M) :
    (timmesfeldFStar (centralizer ({t0} : Set M))).map (centEquiv t0).toMonoidHom =
      timmesfeldFStar ↥(M ⊓ centralizer ({(t0 : Y)} : Set Y)) :=
  Bridge.timmesfeldFStar_map (centEquiv t0)

theorem quotientIso_centralizer (t0 : M) {X : Type*} [Group X]
    {ψ : ↥(M ⊓ centralizer ({(t0 : Y)} : Set Y)) →* X} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = timmesfeldFStar ↥(M ⊓ centralizer ({(t0 : Y)} : Set Y))) :
    timmesfeldQuotientIso (timmesfeldFStar (centralizer ({t0} : Set M))) X := by
  refine ⟨ψ.comp (centEquiv t0).toMonoidHom, hψ.comp (centEquiv t0).surjective, ?_⟩
  ext c
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    ← map_fstar_centEquiv t0]
  exact (mem_map_equiv (f := centEquiv t0)).trans (by simp)

theorem nonempty_fstar_equiv (t0 : M) {N : Subgroup Y}
    (hN : (timmesfeldFStar ↥(M ⊓ centralizer ({(t0 : Y)} : Set Y))).map
      (M ⊓ centralizer ({(t0 : Y)} : Set Y)).subtype = N) :
    Nonempty (timmesfeldFStar (centralizer ({t0} : Set M)) ≃* N) :=
  ⟨(Bridge.equivOfMapEq (centEquiv t0) (map_fstar_centEquiv t0)).trans
    ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hN))⟩

theorem exists_quotient_of_eq {Z X : Type*} [Group Z] [Group X] {K R N : Subgroup Y}
    (hKR : K = R) (ρ : R →* Z) (hker : ∀ r : R, ρ r = 1 ↔ (r : Y) ∈ N) {T : Subgroup Z}
    (hT : ρ.range = T) (e : T ≃* X) (hN : (timmesfeldFStar K).map K.subtype = N) :
    ∃ ψ : K →* X, Function.Surjective ψ ∧ ψ.ker = timmesfeldFStar K := by
  subst hKR hT
  refine ⟨e.toMonoidHom.comp ρ.rangeRestrict, e.surjective.comp ρ.rangeRestrict_surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← Subtype.coe_inj, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, hker, ← hN]
  exact (mem_map_iff_mem Subtype.val_injective)

theorem exists_noncomm_of_mem' {a b : Y} (ha : a ∈ M) (hb : b ∈ M) (hab : a * b ≠ b * a) :
    ∃ x y : M, x * y ≠ y * x :=
  ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

end CFSG.LargeExtraspecial.S14
