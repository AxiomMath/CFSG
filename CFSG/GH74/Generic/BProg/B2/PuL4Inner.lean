module

public import CFSG.GH74.Generic.BProg.B2.T4OutComm
public import CFSG.GH74.Generic.BProg.B2.PumpupTableL3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Comps
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent
public import CFSG.GH74.GLS.Stage2.Final.ModelE
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Gen

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5
  CFSG.GH74.GLS.Stage2.Final CFSG.GH74.Ivk413

namespace PuL4Inner

theorem isCompIn_map_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {C S : Subgroup A}
    (h : IsCompIn C S) : IsCompIn (C.map φ.toMonoidHom) (S.map φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let ψ : ↥C ≃* ↥(C.map φ.toMonoidHom) := C.equivMapOfInjective φ.toMonoidHom φ.injective
  have h1 := CFSG.LocalCores.isComponent_map_mulEquiv ψ h.2
  convert h1 using 1
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 x.2
    have hsc : s = c := φ.injective (hsx.trans hcx.symm)
    subst hsc
    refine Subgroup.mem_map.2 ⟨⟨s, hc⟩, Subgroup.mem_subgroupOf.2 hs, Subtype.ext ?_⟩
    exact hsx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨(y : A), Subgroup.mem_subgroupOf.1 hy, ?_⟩)
    have := congrArg Subtype.val hyx
    exact this


theorem eq_one_or_yP_of_mem_K {F : Type} [Field F] [Finite F] {M : ModelData F} (hG : GoodModel M)
    {S : Subgroup (PG M)} (hS : S = K1 M ∨ S = K2 M) {z : PG M} (hz : z ∈ S) (hz2 : z * z = 1) :
    z = 1 ∨ z = yP M := by
  rcases hS with rfl | rfl
  · obtain ⟨x, rfl⟩ := hz
    have hx : x * x = 1 := iota1_injective M (by rw [map_mul, map_one]; exact hz2)
    rcases H2_sq_one hG hx with rfl | rfl
    · left; exact map_one _
    · right; exact iota1_negOne' M
  · obtain ⟨x, rfl⟩ := hz
    have hx : x * x = 1 := iota2_injective M (by rw [map_mul, map_one]; exact hz2)
    rcases H2_sq_one hG hx with rfl | rfl
    · left; exact map_one _
    · right; exact iota2_negOne' M

section Certified


theorem false_of_inner_shape_model {F : Type} [Field F] [Finite F] {M : ModelData F}
    (hG : GoodModel M) {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}
    (hs : ShapeInCent H t L) (htH : t ∈ H) (e : ↥H ≃* PG M)
    (hconj : IsConj (yP M) (e ⟨t, htH⟩)) : False := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj.symm
  let φ : ↥H ≃* PG M := e.trans (MulAut.conj g)
  have hφt : φ ⟨t, htH⟩ = yP M := by
    simp only [φ, MulEquiv.trans_apply, MulAut.conj_apply]
    exact hg
  have hcomp := CFSG.GH74.Generic.BProg.B2.PumpupTableL3.isCompIn_centralizer_subgroupOf htH hs.comp
  have hmap := isCompIn_map_mulEquiv φ hcomp
  rw [CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' φ ⟨t, htH⟩, hφt] at hmap
  have hK := only_comps' hG hmap
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ :=
    CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv.hasTwoInvolutions_of_shapeInCent hs
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  have key : ∀ (z : N) (hz : z ∈ L), z * z = 1 → z ≠ 1 → φ ⟨z, hLH hz⟩ = yP M := by
    intro z hz hz2 hz1
    have hmem : φ ⟨z, hLH hz⟩ ∈ (L.subgroupOf H).map φ.toMonoidHom :=
      Subgroup.mem_map.2 ⟨⟨z, hLH hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    have hsq : φ ⟨z, hLH hz⟩ * φ ⟨z, hLH hz⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z, hLH hz⟩ : ↥H) * ⟨z, hLH hz⟩ = 1 := Subtype.ext hz2
      rw [this, map_one]
    rcases eq_one_or_yP_of_mem_K hG hK hmem hsq with h1 | h1
    · exfalso
      apply hz1
      have : (⟨z, hLH hz⟩ : ↥H) = 1 := φ.injective (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    · exact h1
  have e1 := key a haL ha2 ha1
  have e2 := key b hbL hb2 hb1
  exact hab (congrArg Subtype.val (φ.injective (e1.trans e2.symm)))

end Certified


theorem isConj_yP_lin {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h8 : Nat.card F % 8 = 5) {x : PG (ModelData.lin F)} (hx : orderOf x = 2) :
    IsConj (yP (ModelData.lin F)) x :=
  all_inv_conj_y (luFacts_lin h2) h2 (hno8_lin h2 h8) (hi_lin (by omega))
    (odd_index_Nsub _ h2 (ModelOrd.odd_index_lin F h2)) hx

theorem isConj_yP_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h2 : (2 : F) ≠ 0) (h8 : p ^ f % 8 = 3)
    {x : PG (ModelData.uni hF)} (hx : orderOf x = 2) : IsConj (yP (ModelData.uni hF)) x :=
  all_inv_conj_y (luFacts_uni hF hp2) h2 (hno8_uni hF h2 h8) (hi_uni hF h8)
    (odd_index_Nsub _ h2 (ModelOrd.odd_index_uni hF hp2)) hx

section Certified2


theorem false_of_inner_shape_W {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hW : T4.PuL4W ↥H) (htH : t ∈ H) : False := by
  obtain ⟨p, f, hp, hp2, hf, h3, ⟨h8, hL⟩ | ⟨h8, hU⟩⟩ := hW
  · obtain ⟨hf1, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have e' : ↥H ≃* PG (ModelData.lin F) := e
    have hG : GoodModel (ModelData.lin F) := goodModel_lin h2 (by rw [hF]; omega)
    have hx : orderOf (e' ⟨t, htH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hs.inv
    exact false_of_inner_shape_model hG hs htH e'
      (isConj_yP_lin h2 (by rw [hF]; exact h8) hx)
  · obtain ⟨hf1, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    have e' : ↥H ≃* PG (ModelData.uni hF) := e
    have hG : GoodModel (ModelData.uni hF) := goodModel_uni hF hp2 (by omega)
    have hx : orderOf (e' ⟨t, htH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hs.inv
    exact false_of_inner_shape_model hG hs htH e' (isConj_yP_uni hF hp2 h2 h8 hx)

end Certified2

end PuL4Inner

end CFSG.GH74.Generic.BProg.B2
