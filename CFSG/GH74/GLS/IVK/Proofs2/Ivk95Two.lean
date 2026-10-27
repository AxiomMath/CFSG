module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Struct

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint

namespace Ivk95Cfg

variable {J : Type} [Group J] [Finite J] {z : J}

theorem cyc_sylow (h : Ivk95Cfg z)
    (S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J))) : IsCyclic ↥S := by
  have hTc : ∀ t ∈ (S : Subgroup ↥(centralizer ((Ez z : Subgroup J) : Set J))).map
      (centralizer ((Ez z : Subgroup J) : Set J)).subtype, ∀ k ∈ Ez z, t * k = k * t := by
    rintro _ ⟨u, -, rfl⟩ k hk
    exact (mem_centralizer_iff.mp u.2 k hk).symm
  have hT2 : IsPGroup 2 ↥((S : Subgroup ↥(centralizer ((Ez z : Subgroup J) : Set J))).map
      (centralizer ((Ez z : Subgroup J) : Set J)).subtype) := S.isPGroup'.map _
  have hTcyc := h.cyc _ hTc hT2
  exact isCyclic_of_surjective
    (((S : Subgroup ↥(centralizer ((Ez z : Subgroup J) : Set J))).equivMapOfInjective
      (centralizer ((Ez z : Subgroup J) : Set J)).subtype
      (centralizer ((Ez z : Subgroup J) : Set J)).subtype_injective).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem false_of_two_involutions (h : Ivk95Cfg z) {a b : J} (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b)
    (hac : ∀ k ∈ Ez z, a * k = k * a) (hbc : ∀ k ∈ Ez z, b * k = k * b) : False := by
  set C := centralizer ((Ez z : Subgroup J) : Set J) with hC
  let a' : ↥C := ⟨a, mem_centralizer_iff.mpr fun k hk => (hac k hk).symm⟩
  let b' : ↥C := ⟨b, mem_centralizer_iff.mpr fun k hk => (hbc k hk).symm⟩
  have ha' : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha2
  have hb' : orderOf b' = 2 := by rw [← Subgroup.orderOf_coe]; exact hb2
  have hcomm : a' * b' = b' * a' := Subtype.ext hab
  exact hne (congrArg Subtype.val
    (eq_of_orderOf_two_of_cyclic_sylow (fun S => h.cyc_sylow S) ha' hb' hcomm))

end Ivk95Cfg

end CFSG.GH74.GLS.IVK.Proofs2
