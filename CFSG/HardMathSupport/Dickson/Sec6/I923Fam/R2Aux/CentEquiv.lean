module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Transport
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    ↥(Subgroup.centralizer ({g} : Set G)) ≃* ↥(Subgroup.centralizer ({e g} : Set H)) where
  toFun x := ⟨e x.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [← map_mul, ← map_mul, h]⟩
  invFun y := ⟨e.symm y.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

def infCentralizerEquiv {G H : Type*} [Group G] [Group H] (J : Subgroup G) (z : G) (hz : z ∈ J)
    (e : ↥J ≃* H) :
    ↥(J ⊓ Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer ({e ⟨z, hz⟩} : Set H)) where
  toFun x := ⟨e ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h⟩
  invFun y := ⟨(e.symm y.1 : G), Subgroup.mem_inf.2 ⟨(e.symm y.1).2, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    have h2 : e.symm y.1 * (⟨z, hz⟩ : ↥J) = (⟨z, hz⟩ : ↥J) * e.symm y.1 := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]
    exact congrArg Subtype.val h2⟩⟩
  left_inv x := by
    apply Subtype.ext
    show ((e.symm (e ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩) : ↥J) : G) = x.1
    rw [MulEquiv.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    show e ⟨((e.symm y.1 : ↥J) : G), (e.symm y.1).2⟩ = y.1
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  map_mul' x y := by
    apply Subtype.ext
    show e ⟨(x * y).1, _⟩ = e ⟨x.1, _⟩ * e ⟨y.1, _⟩
    rw [← map_mul]
    rfl

theorem noL2Sub_centralizer_conj {G : Type} [Group G] [Finite G] (h g : G)
    (H : NoL2Sub (Subgroup.centralizer ({g} : Set G))) :
    NoL2Sub (Subgroup.centralizer ({h * g * h⁻¹} : Set G)) := by
  refine noL2Sub_of_equiv ?_ H
  have e := centralizerEquiv (MulAut.conj h).symm (h * g * h⁻¹)
  have hconj : (MulAut.conj h).symm (h * g * h⁻¹) = g := by
    simp [MulAut.conj_symm_apply, mul_assoc]
  rw [hconj] at e
  exact e

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
