module

public import CFSG.LargeExtraspecial.S4SevenAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_subgroupOf_resV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    ((S.Lbar g).subgroupOf (Rbar S g t)).map (resV haQ t) = LmodN S g t := by
  ext e
  constructor
  · intro he
    obtain ⟨l, hl, rfl⟩ := he
    exact ⟨l, hl, fun v => coe_resV_apply haQ l v⟩
  · intro he
    obtain ⟨x, hx, hex⟩ := he
    refine ⟨⟨x, Lbar_le_Rbar ht hx⟩, hx, ?_⟩
    exact LinearEquiv.ext fun v => Subtype.ext ((coe_resV_apply haQ _ v).trans (hex v).symm)

theorem Nbar_eq_N0bar_or (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (hD : DtEqConj S g t)
    (hpair : NaturalPair (RmodN S g t) (LmodN S g t) (aV ht)) :
    Nbar S g t = N0bar S g t ∨ (A6Pair (RmodN S g t) (LmodN S g t) (aV ht) ∧
      ((N0bar S g t).subgroupOf (Nbar S g t)).index = 3) := by
  have haQ := H.conj_mem
  refine eq_of_centralExtInput hCE N0bar_le_Nbar Nbar_le_Rbar (Lbar_le_Rbar ht)
    (fun r hr x hx => conj_mem_N0bar haQ hr hx) (resV haQ t) (resV_eq_one_iff haQ)
    (aV_ne_zero H ht) hpair (range_resV haQ t) (map_subgroupOf_resV haQ ht)
    (fun n hn r hr => commutator_mem_N0bar H hD hn hr) Lbar_inf_Nbar_le_N0bar
    (Rbar_le_closure_conj hD) (fun x hx => ?_) (fun r hr hconj => ?_)
  · have hfix : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      have := congrArg Subtype.val hx
      rwa [coe_resV_apply] at this
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) haQ H.conj_ne
      (Rbar_le_Mbar x.2) (by simpa using hfix)
    simpa using this
  · obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    rw [← Lbar_mul S k g] at hconj ⊢
    exact Lbar_conj_eq_of_conj_mem H C ht hr hconj

end CFSG.LargeExtraspecial.S4
