module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTL2
import CFSG.GH74.KGroups.L3EpsUniInv
import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.SubgroupLists
  CFSG.GH74.KGroups.L3Eps.Uni CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
open CFSG.GH74.KGroups.L3Eps (GraphData)
open CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3 (omega3_equiv_psl2)
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg.B2 CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
  CFSG.GH74.Generic.BProg.B2.PumpupTableL2 CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
open scoped MatrixGroups commutatorElement

theorem q3Out_u3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    Q3EmptyOut (fun X _ => LieModel X .PSU 3 p f) := by
  intro N _ _ H t L hs htH hH
  have hnorm : H.Normal := hs.normal
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := stated_of_lieModel (Or.inr rfl) hH
  have hf : 1 ≤ f := hadm.2.1
  have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hU e₀
  let c : MulAut ↥H := MulAut.conjNormal t
  have hc2 : c * c = 1 := by
    change MulAut.conjNormal t * MulAut.conjNormal t = 1
    rw [← map_mul, ht2, map_one]
  have hout : c ∉
      (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H : Subgroup (MulAut ↥H)) :=
    fun hin => htH
      (CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3.mem_of_conjNormal_mem_inner H hs.faithful hin)
  obtain ⟨N0, hGD, ⟨eN⟩⟩ := graphData_of_cover_psl2 hU hp2 h5 hq hθ hc2 hout
  set C : Subgroup ↥H := (H ⊓ Subgroup.centralizer ({t} : Set N)).subgroupOf H with hC
  have hmemC : ∀ x : ↥H, x ∈ C ↔ c x = x := by
    intro x
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      change t * (x : N) * t⁻¹ = x
      rw [← hx]
      group
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      change t * (x : N) * t⁻¹ = x at this
      calc (x : N) * t = (t * (x : N) * t⁻¹) * t := by rw [this]
        _ = t * x := by group
  have hSC : N0 ≤ C := fun x hx => (hmemC x).2 (hGD.fixed x hx)
  have hSn : ∀ x ∈ C, ∀ s ∈ N0, x * s * x⁻¹ ∈ N0 := fun x hx s hs' =>
    hGD.conj_mem x ((hmemC x).1 hx) s hs'
  have hSc : ∀ x ∈ C, ∀ z ∈ C, ⁅x, z⁆ ∈ N0 := fun x hx z hz =>
    hGD.commutator_mem x z ((hmemC x).1 hx) ((hmemC z).1 hz)
  have hB : IsCompIn C (L.subgroupOf H) := by
    have hCH : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H := inf_le_left
    exact ⟨Subgroup.comap_mono hs.comp.1,
      (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' (K := L)
        (M := H ⊓ Subgroup.centralizer ({t} : Set N)) (H := H) hCH).2 hs.comp.2⟩
  have hLS : L.subgroupOf H = N0 :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hGD.quasisimple hSC hSn hSc hB
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  let eL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) hU.fixedField :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans ((MulEquiv.subgroupCongr hLS).trans eN)
  have := hU.finite
  exact hs.false_of_psl2 hp hp2
    (lieModel_psl2_of_equiv hp hf (by omega) hU.card_fixedField eL)

end CFSG.GH74.Generic.BProg.B2.T4.PGV
