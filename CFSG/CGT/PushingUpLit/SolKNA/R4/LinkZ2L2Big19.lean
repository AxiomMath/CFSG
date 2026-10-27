module

public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Defs
public import CFSG.ClassicalInvolution.Q3.TL4MF163Res

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Abstract

variable {G : Type} [Group G]

theorem exists_conj_ge_of_isSylow2In [Finite G] {S Q : Subgroup G} (hS : IsSylow2In S ⊤)
    (hQ : IsPGroup 2 ↥Q) : ∃ g : G, Q ≤ conjSub g S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G :=
    { toSubgroup := S
      isPGroup' := hS.2.1
      is_maximal' := fun {Q'} hQ' hle => hS.2.2 Q' le_top hQ' hle }
  obtain ⟨P', hQP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  refine ⟨g⁻¹, ?_⟩
  have hP' : g⁻¹ • P = P' := by rw [← hg, inv_smul_smul]
  have hcoe : (g⁻¹ • P : Sylow 2 G).toSubgroup = conjSub g⁻¹ S := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hcoe, hP']
  exact hQP'

theorem mem_zpowers_of_pow_orderOf_eq_one {K : Type} [Group K] [Finite K] [IsCyclic K]
    {x₀ w : K} (hw : w ^ orderOf x₀ = 1) : w ∈ Subgroup.zpowers x₀ := by
  have hle : Subgroup.zpowers w ≤ Subgroup.zpowers x₀ := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hw
  exact hle (Subgroup.mem_zpowers w)

end Abstract

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
