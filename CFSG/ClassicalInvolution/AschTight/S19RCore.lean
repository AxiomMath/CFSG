module

public import CFSG.ClassicalInvolution.SmallCases.DSplitBranch

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

structure TightStd {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranchD p f K z
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  edgeless : DEdgeless (CoreAssembly.conjClass K)

structure TightStdDelta {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranch p f K z
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  edgeless : DeltaEdgeless K

variable {p f} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem TightStd.toTightBranch (h : TightStd p f K z) : TightStdDelta p f K z :=
  ⟨h.branch.toDBranch, h.normEq, deltaEdgeless_of_dEdgeless h.edgeless⟩

theorem normEq_of_tightBranch (ht : TightBranch p f K z) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hz := ht.branch.member
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hz.subnormal
  let Q : Sylow 2 K := Classical.choice Sylow.nonempty
  have hU : UniqueInvolutionNormal K z :=
    uniqueInvolutionNormal_of_edgeless hz.orderOf_eq_two hz.mem hKC ht.control ht.edgeless Q
      (quaternion_sylow_of_isClassicalMember ht.branch.odd ht.branch.five hz Q)
  apply le_antisymm
  · intro n hn
    have hmem : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hU.2.1
    have hord : orderOf (n * z * n⁻¹) = 2 := by
      have := (MulAut.conj n).orderOf_eq z
      simpa [MulAut.conj_apply, hU.1] using this
    have h := hU.2.2.1 _ hmem hord
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]
  · exact centralizer_le_normalizer_of_edgeless hU.1 hU.2.2.2.1 ht.control ht.edgeless

theorem tightStdDelta_of_tightBranch (ht : TightBranch p f K z) : TightStdDelta p f K z :=
  ⟨ht.branch, normEq_of_tightBranch ht, ht.edgeless⟩

theorem tightStd_of_tightBranchD (ht : TightBranchD p f K z) : TightStd p f K z :=
  ⟨ht.branch, normEq_of_tightBranch ht.toTightBranch, ht.edgeless⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19R
