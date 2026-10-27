module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem u9_simple_nonabelian {Γ : Type} [Group Γ] {A K : Subgroup Γ} (h : S10.InnDiagOn 3 A K) :
    IsSimpleGroup (PSimple 3 K) ∧ ∃ a b : PSimple 3 K, a * b ≠ b * a := by
  obtain ⟨-, lab, -, R, _, I, F, θ, hs, ⟨a, b, hab⟩, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists h.2
  haveI := hs
  refine ⟨θ.isSimpleGroup, θ.symm a, θ.symm b, fun hc => hab ?_⟩
  exact θ.symm.injective (by simpa using hc)

theorem u9_transfer_chev {Γ : Type} [Group Γ] [Finite Γ] {K J : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    (hI1 : S10.InnDiagOn 3 (Subgroup.zpowers x) K)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J) :
    chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ ^ 3 = 1 ∧
      GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩))
        (chevTransfer 3 K J) ∧
      Nonempty (PSimple 3 J ≃* PSimple 3 (chevTransfer 3 K J)) := by
  have hxN : x ∈ Subgroup.normalizer (K : Set Γ) := hI1.1 (Subgroup.mem_zpowers x)
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx
  exact ⟨chevAut_pow_eq_one 3 K hxN hx, glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ,
    nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hJ⟩

theorem u9_transfer {Γ : Type} [Group Γ] [Finite Γ] {K J : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    (hI1 : S10.InnDiagOn 3 (Subgroup.zpowers x) K)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J) :
    ∃ α : MulAut (PSimple 3 K), α ^ 3 = 1 ∧ GLAPComponent 3 (fixSubgroup α) (chevTransfer 3 K J) ∧
      Nonempty (PSimple 3 J ≃* PSimple 3 (chevTransfer 3 K J)) :=
  ⟨_, u9_transfer_chev hx hI1 hJ⟩

end CFSG.LocalAnalysis.GLTheoremA.I141F
