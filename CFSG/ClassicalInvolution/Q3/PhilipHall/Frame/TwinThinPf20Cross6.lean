module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Ker

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem pCoreOf_le_Dz_of_ge_eight (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {m : ℕ} (hm : 8 ≤ m)
    (hAut : TwinThinPf8.AEAut m) (hnb : NbrPiTwin K₀ K K' π g)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g ∧ pCoreOf 2 (piGen π) ≤ Dz K π g := by
  have hker := S.ker_le_zpowers hS hnab hm hAut hnb J
  have hz1 : g * z * g⁻¹ ∈ Dz K π g :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ⟨conjSub g K, S.hg, S.hz.conj g⟩))
  have hz0 : z ∈ Dz K π g :=
    Subgroup.subset_closure (Or.inr (Subgroup.subset_closure S.z_mem_Zset))
  refine S.pCoreOf_le_Dz_of_ker_le (by omega) J ?_ ?_
  · intro x hx
    rcases hker x hx with rfl | rfl
    · exact (Dz K π g).one_mem
    · exact hz1
  · intro x hx
    rw [mem_conjSub_iff] at hx
    rcases hker _ hx with h | h
    · have : x = 1 := by
        have := congrArg (fun t => g⁻¹ * t * g) h
        simpa [mul_assoc] using this
      rw [this]
      exact (Dz K π g).one_mem
    · have : x = z := by
        have := congrArg (fun t => g⁻¹ * t * g) h
        simpa [mul_assoc] using this
      rw [this]
      exact hz0

theorem thinCrossPair_of_secYu_ge7
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {m : ℕ} (hm : 7 ≤ m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) (htw : S.TwinLab m)
    (hnb : NbrPiTwin K₀ K K' π g) (hsec : SecYu K₀ K K' z π g) : ThinCrossPair K π g := by
  have hm5 : 5 ≤ m := by omega
  have hAut := Cross.aeAut_of_five_le hm5
  have hvec := S.exists_vector_of_secYu hm htw hAut J hsec
  by_cases hodd : m % 2 = 1
  · obtain ⟨hO', hO⟩ := S.pCoreOf_le_Dz_of_odd hm5 hodd J
    exact S.thinCrossPair_of_vector hm5 hAut htw J hO' hO hvec
  · obtain ⟨hO', hO⟩ := S.pCoreOf_le_Dz_of_ge_eight hS hnab (by omega) hAut hnb J
    exact S.thinCrossPair_of_vector hm5 hAut htw J hO' hO hvec

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
