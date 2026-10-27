module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Ee2

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

theorem pCoreOf_le_Dz_of_ker_zpowers {m : ℕ} (hm : 5 ≤ m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hker : ∀ k ∈ J.φ.ker.map (pSpan (fam K (conjSub g (piGen π)))).subtype,
      k = 1 ∨ k = g * z * g⁻¹) :
    pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g ∧ pCoreOf 2 (piGen π) ≤ Dz K π g := by
  have hz1 : g * z * g⁻¹ ∈ Dz K π g :=
    Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ⟨conjSub g K, S.hg, S.hz.conj g⟩))
  have hz0 : z ∈ Dz K π g :=
    Subgroup.subset_closure (Or.inr (Subgroup.subset_closure S.z_mem_Zset))
  refine S.pCoreOf_le_Dz_of_ker_le hm J ?_ ?_
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

theorem thinCrossPair_six
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    (J : AEIdent (fam K (conjSub g (piGen π))) 6) (htw : S.TwinLab 6)
    (hnb : NbrPiTwin K₀ K K' π g) (hsec : SecYu K₀ K K' z π g) : ThinCrossPair K π g := by
  have hm5 : 5 ≤ 6 := by norm_num
  have hAut := Cross.aeAut_of_five_le hm5
  have hvec := S.exists_vector_six htw J hsec
  have hker := S.ker_le_zpowers_secYu hS hnab (le_refl 6) htw hodd J hnb hsec
  obtain ⟨hO', hO⟩ := S.pCoreOf_le_Dz_of_ker_zpowers hm5 J hker
  exact S.thinCrossPair_of_vector hm5 hAut htw J hO' hO hvec

theorem thinCrossPair_of_secYu
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {m : ℕ} (hm : 6 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m) (htw : S.TwinLab m)
    (hnb : NbrPiTwin K₀ K K' π g) (hsec : SecYu K₀ K K' z π g) : ThinCrossPair K π g := by
  rcases Nat.lt_or_ge m 7 with h6 | h7
  · obtain rfl : m = 6 := by omega
    exact S.thinCrossPair_six hS hnab hodd J htw hnb hsec
  · exact S.thinCrossPair_of_secYu_ge7 hS hnab h7 J htw hnb hsec

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
