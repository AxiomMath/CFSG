module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

theorem tits
    : FamTits := by
  intro X _ _ hq hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = U at hT
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ :=
    CFSG.QuasithinUnique.Setup.X6.titsSylowOvergroupLattice X hX U hT
  refine A312For.of_solvable_overgroups hq U hT fun M hUM hMtop => ?_
  rcases hlat M hUM with rfl | rfl | rfl | rfl
  · have := hT.2.1.isNilpotent
    infer_instance
  · exact hHs
  · exact hNs
  · exact absurd rfl hMtop

end CFSG.QuasithinUnique.Vol2Native.A312L
