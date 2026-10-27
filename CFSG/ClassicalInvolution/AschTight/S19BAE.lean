module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
public import CFSG.ClassicalInvolution.AschTight.S1911Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

theorem aEmpty_of_tightD (ht : S19R.TightStd p f K z) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ CoreAssembly.conjClass K) : AEmpty (CoreAssembly.conjClass K) K₁ := by
  intro J hJs hJn zK zJ hzK hzJ
  by_contra hno
  have hA : InA (CoreAssembly.conjClass K) K₁ J := ⟨hJs, hJn, zK, zJ, hzK, hzJ, hno⟩
  have hΩ := hypOmegaGen_of_mod ht.branch.odd ht.branch.five (hypOmegaMod_of_tightD ht)
  obtain ⟨-, -, -, -, Kstar, -, -, -, -, -, -, -, -, -, -, -, -, -, hne, htwin, -⟩ :=
    Sec6Gen.l6_4ThreeGen G _ hΩ K₁ hK₁ J hJs.1 hA zK zJ hzK hzJ _ _ rfl rfl
  have hmem : Kstar ∈ twinSet (CoreAssembly.conjClass K) K₁ := by
    rw [htwin]
    exact Or.inr rfl
  obtain ⟨hKs, u, hu₁, hu₂⟩ := hmem
  exact hne (S1911.eq_of_isUniqueInvolution_member ht.toTightBranch hKs hK₁ hu₂ hu₁)

theorem partIHyp_of_tightD (ht : S19R.TightStd p f K z) :
    PartIHyp p f (CoreAssembly.conjClass K) :=
  ⟨ht.branch.odd, ht.branch.five, hypOmegaMod_of_tightD ht, fun _ hK₁ => aEmpty_of_tightD ht hK₁⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
