module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSeven

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.RankTwoStandard
  CFSG.ComponentClassification.CatLeaf


section Main

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

theorem conj_mem_secL_ten (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hm : m = 10)
    (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)))
    (g : secQ (secP O R)) {x : secQ (secP O R)} (hx : x ∈ secL O hR) :
    g * x * g⁻¹ ∈ secL O hR := by
  subst hm
  have hKX : CFSG.SectionRank.IsKGroupCat (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) :=
    (hK.quotient _).quotient _
  have hOX : CFSG.oddCore (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) = ⊥ :=
    ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _
  have hsh := exactShape_secQ O hR (by norm_num)
  rcases exactShape_trichotomy_seven hGLS hO hEO hKX hOX hsh with h1 | h2 | h3
  · exact absurd h1 (secT_notMem_center O hR (by norm_num))
  · exact absurd h2 (not_wreath_of_order O hR (by norm_num))
  · exact conj_mem_secL_of_normal O hR (by norm_num) (normal_of_sym O hR (by norm_num) h3) g hx

include hR in
theorem l0Normal_ten (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hm : m = 10)
    (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G))) :
    L0Normal O R :=
  l0Normal_of_secL O hR (conj_mem_secL_ten O hR hGLS hO hEO hm hK) (by omega)

end Main

theorem shapeTwoCentDoubleAt_eleven (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput)
    (hR2 : RankTwoAlternatingStandard) : ShapeTwoCentDoubleAt 11 := by
  refine centDoubleAt_of_l0 hR2 (m := 10) (by norm_num) ?_
  intro G _ _ z O h4 hK hne
  obtain ⟨hKE, hKy⟩ := isKGroupCat_secP O h4 hK hne
  exact ⟨l0Normal_ten O (secR_klein (by norm_num)) hGLS hO hEO rfl hKE,
    l0Normal_ten O (secR_cyc (by norm_num)) hGLS hO hEO rfl hKy⟩

end CFSG.OddStandard.AltStdSec
