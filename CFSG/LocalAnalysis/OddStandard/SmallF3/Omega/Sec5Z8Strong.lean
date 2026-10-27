module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Ne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZStrong
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZNorm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5z8_strongly_closed (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6) (hU : Asc82FactPocketsUniq6)
    (hSq : Asc82FactSqReflQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTR : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
      sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))
    {x g : G} (hx : x ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)))
    (hg : g ∈ centralizer ({z} : Set G)) (hxg : g * x * g⁻¹ ∈ S) :
    g * x * g⁻¹ ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) := by
  have hzz : z * z = 1 := sec5p510_A_sq h (sec5p510_z_mem_A h)
  have hzS : z ∈ S := h.mem_S
  have hzR : z ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) :=
    sec5p510_z_mem_R h.toSec5Ctx hs.pk.q
  have hzT : z ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) := by
    rw [hTR]
    exact hzR
  have hgz' : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgz : g * z * g⁻¹ = z := by
    rw [hgz']
    group
  by_cases hxz : x ∈ zpowers z
  · have hgx : g * x * g⁻¹ = x := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have hgk : Commute g (z ^ k) := Commute.zpow_right hgz' k
      rw [hgk.eq]
      group
    rw [hgx]
    exact hx
  · by_cases hx2z : x * x ∈ zpowers z
    · obtain ⟨y, hyH, hxy⟩ := hs.T_invol x hx hx2z hxz
      have hgy : g * y * g⁻¹ ∈ conjClassIn (centralizer ({z} : Set G)) t :=
        sec5p510_conj_mem_conj hyH hg
      rcases hxy with rfl | rfl
      · exact sec5z_conj_inter_S_le_T hy h55 h58d hFB h4 h.toSec5Ctx h.nconj hs.pk.q hgy hxg
      · have hgx : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * z := by
          calc g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
            _ = (g * y * g⁻¹) * z := by rw [hgz]
        have hgyS : g * y * g⁻¹ ∈ S := by
          have e : g * y * g⁻¹ = (g * (y * z) * g⁻¹) * z := by
            rw [hgx, mul_assoc (g * y * g⁻¹) z z, hzz, mul_one]
          rw [e]
          exact mul_mem hxg hzS
        have hT := sec5z_conj_inter_S_le_T hy h55 h58d hFB h4 h.toSec5Ctx h.nconj hs.pk.q
          hgy hgyS
        rw [hgx]
        exact mul_mem hT hzT
    · have hxR : x ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) := hTR ▸ hx
      have hx2 := (sec5z8_sq_mem h hs hxR).resolve_left hx2z
      set t' := g * t * g⁻¹ with ht'def
      have hyy : (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      have hyy' : (g * x * g⁻¹) * (g * x * g⁻¹) = t' ∨
          (g * x * g⁻¹) * (g * x * g⁻¹) = t' * z := by
        rcases hx2 with h2 | h2
        · left
          rw [hyy, h2, ht'def]
        · right
          rw [hyy, h2, ht'def]
          calc g * (t * z) * g⁻¹ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
            _ = (g * t * g⁻¹) * z := by rw [hgz]
      have ht'H : t' ∈ conjClassIn (centralizer ({z} : Set G)) t := ⟨g, hg, ht'def.symm⟩
      have ht'S : t' ∈ S := by
        rcases hyy' with h | h
        · rw [← h]
          exact mul_mem hxg hxg
        · have h' : t' = (g * x * g⁻¹) * (g * x * g⁻¹) * z := by
            rw [h, mul_assoc, hzz, mul_one]
          rw [h']
          exact mul_mem (mul_mem hxg hxg) hzS
      by_cases ht't : t' = t
      · have hgt : g * t = t * g := by
          have h1 : g * t * g⁻¹ = t := ht'def.symm.trans ht't
          calc g * t = (g * t * g⁻¹) * g := by group
            _ = t * g := by rw [h1]
        have hgtc : g ∈ centralizer ({t} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hgt
        have hR := sec5z8_conj_mem_R hy hU h.toSec5Ctx hs.pk hgtc hgz' hxR hxg
        rw [hTR]
        exact hR
      · have hcon := sec5z8_sq_ne hy h55 h58d hFB h4 hSq h hs ht'H ht'S ht't hxg
        rcases hyy' with h | h
        · exact absurd h hcon.1
        · exact absurd h hcon.2

end CFSG.OddStandard.SmallF3.Omega
