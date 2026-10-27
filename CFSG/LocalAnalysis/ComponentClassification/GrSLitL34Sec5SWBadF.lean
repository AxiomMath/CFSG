module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWFusEnd

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer


theorem exists_conj_of_field (hMax : MaximalTwoComponentInput) {G : Type} [Group G] [Finite G]
    {a x : G} {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {g : G} (hgS : g⁻¹ * a * g ∈ S)
    (h16 : Nat.card ↥(S ⊓ zStarIn J) = 16) (hF : HarrisLit.EndB.IsL34Field J (g⁻¹ * a * g))
    (haZ : a ∈ S ⊓ zStarIn J) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJper : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨D⟩ := exists_wStd hJper hL34 (GrS4.isSylowTwoIn_inf hS) hS.1
  obtain ⟨y, hyP, hyb, hyy⟩ :=
    D.exists_sq_eq_of_field hJper hS2 hgS hF h16 haZ haa ha1 (hcent _ hgS).symm
  have hyS : y ∈ S := (mem_inf.mp hyP).1
  obtain ⟨h, hbh, hyh⟩ := exists_conj_of_le_centralizer hS2 hcent hSyl (P := zpowers y)
    (hS2.to_le (zpowers_le.mpr hyS)) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyb))
  have hy' : h⁻¹ * y * h ∈ S := hyh y (mem_zpowers y)
  have hah : h⁻¹ * a * h = h⁻¹ * y * h * (h⁻¹ * y * h) := by rw [← hyy]; group
  have hahS : h⁻¹ * a * h ∈ S := by rw [hah]; exact mul_mem hy' hy'
  have hahK : h⁻¹ * a * h ∈ withKernel J := by
    rw [hah]
    exact L34Facts.outSquare G J hJper hL34 _ (hS.1 hy') (hS2.to_le (zpowers_le.mpr hy'))
  exact exists_conj_of_conj ((centralizer_le_normalizer_of_sec4 hMax hset).trans hNJ) hbh
    (exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl hahS hahK)

end CFSG.ComponentClassification.GrSLit.GrS5S
