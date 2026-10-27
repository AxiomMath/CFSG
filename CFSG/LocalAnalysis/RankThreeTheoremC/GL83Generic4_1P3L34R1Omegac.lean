module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts4
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Omegab
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44c
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectc
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34omega_T_sylow (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsSylowOf 3 (l34Img x J ((P : Subgroup G) ⊓ J)) (l34Img x J J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hKt⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨-, hTc, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥(l34Img x J J)) := inferInstance
  exact isSylowOf_of_card hTK (hTc.trans ((hK2 _ hKt Q).1.symm.trans Q.card_eq_multiplicity))

theorem l34omega_mem_of_commute (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {y : G} (hyP : y ∈ (P : Subgroup G))
    (hyC : y ∈ centralizer ({x} : Set G)) (hy3 : y ^ 3 = 1) (hyx : y ∉ zpowers x) {w : G}
    (hwx : w * x = x * w) (hwy : w * y = y * w) : w ∈ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hyx' : y * x = x * y := mem_centralizer_singleton_iff.mp hyC
  have hel : IsElemAbelian 3 (zpowers x ⊔ zpowers y) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) (CFSG.AGLEmbedding.isElemAbelian_zpowers hy3)
      (by
        rw [p34_centralizer_zpowers y]
        exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyx'.symm))
  have hcomm : ∀ e ∈ zpowers x, e * y = y * e := fun e he =>
    mem_centralizer_iff.mp (by rw [p34_centralizer_zpowers x]; exact hyC) e he
  have hcard : Nat.card (zpowers x ⊔ zpowers y : Subgroup G) = 3 ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers x) hy3 hyx hcomm,
      Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    norm_num
  have hle : zpowers x ⊔ zpowers y ≤ (P : Subgroup G) :=
    sup_le (zpowers_le.mpr hgen.1) (zpowers_le.mpr hyP)
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hN := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM (P.isPGroup'.to_le hle)
    (hle.trans hPM) (le_pRank_of_elemAbelian_card le_rfl hel hcard)
  have hwc : zpowers x ⊔ zpowers y ≤ centralizer ({w} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwx.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwy.symm))
  refine hN (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => ?_))
  exact mem_centralizer_singleton_iff.mp (hwc hh)

theorem l34omega_mem_K (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK10 : KFactL34OuterCentralizer) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) {y : G}
    (hyP : y ∈ (P : Subgroup G)) (hyC : y ∈ centralizer ({x} : Set G)) (hy3 : y ^ 3 = 1)
    (hyx : y ∉ zpowers x) : l34Hom x J ⟨y, hyC⟩ ∈ l34Img x J J := by
  by_contra hyK
  obtain ⟨hKn, hKc, hKL⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨-, -, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  have hTsyl := l34omega_T_sylow hS hU0 hK1 hK2 hp hM hgen hJ
  set yc : ↥(centralizer ({x} : Set G)) := ⟨y, hyC⟩ with hyc
  have hyA : y ∈ normalizer (((P : Subgroup G) ⊓ J : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hyP, hJ.centralizer_le hyC⟩
  have hyN := l34insp_hom_mem_normalizer x J ((P : Subgroup G) ⊓ J) (u := yc) hyA
  have hyc3 : yc ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hy3' : l34Hom x J yc ^ 3 = 1 := by rw [← map_pow, hyc3, map_one]
  obtain ⟨c, ⟨hcy, hcK⟩, hcN⟩ :=
    IsConcreteLE.not_le_iff_exists.mp (hK10 _ _ hKn hKc hKL _ hTK hTsyl _ hyN hyK hy3')
  obtain ⟨j, hjJ, rfl⟩ := Subgroup.mem_map.mp hcK
  have hjJ' : (j : G) ∈ J := mem_subgroupOf.mp hjJ
  have hcomm : j * yc * j⁻¹ * yc⁻¹ ∈ primeComplementCore (G := ↥(centralizer ({x} : Set G))) 3 := by
    refine l34_mem_of_ker_of_mem_J hK1 hK2 hJ _ ?_ ?_
    · have h := (mem_normalizer_iff.mp (hJ.centralizer_le hyC) (j : G)⁻¹).mp (J.inv_mem hjJ')
      have h2 := J.mul_mem hjJ' h
      simpa [mul_assoc] using h2
    · have hcy' : l34Hom x J j * l34Hom x J yc = l34Hom x J yc * l34Hom x J j :=
        mem_centralizer_singleton_iff.mp hcy
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcy']
      group
  obtain ⟨o, hoO, hfix⟩ := l34omega_exists_fixed (primeComplementCore_coprime 3) hyc3 hcomm
  have hjoM : ((j * o : ↥(centralizer ({x} : Set G))) : G) ∈ M := by
    refine l34omega_mem_of_commute hS hU0 hp hM hgen hyP hyC hy3 hyx
      (mem_centralizer_singleton_iff.mp (j * o).2) ?_
    exact congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hπo : l34Hom x J o = 1 := by
    have h : QuotientGroup.mk' (primeComplementCore (G := ↥(centralizer ({x} : Set G))) 3) o =
        1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hoO
    change QuotientGroup.mk' _ (QuotientGroup.mk' _ o) = 1
    rw [h, map_one]
  have hmem : l34Hom x J j ∈ l34Img x J M ⊓ l34Img x J J :=
    ⟨⟨j * o, mem_subgroupOf.mpr hjoM, by rw [map_mul, hπo, mul_one]⟩, ⟨j, hjJ, rfl⟩⟩
  rw [l34_Kimg_inf_M hS hU0 hK1 hK2 hp hM hgen hJ] at hmem
  exact hcN hmem.1

end CFSG.LocalAnalysis.RankThreeTheoremC
