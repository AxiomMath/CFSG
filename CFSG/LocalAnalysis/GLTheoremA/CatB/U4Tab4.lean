module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab3
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G]

theorem conj_mk_eq_barAut (K : Subgroup G) (k : ↥K) (hk : (k : G) ∈ Subgroup.normalizer (K : Set G)) :
    MulAut.conj (QuotientGroup.mk k : ↥K ⧸ GLAPPrimeCore 3 ↥K) = barAut 3 K ⟨(k : G), hk⟩ := by
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.conj_apply, barAut_mk]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem innerAut_le_autBar (K W : Subgroup G) (hKW : K ≤ W) (hWN : W ≤ Subgroup.normalizer (K : Set G)) :
    innerAut (↥K ⧸ GLAPPrimeCore 3 ↥K) ≤ autBar 3 W K := by
  rintro φ ⟨q, rfl⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hk : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  refine Subgroup.mem_map.2 ⟨⟨(k : G), hk⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 ⟨hKW k.2, hk⟩
  · exact (conj_mk_eq_barAut K k hk).symm

theorem u4TableAt_of_S (G : Type) [Group G] [Finite G] (h : U4TabS) : U4TableAt G := by
  intro K W u hWN huW hX hKW hu3 hK hJ
  obtain ⟨X, hXK⟩ := hX
  obtain ⟨J, hJ, hJcat⟩ := hJ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hu : u ∈ Subgroup.normalizer (K : Set G) := hWN huW
  have hQq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hXK
  have hQO : GLAPPrimeCore 3 (PQuot 3 K) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hcat : catalogIs (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K)) S9.isTableU4 := hK
  have hv3 : (barAut 3 K ⟨u, hu⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨u, hu⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [h1, map_one]
  have hU4 : U4Hyp (barAut 3 K ⟨u, hu⟩) := u4Hyp_of_component hu hu3 hJ hJcat
  have hA := h.1 (PQuot 3 K) (barAut 3 K ⟨u, hu⟩) hQq hQO hcat hv3 hU4
  obtain ⟨a, b, hO⟩ := h.2 (PQuot 3 K) hQq hQO hcat
  exact isPGroup_two_of_index (innerAut (PQuot 3 K)) (autBar 3 W K)
    (Subgroup.centralizer ({barAut 3 K ⟨u, hu⟩} : Set (MulAut (barOf 3 K))))
    (innerAut_le_autBar K W hKW hWN) hA hO

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
