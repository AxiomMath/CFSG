module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64iiDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64bBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPC
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongK64ii

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
open scoped Pointwise


theorem pComp_of_simpleSectionAt {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {H L M₀ : Subgroup A} {z : A} (hz : orderOf z = p)
    (hL : S622IsSimpleSection L (rankThreePrimeCore p H))
    (hLH : L ≤ H) (hnorm : H ≤ normalizer (L : Set A)) (hzL : z ∈ L)
    (hrk : CFSG.Open.pRank p L ≤ 1)
    (hnc : ¬ L ≤ (M₀ ⊓ L) ⊔ rankThreePrimeCore p H) (hM₀ : M₀ ≤ H) :
    ∃ K : Subgroup A, PComp p (M₀ ⊔ rankThreePrimeCore p H) H K z := by
  have hKD : CFSG.Quasithin.perfectCore L ⊔ rankThreePrimeCore p H = L :=
    Parrott.P614.P614K64b.perfectCore_sup_eq hL
  set D := rankThreePrimeCore p H
  set K := CFSG.Quasithin.perfectCore L
  obtain ⟨hDL, hDn, hDne, hmax, -⟩ := hL
  have hLD : L ≤ normalizer (D : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mp hDn
  have hKL : K ≤ L := CFSG.Quasithin.perfectCore_le L
  have hNK : normalizer (L : Set A) ≤ normalizer (K : Set A) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore L
  have hLK : L ≤ normalizer (K : Set A) := Subgroup.le_normalizer.trans hNK
  have hHD : H ≤ normalizer (D : Set A) := by
    open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple in
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (relPPrimeCore_le H)).mp
      (relPPrimeCore_normal hp H)
  have hDcop : Nat.Coprime p (Nat.card D) := by
    open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple in
    exact coprime_card_relPPrimeCore hp H
  have hz3 : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hzK : z ∈ K := Parrott.P614.P614K64b.mem_of_sup_eq hKL hLK hLD hKD hDcop hzL hz3
  refine ⟨K, ⟨hKL.trans hLH, hnorm.trans hNK, ?_, Subgroup.zpowers_le.mpr hzK, ?_,
    CFSG.Quasithin.perfectCore_perfect L, ?_, ?_⟩⟩
  ·
    intro hK
    apply hnc
    intro l hl
    have hl' : l ∈ ((M₀ ⊔ D : Subgroup A) : Set A) := by
      have hle : K ⊔ D ≤ M₀ ⊔ D := sup_le hK le_sup_right
      exact hle (by rw [hKD]; exact hl)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M₀ D (hM₀.trans hHD)] at hl'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hl'
    have hmL : m ∈ L := by simpa using mul_mem hl (inv_mem (hDL hd))
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hm, hmL⟩))
      (Subgroup.mem_sup_right hd)
  ·
    refine le_antisymm ((CFSG.SectionRank.pRank_mono hp.one_lt hKL).trans hrk) ?_
    exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.mpr hzK)
      (CFSG.Open.isElemAbelian_zpowers hz3) (by rw [Nat.card_zpowers, hz, pow_one])
  ·
    refine lt_of_le_of_ne inf_le_left fun h => hDne ?_
    exact (sup_eq_right.mpr (inf_eq_left.mp h)).symm.trans hKD
  ·
    intro N hNK' hNn (hKDN : K ⊓ D ≤ N)
    have hKN : K ≤ normalizer (N : Set A) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK').mp hNn
    have hN1L : N ⊔ D ≤ L := sup_le (hNK'.trans hKL) hDL
    have hnormal : ((N ⊔ D).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN1L]
      calc L = K ⊔ D := hKD.symm
        _ ≤ normalizer ((N ⊔ D : Subgroup A) : Set A) := sup_le
          ((le_inf hKN (hKL.trans hLD)).trans (Subgroup.inf_normalizer_le_normalizer_sup N D))
          (Parrott.P614.P614K64b.le_normalizer_of_le_of_le hLD le_sup_right hN1L)
    rcases hmax (N ⊔ D) le_sup_right hN1L hnormal with h | h
    · exact Or.inl (le_antisymm (le_inf hNK' (le_sup_left.trans h.le)) hKDN)
    · refine Or.inr ?_
      have hK' : K = N ⊔ (K ⊓ D) := CFSG.Quasithin.A3.eq_sup_inf_of_le_sup
        (hNK'.trans (hKL.trans hLD)) hNK' (hKL.trans h.ge)
      rw [sup_eq_left.mpr hKDN] at hK'
      exact hK'.symm

section Certified


theorem kFact64iiAt_holds {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : KFact64iiAt p := by
  intro A _ _ H Q M₀ x z hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  obtain ⟨L, hL, hLH, hzL, hrk, hncL, -, hHL⟩ :=
    kFact64iiLNorm_of_inputs kFact64iiOuterSylow_holds kFact64iiI121_holds A p H Q M₀ x z
      hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc
  refine ⟨pComp_of_simpleSectionAt hp hzo hL hLH hHL hzL hrk hncL hM₀H, ?_⟩
  exact (kFact64ii_core kFact64iiOuterSylow_holds kFact64iiI121_holds A p H Q M₀ x z
    hp hp3 hKH hxo hzo hxz hxnz hQsyl hBQ hΩ hxfr hwc hQM hM₀H hNz hnc).2
    kFact64iiOuterNPC_holds

theorem kFact64ii_holds : KFact64ii :=
  kFact64ii_iff.mpr fun _ hp hp2 => kFact64iiAt_holds hp (hp.two_le.lt_of_ne' hp2)

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongK64ii
