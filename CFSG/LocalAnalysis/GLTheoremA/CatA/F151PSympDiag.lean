module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpAsmAnalysis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem catalogIs_statedProj_statedSp_charTwo
    (n m : ℕ) (K : Type) [Field K] [Finite K] (hn : 2 ≤ n)
    (hne : ¬ (n = 2 ∧ Nat.card K = 2)) (hcard : Nat.card K = 2 ^ m) :
    catalogIs (StatedProj (StatedSp n K)) (onLie fun d => d.characteristic = 2) := by
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [pow_zero] at hcard
      exact absurd hcard Finite.one_lt_card.ne'
    · exact hm
  let q : TauCeti.PrimePower := ⟨2, m, Nat.prime_two, hmpos⟩
  have hqcard : q.card = 2 ^ m := TauCeti.PrimePower.card_def q
  rcases Nat.lt_or_ge n 3 with hn2 | hn3
  · have hn_eq : n = 2 := by omega
    subst hn_eq
    have hK2 : Nat.card K ≠ 2 := fun h => hne ⟨rfl, h⟩
    have hv : (TauCeti.LieTypeIndex.B 2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      refine ⟨⟨le_rfl, ?_⟩, ?_⟩
      · intro h
        exact hK2 (hcard.trans (hqcard.symm.trans h.2))
      · intro h
        have h2dvd : 2 ∣ q.card := by
          rw [hqcard]
          exact dvd_pow_self 2 hmpos.ne'
        rw [h.2] at h2dvd
        norm_num at h2dvd
    obtain ⟨e⟩ :=
      CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
        (q := q) hv (k := K) (by rw [hcard, hqcard])
    refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩, ?_, ⟨e⟩⟩
    change (TauCeti.LieTypeIndex.B 2 q).characteristic = 2
    exact (TauCeti.LieTypeIndex.characteristic_B 2 q).trans rfl
  · have hv : (TauCeti.LieTypeIndex.B n q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
    obtain ⟨e⟩ :=
      CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
        (r := n) (q := q) hv rfl hn3 (k := K) (by rw [hcard, hqcard])
    refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩, ?_, ⟨e⟩⟩
    change (TauCeti.LieTypeIndex.B n q).characteristic = 2
    exact (TauCeti.LieTypeIndex.characteristic_B n q).trans rfl

theorem sympDiag_of_block (hL : CatLayer) (hC : CatChevComps) (hB : DiagOfBlock)
    (hT : MarkTransport) (hI : ShapeModelDiagIso) (hM : T171Sh.SympComponentBlockAnalysis) :
    SympDiag := by
  intro n m K _ _ hn hne hcard p hp hp2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  haveI : NeZero n := ⟨by omega⟩
  have hbij := proj_bijective_of_charTwo (r := n) (K := K)
  have hcat : catalogIs (StatedProj (StatedSp n K)) (onLie fun d => d.characteristic = 2) :=
    catalogIs_statedProj_statedSp_charTwo n m K hn hne hcard
  have hlayer : ∀ x : StatedProj (StatedSp n K), x ≠ 1 → x ^ p = 1 →
      PerfectInLayer (MulAut.conj x) :=
    hL (StatedProj (StatedSp n K)) p hp hp2 hcat
  have hchev : ∀ x : StatedProj (StatedSp n K), x ≠ 1 → x ^ p = 1 →
      ∀ J : Subgroup (StatedProj (StatedSp n K)),
        GLAPComponent p (Subgroup.centralizer ({x} : Set (StatedProj (StatedSp n K)))) J →
          IsChevSimple 2 (PSimple p J) :=
    hC (StatedProj (StatedSp n K)) p hp hp2 hcat
  have hBA : BlockAnalysisAt (StatedProj (StatedSp n K)) p := by
    intro x y hxp hyp hxy hx1 J hcomp hN
    obtain ⟨x', hx'⟩ := proj_surjective (r := n) (K := K) x
    obtain ⟨y', hy'⟩ := proj_surjective (r := n) (K := K) y
    subst hx'
    subst hy'
    have hinj := hbij.1
    have hx'p : x' ^ p = 1 := hinj (by rw [map_pow, hxp, map_one])
    have hyp' : y' ^ p = 1 := hinj (by rw [map_pow, hyp, map_one])
    have hxy' : x' * y' = y' * x' := hinj (by rw [map_mul, map_mul, hxy])
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    exact hM (m := n) (n := m) (K := K) hcard hn hp hp2 x' y' hx'p hyp' hxy' hx1'
      J hcomp hN
  have hDiagR : ShapeModelDiagAt (StatedProj (StatedSp n K)) p :=
    hB (StatedProj (StatedSp n K)) p hp hp2 hlayer hchev hBA
  have e : StatedProj (StatedSp n K) ≃* ↥(CFSG.Assembly.LargeEvenSpGroup K n) :=
    (MulEquiv.ofBijective (proj n K) hbij).symm
  exact hI hT (StatedProj (StatedSp n K)) ↥(CFSG.Assembly.LargeEvenSpGroup K n) e p hDiagR

end CFSG.LocalAnalysis.GLTheoremA.F151

end
