module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.J2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.RuKFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24KFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4KS219
public import CFSG.RankThree.Asc83Table.M24
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.Asc83Table.Ru
public import CFSG.RankThree.Asc83Table.J4
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRankTwo
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG CFSG.Open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21
open CFSG.Blueprint.NativeSporadic (Carrier)

macro "sporOrd_num" : tactic =>
  `(tactic| (
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderJ4,
      CFSG.Open.orderRu]
    norm_num))

theorem factorization_three_of_sylow {T : Type} [Group T] [Finite T]
    (h : ∀ P : Sylow 3 T, Nat.card P = 27) : (Nat.card T).factorization 3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := h default
  rw [Sylow.card_eq_multiplicity, show (27 : ℕ) = 3 ^ 3 by norm_num] at h1
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1

theorem kd264RowData_of_table {T : Type} [Group T] [Finite T] {k : ℕ} (hk : 5 ≤ k)
    (hS : ∀ P : Sylow 3 T, Nat.card P = 27) (hrank : CFSG.pRank 3 T = 2)
    (hlay : ∀ x : T, x ≠ 1 → IsCentral218 (⊤ : Subgroup T) x →
      x ∈ inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T)) ∧
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover
        ↥(inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set T)))
        (alternatingGroup (Fin k))) :
    KD264RowData 3 T :=
  kd264RowData_of_tripleCover hk (factorization_three_of_sylow hS)
    (fun D hD => CFSG.RankThree.PartTwo.Sec4.Item434Spor.noE27_of_pRank_le_two hrank.le D hD)
    hlay

theorem kd264RowData_J2_three :
    KD264RowData 3 ↥CFSG.Sporadic.Schreier.j2P := by
  have e : ↥CFSG.Sporadic.Schreier.j2P ≃* NativeSporadic.J2 :=
    CFSG.Sporadic.Schreier.j2PermEquiv.symm
  have hcard : Nat.card ↥CFSG.Sporadic.Schreier.j2P = 604800 :=
    CFSG.Sporadic.Schreier.card_j2P
  have h3 : (Nat.card ↥CFSG.Sporadic.Schreier.j2P).factorization 3 = 3 := by
    rw [hcard, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  refine kd264RowData_of_tripleCover (k := 6) (by norm_num) h3 (fun D hD =>
    CFSG.RankThree.PartTwo.Sec4.Item434Spor.noE27_of_extraspecial_sylow h3 (fun P =>
      (CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 _ ⟨e⟩ P _ rfl _ rfl).1.1.1) D hD)
    fun x hx1 hx => CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219.ks219J2 _ ⟨e⟩ x hx1 hx

theorem kd264RowData_He_three :
    KD264RowData 3 ↥CFSG.Sporadic.HeldB.heP := by
  have e : ↥CFSG.Sporadic.HeldB.heP ≃* NativeSporadic.He := CFSG.Sporadic.HeldB.heEquivP.symm
  obtain ⟨hS, hrank, -⟩ := CFSG.RankThree.Asc83Table.He.table (L := ↥CFSG.Sporadic.HeldB.heP) ⟨e⟩
  exact kd264RowData_of_table (k := 7) (by norm_num) hS hrank fun x hx1 hx =>
    CFSG.AGLEmbeddingD2.Wilson.Census219.ks219He _ ⟨e⟩ x hx1 hx

theorem kd264SporAt_M24_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hfs : Finite (Carrier .M24) ∧ IsSimpleGroup (Carrier .M24)) : KD264SporAt 3 .M24 := by
  haveI := hfs.1
  obtain ⟨hS, hrank, -⟩ := CFSG.RankThree.Asc83Table.M24.table (L := Carrier .M24)
    ⟨MulEquiv.refl _⟩
  refine kd264SporAt_of_carrier hOut hbr hOrd hfs (by sporOrd_num) (by sporOrd_num) Nat.prime_three
    (by norm_num) fun _ _ _ => kd264RowData_of_table (k := 6) (by norm_num) hS hrank
      fun x hx1 hx => CFSG.AGLEmbeddingD2.Wilson.Census219.ks219M24 _
        ⟨MulEquiv.refl _⟩ x hx1 hx

theorem kd264SporAt_Ru_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hfs : Finite (Carrier .Ru) ∧ IsSimpleGroup (Carrier .Ru)) : KD264SporAt 3 .Ru := by
  haveI := hfs.1
  have hL : NativeSporadic.IsSporadic (Carrier .Ru) .Ru := ⟨MulEquiv.refl _⟩
  have htab := CFSG.RankThree.Asc83Table.Ru.table hL
  have hlay := CFSG.AGLEmbeddingD2.Wilson.Census219.ks219Ru (Carrier .Ru) ⟨MulEquiv.refl _⟩
  have hRow : KD264RowData 3 (Carrier .Ru) :=
    kd264RowData_of_table (k := 6) (by norm_num) htab.1 htab.2.1 hlay
  have h2 : 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .Ru := by sporOrd_num
  have h2' : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .Ru ≠ 2 := by sporOrd_num
  exact kd264SporAt_of_carrier hOut hbr hOrd hfs h2 h2' Nat.prime_three (by norm_num)
    fun _ _ _ => hRow

theorem kd264SporAt_J4_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hfs : Finite (Carrier .J4) ∧ IsSimpleGroup (Carrier .J4))
    (hM22 : IsSimpleGroup (Carrier .M22)) : KD264SporAt 3 .J4 := by
  haveI := hfs.1
  have hL : NativeSporadic.IsSporadic (Carrier .J4) .J4 := ⟨MulEquiv.refl _⟩
  have htab := CFSG.RankThree.Asc83Table.J4.table hL
  have hlay := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.ks219J4_holds (Carrier .J4)
    ⟨MulEquiv.refl _⟩
  haveI : IsSimpleGroup NativeSporadic.M22 := hM22
  have hRow : KD264RowData 3 (Carrier .J4) := by
    refine kd264RowData_of_layer (factorization_three_of_sylow htab.1)
      (fun D hD => CFSG.RankThree.PartTwo.Sec4.Item434Spor.noE27_of_pRank_le_two htab.2.1.le D hD)
      fun x hx1 hx => ?_
    obtain ⟨-, hc6, ⟨e⟩⟩ := hlay x hx1 hx
    refine ⟨e.isSimpleGroup, ?_⟩
    exact dvd_trans (by rw [hc6]; norm_num) (Subgroup.card_subgroup_dvd_card _)
  have h2 : 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .J4 := by sporOrd_num
  have h2' : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .J4 ≠ 2 := by sporOrd_num
  exact kd264SporAt_of_carrier hOut hbr hOrd hfs h2 h2' Nat.prime_three (by norm_num)
    fun _ _ _ => hRow

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
