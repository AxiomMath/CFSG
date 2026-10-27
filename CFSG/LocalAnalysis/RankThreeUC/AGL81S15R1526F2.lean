module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row28One

variable {X : Type} [Group X] [Finite X]

theorem not_isPSolvable_centralizer_of_commute_aux1 {F : Subgroup X} (hF : IsPGroup 3 F) :
    Subgroup.centralizer (barO2 F : Set (X ⧸ CFSG.pCore 2 X)) ≤
      barO2 (Subgroup.centralizer (F : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hl : ∀ a ∈ F, x⁻¹ * (a * x * a⁻¹) ∈ CFSG.pCore 2 X := by
    intro a ha
    have h := Subgroup.mem_centralizer_iff.1 hy (QuotientGroup.mk' (CFSG.pCore 2 X) a)
      ⟨a, ha, rfl⟩
    have h' : (a : X ⧸ CFSG.pCore 2 X) * (x : X ⧸ CFSG.pCore 2 X) =
        (x : X ⧸ CFSG.pCore 2 X) * (a : X ⧸ CFSG.pCore 2 X) := h
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h']
    group
  obtain ⟨d, hd, hfix⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint.exists_fixed_point_in_coset
    F (CFSG.pCore 2 X) hF (pRank_barO2_eq_aux_notDvdCard Nat.prime_three (by norm_num))
    (fun a _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨fun hn => Subgroup.Normal.conj_mem inferInstance n hn a, fun hn => ?_⟩
      have h1 := Subgroup.Normal.conj_mem inferInstance _ hn a⁻¹
      have e : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
      rwa [e] at h1) x hl
  refine ⟨x * d, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hfix a ha
    calc a * (x * d) = a * (x * d) * a⁻¹ * a := by group
      _ = (x * d) * a := by rw [h]
  · have hd1 : (d : X ⧸ CFSG.pCore 2 X) = 1 := (QuotientGroup.eq_one_iff d).2 hd
    change (QuotientGroup.mk (x * d) : X ⧸ CFSG.pCore 2 X) = (x : X ⧸ CFSG.pCore 2 X)
    rw [QuotientGroup.mk_mul, hd1, mul_one]

theorem not_isPSolvable_centralizer_of_commute {F K : Subgroup X} (hF : IsPGroup 3 F)
    (hcomm : ⁅barO2 F, barO2 K⁆ = ⊥) (hK : ¬ CFSG.HallHigman.IsPSolvable 7 ↥(barO2 K)) :
    ¬ CFSG.HallHigman.IsPSolvable 7 ↥(Subgroup.centralizer (F : Set X)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hps
  apply hK
  have h2 : CFSG.HallHigman.IsPSolvable 7 ↥(barO2 (Subgroup.centralizer (F : Set X))) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      (QuotientGroup.mk' (CFSG.pCore 2 X)) hps
  refine CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le h2
    (le_trans ?_ (not_isPSolvable_centralizer_of_commute_aux1 hF))
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 : ⁅f, k⁆ ∈ ⁅barO2 F, barO2 K⁆ := Subgroup.commutator_mem_commutator hf hk
  rw [hcomm, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem two_le_pRank_centralizer_of_le {L F : Subgroup X} (hF : IsPGroup 3 F) (hFL : F ≤ L)
    (hrank : 1 < CFSG.Open.pRank 7 (cMBar L)) :
    2 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer (F : Set X)) := by
  have hFL' : (barO2 F : Set (X ⧸ CFSG.pCore 2 X)) ⊆ (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) :=
    SetLike.coe_subset_coe.2 (Subgroup.map_mono hFL)
  have h1 : cMBar L ≤ barO2 (Subgroup.centralizer (F : Set X)) :=
    le_trans (Subgroup.centralizer_le hFL') (not_isPSolvable_centralizer_of_commute_aux1 hF)
  have h2 : CFSG.Open.pRank 7 (cMBar L) ≤
      CFSG.Open.pRank 7 (barO2 (Subgroup.centralizer (F : Set X))) :=
    CFSG.SectionRank.pRank_mono (by norm_num) h1
  rw [← pRank_barO2_eq_aux_eq (Subgroup.centralizer (F : Set X)) (by norm_num) (by norm_num)] at h2
  omega

end Row28One

end CFSG.LocalAnalysis.RankThreeUC.S15
