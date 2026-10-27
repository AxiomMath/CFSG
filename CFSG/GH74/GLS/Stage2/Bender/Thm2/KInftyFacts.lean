module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Conj

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem Kfam_subset_classTwo (P : Subgroup G) (n : ℕ) : Kfam P n ⊆ classTwo P := by
  cases n with
  | zero => exact fun B hB => hB
  | succ n =>
    show (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))) ⊆ classTwo P
    split_ifs
    · exact fun B hB => hB.1
    · exact fun B hB => hB.1

theorem le_of_mem_Kfam {P B : Subgroup G} {n : ℕ} (hB : B ∈ Kfam P n) : B ≤ P :=
  (Kfam_subset_classTwo P n hB).1

theorem gen_Kfam_le (P : Subgroup G) (n : ℕ) : gen (Kfam P n) ≤ P := by
  unfold gen
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨B, hB, hxB⟩ := hx
  exact le_of_mem_Kfam hB hxB

theorem bot_mem_classTwo (P : Subgroup G) : (⊥ : Subgroup G) ∈ classTwo P :=
  ⟨bot_le, by simp⟩

theorem bot_mem_Kup (P Q : Subgroup G) : (⊥ : Subgroup G) ∈ Kup P Q :=
  ⟨bot_mem_classTwo P, by simp⟩

theorem bot_mem_Klow (P Q : Subgroup G) : (⊥ : Subgroup G) ∈ Klow P Q := by
  refine ⟨bot_mem_classTwo P, ?_, fun A _ _ _ _ _ => by simp⟩
  intro q _
  have : normalizer (((⊥ : Subgroup G)) : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr inferInstance
  rw [this]
  exact Subgroup.mem_top q

theorem bot_mem_Kfam (P : Subgroup G) (n : ℕ) : (⊥ : Subgroup G) ∈ Kfam P n := by
  cases n with
  | zero => exact bot_mem_classTwo P
  | succ n =>
    show (⊥ : Subgroup G) ∈ (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n)))
    split_ifs
    · exact bot_mem_Klow P _
    · exact bot_mem_Kup P _

theorem kInfty_le (P : Subgroup G) : kInfty P ≤ P := by
  unfold kInfty gen
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨B, hB, hxB⟩ := hx
  have h0 : B ∈ Kfam P (2 * 0) := Set.mem_iInter.mp hB 0
  exact le_of_mem_Kfam h0 hxB

end Basic

section Ext

variable {G : Type} [Group G] [Finite G]

theorem exists_central_ext {p : ℕ} (hp : p.Prime) {P B : Subgroup G} (hP : IsPGroup p ↥P) (hBP : B ≤ P)
    (hC : ¬ P ⊓ centralizer (B : Set G) ≤ B) :
    ∃ x ∈ P ⊓ centralizer (B : Set G), x ∉ B ∧ ∀ n ∈ P ⊓ normalizer (B : Set G), ⁅x, n⁆ ∈ zOf B := by
  have hBN : B ≤ P ⊓ normalizer (B : Set G) := le_inf hBP Subgroup.le_normalizer
  have hCN : P ⊓ centralizer (B : Set G) ≤ P ⊓ normalizer (B : Set G) :=
    fun c hc => ⟨hc.1, Subgroup.centralizer_le_normalizer _ hc.2⟩
  have hZB : zOf B ≤ B := inf_le_left
  have hZN : zOf B ≤ P ⊓ normalizer (B : Set G) := hZB.trans hBN
  have hNZ : P ⊓ normalizer (B : Set G) ≤ normalizer ((zOf B : Subgroup G) : Set G) := by
    intro g hg
    have hmap : mapS (MulAut.conj g) B = B := map_conj_eq_of_mem_normalizer hg.2
    have h1 := mapS_zOf (MulAut.conj g) B
    rw [hmap] at h1
    exact mem_normalizer_of_map_conj_eq h1
  have hCnorm : P ⊓ normalizer (B : Set G) ≤ normalizer ((P ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg.1) (normalizer_le_normalizer_centralizer B hg.2)
  have : Fact p.Prime := ⟨hp⟩
  have hNp : IsPGroup p ↥(P ⊓ normalizer (B : Set G)) := hP.to_le inf_le_left
  have hZsn : ((zOf B).subgroupOf (P ⊓ normalizer (B : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).mpr hNZ
  have hCsn : ((P ⊓ centralizer (B : Set G)).subgroupOf (P ⊓ normalizer (B : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hCnorm
  have hq : IsPGroup p (↥(P ⊓ normalizer (B : Set G)) ⧸ (zOf B).subgroupOf (P ⊓ normalizer (B : Set G))) :=
    hNp.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : Group.IsNilpotent (↥(P ⊓ normalizer (B : Set G)) ⧸ (zOf B).subgroupOf (P ⊓ normalizer (B : Set G))) :=
    hq.isNilpotent
  set Cbar : Subgroup (↥(P ⊓ normalizer (B : Set G)) ⧸ (zOf B).subgroupOf (P ⊓ normalizer (B : Set G))) :=
    ((P ⊓ centralizer (B : Set G)).subgroupOf (P ⊓ normalizer (B : Set G))).map
      (QuotientGroup.mk' ((zOf B).subgroupOf (P ⊓ normalizer (B : Set G)))) with hCbardef
  have : Cbar.Normal := Subgroup.Normal.map hCsn _ (QuotientGroup.mk'_surjective _)
  have hCbar : Cbar ≠ ⊥ := by
    intro hb
    rw [hCbardef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    apply hC
    intro c hc
    have h1 : (⟨c, hCN hc⟩ : ↥(P ⊓ normalizer (B : Set G))) ∈
        (P ⊓ centralizer (B : Set G)).subgroupOf (P ⊓ normalizer (B : Set G)) := hc
    exact hZB (hb h1)
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hCbar)
  obtain ⟨⟨c', hc'Cs, hc'⟩, hycen⟩ := y.2
  have hc'C : (c' : G) ∈ P ⊓ centralizer (B : Set G) := hc'Cs
  have hy1 : y.1 ≠ 1 := fun h => hy (Subtype.ext h)
  refine ⟨c', hc'C, ?_, ?_⟩
  · intro hB
    apply hy1
    rw [← hc', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨hB, hc'C.2⟩
  · intro n hn
    have hcomm := Subgroup.mem_center_iff.mp hycen (QuotientGroup.mk' _ ⟨n, hn⟩)
    rw [← hc'] at hcomm
    have h2 : QuotientGroup.mk' ((zOf B).subgroupOf (P ⊓ normalizer (B : Set G))) ⁅c', ⟨n, hn⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    exact (QuotientGroup.eq_one_iff (N := (zOf B).subgroupOf (P ⊓ normalizer (B : Set G))) ⁅c', ⟨n, hn⟩⁆).mp h2

end Ext

end CFSG.GH74.GLS.Stage2.Bender.Thm2
