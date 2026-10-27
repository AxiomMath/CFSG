module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6b
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnOrd6
import CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU (reindexGL reindexGL_val mem_statedSU_of reindex_unitary)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace U4InnU6

variable {D : GL (Fin 6) F4} {d : Fin 6 → F4}
  (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)

section Big

variable (c : F4)

include hD in
theorem pPrimeCore_K1_big (ha4 : 4 ≤ Fintype.card (Blk d c)) (ha5 : Fintype.card (Blk d c) ≤ 5)
    (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 2)
    (hL : ∃ L : Subgroup M6, L ≤ CenD D ∧ Group.IsPerfect ↥L ∧ 25920 ∣ Nat.card L) :
    CFSG.pPrimeCore 3 ↥(K1 hD) = ⊥ := by
  obtain ⟨L, hLC, hLp, hLd⟩ := hL
  have hperfL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hLp
  have hsmall3 : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3 := fun c' h => by
    have := hsmall c' h
    omega
  have hLK : L ≤ (embSU d c).range := le_range_embSU d c hD hsmall3 hLC hperfL
  have hKC : (embSU d c).range ≤ CenD D := by
    rintro _ ⟨A, rfl⟩
    exact embSU_mem_CenD d c hD A
  have ha : Fintype.card (Blk d c) = 4 ∨ Fintype.card (Blk d c) = 5 := by omega
  let eK := MonoidHom.ofInjective (embSU_injective d c)
  haveI := isSimple_statedSU _ ha
  haveI hsK : IsSimpleGroup ↥(embSU d c).range := eK.symm.isSimpleGroup
  have h3K : 3 ∣ Nat.card ↥(embSU d c).range :=
    (show 3 ∣ 25920 by norm_num).trans (hLd.trans (Subgroup.card_dvd_of_le hLK))
  have hncK : ¬ ∀ a b : ↥(embSU d c).range, a * b = b * a := by
    intro hcomm
    haveI : IsMulCommutative ↥L := ⟨⟨fun x y => Subtype.ext (by
      have := congrArg Subtype.val (hcomm ⟨x.1, hLK x.2⟩ ⟨y.1, hLK y.2⟩)
      exact this)⟩⟩
    haveI : Subsingleton ↥L := Group.IsPerfect.subsingleton_of_isMulCommutative
    have h1 : Nat.card ↥L = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩
    rw [h1] at hLd
    exact absurd (Nat.le_of_dvd one_pos hLd) (by norm_num)
  have hZK : Subgroup.center ↥(embSU d c).range = ⊥ := center_eq_bot_of_simple_of_not_comm hncK
  have hOK : CFSG.pPrimeCore 3 ↥(embSU d c).range = ⊥ := pPrimeCore_eq_bot_of_simple h3K
  have hperfK : ⁅(embSU d c).range, (embSU d c).range⁆ = (embSU d c).range := by
    haveI : Group.IsPerfect ↥(embSU d c).range := by
      refine ⟨?_⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(embSU d c).range) with h | h
      · exfalso
        apply hncK
        intro a b
        have : ⁅a, b⁆ ∈ commutator ↥(embSU d c).range :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      · exact h
    exact Subgroup.isPerfect_iff.1 inferInstance
  have hKn : ∀ x ∈ K1 hD, ∀ k ∈ (embSU d c).range, x * k * x⁻¹ ∈ (embSU d c).range := by
    intro x hx k hk
    have hxC := K1_le_CenD hD hx
    let K' : Subgroup M6 := (embSU d c).range.map (MulAut.conj x).toMonoidHom
    have hK'C : K' ≤ CenD D := by
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hxC (hKC hy)) (inv_mem hxC)
    have hK'perf : ⁅K', K'⁆ = K' := by
      show ⁅(embSU d c).range.map (MulAut.conj x).toMonoidHom,
        (embSU d c).range.map (MulAut.conj x).toMonoidHom⁆ = _
      rw [← Subgroup.map_commutator, hperfK]
    have := le_range_embSU d c hD hsmall3 hK'C hK'perf
    exact this ⟨k, hk, rfl⟩
  have hR : CFSG.pPrimeCore 3 ↥(Rc hD c) = ⊥ ∧
      ∀ r ∈ Rc hD c, (∀ r' ∈ Rc hD c, r * r' = r' * r) → r = 1 := by
    by_cases h1 : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 1
    · rw [Rc_eq_bot hD c h1]
      refine ⟨pPrimeCore_eq_bot_of_exponent fun g => ⟨0, ?_⟩, fun r hr _ => ?_⟩
      · exact Subsingleton.elim _ _
      · exact Subgroup.mem_bot.1 hr
    · push Not at h1
      obtain ⟨c₂, hc₂, hc₂2⟩ := h1
      have hc₂eq : Fintype.card (Blk d c₂) = 2 := by
        have := hsmall c₂ hc₂
        omega
      have hcard := card_blk_add_le d (c := c) (c' := c₂) (Ne.symm hc₂)
      have h6 : Fintype.card (Blk d c) + Fintype.card (Blk d c₂) = 6 := by omega
      have hcover := cover_of_card c c₂ (Ne.symm hc₂) h6
      have hReq := Rc_eq_range hD c c₂ (Ne.symm hc₂) hcover
      let e2 := MonoidHom.ofInjective (embSU_injective d c₂)
      have h6' : Nat.card ↥(Rc hD c) = 6 := by
        rw [hReq, ← Nat.card_congr e2.toEquiv]
        exact card_statedSU_six _ hc₂eq
      have hnc2 : ¬ ∀ a b : ↥(Rc hD c), a * b = b * a := by
        intro hcomm
        apply not_comm_statedSU _ hc₂eq
        intro a b
        have := congrArg Subtype.val
          (hcomm ⟨embSU d c₂ a, hReq ▸ ⟨a, rfl⟩⟩ ⟨embSU d c₂ b, hReq ▸ ⟨b, rfl⟩⟩)
        apply embSU_injective d c₂
        rw [map_mul, map_mul]
        exact this
      refine ⟨pPrimeCore_eq_bot_of_card_six h6' hnc2, fun r hr hr' => ?_⟩
      have hz := center_eq_bot_of_card_six h6' hnc2
      have : (⟨r, hr⟩ : ↥(Rc hD c)) ∈ Subgroup.center ↥(Rc hD c) := by
        rw [Subgroup.mem_center_iff]
        intro b
        exact Subtype.ext (hr' b.1 b.2).symm
      rw [hz, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
  refine pPrimeCore_eq_bot_of_normal_in (K1 hD) ![(embSU d c).range, Rc hD c] ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact fun g hg => embSU_mem_K1_of_mem_range d c hD hg
    · exact Rc_le_K1 hD c
  · intro i x hx k hk
    fin_cases i
    · exact hKn x hx k hk
    · exact Rc_normal hD c hx hk
  · intro i
    fin_cases i
    · exact hOK
    · exact hR.1
  · intro g hg hcent
    obtain ⟨k, hk, r, hr, rfl⟩ := K1_eq_mul hD c hg
    have hcomm_kr : ∀ k' ∈ (embSU d c).range, r * k' = k' * r := by
      rintro _ ⟨A, rfl⟩
      obtain ⟨-, hrC, hrb⟩ := (mem_Rc hD c).1 hr
      exact (embSU_comm_of_blk_one d c hD A hrC hrb).symm
    have hk1 : k = 1 := by
      have : (⟨k, hk⟩ : ↥(embSU d c).range) ∈ Subgroup.center ↥(embSU d c).range := by
        rw [Subgroup.mem_center_iff]
        intro b
        have h2 := hcent 0 b.1 b.2
        apply Subtype.ext
        show b.1 * k = k * b.1
        have h3 : k * r * b.1 = b.1 * (k * r) := h2
        rw [mul_assoc, hcomm_kr b.1 b.2, ← mul_assoc, ← mul_assoc] at h3
        exact (mul_right_cancel h3).symm
      rw [hZK, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    subst hk1
    have hr1 : r = 1 := hR.2 r hr (fun r' hr' => by
      have h2 := hcent 1 r' hr'
      simpa using h2)
    exact ⟨0, by simp [hr1]⟩

end Big

end U4InnU6

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
