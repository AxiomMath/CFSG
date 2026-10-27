module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutI

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open scoped commutatorElement Matrix

variable {K : Type} [Field K] {a : K}

theorem gI_mem_fixI (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    gI ha k ∈ fixI a ha := by
  show conjSp 2 K (aIgsp ha) (gI ha k) = gI ha k
  apply sp_ext
  set A : GL (Fin 2 ⊕ Fin 2) K := ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = aI a := rfl
  rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA, coe_gI, aI_comm_gI ha,
    Matrix.mul_assoc, ← hA, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem detI_gI (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    detI ha ⟨gI ha k, gI_mem_fixI ha k⟩ = 1 := by
  have hZ : blocksI ha ⟨gI ha k, gI_mem_fixI ha k⟩ =
      (k : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (QuadraticAlgebra K a 0)) := by
    apply qBlock_injective a
    rw [qBlock_blocksI, qBlock_map]
    change bAinv a * (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) * bA a =
      kron (k : Matrix (Fin 2) (Fin 2) K) 1
    simp only [Matrix.mul_assoc]
    rw [bAinv_mul_bA ha, Matrix.mul_one, ← Matrix.mul_assoc, bAinv_mul_bA ha, Matrix.one_mul]
  show (blocksI ha ⟨gI ha k, gI_mem_fixI ha k⟩).det = 1
  rw [hZ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, k.2, map_one]

theorem conj_gI_mem_range (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (x : fixI a ha)
    (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((x * ⟨gI ha k, gI_mem_fixI ha k⟩ * x⁻¹ : fixI a ha) : StatedSp 2 K) ∈ (gI ha).range := by
  apply mem_range_gI_of_detI ha h2
  rw [map_mul, map_mul]
  calc detI ha x * detI ha ⟨gI ha k, gI_mem_fixI ha k⟩ * detI ha x⁻¹
      = detI ha x * detI ha x⁻¹ * detI ha ⟨gI ha k, gI_mem_fixI ha k⟩ := by
        rw [mul_assoc, mul_comm (detI ha ⟨gI ha k, gI_mem_fixI ha k⟩), ← mul_assoc]
    _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one, one_mul, detI_gI]

theorem conj_mem_JI (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ (fixI a ha).map (proj 2 K)) {l : StatedProj (StatedSp 2 K)} (hl : l ∈ JI ha) :
    x * l * x⁻¹ ∈ JI ha := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hl
  obtain ⟨m, hm⟩ := conj_gI_mem_range ha h2 ⟨g, hg⟩ k
  refine ⟨_, ⟨m, rfl⟩, ?_⟩
  change proj 2 K (gI ha m) = _
  rw [hm]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]

theorem kaSp4I_struct {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (h5 : 5 ≤ Nat.card F) {a : F} (ha : a ≠ 0) :
    JI ha ≤ (fixI a ha).map (proj 2 F) ∧
    (∀ x ∈ (fixI a ha).map (proj 2 F), x ∈ normalizer (JI ha : Set (StatedProj (StatedSp 2 F)))) ∧
    ⁅JI ha, JI ha⁆ = JI ha ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup (StatedProj (StatedSp 2 F)), M ≤ JI ha →
      IsPGroup p ↥M → (∀ l ∈ JI ha, l ∈ normalizer (M : Set (StatedProj (StatedSp 2 F)))) →
        ∀ m ∈ M, ∀ l ∈ JI ha, m * l = l * m) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have h4 : 4 ≤ Nat.card F := by omega
  have hsimple : IsSimpleGroup ↥(JI ha) := isSimpleGroup_JI ha h4
  have hperf : ⁅JI ha, JI ha⁆ = JI ha := by
    have hP := (isQuasisimple_SL2' (K := F) h4).1
    have hJ : JI ha = (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map
        ((proj 2 F).comp (gI ha)) := by
      rw [JI, ← MonoidHom.range_comp, MonoidHom.range_eq_map]
    rw [hJ, ← Subgroup.map_commutator, ← _root_.commutator_def]
    rw [Group.isPerfect_def.mp hP]
  refine ⟨?_, ?_, hperf, ?_⟩
  · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨gI ha k, gI_mem_fixI ha k, rfl⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · exact fun hl => conj_mem_JI ha h2 hx hl
    · intro hl
      have hx' : x⁻¹ ∈ (fixI a ha).map (proj 2 F) := inv_mem hx
      have := conj_mem_JI ha h2 hx' hl
      simpa [mul_assoc] using this
  · intro p hp hp2 M hML hMp hMn m hm l hl
    have : Fact p.Prime := ⟨hp⟩
    have hN : (M.subgroupOf (JI ha)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hML).2 fun l hl => hMn l hl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (JI ha)) with hbot | htop
    · have : m = 1 := by
        have h1 : (⟨m, hML hm⟩ : ↥(JI ha)) ∈ M.subgroupOf (JI ha) := hm
        rw [hbot, Subgroup.mem_bot] at h1
        exact congrArg Subtype.val h1
      rw [this, one_mul, mul_one]
    · exfalso
      have hJM : JI ha ≤ M := Subgroup.subgroupOf_eq_top.1 htop
      have hJp : IsPGroup p ↥(JI ha) := hMp.to_le hJM
      have hnil : Group.IsNilpotent ↥(JI ha) := hJp.isNilpotent
      have hsol : Group.IsSolvable ↥(JI ha) := inferInstance
      have hnt : Nontrivial ↥(JI ha) := hsimple.toNontrivial
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(JI ha)
      have hc : commutator ↥(JI ha) = ⊤ := by
        have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥(JI ha)))
          (H₂ := (⊤ : Subgroup ↥(JI ha))) (f := (JI ha).subtype)
        have h2' : (⊤ : Subgroup ↥(JI ha)).map (JI ha).subtype = JI ha := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [h2', hperf] at h1
        rw [_root_.commutator_def]
        exact Subgroup.map_injective (JI ha).subtype_injective (h1.trans h2'.symm)
      rw [hc] at hlt
      exact lt_irrefl _ hlt

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
