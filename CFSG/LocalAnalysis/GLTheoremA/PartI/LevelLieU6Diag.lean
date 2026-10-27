module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Big
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem exists_diag6 (B : primeFormUnitary hF4 (idGram F4 6)) (hB3 : B ^ 3 = 1) :
    ∃ P : primeFormUnitary hF4 (idGram F4 6), ∃ d : Fin 6 → F4,
      (((P⁻¹ * B * P : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := by
  have hcomm : ∀ x ∈ Subgroup.zpowers B, ∀ y ∈ Subgroup.zpowers B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.refl B).zpow_zpow k l).eq
  have hpow : ∀ x ∈ Subgroup.zpowers B, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h3 : B ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hB3
    rw [← zpow_natCast, Nat.cast_ofNat, ← zpow_mul, mul_comm, zpow_mul, h3, one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m hF4
    F4_omega_primitive (by norm_num) (Subgroup.zpowers B) hcomm hpow
  exact ⟨P, _, (hP B (Subgroup.mem_zpowers B)).diagonal_diag.symm⟩

theorem map_CenD_conj (Q : primeFormUnitary hF4 (idGram F4 6)) (B : GL (Fin 6) F4) :
    (CenD B).map (conjM6 Q).toMonoidHom = CenD ((Q : GL (Fin 6) F4) * B * (Q : GL (Fin 6) F4)⁻¹) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_CenD, mem_CenD]
  have hz : (((conjM6 Q).symm y : M6) : GL (Fin 6) F4) =
      (Q : GL (Fin 6) F4)⁻¹ * y * (Q : GL (Fin 6) F4) := by
    have h := congrArg Subtype.val ((conjM6 Q).apply_symm_apply y)
    rw [conjM6_apply] at h
    calc (((conjM6 Q).symm y : M6) : GL (Fin 6) F4)
        = (Q : GL (Fin 6) F4)⁻¹ * ((Q : GL (Fin 6) F4) * (((conjM6 Q).symm y : M6) : GL (Fin 6) F4) *
            (Q : GL (Fin 6) F4)⁻¹) * (Q : GL (Fin 6) F4) := by group
      _ = (Q : GL (Fin 6) F4)⁻¹ * y * (Q : GL (Fin 6) F4) := by rw [h]
  rw [hz]
  constructor
  · intro h
    calc (y : GL (Fin 6) F4) * ((Q : GL (Fin 6) F4) * B * (Q : GL (Fin 6) F4)⁻¹)
        = (Q : GL (Fin 6) F4) * (((Q : GL (Fin 6) F4)⁻¹ * y * (Q : GL (Fin 6) F4)) * B) *
            (Q : GL (Fin 6) F4)⁻¹ := by group
      _ = (Q : GL (Fin 6) F4) * (B * ((Q : GL (Fin 6) F4)⁻¹ * y * (Q : GL (Fin 6) F4))) *
            (Q : GL (Fin 6) F4)⁻¹ := by rw [h]
      _ = ((Q : GL (Fin 6) F4) * B * (Q : GL (Fin 6) F4)⁻¹) * y := by group
  · intro h
    calc ((Q : GL (Fin 6) F4)⁻¹ * y * (Q : GL (Fin 6) F4)) * B
        = (Q : GL (Fin 6) F4)⁻¹ * (y * ((Q : GL (Fin 6) F4) * B * (Q : GL (Fin 6) F4)⁻¹)) *
            (Q : GL (Fin 6) F4) := by group
      _ = (Q : GL (Fin 6) F4)⁻¹ * (((Q : GL (Fin 6) F4) * B * (Q : GL (Fin 6) F4)⁻¹) * y) *
            (Q : GL (Fin 6) F4) := by rw [h]
      _ = B * ((Q : GL (Fin 6) F4)⁻¹ * y * (Q : GL (Fin 6) F4)) := by group

theorem card_blk_add_le (d : Fin 6 → F4) {c c' : F4} (h : c ≠ c') :
    Fintype.card (Blk d c) + Fintype.card (Blk d c') ≤ 6 := by
  have hinj : Function.Injective
      (Sum.elim (fun i : Blk d c => i.1) (fun i : Blk d c' => i.1)) := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · exact absurd (a.2.symm.trans ((congrArg d hab).trans b.2)) h
    · exact absurd (b.2.symm.trans ((congrArg d hab.symm).trans a.2)) h
    · exact congrArg Sum.inr (Subtype.ext hab)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_sum] using this

theorem card_blk_le_five (d : Fin 6 → F4) (hd : ¬ ∀ i, d i = d 0) (c : F4) :
    Fintype.card (Blk d c) ≤ 5 := by
  by_cases hc : ∀ i, d i = c
  · exact absurd (fun i => (hc i).trans (hc 0).symm) hd
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hpos : 0 < Fintype.card (Blk d (d i)) := Fintype.card_pos_iff.2 ⟨⟨i, rfl⟩⟩
    have := card_blk_add_le d (c := c) (c' := d i) (fun h => hi h.symm)
    omega

theorem level_of_cube_one (B : primeFormUnitary hF4 (idGram F4 6)) (hB3 : B ^ 3 = 1)
    (hns : ¬ ∃ c : F4ˣ, (B : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD (B : GL (Fin 6) F4)) J) :
    kLevel 3 (PSimple 3 J) ≤ 2 := by
  obtain ⟨P, d, hd⟩ := exists_diag6 B hB3
  set D : GL (Fin 6) F4 :=
    ((P⁻¹ * B * P : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) with hDdef
  have hDeq : D = (P : GL (Fin 6) F4)⁻¹ * (B : GL (Fin 6) F4) * (P : GL (Fin 6) F4) := rfl
  have hmap := glaPComponent_map_mulEquiv Nat.prime_three (conjM6 P⁻¹) hJ
  rw [map_CenD_conj] at hmap
  have hCen : ((P⁻¹ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) *
      (B : GL (Fin 6) F4) * ((P⁻¹ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)⁻¹ = D := by
    rw [hDeq]
    simp
  rw [hCen] at hmap
  obtain ⟨e⟩ := pSimple_map_equiv 3 (conjM6 P⁻¹) J
  rw [← kLevel_congr 3 e]
  have hperf := glaPComponent_perfect hmap
  have hDd : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hd
  have hnc : ¬ ∀ i, d i = d 0 := by
    intro hconst
    apply hns
    have hd0 : d 0 ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun (D.val_inv) 0) 0
      rw [hDd, Matrix.diagonal_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨Units.mk0 (d 0) hd0, ?_⟩
    have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) hd0) := by
      apply Units.ext
      rw [hDd, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hconst i]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hB : (B : GL (Fin 6) F4) = (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ := by
      rw [hDeq]
      group
    rw [hB, hDs, (commute_scalar (Units.mk0 (d 0) hd0) (P : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  by_cases hbig : ∃ c : F4, 4 ≤ Fintype.card (Blk d c)
  · obtain ⟨c, hc4⟩ := hbig
    have hc5 := card_blk_le_five d hnc c
    refine level_of_big d c hDd hc4 hc5 (fun c' hc' => ?_) hmap
    have := card_blk_add_le d (c := c) (c' := c') (Ne.symm hc')
    omega
  · push Not at hbig
    exfalso
    exact glaPComponent_ne_bot' hmap
      (eq_bot_of_perfect_of_small hDd (fun c => by have := hbig c; omega) hmap.1 hperf)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
