module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T1Data
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabDecode
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LChk1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LChk5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps4
public import Mathlib.GroupTheory.OrderOfElement
public import Std.Data.HashSet
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred2
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabRank
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameKit
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabHom
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.SylowConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjFacts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameLe
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LGroup
import Certificates.Kernel.G2Three.Sec1T1Glue
import Certificates.Data.Kernel.G2Three.Sec1T1
import Certificates.Kernel.G2Three.Sec1T1Rec
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.G2Three.Sec1Tab
import CFSG.Certificates.Kernel.Co1DceCover
import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef
import Certificates.Kernel.G2Three.Sec1T3Glue
import Certificates.Kernel.G2Three.Sec1T5Glue
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T5Facts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T1Facts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.AutBound
public import Certificates.Certificate442055
public import Certificates.Certificate442056
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.CountE

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure G23LCtx (m : G23Model G) where
  f1 : G23T1Facts m
  f5 : G23T5Facts m

theorem g23lctx_exists
    (m : G23Model G) : Nonempty (G23LCtx m) :=
  ⟨⟨Certificates.certificate442055 m, Certificates.certificate442056 m⟩⟩

variable {m : G23Model G}

private theorem gen5_mem_L (m : G23Model G) (s : ℕ) (hs : s < 7) : gen5 m s ∈ m.L := by
  interval_cases s
  · simpa [gen5, sGen_zero] using frame_a1_mem m
  · simpa [gen5, sGen_one] using frame_b1_mem m
  · simpa [gen5, sGen_two] using frame_a2_mem m
  · simpa [gen5, sGen_three] using frame_b2_mem m
  · simpa [gen5, sGen_four] using frame_h0_mem m
  · simpa [gen5] using (gen5_mem m).1
  · simpa [gen5] using (gen5_mem m).2

theorem g23H_sup_sigma (m : G23Model G) : g23H m ⊔ closure {(frameOf m).σ} = g23T1 m := by
  simp only [g23H, g23T1, SFrame.K₁, SFrame.K₂]
  rw [← Subgroup.closure_union, ← Subgroup.closure_union, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem g23H_le (m : G23Model G) : g23H m ≤ m.L := by
  simp only [g23H, SFrame.K₁, SFrame.K₂]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (Subgroup.closure_le _).mpr (by
      rintro x (rfl | rfl)
      exacts [frame_u1_mem m, frame_b1_mem m])
  · exact (Subgroup.closure_le _).mpr (by
      rintro x (rfl | rfl)
      exacts [frame_u2_mem m, frame_b2_mem m])
  · exact (Subgroup.closure_le _).mpr (by
      rintro x rfl
      exact frame_h0_mem m)

theorem g23T5_le (m : G23Model G) : g23T5 m ≤ m.L := by
  simp only [g23T5]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨s, hs, rfl⟩
  exact gen5_mem_L m s hs

theorem frame_S_le_T5 (m : G23Model G) : (frameOf m).S ≤ g23T5 m := by
  simp only [SFrame.S, g23T5]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl | rfl | rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, by norm_num, by simp [gen5, sGen_zero]⟩
  · exact Subgroup.subset_closure ⟨1, by norm_num, by simp [gen5, sGen_one]⟩
  · exact Subgroup.subset_closure ⟨2, by norm_num, by simp [gen5, sGen_two]⟩
  · exact Subgroup.subset_closure ⟨3, by norm_num, by simp [gen5, sGen_three]⟩
  · exact Subgroup.subset_closure ⟨4, by norm_num, by simp [gen5, sGen_four]⟩

theorem G23LCtx.z_mem_invols (X : G23LCtx m) : (frameOf m).z ∈ invols m.L :=
  ⟨frame_z_mem m, X.f1.z_order⟩

theorem G23LCtx.z_sq (X : G23LCtx m) : (frameOf m).z * (frameOf m).z = 1 := by
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [X.z_mem_invols.2])

theorem G23LCtx.z_ne_one (X : G23LCtx m) : (frameOf m).z ≠ 1 := by
  intro h
  have h2 := X.z_mem_invols.2
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem G23LCtx.card_H (X : G23LCtx m) : Nat.card (g23H m) = 576 := X.f1.card_H

theorem G23LCtx.centEl_z (X : G23LCtx m) : centEl m.L (frameOf m).z = g23H m := by
  have hle : g23H m ≤ centEl m.L (frameOf m).z := by
    rw [centEl]
    refine le_inf (g23H_le m) fun h hh => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (X.f1.H_cent_z h hh)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [m.card_cent (frameOf m).z X.z_mem_invols, X.card_H]

theorem G23LCtx.centIn_F (X : G23LCtx m) : centIn m.L (frameOf m).F = (frameOf m).F := by
  have hHF : centIn (g23H m) (frameOf m).F = (frameOf m).F := X.f1.centIn_H_F
  rw [centIn_eq_centIn_centEl (X := (frameOf m).F) (z := (frameOf m).z)
    (Subgroup.subset_closure (by simp)), X.centEl_z, hHF]

theorem G23LCtx.normIn_F (X : G23LCtx m) : normIn m.L (frameOf m).F = g23T5 m := by
  have hT5norm : g23T5 m ≤ Subgroup.normalizer ((frameOf m).F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((F_le_S (frameOf m).toSFrame).trans (frame_S_le_T5 m))).mp X.f5.F_normal
  have hle : g23T5 m ≤ normIn m.L (frameOf m).F := by
    rw [normIn]
    exact le_inf (g23T5_le m) hT5norm
  have hNnorm : normIn m.L (frameOf m).F ≤ Subgroup.normalizer ((frameOf m).F : Set G) := by
    rw [normIn]
    exact inf_le_right
  have hAut := card_mulAut_of_isE3 X.f5.F_isE
  have hbound := card_le_mulAut_mul_centIn hNnorm (by rw [hAut]; norm_num)
  have hcent_le : centIn (normIn m.L (frameOf m).F) (frameOf m).F ≤ centIn m.L (frameOf m).F := by
    intro x hx
    rw [centIn] at hx ⊢
    rw [normIn] at hx
    exact ⟨hx.1.1, hx.2⟩
  have hcardCent : Nat.card (centIn (normIn m.L (frameOf m).F) (frameOf m).F) ≤ 8 := by
    calc Nat.card (centIn (normIn m.L (frameOf m).F) (frameOf m).F)
        ≤ Nat.card (frameOf m).F := Subgroup.card_le_of_le (hcent_le.trans (le_of_eq X.centIn_F))
      _ = 8 := by rw [X.f5.F_isE.2]; norm_num
  have hcard : Nat.card (normIn m.L (frameOf m).F) ≤ Nat.card (g23T5 m) := by
    calc Nat.card (normIn m.L (frameOf m).F)
        ≤ 168 * Nat.card (centIn (normIn m.L (frameOf m).F) (frameOf m).F) := by
            rw [← hAut]
            exact hbound
      _ ≤ 168 * 8 := Nat.mul_le_mul_left 168 hcardCent
      _ = 1344 := by norm_num
      _ = Nat.card (g23T5 m) := X.f5.card_T5.symm
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
