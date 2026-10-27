module

public import Mathlib
public import CFSG.GH74.KGroups.Generic3
public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.KGroups.Generic7
public import CFSG.GH74.KGroups.M11Tables
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.M11Tables
public import CFSG.GH74.KGroups.CoverM11Inputs
public meta import CFSG.GH74.KGroups.CoverM11Inputs
public import Certificates.Certificate5113
public import Certificates.Certificate5125
public import Certificates.Certificate5126

public section

namespace CFSG.GH74.KGroups.M11

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74 CFSG.GH74.Generic Subgroup

theorem fw_rels :
    fw ^ 3 = 1 ∧ fw * sR ^ 4 * fw⁻¹ = sR ^ 4 ∧ fw * sR ^ 2 * fw⁻¹ = sT * sR :=
  Certificates.certificate5113.1

theorem fg_rels :
    fg1 * sT * fg1⁻¹ = sR ^ 4 ∧ fg2 * sT * fg2⁻¹ = sT * sR ^ 2 :=
  Certificates.certificate5113.2.1

theorem fw_mem_check : Q.sift fw 0 = true :=
  Certificates.certificate5113.2.2.1

theorem fw_mem :
    fw ∈ Q.originalSubgroup := (mem_iff_sift Q Q_ok fw).2 fw_mem_check

theorem fg1_mem_check : Q.sift fg1 0 = true :=
  Certificates.certificate5113.2.2.2.1

theorem fg1_mem :
    fg1 ∈ Q.originalSubgroup := (mem_iff_sift Q Q_ok fg1).2 fg1_mem_check

theorem fg2_mem_check : Q.sift fg2 0 = true :=
  Certificates.certificate5113.2.2.2.2

theorem fg2_mem :
    fg2 ∈ Q.originalSubgroup := (mem_iff_sift Q Q_ok fg2).2 fg2_mem_check

theorem sR_mem :
    sR ∈ Q.originalSubgroup := by
  apply QS_le
  rw [QS_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem sT_mem :
    sT ∈ Q.originalSubgroup := by
  apply QS_le
  rw [QS_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem noTwoCover_M11
    (S : Type) [Group S] (h : NativeSporadic.IsSporadic S .M11) :
    NoTwoCover S := by
  intro K _ _ hK hZ2 ⟨e⟩
  by_contra hZ
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨C, _, _, -, -, -, hperfC, hcard, ⟨eC⟩⟩ := exists_double_cover hperf hZ2 hZ hJ
  obtain ⟨eP⟩ := equiv_of_sporadic h
  let ε : C ⧸ Subgroup.center C ≃* Q.originalSubgroup := (eC.trans e).trans eP
  have hrels := sd16_rels
  have hfw := fw_rels
  have hfg := fg_rels
  let π : C →* C ⧸ Subgroup.center C := QuotientGroup.mk' (Subgroup.center C)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = Subgroup.center C := QuotientGroup.ker_mk' _
  have hZc : ∀ z ∈ π.ker, ∀ g : C, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 (hπker ▸ hz) g
  have hZ2' : ∀ z ∈ π.ker, z ^ 2 = 1 := fun z hz =>
    sq_eq_one_of_card_two (Subgroup.center C) hcard z (hπker ▸ hz)
  let X : C ⧸ Subgroup.center C := ε.symm ⟨sR, sR_mem⟩
  let Y : C ⧸ Subgroup.center C := ε.symm ⟨sT, sT_mem⟩
  let W : C ⧸ Subgroup.center C := ε.symm ⟨fw, fw_mem⟩
  let G1 : C ⧸ Subgroup.center C := ε.symm ⟨fg1, fg1_mem⟩
  let G2 : C ⧸ Subgroup.center C := ε.symm ⟨fg2, fg2_mem⟩
  have hεX : (ε X : Equiv.Perm (Fin 11)) = sR := by simp [X]
  have hεY : (ε Y : Equiv.Perm (Fin 11)) = sT := by simp [Y]
  have hεW : (ε W : Equiv.Perm (Fin 11)) = fw := by simp [W]
  have hεG1 : (ε G1 : Equiv.Perm (Fin 11)) = fg1 := by simp [G1]
  have hεG2 : (ε G2 : Equiv.Perm (Fin 11)) = fg2 := by simp [G2]
  have key : ∀ a b : C ⧸ Subgroup.center C, (ε a : Equiv.Perm (Fin 11)) = (ε b : Equiv.Perm (Fin 11)) →
      a = b := fun a b hab => ε.injective (Subtype.ext hab)
  have hy2 : Y ^ 2 = 1 := key _ _ (by simpa [hεY] using hrels.2.1)
  have hyx : Y * X * Y⁻¹ = X ^ 3 := key _ _ (by simpa [hεY, hεX] using hrels.2.2.1)
  have hw3 : W ^ 3 = 1 := key _ _ (by simpa [hεW] using hfw.1)
  have hwx4 : W * X ^ 4 * W⁻¹ = X ^ 4 := key _ _ (by simpa [hεW, hεX] using hfw.2.1)
  have hwx2 : W * X ^ 2 * W⁻¹ = Y * X := key _ _ (by simpa [hεW, hεX, hεY] using hfw.2.2)
  have hg1 : G1 * Y * G1⁻¹ = X ^ 4 := key _ _ (by simpa [hεG1, hεY, hεX] using hfg.1)
  have hg2 : G2 * Y * G2⁻¹ = Y * X ^ 2 := key _ _ (by simpa [hεG2, hεY, hεX] using hfg.2)
  have hS : 16 ≤ Nat.card (Subgroup.closure ({X, Y} : Set (C ⧸ Subgroup.center C))) := by
    have h1 := card_closure_pair_equiv Q.originalSubgroup ε X Y
    rw [hεX, hεY, ← QS_closure, card_S] at h1
    omega
  have hJcard : Nat.card (C ⧸ Subgroup.center C) = 16 * 495 := by
    rw [Nat.card_congr ε.toEquiv, card_group Q Q_ok, Q_valid.2]
  have hbot := ker_eq_bot_of_sd16 π hπ hperfC hZc hZ2' X Y W G1 G2 hy2 hyx hw3 hwx4 hwx2 hg1 hg2
    hS 495 hJcard (by decide)
  rw [hπker] at hbot
  have h1 : Nat.card (Subgroup.center C) = 1 := by rw [hbot]; simp
  omega

end CFSG.GH74.KGroups.M11
