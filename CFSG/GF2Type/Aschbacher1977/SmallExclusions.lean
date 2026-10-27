module

public import CFSG.LargeExtraspecial.S3Basic
import CFSG.GH74.Generic.S1.KL5LyRee
import CFSG.GH74.Generic.S45.LSporMathA
import CFSG.GH74.KGroups.L34Tables
import CFSG.GH74.KGroups.Sz8Tables
import CFSG.LargeExtraspecial.AS35WLocal
import CFSG.LargeExtraspecial.AS62W6
import CFSG.LargeExtraspecial.S14C12TOrd
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Centralizer
import CFSG.Sporadic.SmallOddCore.McLLocal
public import CFSG.GH74.KGroups.L34
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.PairMcLCertBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint CFSG.LargeExtraspecial Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_M_eq_thirtyTwo_mul (S : Setting G) (hw : S.width = 2) :
    Nat.card S.M = 32 * Nat.card S.Mbar := by
  rw [S14.card_M_eq_card_Q_mul S, S.card_Q_eq, hw]
  norm_num

theorem false_of_not_dvd_card (S : Setting G) (hw : S.width = 2) (h : ¬ 32 ∣ Nat.card G) :
    False := by
  apply h
  have h1 := Subgroup.card_subgroup_dvd_card S.QG
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw] at h1
  norm_num at h1
  exact h1

theorem false_of_card_M_not_dvd (S : Setting G) (hw : S.width = 2)
    (h : ¬ Nat.card S.M ∣ 11520) : False := by
  apply h
  have h1 := S.card_M_dvd_of_width_two hw
  norm_num at h1
  exact h1

theorem false_of_card_M_eq_64 (S : Setting G) (hw : S.width = 2) (h : Nat.card S.M = 64) :
    False := by
  have h32 := card_M_eq_thirtyTwo_mul S hw
  have hbar : Nat.card S.Mbar = 2 := by omega
  have htop : IsPGroup 2 (⊤ : Subgroup S.Mbar) :=
    IsPGroup.of_card (n := 1) (by rw [Subgroup.card_top, hbar, pow_one])
  have hle : (⊤ : Subgroup S.Mbar) ≤ CFSG.pCore 2 S.Mbar :=
    le_sSup (s := {K : Subgroup S.Mbar | K.Normal ∧ IsPGroup 2 K}) ⟨inferInstance, htop⟩
  rw [S.pCore_Mbar_eq_bot, le_bot_iff] at hle
  have h2 : Nat.card (⊤ : Subgroup S.Mbar) = 2 := by rw [Subgroup.card_top, hbar]
  rw [hle, Subgroup.card_bot] at h2
  omega

theorem false_of_card_M_eq_384 (S : Setting G) (hw : S.width = 2) (h : Nat.card S.M = 384) :
    False := by
  have h32 := card_M_eq_thirtyTwo_mul S hw
  have hbar : Nat.card S.Mbar = 12 := by omega
  exact AS62.pCore_ne_bot_of_card_eq_three_mul (n := 2) (by norm_num [hbar]) le_rfl
    S.pCore_Mbar_eq_bot

theorem false_of_two_lt_card_inf_centralizer (S : Setting G)
    (h : ∀ P : Sylow 2 G, 2 < Nat.card ↥((P : Subgroup G) ⊓ centralizer (P : Set G))) :
    False := by
  obtain ⟨P, hQP, -⟩ := S.exists_sylow_le_M
  have hle : ((P : Subgroup G) ⊓ centralizer (P : Set G)) ≤ zpowers S.z := by
    have h' : ((P : Subgroup G) ⊓ centralizer (P : Set G)) ≤ centralizer (S.QG : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le hQP)
    rwa [S.centralizer_QG_eq] at h'
  have hcard : Nat.card ↥((P : Subgroup G) ⊓ centralizer (P : Set G)) ≤ 2 := by
    calc Nat.card ↥((P : Subgroup G) ⊓ centralizer (P : Set G))
        ≤ Nat.card ↥(zpowers S.z) := Subgroup.card_le_of_le hle
      _ = orderOf S.z := Nat.card_zpowers S.z
      _ = 2 := S.orderOf_z
  have := h P
  omega

theorem not_lieModel_PSL_2_2_3 (S : Setting G) (hw : S.width = 2) (h : LieModel G .PSL 2 2 3) :
    False := by
  apply false_of_not_dvd_card S hw
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
  decide

theorem not_lieModel_PSL_2_2_4 (S : Setting G) (hw : S.width = 2) (h : LieModel G .PSL 2 2 4) :
    False := by
  apply false_of_not_dvd_card S hw
  rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
  decide

theorem not_isSporadic_J1 (S : Setting G) (hw : S.width = 2)
    (h : NativeSporadic.IsSporadic G .J1) : False := by
  apply false_of_not_dvd_card S hw
  obtain ⟨e⟩ := h
  have hcard : Nat.card G = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  rw [hcard]
  norm_num

theorem not_lieModel_twistedB2_0_2_3
    (S : Setting G) (h : LieModel G .twistedB2 0 2 3) : False := by
  apply false_of_two_lt_card_inf_centralizer S
  intro P
  have h8 : Nat.card ↥((P : Subgroup G) ⊓ centralizer (P : Set G)) = 8 :=
    CFSG.GH74.KGroups.Sz8.bender_card h (P : Subgroup G) P.isPGroup' P.not_dvd_index
  rw [h8]
  norm_num

theorem not_lieModel_PSL_3_2_2
    (S : Setting G) (hw : S.width = 2)
    (h : LieModel G .PSL 3 2 2) : False := by
  apply false_of_card_M_eq_64 S hw
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel h
  have hres := (CFSG.GH74.KGroups.L34.ki3_model (⊤ : Subgroup G) le_top
    (Subgroup.topEquiv.trans e) S.z trivial S.orderOf_z).2.2
  simpa using hres

theorem not_isSporadic_M22
    (S : Setting G) (hw : S.width = 2)
    (h : NativeSporadic.IsSporadic G .M22) : False := by
  apply false_of_card_M_eq_384 S hw
  obtain ⟨e⟩ := h
  have hz2 : orderOf (e S.z) = 2 := by rw [MulEquiv.orderOf_eq, S.orderOf_z]
  have hc := CFSG.EvenSporadicStandard.M22Std.card_centralizer_involution (t := e S.z) hz2
  change Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) = 384
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv e S.z]
  exact hc

theorem not_isSporadic_M23
    (S : Setting G) (hw : S.width = 2)
    (h : NativeSporadic.IsSporadic G .M23) : False := by
  apply false_of_card_M_not_dvd S hw
  obtain ⟨e⟩ := h
  let u : ↥NativeSporadic.M23 := e S.z
  have hmem : (u : Equiv.Perm (Fin 23)) ∈ NativeSporadic.M23 := u.2
  have hord : orderOf (u : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe]
    show orderOf (e S.z) = 2
    rw [MulEquiv.orderOf_eq, S.orderOf_z]
  have hcard := CFSG.GH74.Generic.S45.LAlt.m23_class_card (u : Equiv.Perm (Fin 23)) hmem hord
  have hmain : Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) = 2688 := by
    rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn
      (H := NativeSporadic.M23) e S.z]
    exact hcard
  change ¬ Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) ∣ 11520
  rw [hmain]
  norm_num

theorem not_isSporadic_McL
    (S : Setting G) (hw : S.width = 2) (h : NativeSporadic.IsSporadic G .McL) : False := by
  apply false_of_card_M_not_dvd S hw
  obtain ⟨e⟩ := h
  let e' : G ≃* ↥CFSG.Sporadic.Schreier.mclP := e.trans CFSG.Sporadic.Schreier.mclPermEquiv
  have hz2 : orderOf ((e' S.z) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, S.orderOf_z]
  obtain ⟨-, -, -, hcard, hcover⟩ := CFSG.Sporadic.SmallOddCore.mclT0_facts
  obtain ⟨g, hg, hgτ⟩ := hcover ((e' S.z) : Equiv.Perm (Fin 275)) (e' S.z).2 hz2
  have hmem : ((e' S.z) : Equiv.Perm (Fin 275)) ∈
      CFSG.Sporadic.Schreier.conjClass CFSG.Sporadic.Schreier.mclP
        CFSG.Sporadic.SmallOddCore.mclT0 := ⟨g, hg, hgτ⟩
  have hmain : Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) = 40320 := by
    rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn
      (H := CFSG.Sporadic.Schreier.mclP) e' S.z,
      CFSG.GH74.GLS.IVK.GHInv.card_centralizerIn_eq_of_mem_conjClass
        CFSG.Sporadic.Schreier.mclP hmem]
    exact hcard
  change ¬ Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) ∣ 11520
  rw [hmain]
  norm_num

theorem not_isSporadic_Ly
    (S : Setting G) (hw : S.width = 2) (h : NativeSporadic.IsSporadic G .Ly) : False := by
  apply false_of_card_M_not_dvd S hw
  have hcard := CFSG.GH74.Generic.S1.kl5_card_centralizer_ly h S.orderOf_z
  change ¬ Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) ∣ 11520
  rw [hcard]
  norm_num

end CFSG.GF2Type.Aschbacher1977
