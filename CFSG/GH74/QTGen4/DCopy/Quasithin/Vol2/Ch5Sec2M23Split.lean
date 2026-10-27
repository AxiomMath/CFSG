module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Split
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Fus

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.A7Fano CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_isComplement_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ A : Subgroup ↥M2, ((pCoreOf 2 M2).subgroupOf M2).IsComplement' A := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', -, hsurj, hker, -, -, hU16, hU2', -, -, hπ'⟩ := exists_rho_of_setting_F4 hQ hyp hM23 hS
  obtain ⟨k, hkK, hk3, hfpf⟩ := exists_fpf_three_of_setting_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hkM2 : k ∈ M2 := hS.K_lt.le hkK
  have hct := cycleType_map_eq_three_of_mem_oTwoUpper_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hkK
    hk3 hkM2
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hk3' : orderOf (⟨k, hkM2⟩ : ↥M2) = 3 := by rw [← Subgroup.orderOf_coe]; exact hk3
  obtain ⟨hdisj, hcardN⟩ := card_normalizer_fpf_three hsurj hker hU2 hUM2 hk3'
    (by rw [hπ']; exact hct) hfpf
  set N := Subgroup.normalizer (Subgroup.zpowers (⟨k, hkM2⟩ : ↥M2) : Set ↥M2) with hN

  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 2 (n := 3)
    (by rw [hcardN]; norm_num)
  set P := P₀.map N.subtype with hP
  have hPN : P ≤ N := Subgroup.map_subtype_le P₀
  have hcardP : Nat.card P = 8 := by
    rw [hP, Subgroup.card_map_of_injective N.subtype_injective, hP₀]
    norm_num
  set Y := (pCoreOf 2 M2).subgroupOf M2 with hY
  have hYn : Y.Normal := hker ▸ π'.normal_ker
  have hcardY : Nat.card Y = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM2).toEquiv).trans hU16
  have hYP : Disjoint Y P :=
    disjoint_iff.mpr (eq_bot_iff.mpr ((inf_le_inf_left Y hPN).trans hdisj.le))

  have hcardW : Nat.card ↥(Y ⊔ P) = 128 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y P
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hYP, hcardY, hcardP]
  have hcardM2 : Nat.card M2 = 40320 := by
    have h1 := card_map_mul_card_inf hS.ker_eq (le_refl M2)
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hS.range_eq,
      CFSG.Quasithin.H13.card_alternatingGroup_seven, inf_of_le_right hUM2, hU16] at h1
    exact h1.symm
  have hW2 : IsPGroup 2 ↥(Y ⊔ P) := IsPGroup.of_card (n := 7) (by rw [hcardW]; norm_num)
  have hidx : ¬ 2 ∣ (Y ⊔ P).index := by
    have h := Subgroup.index_mul_card (Y ⊔ P)
    rw [hcardW, hcardM2] at h
    have h315 : (Y ⊔ P).index = 315 := by omega
    rw [h315]
    norm_num

  have hcU : ∀ a b : ↥(pCoreOf 2 M2), a * b = b * a := fun a b => by
    have e1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2' _)
    have ea : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2' _)
    have eb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2' _)
    calc a * b = (a * b)⁻¹ := e1.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ea, eb]
  have hYc : IsMulCommutative Y := ⟨⟨fun a b => by
    have h := congrArg Subtype.val (hcU ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
      ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hYp : IsPGroup 2 Y := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM2).symm
  obtain ⟨A, hA1, hA2⟩ := (gaschutz hYp (hW2.toSylow hidx)).mpr
    ⟨P, by rw [IsPGroup.toSylow_coe]; exact le_sup_right, disjoint_iff.mp hYP,
      by rw [IsPGroup.toSylow_coe]⟩
  refine ⟨A, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hA1) ?_⟩
  rw [← Subgroup.normal_mul, hA2, Subgroup.coe_top]

end CFSG.Quasithin.H13
