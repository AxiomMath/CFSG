module

public import CFSG.Quasithin.H13.L32ASk3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL24
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AStatements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Hyp147

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem setting147_hz_F4 (h : Hyp147 G T L V) (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4)
    (hMod : StmtL32NModule_F4) : Setting147 G T L V (L32A.hz T V) := by
  have hT := h.isTSub_V1_F4 hMod
  obtain ⟨-, hV1c, hTN⟩ := hT
  have hV1 : Nat.card (fsuV1 T V) = 2 := by rw [hV1c, pow_one]
  have hHN : L32A.hz T V = Subgroup.normalizer (fsuV1 T V : Set G) :=
    (L32A.normalizer_eq_centralizer_of_card_two hV1).symm
  refine ⟨h, ⟨⟨?_, ?_⟩, hHN.le, ?_⟩⟩
  · rw [hHN]
    exact sup_le ((oTwoUpper_le _).trans inf_le_right) hTN
  · have hp : IsPGroup 2 (fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hV1)
    have hle : fsuV1 T V ≤ pCoreOf 2 (L32A.hz T V) :=
      le_pCoreOf_of_le_normalizer 2 (by rw [hHN]; exact Subgroup.le_normalizer) hHN.le hp
    intro hbot
    have h1 : fsuV1 T V = ⊥ := le_bot_iff.mp (hbot ▸ hle)
    rw [h1, Subgroup.card_bot] at hV1
    exact absurd hV1 (by norm_num)
  · rw [hHN]
    exact lemma12_8_3_four_F4 h12213 (h.hyp1281One_F4 h13322 hMod) (h.isTSub_V1_F4 hMod)

end Hyp147

theorem L32A.thm14_7_63_of_F4 (h12213 : Stmt12_2_13_F4)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (h40 : Thm14_7_40_F4) (h48 : Lemma14_7_48_F4)
    (h52 : Thm14_7_52_F4) (h53 : Thm14_7_53_F4) : Thm14_7_63_F4 := by
  intro G _ _ T L V h
  have S := h.setting147_hz_F4 h12213 h13322 hMod
  obtain ⟨K, hC, hKT, hUK⟩ := h48 G T L V _ S
  have hK : K ∈ cComp (L32A.hz T V) := by rw [hC]; rfl
  obtain ⟨-, -, huniq, hU, hA5U3⟩ := h52 G T L V _ S K hK
  have hA5 : IsAlt 5 (L32A.cStar K) := hA5U3.resolve_right (h53 G T L V _ S K hK)
  have hTH : T ≤ L32A.hz T V := by rw [hKT]; exact le_sup_right
  have hL1H : L32A.l1 T L V ≤ L32A.hz T V := le_sup_left.trans S.hz.1.1
  have hKH : K ≤ L32A.hz T V := by rw [hKT]; exact le_sup_left
  have hH : L32A.hz T V = K ⊔ (L32A.l1 T L V ⊔ T) := by
    refine le_antisymm ?_ (sup_le hKH (sup_le hL1H hTH))
    rw [hKT]
    exact sup_le_sup_left le_sup_right K
  obtain ⟨hS5, hL24⟩ := h40 G T L V _ S K hK hH 2 (by norm_num)
    (L32A.isLieChar2_two_of_isAlt_five hA5)
  have hTp : IsPGroup 2 T := h.fsu.sylow.1
  have hkz : L32A.kz T V = K := L32A.oTwoUpper_eq_of_cComp_eq hC hKT hTp
  rw [hU] at hL24 hUK
  rw [← hkz] at hL24 hUK hK
  refine ⟨⟨S.hz.1, S.hz.2.2, S.hz.2.1⟩, fun H hH' => huniq H ⟨h, ⟨hH'.1, hH'.2.2, hH'.2.1⟩⟩,
    by rw [hkz]; exact hKT, hK, hS5, ?_, ⟨L32A.u0 T V, fun u => L32A.mem_u0_iff_F4 h hMod, hL24⟩⟩
  have hV1U : fsuV1 T V ≤ L32A.u0 T V := L32A.fsuV1_le_u0_F4 h hMod
  have hUe := L32A.isElemAbelian_fsuU_of_F4 h hMod
  refine L32A.isIndecOnSection_of_isL24Section hL24 hV1U (centralizerMod_le_left _ _ _)
    ((oTwoUpper_le _).trans (L32A.hz_le_normalizer_u0_F4 h hMod)) (fun c hc k hk => ?_)
    (fun x hx y hy => F7.isElemAbelian_comm hUe hx hy) hUK
  have h1 := ((L32A.mem_u0_iff_F4 h hMod).mp hc).2 k hk
  exact h1

end CFSG.Quasithin.H13
