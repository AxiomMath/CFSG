module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.H13.U3S1349A

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setting

variable {T L V H : Subgroup G}

theorem normalizer_T_le_F4 (h331 : Stmt3_3_1_F4) (h1332 : Stmt13_3_2_F4) (S : Setting147 G T L V H) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hL13 := h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
  exact (h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).1 _ L
    hL13.2.1.2.2.1 hL13.2.1.1 S.hyp.fsu.maximal Subgroup.le_normalizer S.hyp.fsu.quasisimple

theorem le_M_of_index_three_F4 (h331 : Stmt3_3_1_F4) (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) {Y₁ : Subgroup G}
    (hY₁H : Y₁ ≤ H) (hY₁o : oTwoUpper Y₁ = Y₁) (hTY₁ : T ≤ Subgroup.normalizer (Y₁ : Set G))
    (h3 : (pCoreOf 2 Y₁).relIndex Y₁ = 3)
    (hperm : (Y₁ : Set G) * (l1 T L V : Set G) = (l1 T L V : Set G) * (Y₁ : Set G)) :
    Y₁ ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  have hO₂T : pCoreOf 2 Y₁ ≤ T := by
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y₁).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 Y₁)).trans (pCoreOf_le_of_le S.hyp le_sup_right)
    exact sup_le (le_normalizer_pCoreOf 2 Y₁) (F7.le_normalizer_pCoreOf_of_le_normalizer hTY₁)
  have hinf : (Y₁ ⊓ T).relIndex Y₁ = 3 := by
    have hle : pCoreOf 2 Y₁ ≤ Y₁ ⊓ T := le_inf (pCoreOf_le 2 Y₁) hO₂T
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
    rw [h3] at hmul
    have hd : (Y₁ ⊓ T).relIndex Y₁ ∣ 3 := ⟨_, by rw [mul_comm]; exact hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h

      have hY₁2 : IsPGroup 2 Y₁ := S.hyp.fsu.sylow.1.to_le (h.trans inf_le_right)
      have hY₁O : Y₁ ≤ pCoreOf 2 Y₁ :=
        le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hY₁2
      rw [Subgroup.relIndex_eq_one.mpr hY₁O] at h3
      exact absurd h3 (by norm_num)
    · exact h
  have hT3 : T.relIndex (Y₁ ⊔ T) = 3 := by rw [U3.relIndex_sup_eq hTY₁, hinf]
  by_cases hN : Y₁ ⊔ T ≤ Subgroup.normalizer (T : Set G)
  · exact (le_sup_left.trans hN).trans (normalizer_T_le_F4 h331 h1332 S)
  · have hsyl : IsSylowTwoOf T (Y₁ ⊔ T) :=
      isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow le_sup_right
    have hS3 := U3.quot_S3_of_index_three hsyl hT3 hN
    have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
    obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
    have hY₁G : Y₁ ≤ A6.g1 T V := hY₁H.trans S.hz.2.1
    exact (hThm G T L V S.hyp Y₁ V₂ hV2 hY₁o hY₁G hTY₁ hS3).2.1 hperm

end Setting

end CFSG.Quasithin.H13.L32A
