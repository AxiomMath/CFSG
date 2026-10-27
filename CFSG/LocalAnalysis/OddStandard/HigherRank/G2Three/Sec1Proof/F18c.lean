module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18a

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

set_option quotPrecheck false in
local notation "D1" => (t1G ()).tab
set_option quotPrecheck false in
local notation "I1" => idx1 (t1G ()).tab
set_option quotPrecheck false in
local notation "D5" => (t5G ()).tab
local notation "I5" => idx5

theorem E_le_L (m : G23Model G) : (frameOf m).E ≤ m.L :=
  (E_le_S (frameOf m).toSFrame).trans (frame_S_le m)

theorem z_mem_E (m : G23Model G) : (frameOf m).z ∈ (frameOf m).E :=
  subset_closure (by simp)

theorem G23LCtx.card_E (X : G23LCtx m) : Nat.card (frameOf m).E = 8 := X.f1.card_E

theorem G23LCtx.elemAb_E (X : G23LCtx m) : IsElemAbelian 2 (frameOf m).E := X.f1.elemAb_E

theorem G23LCtx.centIn_E (X : G23LCtx m) : centIn m.L (frameOf m).E = (frameOf m).E := by
  rw [centIn_eq_centIn_centEl (X := (frameOf m).E) (z := (frameOf m).z) (z_mem_E m),
    X.centEl_z]
  exact X.f1.centIn_H_E

theorem G23LCtx.card_normIn_H_E (X : G23LCtx m) :
    Nat.card (normIn (g23H m) (frameOf m).E) = 192 := X.f1.card_normIn_H_E

theorem G23LCtx.fix_E (X : G23LCtx m) :
    ∀ e ∈ (frameOf m).E, e ∉ zpowers (frameOf m).z →
      ∃ k ∈ normIn (g23H m) (frameOf m).E, k * e ≠ e * k := X.f1.fix_E

theorem G23LCtx.nine_conj_E (X : G23LCtx m) :
    ∃ Ws : List (Subgroup G), Ws.Nodup ∧ Ws.length = 9 ∧
      ∀ W ∈ Ws, (∃ t ∈ g23T5 m, W = conjSub t (frameOf m).E) ∧ (frameOf m).z ∈ W :=
  X.f5.nine_conj_E

theorem G23LCtx.card_normIn_E_lt (X : G23LCtx m) :
    Nat.card (normIn m.L (frameOf m).E) < 3 * Nat.card (normIn (g23H m) (frameOf m).E) := by
  obtain ⟨Ws, hnodup, hlen, hWs⟩ := X.nine_conj_E
  have hconj : ∀ v ∈ invols m.L, ∃ l ∈ m.L, v = l * (frameOf m).z * l⁻¹ :=
    fun v hv => m.invol_conj (frameOf m).z X.z_mem_invols v hv
  have hWsL : ∀ W ∈ Ws, (∃ l ∈ m.L, W = conjSub l (frameOf m).E) ∧ (frameOf m).z ∈ W := by
    intro W hW
    obtain ⟨⟨t, htT5, hWt⟩, hzW⟩ := hWs W hW
    exact ⟨⟨t, g23T5_le m htT5, hWt⟩, hzW⟩
  have hcount := card_normIn_mul_le X.z_mem_invols hconj (E_le_L m) X.card_E X.elemAb_E
    Ws hnodup hWsL
  have h576 : Nat.card (centEl m.L (frameOf m).z) = 576 :=
    m.card_cent (frameOf m).z X.z_mem_invols
  have hinv : Nat.card (invols m.L) = 7371 := by
    have h := card_invols_mul X.z_mem_invols hconj
    rw [h576, m.card_L] at h
    rw [← show (7371 : ℕ) * 576 = 4245696 by norm_num] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hle : Nat.card (normIn m.L (frameOf m).E) ≤ 448 := by
    rw [hlen, hinv, m.card_L] at hcount
    omega
  rw [X.card_normIn_H_E]
  omega

theorem G23LCtx.normIn_E (X : G23LCtx m) :
    normIn m.L (frameOf m).E = normIn (g23H m) (frameOf m).E := by
  have h := normIn_eq_of_index_le_two (L := m.L) (E := (frameOf m).E) (z := (frameOf m).z)
    (z_mem_E m) X.z_mem_invols.2 (by rw [X.centEl_z]; exact X.card_normIn_E_lt)
    (by rw [X.centEl_z]; exact X.fix_E)
  rwa [X.centEl_z] at h

theorem G23LCtx.normIn_E_le_A (X : G23LCtx m) :
    normIn m.L (frameOf m).E ≤ normIn m.L (frameOf m).A := by
  rw [X.normIn_E, X.normIn_A]
  exact inf_le_left

theorem G23LCtx.E_S3 (X : G23LCtx m) :
    SecProp (normIn (g23H m) (frameOf m).E) (frameOf m).A
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := X.f1.E_S3

theorem G23LCtx.E_trans (X : G23LCtx m) :
    ∀ u ∈ (frameOf m).E, u ∉ (frameOf m).Z → ∀ v ∈ (frameOf m).E, v ∉ (frameOf m).Z →
      ∃ k ∈ normIn (g23H m) (frameOf m).E, k * u * k⁻¹ = v := X.f1.E_trans

theorem G23LCtx.E_sylow (X : G23LCtx m) :
    ∀ T : Subgroup G, IsSylowIn 3 (normIn (g23H m) (frameOf m).E) T →
      ActsRegularly T (frameOf m).E (frameOf m).Z ∧
        ActsRegularly T (frameOf m).A (frameOf m).E := X.f1.E_sylow

theorem G23LCtx.fact18_4 (X : G23LCtx m) :
    centIn m.L (frameOf m).E = (frameOf m).E ∧
      normIn m.L (frameOf m).E ≤ normIn m.L (frameOf m).A ∧
      SecProp (normIn m.L (frameOf m).E) (frameOf m).A
        (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
      (∀ u ∈ (frameOf m).E, u ∉ (frameOf m).Z → ∀ v ∈ (frameOf m).E, v ∉ (frameOf m).Z →
        ∃ k ∈ normIn m.L (frameOf m).E, k * u * k⁻¹ = v) ∧
      ∀ T : Subgroup G, IsSylowIn 3 (normIn m.L (frameOf m).E) T →
        ActsRegularly T (frameOf m).E (frameOf m).Z ∧
          ActsRegularly T (frameOf m).A (frameOf m).E := by
  have h := X.normIn_E
  have hle := X.normIn_E_le_A
  rw [h] at hle ⊢
  exact ⟨X.centIn_E, hle, X.E_S3, X.E_trans, X.E_sylow⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
