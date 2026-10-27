module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LBase

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

theorem thompson_B_of_fact14 {fr : Frame G} (h : fr.Fact14) :
    thompsonSubgroup fr.B = closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} := by
  obtain ⟨-, -, ⟨-, -, -, -, -, -, h7, -⟩, -⟩ := h
  exact h7

theorem G23LCtx.cen_B (X : G23LCtx m) :
    cen (frameOf m).B = closure {(frameOf m).b₁ * (frameOf m).b₂, (frameOf m).z} :=
  X.f5.cen_B

theorem G23LCtx.card_B (X : G23LCtx m) : Nat.card (frameOf m).B = 32 :=
  X.f5.card_B

theorem G23LCtx.centIn_cen_B (X : G23LCtx m) :
    centIn m.L (cen (frameOf m).B) = (frameOf m).B := by
  have hz : (frameOf m).z ∈ cen (frameOf m).B := by
    rw [X.cen_B]
    exact Subgroup.subset_closure (by simp)
  rw [centIn_eq_centIn_centEl hz, X.centEl_z]
  exact X.f1.centIn_H_cen_B

theorem G23LCtx.normIn_B_eq_cen (X : G23LCtx m) :
    normIn m.L (frameOf m).B = normIn m.L (cen (frameOf m).B) := by
  exact le_antisymm normIn_le_normIn_cen (normIn_cen_le X.centIn_cen_B)

theorem G23LCtx.card_normIn_cen_B_le (X : G23LCtx m) :
    Nat.card (normIn m.L (cen (frameOf m).B)) ≤ 192 := by
  have hN : normIn m.L (cen (frameOf m).B) ≤ normalizer (cen (frameOf m).B : Set G) :=
    inf_le_right
  have hAut := card_mulAut_of_isE2 X.f5.cen_B_isE
  have hle := card_le_mulAut_mul_centIn hN (by rw [hAut]; norm_num)
  rw [hAut] at hle
  have hcent : centIn (normIn m.L (cen (frameOf m).B)) (cen (frameOf m).B) ≤ (frameOf m).B := by
    intro x hx
    rw [← X.centIn_cen_B]
    exact ⟨hx.1.1, hx.2⟩
  have hc32 : Nat.card (centIn (normIn m.L (cen (frameOf m).B)) (cen (frameOf m).B)) ≤ 32 := by
    calc Nat.card (centIn (normIn m.L (cen (frameOf m).B)) (cen (frameOf m).B))
        ≤ Nat.card ((frameOf m).B) := Subgroup.card_le_of_le hcent
      _ = 32 := X.card_B
  calc Nat.card (normIn m.L (cen (frameOf m).B))
      ≤ 6 * Nat.card (centIn (normIn m.L (cen (frameOf m).B)) (cen (frameOf m).B)) := hle
    _ ≤ 6 * 32 := Nat.mul_le_mul_left 6 hc32
    _ = 192 := by norm_num

theorem G23LCtx.card_normIn_T5_B (X : G23LCtx m) :
    Nat.card (normIn (g23T5 m) (frameOf m).B) = 192 :=
  X.f5.card_normIn_B

theorem G23LCtx.normIn_B (X : G23LCtx m) :
    normIn m.L (frameOf m).B = normIn (g23T5 m) (frameOf m).B := by
  have hle : normIn (g23T5 m) (frameOf m).B ≤ normIn m.L (frameOf m).B := by
    intro x hx
    exact ⟨g23T5_le m hx.1, hx.2⟩
  have hcard : Nat.card (normIn m.L (frameOf m).B) ≤
      Nat.card (normIn (g23T5 m) (frameOf m).B) := by
    rw [X.normIn_B_eq_cen, X.card_normIn_T5_B]
    exact X.card_normIn_cen_B_le
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem G23LCtx.normIn_B_le_F (X : G23LCtx m) :
    normIn m.L (frameOf m).B ≤ normIn m.L (frameOf m).F := by
  rw [X.normIn_B, X.normIn_F]
  exact inf_le_left

theorem G23LCtx.B_S3 (X : G23LCtx m) :
    SecProp (normIn m.L (frameOf m).B) (frameOf m).B
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
  rw [X.normIn_B]
  exact X.f5.B_S3

theorem G23LCtx.B_sylow (X : G23LCtx m)
    (hJ : thompsonSubgroup (frameOf m).B =
      closure {(frameOf m).b₁, (frameOf m).a₁ * (frameOf m).a₂ * (frameOf m).h₀}) :
    ∀ T : Subgroup G, IsSylowIn 3 (normIn m.L (frameOf m).B) T →
      ActsRegularly T (cen (frameOf m).B) ⊥ ∧
        ActsRegularly T (thompsonSubgroup (frameOf m).B) (cen (frameOf m).B) := by
  rw [X.normIn_B, hJ]
  exact X.f5.B_sylow

theorem G23LCtx.fact18_3 (X : G23LCtx m) (h14 : (frameOf m).Fact14) :
    normIn m.L (frameOf m).B = normIn m.L (cen (frameOf m).B) ∧
      normIn m.L (frameOf m).B ≤ normIn m.L (frameOf m).F ∧
      SecProp (normIn m.L (frameOf m).B) (frameOf m).B
        (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
      (∀ T : Subgroup G, IsSylowIn 3 (normIn m.L (frameOf m).B) T →
        ActsRegularly T (cen (frameOf m).B) ⊥ ∧
          ActsRegularly T (thompsonSubgroup (frameOf m).B) (cen (frameOf m).B)) ∧
      centIn m.L (cen (frameOf m).B) = (frameOf m).B :=
  ⟨X.normIn_B_eq_cen, X.normIn_B_le_F, X.B_S3, X.B_sylow (thompson_B_of_fact14 h14),
    X.centIn_cen_B⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
