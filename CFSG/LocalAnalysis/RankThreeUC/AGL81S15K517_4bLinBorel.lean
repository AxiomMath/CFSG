module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34SqAbs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem le_of_isHallSubgroup_of_quotient_isPGroup {G : Type} [Group G] [Finite G]
    (B : Subgroup G) [B.Normal] (hquot : IsPGroup 2 (G ⧸ B)) {H : Subgroup G}
    (hH : IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H) : H ≤ B := by
  classical
  let π : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) ≠ 2}
  have hpi : IsPiSubgroup π (H.map (QuotientGroup.mk' B)) :=
    CFSG.LocalCores.isPiSubgroup_map hH.p_in_pi_of_p_dvd_card (QuotientGroup.mk' B)
  have himg2 : IsPGroup 2 ↥(H.map (QuotientGroup.mk' B)) :=
    hquot.to_subgroup (H.map (QuotientGroup.mk' B))
  obtain ⟨k, hk⟩ := himg2.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ Nat.card ↥(H.map (QuotientGroup.mk' B)) := by
      rw [hk]
      exact dvd_pow_self 2 (Nat.pos_of_ne_zero hk0).ne'
    have hmem : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ π := hpi ⟨2, Nat.prime_two⟩ h2dvd
    exact hmem rfl
  have hbot : H.map (QuotientGroup.mk' B) = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, hk, hk0, pow_zero]
  have hle : H ≤ (QuotientGroup.mk' B).ker :=
    (Subgroup.map_eq_bot_iff (H := H) (f := QuotientGroup.mk' B)).mp hbot
  exact hle.trans (le_of_eq (QuotientGroup.ker_mk' B))

end CFSG.LocalAnalysis.RankThreeUC.S15

end
