module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeClasses

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem nonempty_mulEquiv_of_card {A : Type*} [Group A] [Finite A] (P : Sylow 2 A)
    {K : Subgroup A} {k : ℕ} (hK : Nat.card K = 2 ^ k) (hidx : Odd K.index) :
    Nonempty (K ≃* (P : Subgroup A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 K := IsPGroup.of_card hK
  have h2 : ¬ 2 ∣ K.index := fun h => (Nat.not_even_iff_odd.2 hidx) (even_iff_two_dvd.2 h)
  set S := hP.toSylow h2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S P
  have hS : (S : Subgroup A) = K := IsPGroup.toSylow_coe hP h2
  have h1 : (P : Subgroup A) = MulAut.conj g • (S : Subgroup A) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  exact ⟨(MulEquiv.subgroupCongr hS.symm).trans
    ((Subgroup.equivSMul (MulAut.conj g) (S : Subgroup A)).trans
      (MulEquiv.subgroupCongr h1.symm))⟩

theorem nonempty_mulEquiv_sylowT_plus {S₀ : Subgroup G}
    (j : S₀ →* Equiv.Perm (Fin 360)) (hj : Function.Injective j)
    (hjA : ∀ s, j s ∈ OmegaEight.autT) (hcard : Nat.card S₀ = 8192) :
    Nonempty (S₀ ≃* OmegaEight.sylowT) := by
  set j' : S₀ →* OmegaEight.autT := j.codRestrict OmegaEight.autT hjA
  have hj' : Function.Injective j' := fun x y h => hj (congrArg Subtype.val h)
  set K := j'.range
  have hK : Nat.card K = 2 ^ 13 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj').toEquiv, hcard]
    norm_num
  have hidx : Odd K.index := by
    have h := K.card_mul_index
    rw [hK, OmegaEight.card_autT] at h
    have : K.index = 127575 := by omega
    rw [this]
    decide
  obtain ⟨e⟩ := nonempty_mulEquiv_of_card OmegaEight.sylowA hK hidx
  exact ⟨((MonoidHom.ofInjective hj').trans e).trans
    ((MulEquiv.subgroupCongr OmegaEight.coe_sylowA).trans
      (Subgroup.subgroupOfEquivOfLe OmegaEight.sylowT_le_autT))⟩

theorem nonempty_mulEquiv_sylowT_minus {S₀ : Subgroup G}
    (j : S₀ →* Equiv.Perm (Fin 136)) (hj : Function.Injective j)
    (hjA : ∀ s, j s ∈ OmegaEightMinus.autT) (hcard : Nat.card S₀ = 8192) :
    Nonempty (S₀ ≃* OmegaEightMinus.sylowT) := by
  set j' : S₀ →* OmegaEightMinus.autT := j.codRestrict OmegaEightMinus.autT hjA
  have hj' : Function.Injective j' := fun x y h => hj (congrArg Subtype.val h)
  set K := j'.range
  have hK : Nat.card K = 2 ^ 13 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj').toEquiv, hcard]
    norm_num
  have hidx : Odd K.index := by
    have h := K.card_mul_index
    rw [hK, OmegaEightMinus.card_autT] at h
    have : K.index = 48195 := by omega
    rw [this]
    decide
  obtain ⟨e⟩ := nonempty_mulEquiv_of_card OmegaEightMinus.sylowA hK hidx
  exact ⟨((MonoidHom.ofInjective hj').trans e).trans
    ((MulEquiv.subgroupCongr OmegaEightMinus.coe_sylowA).trans
      (Subgroup.subgroupOfEquivOfLe OmegaEightMinus.sylowT_le_autT))⟩

end CFSG.EvenSmallLie.OmegaEight.SplitC
