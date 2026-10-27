module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4Kill
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87KindIdx

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.Assembly.LowTwoRank

@[expose] def MinIndexU33 : Prop :=
  ∀ (Y : Type) [Group Y], LieModel Y .PSU 3 3 1 → ∀ H : Subgroup Y, H ≠ ⊤ → 11 < H.index

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem lieModel_statedProj_three_three (hK : Nat.card K = (3 ^ 1) ^ 2) :
    LieModel (StatedProj (StatedSU 3 (3 ^ 1) K)) .PSU 3 3 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩, K, inferInstance, inferInstance,
    hK, ⟨MulEquiv.refl _⟩⟩

theorem not_kindFactor_statedProj_three_three (hMin : MinIndexU33) [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq3 : p ^ f = 3) (k : Kind) :
    ¬ KindFactor k (StatedProj (StatedSU 3 (p ^ f) K)) := by
  intro h
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hq3
  have hmin := hMin _ (lieModel_statedProj_three_three hK)
  have hs := isSimpleGroup_statedProj_three_odd (K := K) (p := 3) (f := 1) hK (by norm_num)
  have : Nontrivial (StatedProj (StatedSU 3 (3 ^ 1) K)) := IsSimpleGroup.toNontrivial
  have hinv := involved_qdSL_statedProj_three (K := K) (p := 3) (f := 1) hK
  cases k with
  | g2 => exact not_isL2_of_involved (by norm_num) hinv h
  | psp4 => exact not_isL2_of_involved (by norm_num) hinv h
  | l4 ε => exact not_isL2_of_involved (by norm_num) hinv h
  | m12 => exact h
  | mcl => exact not_kindFactorAll_mclly_of_index (Or.inl rfl) hmin (KindFactor.all h)
  | ly => exact not_kindFactorAll_mclly_of_index (Or.inr rfl) hmin (KindFactor.all h)

theorem genericKill_of_su3_block_of_bad [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) {P : Type} [Group P] (α : MulAut P) (θ : ↥(StatedSU 3 (p ^ f) K) →* P)
    (hθ : Function.Injective θ) (hfix : ∀ g, α (θ g) = θ g)
    (hbad : ∀ k : Kind, ¬ KindFactor k (StatedProj (StatedSU 3 (p ^ f) K))) : GenericKill P α := by
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hP3 := isPerfect_statedSU_three_odd (K := K) hK hp2
  have : Group.IsPerfect θ.range := Group.IsPerfect.range θ
  let c : ↥θ.range →* StatedProj (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.mk' _).comp (MonoidHom.ofInjective hθ).symm.toMonoidHom
  have hc : Function.Surjective c :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hθ).symm.surjective
  have hs := isSimpleGroup_statedProj_three_odd (K := K) hK (by omega)
  have : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Nontrivial (StatedProj (StatedSU 3 (p ^ f) K)) := IsSimpleGroup.toNontrivial
  refine Or.inl ⟨θ.range, ‹_›, ?_, StatedProj (StatedSU 3 (p ^ f) K), inferInstance, hs, c, hc,
    Group.IsPerfect.not_isSolvable _, hbad⟩
  rintro _ ⟨g, rfl⟩
  exact hfix g

theorem genericKill_of_su3_block_odd (hMin : MinIndexU33) [Fact p.Prime] [CharP K p] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {P : Type} [Group P] (α : MulAut P)
    (θ : ↥(StatedSU 3 (p ^ f) K) →* P) (hθ : Function.Injective θ) (hfix : ∀ g, α (θ g) = θ g) :
    GenericKill P α := by
  by_cases hq : 5 ≤ p ^ f
  · exact genericKill_of_su3_block hf hK hp2 hq α θ hθ hfix
  · have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    have h2 : 2 ≤ p ^ f := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p)
    have hq3 : p ^ f = 3 := by omega
    exact genericKill_of_su3_block_of_bad hK hp2 α θ hθ hfix
      (not_kindFactor_statedProj_three_three hMin hK hq3)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
