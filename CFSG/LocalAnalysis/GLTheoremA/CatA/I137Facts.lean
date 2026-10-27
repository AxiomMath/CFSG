module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 TauCeti

@[expose] def fixSubgroup {K : Type} [Group K] (α : MulAut K) : Subgroup K where
  carrier := {k | α k = k}
  one_mem' := map_one α
  mul_mem' := fun {a b} ha hb => by
    show α (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  inv_mem' := fun {a} ha => by
    show α a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

@[expose] def I137BorelTits : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsChevSimple 2 K →
    ∀ (T : Subgroup K), IsPGroup 2 T → T ≠ ⊥ →
      ∃ P : Subgroup K, P ≠ ⊤ ∧ Subgroup.normalizer (T : Set K) ≤ P

@[expose] def I137Order5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → fullCoverLevel 5 K ≤ 2 →
    IsChevSimple 2 (K ⧸ Subgroup.center K) →
    ∀ (Q₀ : Type) [Group Q₀], catalogIs Q₀ (S9.isList93 5) →
      Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card Q₀

@[expose] def I137LieCore3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → fullCoverLevel 3 K ≤ 2 →
    IsChevSimple 2 (K ⧸ Subgroup.center K) →
    ∀ (T A : Subgroup (K ⧸ Subgroup.center K)), IsPGroup 2 T → T ≠ ⊥ →
      A ≤ Subgroup.normalizer (T : Set (K ⧸ Subgroup.center K)) →
      ∀ (Q₀ : Type) [Group Q₀], (∃ f : A →* Q₀, Function.Surjective f) →
        catalogIs Q₀ (S9.isList93 3) → catalogIs Q₀ S9.isL3four

theorem isList93_eq_false_of_ge_seven {p : ℕ} (hp : 7 ≤ p) (i : TauCeti.CFSGIndex) :
    ¬ S9.isList93 p i := by
  intro h
  unfold S9.isList93 at h
  rcases h with ⟨h5, _⟩ | ⟨h3, _⟩
  · omega
  · omega

end CFSG.LocalAnalysis.GLTheoremA
