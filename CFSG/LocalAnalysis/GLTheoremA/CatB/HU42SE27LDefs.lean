module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmega
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def InvCentOn (G : Type) [Group G] : Prop :=
  ∀ (E U₀ : Subgroup G) (s : G), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → IsPGroup 2 ↥U₀ →
    U₀ ≠ ⊥ → E ≤ Subgroup.normalizer (U₀ : Set G) → s ∈ E → s ≠ 1 → ¬ NoU4Sect s →
      ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ e ∈ E, z * e = e * z

@[expose] def U42InvFact : Prop :=
  ∀ (Y : Type) [Group Y], catalogIs Y S9.isU4two → ∀ (F : Subgroup Y) (z : Y),
    Nat.card F = 9 → z ^ 2 = 1 → z ≠ 1 → (∀ f ∈ F, z * f = f * z) →
      ∃ T : Subgroup Y, IsPGroup 2 ↥T ∧ 8 < Nat.card T ∧ F ≤ Subgroup.normalizer (T : Set Y) ∧
        (⁅T, F⁆ : Subgroup Y) ≠ ⊥

@[expose] def SUInvCent (n : ℕ) : Prop :=
  ∀ (E U₀ : Subgroup ↥(StatedSU n (2 ^ 1) CFSG.Fischer.F4)), IsPGroup 2 ↥U₀ → U₀ ≠ ⊥ →
    E ≤ Subgroup.normalizer (U₀ : Set ↥(StatedSU n (2 ^ 1) CFSG.Fischer.F4)) →
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ e ∈ E, e ^ 3 = 1) →
      ∃ z : ↥(StatedSU n (2 ^ 1) CFSG.Fischer.F4), z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ e ∈ E, z * e = e * z

@[expose] def OmTSFact : Prop :=
  ∀ (E U₀ : Subgroup ↥CFSG.AGLEmbedding.Om8), IsPGroup 2 ↥U₀ → U₀ ≠ ⊥ →
    E ≤ Subgroup.normalizer (U₀ : Set ↥CFSG.AGLEmbedding.Om8) →
      ∃ R₀ : Submodule (ZMod 2) (CFSG.AGLEmbedding.ι8 → ZMod 2), R₀ ≠ ⊥ ∧
        (∀ x ∈ R₀, CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) x = 0) ∧
        ∀ e ∈ E, ∀ x ∈ R₀,
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv CFSG.AGLEmbedding.ι8 (ZMod 2)
            ((e : ↥CFSG.AGLEmbedding.Om8) : GL CFSG.AGLEmbedding.ι8 (ZMod 2)) x ∈ R₀

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
