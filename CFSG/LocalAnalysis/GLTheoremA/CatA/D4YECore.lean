module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T

section Core

variable {H : Type} [Group H] [Finite H] {K B : Subgroup H}

abbrev Bo (K B : Subgroup H) : Subgroup H := B ⊓ Subgroup.centralizer (K : Set H)

theorem Bo_cent {s : H} (hs : s ∈ Bo K B) : ∀ k ∈ K, s * k = k * s := fun k hk =>
  (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hs).2 k hk).symm

theorem big_sup (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) (hB : IsElemAbelian 3 B)
    {E : Subgroup H} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 (E ⊔ Bo K B) ∧ Nat.card ↥(E ⊔ Bo K B) = Nat.card E * Nat.card (Bo K B) := by
  have hBoel : IsElemAbelian 3 (Bo K B) := isElemAbelian_mono hB inf_le_left
  refine ⟨hE.sup_of_commute hBoel fun e he s hs => (Bo_cent hs e (hEK he)).symm, ?_⟩
  have hnorm : Bo K B ≤ Subgroup.normalizer (E : Set H) :=
    fun s hs => mem_normalizer_of_centralizes fun w hw => Bo_cent hs w (hEK hw)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
  have hinf : E ⊓ Bo K B = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
    rw [Subgroup.mem_bot]
    exact hKc z (hEK hz1) fun y hy => (Bo_cent hz2 y hy).symm
  rw [hinf, Subgroup.card_bot, mul_one] at h1
  exact h1

theorem core_all (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) (hB : IsElemAbelian 3 B)
    {E : Subgroup H} (hEK : E ≤ K) (hE : IsElemAbelian 3 E)
    (hlt : Nat.card B < Nat.card E * Nat.card (Bo K B))
    (hall : ∀ P : Subgroup H, IsElemAbelian 3 P → Nat.card P ≤ Nat.card B) : False := by
  obtain ⟨hPel, hPc⟩ := big_sup hKc hB hEK hE
  have := hall _ hPel
  rw [hPc] at this
  omega

theorem core_two (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) (hB : IsElemAbelian 3 B)
    {E : Subgroup H} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) {W : Subgroup H} (hW2 : IsPGroup 2 W)
    (hWne : W ≠ ⊥) (hEW : E ≤ Subgroup.normalizer (W : Set H))
    (hBoW : Bo K B ≤ Subgroup.normalizer (W : Set H))
    (hlt : Nat.card B < Nat.card E * Nat.card (Bo K B))
    (hmax : ∀ P W' : Subgroup H, IsElemAbelian 3 P → IsPGroup 2 W' → W' ≠ ⊥ →
      P ≤ Subgroup.normalizer (W' : Set H) → Nat.card P ≤ Nat.card B) : False := by
  obtain ⟨hPel, hPc⟩ := big_sup hKc hB hEK hE
  have := hmax _ W hPel hW2 hWne (sup_le hEW hBoW)
  rw [hPc] at this
  omega

end Core

end CFSG.LocalAnalysis.GLTheoremA.D4Y
