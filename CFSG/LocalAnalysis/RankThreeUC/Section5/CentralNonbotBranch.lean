module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralCyclicBlocks
public import CFSG.GroupTheory.CoprimeActionSupport.CyclicBlockStabilizerAbelian
public import CFSG.GroupTheory.AutomorphismAction.AbelianTwoGroupSplitting
public import CFSG.LocalAnalysis.RankThreeUC.Section5.AbelianImageCentralizerScalar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralNonbotBranch

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks CFSG.LocalAnalysis.RankThreeUC

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

private theorem normalizes_image (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    Bstar P B ≤ Subgroup.normalizer
      ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) : Subgroup (MulAut P)) : Set (MulAut P)) := by
  have hBT := hc.oddPrimeClassTwoAction.normalizes he
  have key : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := fun b hb t ht =>
    (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
  rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
  have hb' : b ∈ B := Subgroup.mem_subgroupOf.mp hb
  have hφ : Subgroup.normalizerMonoidHom P ⟨b, hbN⟩ = conjOnP P hc.faithfulBinaryIrreducibleAction.normal b := rfl
  rw [hφ, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨b * t * b⁻¹, key b hb' t ht, by simp⟩
  · rintro ⟨t, ht, hth⟩
    refine ⟨b⁻¹ * t * b, ?_, ?_⟩
    · have := key b⁻¹ (B.inv_mem hb') t ht
      simpa using this
    · have : h = (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b)⁻¹ * (conjOnP P hc.faithfulBinaryIrreducibleAction.normal t) *
          conjOnP P hc.faithfulBinaryIrreducibleAction.normal b := by
        rw [hth]; group
      rw [this]; simp [map_mul, map_inv]

theorem abelian (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) : IsMulCommutative (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) := by
  obtain ⟨I, _, E, hcyc, hgen, hstab⟩ :=
    CentralCyclicBlocks.blocks hc hr hXne
  exact CFSG.GroupTheory.CoprimeActionSupport.CyclicBlockStabilizerAbelian.abelian _ E hcyc hgen hstab

theorem abelian_twoGroup_splitting (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) :
    Sstar P T B ⊔ (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P))) =
        T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ∧
      Disjoint (Sstar P T B) (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P))) ∧
      Sstar P T B ≤ Subgroup.centralizer
        ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
          Subgroup.centralizer (Bstar P B : Set (MulAut P)) : Subgroup (MulAut P)) :
          Set (MulAut P)) := by
  have he : Odd e := (PrimeB.prime_order hc hr).2.2.1
  have hodd : Odd (Nat.card (Bstar P B)) :=
    (CoprimeStarSubgroupStructure.structure hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).2.2.1
  have hR2 : IsPGroup 2 (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) :=
    hc.oddPrimeClassTwoAction.setting.twoGroup.map _
  have hnorm : Bstar P B ≤ Subgroup.normalizer
      ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) : Subgroup (MulAut P)) : Set (MulAut P)) :=
    normalizes_image hc he
  have h := CFSG.GroupTheory.AutomorphismAction.abelian_twoGroup_splitting
    (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) (Bstar P B) hR2 hodd hnorm (abelian hc hr hXne)
  rw [← OddExponentCommutatorImage.commutator_image hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction.normal he] at h
  exact h

theorem scalar (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) :
    ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P)),
      ∃ k : ℤ, ∀ x : P, φ x = x ^ k :=
  AbelianImageCentralizerScalar.scalar hc (abelian hc hr hXne)
    (PrimeB.prime_order hc hr).2.2.1

theorem branch (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) :
    IsMulCommutative (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) ∧
      (Sstar P T B ⊔ (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P))) =
        T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ∧
      Disjoint (Sstar P T B) (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P))) ∧
      Sstar P T B ≤ Subgroup.centralizer
        ((T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
          Subgroup.centralizer (Bstar P B : Set (MulAut P)) : Subgroup (MulAut P)) :
          Set (MulAut P))) ∧
      ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P)),
      ∃ k : ℤ, ∀ x : P, φ x = x ^ k :=
  ⟨abelian hc hr hXne, abelian_twoGroup_splitting hc hr hXne, scalar hc hr hXne⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralNonbotBranch
