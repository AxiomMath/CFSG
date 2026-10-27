module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralNonbotBranch
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BottomAbelianImageByDeterminant

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

def Tstar (P T : Subgroup G) : Subgroup (MulAut ↥P) :=
  (T.subgroupOf (Subgroup.normalizer (P : Set G))).map (Subgroup.normalizerMonoidHom P)

theorem Tstar_eq {P T : Subgroup G} (hP : P.Normal) :
    Tstar P T = T.map (CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary.conjOnP P hP) := by
  ext φ
  simp only [Tstar, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.1, hn, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, FaithfulPImageVocabulary.mem_normalizer hP t⟩, ht, rfl⟩

private theorem normalizes_image {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e) :
    Bstar P B ≤ Subgroup.normalizer
      ((T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal) :
        Subgroup (MulAut ↥P)) : Set (MulAut ↥P)) := by
  have hBT := hc.oddPrimeClassTwoAction.normalizes he
  have key : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := fun b hb t ht =>
    (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
  rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
  have hb' : b ∈ B := Subgroup.mem_subgroupOf.mp hb
  have hφ : Subgroup.normalizerMonoidHom P ⟨b, hbN⟩ =
      FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal b := rfl
  rw [hφ, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨b * t * b⁻¹, key b hb' t ht, by simp⟩
  · rintro ⟨t, ht, hth⟩
    refine ⟨b⁻¹ * t * b, ?_, ?_⟩
    · have := key b⁻¹ (B.inv_mem hb') t ht
      simpa using this
    · have : h = (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal b)⁻¹ *
          (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal t) *
          FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal b := by
        rw [hth]; group
      rw [this]; simp [map_mul, map_inv]

private theorem splitting_of_comm {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hTab : IsMulCommutative (T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal))) :
    Sstar P T B ⊔ (T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut ↥P))) =
        T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ∧
      Disjoint (Sstar P T B) (T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut ↥P))) ∧
      Sstar P T B ≤ Subgroup.centralizer
        ((T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal) ⊓
          Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) : Subgroup (MulAut ↥P)) :
          Set (MulAut ↥P)) := by
  have he : Odd e := (PrimeB.prime_order hc hr).2.2.1
  have hodd : Odd (Nat.card (Bstar P B)) :=
    (CoprimeStarSubgroupStructure.structure hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).2.2.1
  have hR2 : IsPGroup 2 (T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) :=
    hc.oddPrimeClassTwoAction.setting.twoGroup.map _
  have hnorm := normalizes_image hc he
  have h := CFSG.GroupTheory.AutomorphismAction.abelian_twoGroup_splitting
    (T.map (FaithfulPImageVocabulary.conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) (Bstar P B) hR2 hodd
    hnorm hTab
  rw [← OddExponentCommutatorImage.commutator_image hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction.normal he] at h
  exact h

theorem sylow_image_directProduct_and_isMulCommutative_and_centralizer_scalar {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1)) :
    (Sstar P T B ⊔ (Tstar P T ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P))) =
        Tstar P T ∧
      Disjoint (Sstar P T B) (Tstar P T ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P))) ∧
      Sstar P T B ≤ Subgroup.centralizer
        ((Tstar P T ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) :
          Subgroup (MulAut ↥P)) : Set (MulAut ↥P)) ∧
      IsMulCommutative ↥(Tstar P T)) ∧
    ∀ φ ∈ Tstar P T ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)),
      ∃ k : ℤ, ∀ x : ↥P, φ x = x ^ k := by
  rw [Tstar_eq hc.faithfulBinaryIrreducibleAction.normal]
  by_cases hX : CentralBinaryBlocks.X hc = ⊥
  · have hTab := CFSG.LocalAnalysis.RankThreeUC.Section5.BottomAbelianImageByDeterminant.abelian hc hr hX
    have hS := splitting_of_comm hc hr hTab
    exact ⟨⟨hS.1, hS.2.1, hS.2.2, hTab⟩,
      AbelianImageCentralizerScalar.scalar hc hTab (PrimeB.prime_order hc hr).2.2.1⟩
  · obtain ⟨hcomm, ⟨s1, s2, s3⟩, hsc⟩ := CentralNonbotBranch.branch hc hr hX
    exact ⟨⟨s1, s2, s3, hcomm⟩, hsc⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
