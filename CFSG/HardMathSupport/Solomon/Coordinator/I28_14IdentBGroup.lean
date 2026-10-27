module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Linear
import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFacts
import CFSG.Foundations
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
import CFSG.LocalAnalysis.QuasithinUnique.Setting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import Certificates.Certificate43

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def i28_14_identB_inf {G : Type} [Group G] (K : Subgroup G) : Subgroup G :=
  (⨅ n : ℕ, derivedSeries ↥K n).map K.subtype

theorem i28_14_identB_ne_bot {G : Type} [Group G] {K : Subgroup G}
    (h : ∃ a b : ↥K, a * b ≠ b * a) : K ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := h
  intro hK
  apply hab
  have ha : a = 1 := Subtype.ext (by simpa [hK] using a.2)
  rw [ha]
  simp

theorem i28_14_identB_derivedSeries_pi {ι : Type} [Finite ι] {G : ι → Type} [∀ i, Group (G i)]
    (n : ℕ) (h : ∀ i, derivedSeries (G i) n = ⊥) : derivedSeries (∀ i, G i) n = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext i
  have h1 := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom G i) n ⟨g, hg, rfl⟩
  rw [h i, Subgroup.mem_bot] at h1
  exact h1

theorem i28_14_identB_derivedSeries_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (n : ℕ)
    (h : derivedSeries A n = ⊥) : derivedSeries B n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 := map_derivedSeries_le_derivedSeries e.symm.toMonoidHom n ⟨x, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact e.symm.injective (h1.trans (map_one e.symm).symm)

theorem i28_14_identB_inf_le {G : Type} [Group G] {Wj A : Subgroup G} [Finite Wj]
    (hW : UniquenessMaximal.IsMcLaughlinGroup ↥Wj) (hA : UniquenessMaximal.IsMcLaughlinGroup ↥A)
    (hAW : A ≤ Wj) (hnorm : ∀ g ∈ Wj, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hns : ¬ Group.IsSolvable ↥A) :
    i28_14_identB_inf Wj ≤ A ∧ i28_14_identB_inf Wj ≠ ⊥ := by
  have : Finite A := Finite.of_injective _ (Subgroup.inclusion_injective hAW)
  have hnsW : ¬ Group.IsSolvable ↥Wj := fun h =>
    hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAW)
      (Subgroup.inclusion_injective hAW))
  obtain ⟨⟨hsimp, hab⟩, -⟩ := (inputMcLaughlinTypeFacts_holds ↥Wj hW).2 hnsW
  obtain ⟨⟨-, habA⟩, -⟩ := (inputMcLaughlinTypeFacts_holds ↥A hA).2 hns
  set L : Subgroup ↥Wj := ⨅ n : ℕ, derivedSeries ↥Wj n with hL
  set LA : Subgroup ↥A := ⨅ n : ℕ, derivedSeries ↥A n with hLA
  set f : ↥A →* ↥Wj := Subgroup.inclusion hAW with hf
  have hLAne : LA ≠ ⊥ := i28_14_identB_ne_bot (K := LA) habA
  have hLAL : LA.map f ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hL, Subgroup.mem_iInf]
    intro n
    exact map_derivedSeries_le_derivedSeries f n ⟨y, (Subgroup.mem_iInf.1 hy) n, rfl⟩
  have hconj : ∀ w : ↥Wj, ∀ x ∈ LA.map f, w * x * w⁻¹ ∈ LA.map f := by
    intro w x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : ↥A →* ↥A := ((MulAut.conj (w : G)).toMonoidHom.comp A.subtype).codRestrict A
      (fun a => hnorm w w.2 a a.2)
    have hφ : φ y ∈ LA := by
      rw [hLA, Subgroup.mem_iInf]
      intro n
      exact map_derivedSeries_le_derivedSeries φ n ⟨y, (Subgroup.mem_iInf.1 hy) n, rfl⟩
    exact ⟨φ y, hφ, Subtype.ext rfl⟩
  have hN : ((LA.map f).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj g _ hn
  have hLsub : L ≤ LA.map f := by
    have := hN
    rcases hsimp.eq_bot_or_eq_top_of_normal ((LA.map f).subgroupOf L) with h | h
    · exfalso
      apply hLAne
      rw [eq_bot_iff]
      intro y hy
      have hyL : f y ∈ L := hLAL ⟨y, hy, rfl⟩
      have : (⟨f y, hyL⟩ : ↥L) ∈ (LA.map f).subgroupOf L := ⟨y, hy, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      have h1 : f y = 1 := congrArg Subtype.val this
      rw [Subgroup.mem_bot]
      exact Subgroup.inclusion_injective hAW (h1.trans (map_one f).symm)
    · intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ (LA.map f).subgroupOf L := by rw [h]; trivial
      exact this
  refine ⟨?_, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    obtain ⟨y, -, hy⟩ := hLsub hl
    rw [← hy]
    exact y.2
  · intro h
    refine i28_14_identB_ne_bot (K := L) hab ?_
    rw [eq_bot_iff]
    intro l hl
    have : (l : G) ∈ i28_14_identB_inf Wj := ⟨l, hl, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this

end CFSG.HardMathSupport.Solomon.Coordinator
