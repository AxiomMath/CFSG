module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneAct
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneAct

@[expose] def I1015oneSp4Inner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isSp4eight →
    ∀ A : Subgroup (MulAut K), IsElemAbelian 3 A → (∀ α ∈ A, α ∈ (MulAut.conj : K →* MulAut K).range) →
      ∀ T : Subgroup K, IsPGroup 2 T → T ≠ ⊥ → (∀ α ∈ A, ∀ y ∈ T, α y ∈ T) → Nat.card A ≤ 3

@[expose] def I1015oneSp4Out : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isSp4eight →
    ∀ A : Subgroup (MulAut K), IsElemAbelian 3 A →
      Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : K →* MulAut K).range)

@[expose] def I1015oneSp4Rank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isSp4eight →
    ∀ A : Subgroup (MulAut K), IsElemAbelian 3 A → ∀ T : Subgroup K, IsPGroup 2 T → T ≠ ⊥ →
      (∀ α ∈ A, ∀ y ∈ T, α y ∈ T) → Nat.card A ≤ 9

@[expose] def I1015oneU3Rank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 →
    ∀ A : Subgroup (MulAut K), IsElemAbelian 3 A → ∀ T : Subgroup K, IsPGroup 2 T → T ≠ ⊥ →
      (∀ α ∈ A, ∀ y ∈ T, α y ∈ T) → Nat.card A ≤ 9

theorem isElemAbelian_inf_left {M : Type} [Group M] {A H : Subgroup M} (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A ⊓ H) := by
  unfold IsElemAbelian at hA ⊢
  obtain ⟨hcomm, hexp⟩ := hA
  refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
  · intro a ha b hb
    exact congrArg Subtype.val (isMulCommutative_iff.1 hcomm ⟨a, (Subgroup.mem_inf.1 ha).1⟩
      ⟨b, (Subgroup.mem_inf.1 hb).1⟩)
  · intro x hx
    exact hexp x (Subgroup.mem_inf.1 hx).1

theorem i1015oneSp4Rank_of_inner_outer (hI : I1015oneSp4Inner) (hO : I1015oneSp4Out) :
    I1015oneSp4Rank := by
  intro K _ _ hK A hA T hT2 hT0 hinv
  have hO' := hO K hK A hA
  have hI' := hI K hK (A ⊓ (MulAut.conj : K →* MulAut K).range) (isElemAbelian_inf_left hA)
    (fun α hα => (Subgroup.mem_inf.1 hα).2) T hT2 hT0
    (fun α hα => hinv α (Subgroup.mem_inf.1 hα).1)
  omega

theorem i1015oneAt_of_rank (hS : I1015oneSp4Rank) (hU : I1015oneU3Rank) (G : Type) [Group G]
    [Finite G] : I1015oneAt G := by
  intro X L B T hL hBN hB hcard hTL hT2 hBT hTn hcat
  obtain ⟨h27, hA, hne, hT2', hinv⟩ := i1015oneConfig hL hBN hB hcard hTL hT2 hBT hTn
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hle : Nat.card ↥(i1015oneAct hBN).range ≤ 9 := by
    rcases hi with hi | hi
    · exact hS (PSimple 3 L) ⟨i, hi, ⟨e⟩⟩ _ hA _ hT2' hne hinv
    · exact hU (PSimple 3 L) ⟨i, hi, ⟨e⟩⟩ _ hA _ hT2' hne hinv
  omega

theorem i1015oneAt_of_residuals (hI : I1015oneSp4Inner) (hO : I1015oneSp4Out)
    (hU : I1015oneU3Rank) (G : Type) [Group G] [Finite G] : I1015oneAt G :=
  i1015oneAt_of_rank (i1015oneSp4Rank_of_inner_outer hI hO) hU G

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes
