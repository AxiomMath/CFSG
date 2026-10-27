module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Stmt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)
open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex (isLThreeTwo_map_equiv)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves (exists_conj_eq_of_card_eq_three)

theorem f1_isSylowOf_two_map_equiv {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G) {S : Subgroup K} (h : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S.map e.toMonoidHom) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨-, hp, hidx⟩ := h
  refine ⟨le_top, hp.map _, ?_⟩
  rw [Subgroup.relIndex_top_right] at hidx ⊢
  have h1 : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv S e
  rwa [h1]

theorem f1For_of_core {K G : Type} [Group K] [Finite K] [Group G] [Finite G] (e : K ≃* G)
    (h : F1Core G) : F1For K := by
  intro _ _ _ hcyc A W Y hA hNW hYW hAY hY hW S hS hSW
  have hcycG : ∀ X : Subgroup G, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    set e' := X.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have h1 : IsPGroup 3 ↥(X.map e.symm.toMonoidHom) := hX.map _
    have h2 := hcyc _ h1
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective
  have hcard : Nat.card (A.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hA]
  have hN : Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup G) : Set G) ≤
      W.map e.toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hWtop : W.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hW
    have h1 : (W.map e.toMonoidHom).index = W.index := Subgroup.index_map_equiv W e
    rw [htop, Subgroup.index_top] at h1
    exact Subgroup.index_eq_one.mp h1.symm
  have hmain := h hcycG _ _ _ hcard hN (Subgroup.map_mono hYW) (Subgroup.map_mono hAY)
    (isLThreeTwo_map_equiv e Y hY) hWtop _ (f1_isSylowOf_two_map_equiv e hS)
    (Subgroup.map_mono hSW)
  intro g hg
  have hg' : e g ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨g, hg, rfl⟩
  obtain ⟨w, hw, hwg⟩ := hmain hg'
  have : w = g := e.injective hwg
  exact this ▸ hw

theorem f1Core_of_A0 {G : Type} [Group G] [Finite G] {A₀ : Subgroup G} (hA₀ : Nat.card A₀ = 3)
    (h : ∀ W Y : Subgroup G, Subgroup.normalizer (A₀ : Set G) ≤ W → Y ≤ W → A₀ ≤ Y →
      IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W ≠ ⊤ →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → S ≤ W →
        Subgroup.normalizer (S : Set G) ≤ W) :
    F1Core G := by
  intro hcyc A W Y hA hNW hYW hAY hY hWtop S hS hSW
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc hA hA₀
  set cg := (MulAut.conj g).toMonoidHom
  have hNW' : Subgroup.normalizer (A₀ : Set G) ≤ W.map cg := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hAY' : A₀ ≤ Y.map cg := hg ▸ Subgroup.map_mono hAY
  have hWtop' : W.map cg ≠ ⊤ := by
    intro htop
    apply hWtop
    have h1 : (W.map cg).index = W.index := Subgroup.index_map_equiv W (MulAut.conj g)
    rw [htop, Subgroup.index_top] at h1
    exact Subgroup.index_eq_one.mp h1.symm
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (S.map cg) ⊤ :=
    f1_isSylowOf_two_map_equiv (MulAut.conj g) hS
  have hmain := h (W.map cg) (Y.map cg) hNW' (Subgroup.map_mono hYW) hAY'
    (isLThreeTwo_map_equiv (MulAut.conj g) Y hY) hWtop' (S.map cg) hS' (Subgroup.map_mono hSW)
  intro x hx
  have hx' : cg x ∈ Subgroup.normalizer ((S.map cg : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨x, hx, rfl⟩
  obtain ⟨w, hw, hwx⟩ := hmain hx'
  have : w = x := (MulAut.conj g).injective hwx
  exact this ▸ hw

end CFSG.LocalAnalysis.RankThreeUC.S15
