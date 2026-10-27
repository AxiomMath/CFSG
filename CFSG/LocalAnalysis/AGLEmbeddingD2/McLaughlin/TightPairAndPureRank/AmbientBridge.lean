module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.T2Group
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Quasithin.G11 CFSG.Open

variable {G : Type} [Group G] {N : Subgroup G}

@[expose] def VN (_hN : IsElemAbelian 2 N) : Type := ↥N

@[expose] def VN.toN {hN : IsElemAbelian 2 N} (v : VN hN) : ↥N := v

@[expose] def VN.ofN (hN : IsElemAbelian 2 N) (n : ↥N) : VN hN := n

instance (hN : IsElemAbelian 2 N) : CommGroup (VN hN) := commGroupOfElemAbelian hN

instance (hN : IsElemAbelian 2 N) : ExpTwo (VN hN) := expTwo_of_elemAbelian hN

instance [Finite G] (hN : IsElemAbelian 2 N) : Finite (VN hN) := inferInstanceAs (Finite ↥N)

@[expose] noncomputable def actGL (hN : IsElemAbelian 2 N) (Y : Subgroup G)
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) : ↥Y →* GLV (Additive (VN hN)) :=
  toGL.comp (actHom N Y hY)

@[expose] noncomputable def imgGL (hN : IsElemAbelian 2 N) (Y : Subgroup G)
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) : Subgroup (GLV (Additive (VN hN))) :=
  (actGL hN Y hY).range

theorem mem_imgGL {hN : IsElemAbelian 2 N} {Y : Subgroup G}
    {hY : Y ≤ Subgroup.normalizer (N : Set G)} {g : GLV (Additive (VN hN))} :
    g ∈ imgGL hN Y hY ↔ ∃ y : ↥Y, actGL hN Y hY y = g := Iff.rfl

@[expose] def subgroupOfSub (hN : IsElemAbelian 2 N)
    (W : Submodule (ZMod 2) (Additive (VN hN))) : Subgroup G where
  carrier := {g | ∃ n : ↥N, (n : G) = g ∧ Additive.ofMul (VN.ofN hN n) ∈ W}
  mul_mem' := by
    rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
    exact ⟨a * b, rfl, W.add_mem ha hb⟩
  one_mem' := ⟨1, rfl, W.zero_mem⟩
  inv_mem' := by
    rintro _ ⟨a, rfl, ha⟩
    refine ⟨a⁻¹, rfl, ?_⟩
    have : Additive.ofMul (VN.ofN hN a⁻¹) = -Additive.ofMul (VN.ofN hN a) := rfl
    rw [this]
    exact W.neg_mem ha

theorem subgroupOfSub_le (hN : IsElemAbelian 2 N) (W : Submodule (ZMod 2) (Additive (VN hN))) :
    subgroupOfSub hN W ≤ N := by
  rintro _ ⟨n, rfl, -⟩
  exact n.2

theorem normalizer_subgroupOfSub (hN : IsElemAbelian 2 N) {L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (N : Set G)) (W : Submodule (ZMod 2) (Additive (VN hN)))
    (hW : Invariant (imgGL hN L hL) W) : L ≤ Subgroup.normalizer (subgroupOfSub hN W : Set G) := by
  refine CFSG.AGLEmbedding.le_normalizer_of_forall_map_conj_le fun l hl => ?_
  rintro _ ⟨_, ⟨n, rfl, hn⟩, rfl⟩
  refine ⟨actHom N L hL ⟨l, hl⟩ n, ?_, ?_⟩
  · simp [actHom_apply_coe, MulAut.conj_apply]
  · exact hW _ ⟨⟨l, hl⟩, rfl⟩ _ hn

theorem eq_bot_or_top_of_sub (hN : IsElemAbelian 2 N) (W : Submodule (ZMod 2) (Additive (VN hN)))
    (h : subgroupOfSub hN W = ⊥ ∨ subgroupOfSub hN W = N) : W = ⊥ ∨ W = ⊤ := by
  rcases h with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨m, rfl⟩ := Additive.ofMul.surjective w
    have : ((VN.toN m : ↥N) : G) ∈ subgroupOfSub hN W := ⟨VN.toN m, rfl, hw⟩
    rw [h] at this
    have h1 : ((VN.toN m : ↥N) : G) = 1 := this
    have : VN.toN m = 1 := Subtype.ext h1
    simp [Submodule.mem_bot]
    exact this
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨m, rfl⟩ := Additive.ofMul.surjective w
    have hm : ((VN.toN m : ↥N) : G) ∈ subgroupOfSub hN W := by
      rw [h]
      exact (VN.toN m).2
    obtain ⟨n, hn, hnW⟩ := hm
    have : n = VN.toN m := Subtype.ext hn
    subst this
    exact hnW

theorem actGL_eq_one_iff (hN : IsElemAbelian 2 N) (Y : Subgroup G)
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) (y : ↥Y) :
    actGL hN Y hY y = 1 ↔ (y : G) ∈ Subgroup.centralizer (N : Set G) := by
  rw [← actHom_eq_one_iff N Y hY y]
  constructor
  · intro h
    exact toGL_injective (V := VN hN)
      (show toGL (V := VN hN) (actHom N Y hY y) = toGL (V := VN hN) 1 by rw [map_one]; exact h)
  · intro h
    exact (congrArg (toGL (V := VN hN)) h).trans (map_one _)

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
