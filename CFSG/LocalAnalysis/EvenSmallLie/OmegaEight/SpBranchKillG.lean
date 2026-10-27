module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillSpec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem like_iff {T : Subgroup G} {t u : G} (ht : t ∈ T) (hu : u ∈ T) :
    Like T t u ↔ ALike (⟨t, ht⟩ : T) ⟨u, hu⟩ := by
  have hcard : ∀ (v : G) (hv : v ∈ T), Nat.card (T ⊓ centralizer ({v} : Set G) : Subgroup G) =
      Nat.card (centralizer ({(⟨v, hv⟩ : T)} : Set T)) := by
    intro v hv
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
          (mem_centralizer_singleton_iff.1 x.2.2))⟩
        invFun := fun y => ⟨y.1, y.1.2, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hinv : ∀ (v : G) (hv : v ∈ T), nInv (T ⊓ centralizer ({v} : Set G)) =
      aInv (⟨v, hv⟩ : T) := by
    intro v hv
    unfold nInv aInv
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1.1⟩, Subtype.ext x.2.2.1, fun h => x.2.2.2
          (congrArg Subtype.val h), Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1.2)⟩
        invFun := fun y => ⟨y.1, ⟨y.1.2, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val y.2.2.2)⟩, congrArg Subtype.val y.2.1,
          fun h => y.2.2.1 (Subtype.ext h)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hord : ∀ (v : G) (hv : v ∈ T), nOrd4 (T ⊓ centralizer ({v} : Set G)) =
      aOrd4 (⟨v, hv⟩ : T) := by
    intro v hv
    unfold nOrd4 aOrd4
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1.1⟩, fun h => x.2.2.1 (congrArg Subtype.val h),
          Subtype.ext x.2.2.2, Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1.2)⟩
        invFun := fun y => ⟨y.1, ⟨y.1.2, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val y.2.2.2)⟩, fun h => y.2.1 (Subtype.ext h),
          congrArg Subtype.val y.2.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  unfold Like ALike
  rw [hcard u hu, hcard t ht, hinv u hu, hinv t ht, hord u hu, hord t ht]
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    exact ⟨Subtype.ext h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hu, congrArg Subtype.val h1, h2, h3, h4⟩

section Kill

variable [Finite G] {t : G} {TH T : Subgroup G} (hTp : IsPGroup 2 T) (hTHT : TH ≤ T)
  (hTH : TH ≤ centralizer ({t} : Set G))
  (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
  (ht : t ∈ T) (ht2 : t * t = 1)
  {N : ℕ} {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {gens : List ℕ} (Φ : CodeIso T N mul)
  (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
  (hG : Gen mul gens N) {m : ℕ} (hm : 1 < m)
  (hgood : ∀ c ∈ kInv mul N, kRecGood mul inv gens N m c = true)

@[expose] noncomputable def chiSub {b : List Bool} {χ : Array Bool}
    (hchi : chiOK mul gens N b χ = true) : Subgroup G :=
  (chiHom Φ h0 hinv hgens hG hchi).ker.map T.subtype

omit [Finite G] in
include hinv hgens hG in
theorem chiSub_spec {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true)
    (htχ : χ[Φ.f ⟨t, ht⟩]! = true) :
    chiSub Φ h0 hinv hgens hG hchi ≤ T ∧ (chiSub Φ h0 hinv hgens hG hchi).relIndex T = 2 ∧
      (∀ h ∈ T, ∀ x ∈ chiSub Φ h0 hinv hgens hG hchi,
        h * x * h⁻¹ ∈ chiSub Φ h0 hinv hgens hG hchi) ∧
      t ∉ chiSub Φ h0 hinv hgens hG hchi ∧
      ∀ (x : T), (x : G) ∈ chiSub Φ h0 hinv hgens hG hchi ↔ χ[Φ.f x]! = false := by
  have hmem : ∀ (x : T), (x : G) ∈ chiSub Φ h0 hinv hgens hG hchi ↔ χ[Φ.f x]! = false := by
    intro x
    unfold chiSub
    rw [← mem_ker_chiHom Φ h0 hinv hgens hG hchi]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨map_subtype_le _, ?_, fun h hh x hx => ?_, fun hh => ?_, hmem⟩
  · have e : (chiSub Φ h0 hinv hgens hG hchi).subgroupOf T =
        (chiHom Φ h0 hinv hgens hG hchi).ker := by
      ext x
      rw [mem_subgroupOf, hmem, mem_ker_chiHom]
    unfold relIndex
    rw [e, index_ker_chiHom Φ h0 hinv hgens hG hchi htχ]
  · have hxT : x ∈ T := map_subtype_le _ hx
    have hx' := (hmem ⟨x, hxT⟩).1 hx
    have hk : (⟨x, hxT⟩ : T) ∈ (chiHom Φ h0 hinv hgens hG hchi).ker :=
      (mem_ker_chiHom Φ h0 hinv hgens hG hchi _).2 hx'
    have hk' := (chiHom Φ h0 hinv hgens hG hchi).normal_ker.conj_mem _ hk ⟨h, hh⟩
    exact ⟨_, hk', rfl⟩
  · have := (hmem ⟨t, ht⟩).1 hh
    rw [htχ] at this
    exact Bool.noConfusion this

end Kill

end CFSG.EvenSmallLie.OmegaEight.SpBranch
