module

public import CFSG.ClassicalInvolution.SmallCases.NDBH4R1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def nbhd (Ω : Set (Subgroup G)) (L : Subgroup G) : Set (Subgroup G) :=
  {N | N ∈ Ω ∧ N ≠ L ∧ Commutes L N}

@[expose] def layer (Ω : Set (Subgroup G)) (L : Subgroup G) : Subgroup G :=
  ⨆ N ∈ nbhd Ω L, N

theorem le_layer {Ω : Set (Subgroup G)} {L N : Subgroup G} (h : N ∈ nbhd Ω L) :
    N ≤ layer Ω L :=
  le_iSup₂ (f := fun N (_ : N ∈ nbhd Ω L) => N) N h

theorem nbhd_symm {Ω : Set (Subgroup G)} {L N : Subgroup G} (hL : L ∈ Ω) (h : N ∈ nbhd Ω L) :
    L ∈ nbhd Ω N :=
  ⟨hL, fun e => h.2.1 e.symm, h.2.2.symm⟩

theorem nbhd_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) {L N : Subgroup G}
    (h : N ∈ nbhd Ω L) : conjSub g N ∈ nbhd Ω (conjSub g L) :=
  ⟨hΩ g N h.1, fun e => h.2.1 (conjSub_injective g e), h.2.2.conjSub g⟩

theorem layer_le_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) (L : Subgroup G) :
    layer Ω L ≤ conjSub g⁻¹ (layer Ω (conjSub g L)) := by
  refine iSup₂_le fun N hN => ?_
  have h2 : conjSub g N ≤ layer Ω (conjSub g L) := le_layer (nbhd_conj hΩ g hN)
  have h3 := conjSub_mono (n := g⁻¹) h2
  rwa [conjSub_inv_conjSub] at h3

theorem conjSub_layer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) (L : Subgroup G) :
    conjSub g (layer Ω L) = layer Ω (conjSub g L) := by
  refine le_antisymm ?_ ?_
  · have h := conjSub_mono (n := g) (layer_le_conj hΩ g L)
    rwa [conjSub_conjSub_inv] at h
  · have h := layer_le_conj hΩ g⁻¹ (conjSub g L)
    rwa [inv_inv, conjSub_inv_conjSub] at h

structure Ctx (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (L : Subgroup G) (w : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  inClass : InClass p f Ω
  exact : ExactMembers Ω
  uniq : ∀ M ∈ Ω, ∀ M' ∈ Ω, ∀ x : G, IsClassicalMember p f M x → IsClassicalMember p f M' x →
    M = M'
  mfz : FundNoncentral p
  shared : G2D4SharedInvolution p
  inv : Balance.Bootstrap.TwoClassInvolutionsConj p
  p1 : LocalOddCentral Ω {w}
  mem : L ∈ Ω
  cls : IsClassicalMember p f L w
  shape : ∃ (tY : StatedLieTag) (nY : ℕ), (tY = .G2 ∨ tY = .trialityD4) ∧
    LocalShapeT p f 1 tY nY Ω w

namespace Ctx

theorem conj {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G} (C : Ctx p f Ω L w) (g : G) :
    Ctx p f Ω (conjSub g L) (g * w * g⁻¹) where
  odd := C.odd
  five := C.five
  inClass := C.inClass
  exact := C.exact
  uniq := C.uniq
  mfz := C.mfz
  shared := C.shared
  inv := C.inv
  p1 := localOddCentral_conj C.inClass.conjInvariant g w C.p1
  mem := C.inClass.conjInvariant g L C.mem
  cls := C.cls.conj g
  shape := by
    obtain ⟨tY, nY, htY, hsh⟩ := C.shape
    exact ⟨tY, nY, htY, LocalShapeT.conj C.inClass.conjInvariant g hsh⟩

theorem exists_data {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G} (C : Ctx p f Ω L w) :
    ∃ (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card),
      D.card = 2 ∧ (D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4) ∧
        ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2 := by
  obtain ⟨tY, nY, htY, D, hcard, i₁, ht, -, hrest⟩ := C.shape
  exact ⟨D, i₁, by omega, by rw [ht]; exact htY, hrest⟩

end Ctx

theorem ctx_of_setup [Finite G] {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hmfz : FundNoncentral p) (hshared : G2D4SharedInvolution p)
    (hinv : Balance.Bootstrap.TwoClassInvolutionsConj p)
    (hnt : ¬ HasTwin p f K z) {tY : StatedLieTag} {nY : ℕ}
    (htY : tY = .G2 ∨ tY = .trialityD4) (hsh : LocalShapeT p f 1 tY nY (𝒞 K) z) :
    Ctx p f (𝒞 K) K z where
  odd := S.odd
  five := S.five
  inClass := S.inClass
  exact := S.exact
  uniq := fun _ hM _ hM' _ hx hx' =>
    NDBH2.eq_of_isClassicalMember S.odd S.five S.cls hnt hM hM' hx hx'
  mfz := hmfz
  shared := hshared
  inv := hinv
  p1 := S.p1
  mem := mem_conjClass_self K
  cls := S.cls
  shape := ⟨tY, nY, htY, hsh⟩

end CFSG.ClassicalInvolution.NDB.G2S
