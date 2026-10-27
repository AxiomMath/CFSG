module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LInputs

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi23Transpositions : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsSporadic ↥K .Fi23 →
    (∃ u : G, Fi23Transposition K u) ∧
      ∀ u : G, Fi23Transposition K u → CFSG.IsQuasisimple ↥(K ⊓ centralizer ({u} : Set G))

@[expose] def Fi23TranspositionAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (u : G), OddCover .Fi24Prime L → K ≤ L →
    IsSporadic ↥K .Fi23 → Fi23Transposition K u →
      Group.IsSolvable ↥(autCentralizer L (K ⊓ centralizer ({u} : Set G)))

@[expose] def Fi23InvolutionFixed : Prop :=
  ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
    IsSporadic (K₂ ⧸ center K₂) .Fi23 → ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
      ¬ Group.IsSolvable ↥(fixSubgroup α)

structure FiV3RowFacts : Prop where
  thm24 : Hyp.Thm24Hex .Fi24Prime
  transpositions : Fi23Transpositions
  autSolv : Fi23TranspositionAut
  fixed : Fi23InvolutionFixed

structure FiV3Basic : Prop where
  pinned : FiPinned
  order23 : Fi23Order
  selfCent : Fi23SelfCentralizing
  outerFixed : Fi24OuterFixed

theorem fi23AutCentSolvable_of_rowFacts (pf : FiPinned) (rf : FiV3RowFacts) :
    Fi23AutCentSolvable := by
  intro G _ _ L K hcov hKL hKq hKcq
  have hKs : IsSporadic ↥K .Fi23 := isSporadic_of_center_eq_bot (pf.mult23 ↥K hKq hKcq) hKcq
  obtain ⟨⟨u, hu⟩, -⟩ := rf.transpositions G K hKs
  have hsolv := rf.autSolv G L K u hcov hKL hKs hu
  have hle : autCentralizer L K ≤ autCentralizer L (K ⊓ centralizer ({u} : Set G)) :=
    fun α hα k hk => hα k (Subgroup.mem_inf.1 hk).1
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem FiV3Basic.toPinned (b : FiV3Basic) (rf : FiV3RowFacts) : FiV3Pinned :=
  { pinned := b.pinned
    order23 := b.order23
    selfCent := b.selfCent
    autSolv := fi23AutCentSolvable_of_rowFacts b.pinned rf
    outerFixed := b.outerFixed }

@[expose] def CanLocV3 {H : Type} [Group H] (K₁ N₀ : Subgroup H) : Prop :=
  ∃ u : H, Fi23Transposition K₁ u ∧ N₀ = K₁ ⊓ centralizer ({u} : Set H)

theorem normalizer_zpowers_eq_centralizer {H : Type} [Group H] {u : H} (hu : orderOf u = 2) :
    normalizer ((zpowers u : Subgroup H) : Set H) = centralizer ({u} : Set H) := by
  ext n
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hn
    have h1 : n * u * n⁻¹ ∈ zpowers u := ((mem_normalizer_iff.1 hn) u).1 (mem_zpowers u)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h1
    have hmod : u ^ k = u ^ (k % 2) := by
      have h := zpow_mod_orderOf u k
      rw [hu] at h
      simpa using h.symm
    have hcase : k % 2 = 0 ∨ k % 2 = 1 := by omega
    have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
    rcases hcase with h0 | h1'
    · rw [hmod, h0, zpow_zero] at hk
      exfalso
      apply hu1
      have : n * u * n⁻¹ = 1 := hk.symm
      simpa using this
    · rw [hmod, h1', zpow_one] at hk
      calc n * u = n * u * n⁻¹ * n := by group
        _ = u * n := by rw [← hk]
  · intro hn
    refine Subgroup.centralizer_le_normalizer (zpowers u : Set H) ?_
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    exact (Commute.zpow_right (show Commute n u from hn) m).eq.symm

theorem fi23Transposition_map {H : Type} [Group H] {K₁ : Subgroup H} {u : H}
    (h : Fi23Transposition K₁ u) (e : H ≃* H) :
    Fi23Transposition (K₁.map e.toMonoidHom) (e u) ∧
      (K₁ ⊓ centralizer ({u} : Set H)).map e.toMonoidHom =
        K₁.map e.toMonoidHom ⊓ centralizer ({e u} : Set H) := by
  obtain ⟨huK, hu2, hcard⟩ := h
  have hmap : (K₁ ⊓ centralizer ({u} : Set H)).map e.toMonoidHom =
      K₁.map e.toMonoidHom ⊓ centralizer ({e u} : Set H) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, ⟨hy, hyu⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      show e y * e u = e u * e y
      rw [← map_mul, ← map_mul, hyu]
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      have : e (y * u) = e (u * y) := by rw [map_mul, map_mul]; exact hx
      exact e.injective this
  refine ⟨⟨Subgroup.mem_map_of_mem _ huK, ?_, ?_⟩, hmap⟩
  · rw [MulEquiv.orderOf_eq]
    exact hu2
  · rw [← hmap, Subgroup.card_map_of_injective e.injective]
    exact hcard

theorem canLocSpec_v3 (pf : FiPinned) (rf : FiV3RowFacts) (H : Type) [Group H] [Finite H] :
    CanLocSpec H IsKFi23 CanLocV3 where
  le := by
    rintro K₁ N₀ ⟨u, -, rfl⟩
    exact inf_le_left
  isTwoLocalIn := by
    rintro K₁ N₀ ⟨u, ⟨huK, hu2, -⟩, rfl⟩
    have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
    refine ⟨zpowers u, ?_, isPGroup_zpowers_of_orderOf_two hu2, zpowers_le.2 huK, ?_⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      exact hu1
    · rw [normalizer_zpowers_eq_centralizer hu2, inf_comm]
  map := by
    rintro e K₁ N₀ ⟨u, hu, rfl⟩
    obtain ⟨hu', hmap⟩ := fi23Transposition_map hu e
    exact ⟨e u, hu', hmap⟩
  exists_loc := by
    intro K₁ hq hK
    have hcq := isSporadic_cq_of_isKFi23 hq hK
    have hKs : IsSporadic ↥K₁ .Fi23 := isSporadic_of_center_eq_bot (pf.mult23 ↥K₁ hq hcq) hcq
    obtain ⟨⟨u, hu⟩, -⟩ := rf.transpositions H K₁ hKs
    exact ⟨_, u, hu, rfl⟩

end CFSG.EvenSporadicStandard.Induction.Fi.V3
