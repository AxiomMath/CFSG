module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionHullSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

private theorem centralizer_subgroupOf_centralizer_eq_zpowers {G : Type*} [Group G] {u : G}
    {L : Subgroup G} (hLM : L ≤ Subgroup.centralizer ({u} : Set G))
    (hK : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers u) :
    Subgroup.centralizer ((L.subgroupOf (Subgroup.centralizer ({u} : Set G)) :
        Subgroup (Subgroup.centralizer ({u} : Set G))) :
        Set (Subgroup.centralizer ({u} : Set G))) =
      Subgroup.zpowers (⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({u} : Set G)) := by
  ext m
  have h1 : m ∈ Subgroup.centralizer ((L.subgroupOf (Subgroup.centralizer ({u} : Set G)) :
        Subgroup (Subgroup.centralizer ({u} : Set G))) :
        Set (Subgroup.centralizer ({u} : Set G))) ↔
      (m : G) ∈ Subgroup.centralizer (L : Set G) := by
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hm l hl
      exact congrArg Subtype.val (hm ⟨l, hLM hl⟩ (Subgroup.mem_subgroupOf.mpr hl))
    · intro hm l hl
      exact Subtype.ext (hm l (Subgroup.mem_subgroupOf.mp hl))
  have h2 : m ∈ Subgroup.zpowers (⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({u} : Set G)) ↔ (m : G) ∈ Subgroup.zpowers u := by
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [← hk]; rfl)⟩
  rw [h1, h2, ← hK]
  exact ⟨fun hm => ⟨m.2, hm⟩, fun hm => hm.2⟩

theorem centralizer_no_order_four_of_SL2_hull {G : Type} [Group G] [Finite G] {u : G}
    (hu : orderOf u = 2) {L U : Subgroup G} (hLM : L ≤ Subgroup.centralizer ({u} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal) (huL : u ∉ L)
    (hK : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers u)
    {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) (hodd : Odd n)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hUL : U ≤ L) (hUidx : ¬ 2 ∣ U.relIndex L) [IsElementaryAbelian 2 U] :
    ∀ x ∈ Subgroup.centralizer ({u} : Set G), orderOf x ≠ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  set M := Subgroup.centralizer ({u} : Set G) with hMdef
  let u' : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hu' : orderOf u' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hu
  have huZ : u' ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2)
  have huL' : u' ∉ L.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact huL
  have hOut : Odd (MulAut.conj : L.subgroupOf M →* MulAut (L.subgroupOf M)).range.index := by
    obtain ⟨-, -, -, hcardOut, -⟩ :=
      LocalCriterionSquareField.even_SL2_full_automorphism_semilinear_model hn hcard
    change Odd (Nat.card (Outer (L.subgroupOf M)))
    rw [Nat.card_congr (equivalence ((Subgroup.subgroupOfEquivOfLe hLM).trans e)).toEquiv,
      hcardOut]
    exact hodd
  have hRL : U.subgroupOf M ≤ L.subgroupOf M := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hUL (Subgroup.mem_subgroupOf.mp hy))
  have hRidx : ¬ 2 ∣ (U.subgroupOf M).relIndex (L.subgroupOf M) := by
    rw [Subgroup.relIndex_subgroupOf hLM]
    exact hUidx
  have : IsElementaryAbelian 2 (U.subgroupOf M) :=
    IsElementaryAbelian.subgroupOf (hUL.trans hLM)
  have hRelem : IsElemAbelian 2 (U.subgroupOf M) :=
    ⟨inferInstance, fun y hy => elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy⟩
  obtain ⟨-, -, -, hno⟩ :=
    CentralInvolutionHull.central_involution_hull_odd_outer_quotient_elementary_sylow
      (L.subgroupOf M) hu' huZ huL' (centralizer_subgroupOf_centralizer_eq_zpowers hLM hK) hOut
      (U.subgroupOf M) hRL hRidx hRelem
  have := hno ⟨x, hx⟩
  rwa [Subgroup.orderOf_mk] at this

end CFSG.ProperTwoGeneratedCore.HighRankPair
