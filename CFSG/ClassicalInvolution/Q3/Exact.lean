module

public import CFSG.ClassicalInvolution.Q3.Frame
public import CFSG.ClassicalInvolution.Q3.Induction
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic
public import CFSG.ClassicalInvolution.SmallCases.FrameRank

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped MatrixGroups

section Image

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_le_of_card_image_eq {Y K : Subgroup G} (hKY : K ≤ Y) {z : G}
    (hK : IsClassicalMember3 K z)
    (h24 : Nat.card ((K.subgroupOf Y).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))) = 24) :
    oddCoreIn K ≤ oddCoreIn Y := by
  set π : ↥Y →* ↥Y ⧸ classicalInvolutionOddCore ↥Y := QuotientGroup.mk' _ with hπ
  set φ : ↥K →* ↥Y ⧸ classicalInvolutionOddCore ↥Y := π.comp (Subgroup.inclusion hKY) with hφ
  have hrange : φ.range = (K.subgroupOf Y).map π := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  set N : Subgroup ↥K := φ.ker with hN
  have hNmem : ∀ x : ↥K, x ∈ N ↔
      ((Subgroup.inclusion hKY x : ↥Y)) ∈ classicalInvolutionOddCore ↥Y := by
    intro x
    rw [hN, MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff _
  have hNidx : N.index = 24 := by
    rw [Subgroup.index_eq_card, ← h24, ← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hNodd : Odd (Nat.card N) := by
    let θ : ↥N →* ↥(classicalInvolutionOddCore ↥Y) :=
      ((Subgroup.inclusion hKY).comp N.subtype).codRestrict (classicalInvolutionOddCore ↥Y)
        (fun x => (hNmem x.1).mp x.2)
    have hθ : Function.Injective θ := by
      intro a b hab
      have : Subgroup.inclusion hKY a.1 = Subgroup.inclusion hKY b.1 := congrArg Subtype.val hab
      exact Subtype.ext (Subgroup.inclusion_injective hKY this)
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥Y).of_dvd_nat
      (Subgroup.card_dvd_of_injective θ hθ)
  have hNle : N ≤ classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.maximal ↥K N inferInstance hNodd
  have hOidx : (classicalInvolutionOddCore ↥K).index = 24 := by
    obtain ⟨e⟩ := hK.nonempty_equiv
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hrel : N.relIndex (classicalInvolutionOddCore ↥K) = 1 := by
    have h1 := Subgroup.relIndex_mul_index hNle
    rw [hNidx, hOidx] at h1
    omega
  have hON : classicalInvolutionOddCore ↥K ≤ N := Subgroup.relIndex_eq_one.mp hrel
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxN : x ∈ N := hON hx
  exact ⟨Subgroup.inclusion hKY x, (hNmem x).mp hxN, rfl⟩

end Image

section Layer

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_centralizingLayer_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (f : G) :
    oddCoreIn (centralizingLayer Ω {f}) ≤ CFSG.Assembly.Dichotomy.involutionOddCore f := by
  rw [involutionOddCore_eq_oddCoreIn]
  refine le_oddCoreIn_of_normalizes
    ((oddCoreIn_le _).trans (centralizingLayer_le_centralizer Ω {f}))
    (fun n hn => mem_normalizer_oddCoreIn_centralizingLayer hΩ hn) (odd_card_oddCoreIn _)

end Layer

section FourGroup

variable {G : Type} [Group G] [Finite G]

theorem exists_card_four_le_axisSub {E K : Subgroup G} (hE : ∀ x ∈ E, x * x = 1)
    (h16 : 16 ≤ Nat.card E) (hidx : (axisSub E K).relIndex E = 2) :
    ∃ F : Subgroup G, F ≤ axisSub E K ∧ Nat.card F = 4 := by
  set L : Subgroup G := axisSub E K with hL
  have hLE : L ≤ E := inf_le_left
  have hEL : Nat.card E = 2 * Nat.card L := by
    have h1 := (L.subgroupOf E).card_mul_index
    rw [Subgroup.relIndex] at hidx
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLE).toEquiv] at h1
    omega
  have hLsq : ∀ x ∈ L, x * x = 1 := fun x hx => hE x (hLE hx)
  obtain ⟨m, hm⟩ := (isPGroup_two_of_mul_self_eq_one hLsq).exists_card_eq
  have h8L : 2 ^ 2 ∣ Nat.card L := by
    rw [hm]
    refine Nat.pow_dvd_pow 2 ?_
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 2 h8L
  refine ⟨F'.map L.subtype, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hF']
    norm_num

end FourGroup

section Exact

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

theorem WeakPreFrame3.oddCore_eq_bot (Fr : WeakPreFrame3 Ω E S) (h16 : 16 ≤ Nat.card E)
    (hnc : ∀ f ∈ E, f ≠ 1 → f ∉ Subgroup.center G)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E, deltaCore F = ⊥) (hLoc : LocalLieSystems3 Ω)
    {K : Subgroup G} (hK : K ∈ S) : classicalInvolutionOddCore ↥K = ⊥ := by
  obtain ⟨hKΩ, hσ⟩ := Fr.mem_iff.mp hK
  obtain ⟨z, hz, -⟩ := hσ.member
  obtain ⟨F, hFL, hF4⟩ := exists_card_four_le_axisSub Fr.elem h16 hσ.index_two
  have hFE : F ∈ signalizerFunctorEk 2 2 E := ⟨hFL.trans inf_le_left, by simpa using hF4⟩
  have hKF : ∀ f ∈ F, K ≤ Subgroup.centralizer ({f} : Set G) := by
    intro f hf k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_axisSub_iff.mp (hFL hf)).2 k hk
  have hle : oddCoreIn K ≤ deltaCore F := by
    refine le_deltaCore fun f hf hf1 => ?_
    have hfE : f ∈ E := (hFL hf).1
    have hKm : K ∈ centralizingMembers Ω {f} := ⟨hKΩ, hKF f hf⟩
    have hKY : K ≤ centralizingLayer Ω {f} := le_centralizingLayer hKm
    have hLie := hLoc {f} (by
      rw [Set.singleton_subset_iff]
      exact hnc f hfE hf1)
    obtain ⟨ι, -, ⟨D⟩⟩ := hLie
    have hmemΦ : (K.subgroupOf (centralizingLayer Ω {f})).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {f}))) ∈
        oddQuotientFamily (restrictFamily (centralizingMembers Ω {f})
          (centralizingLayer Ω {f})) :=
      ⟨K.subgroupOf (centralizingLayer Ω {f}), ⟨K, hKm, hKY, rfl⟩, rfl⟩
    have h24 := D.card_eq _ hmemΦ
    exact (oddCoreIn_le_of_card_image_eq hKY hz h24).trans
      (oddCoreIn_centralizingLayer_le Fr.inv f)
  rw [hΔ F hFE, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle

end Exact

end CFSG.ClassicalInvolution.Q3
