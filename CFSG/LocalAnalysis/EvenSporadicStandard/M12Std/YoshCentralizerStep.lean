module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshInput
import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshCentralQuotient
import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshExistsE
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

structure CentralizerQuotientOut (G : Type) [Group G] (c : G) : Prop where
  center_le : ∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)),
    (z : G) = 1 ∨ (z : G) = c
  perfect : commutator ↥(Subgroup.centralizer ({c} : Set G)) = ⊤
  card_center : Nat.card (Subgroup.center ↥(Subgroup.centralizer ({c} : Set G))) = 2
  fusionSimple : CFSG.EvenSporadicStandard.M12Std.FusionSimple
    (↥(Subgroup.centralizer ({c} : Set G)) ⧸ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)))
  exists_E : ∃ E' : Subgroup (↥(Subgroup.centralizer ({c} : Set G)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({c} : Set G))),
    (∀ x ∈ E', x * x = 1) ∧ Nat.card E' = 2 ^ 6 ∧
      Nat.card (Subgroup.normalizer (SetLike.coe E')) = 2 ^ 6 * 168 ∧ ¬ E'.Normal ∧
      Nonempty (↥(Subgroup.normalizer (E' : Set _)) ⧸
        E'.subgroupOf (Subgroup.normalizer (E' : Set _)) ≃* GL (Fin 3) (ZMod 2))

private theorem eq_bot_of_normal_odd {G : Type*} [Group G] (c : G)
    (hO : ∀ Q : Subgroup G, (∀ q ∈ Q, q * c = c * q) →
      (∀ g : G, g * c = c * g → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) → Odd (Nat.card Q) → Q = ⊥)
    (Q : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) [hQ : Q.Normal]
    (hodd : Odd (Nat.card Q)) : Q = ⊥ := by
  refine (Subgroup.map_eq_bot_iff_of_injective Q (Subgroup.subtype_injective _)).1
    (hO _ ?_ ?_ ?_)
  · rintro _ ⟨q, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 q.2
  · rintro g hg _ ⟨q, hq, rfl⟩
    exact ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 hg⟩ * q *
      ⟨g, Subgroup.mem_centralizer_singleton_iff.2 hg⟩⁻¹, hQ.conj_mem q hq _, rfl⟩
  · rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

private theorem commutator_subgroupOf_eq_self {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hperf : ⁅H, H⁆ = H) :
    ⁅H.subgroupOf K, H.subgroupOf K⁆ = H.subgroupOf K := by
  refine Subgroup.map_injective (Subgroup.subtype_injective K) ?_
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHK, hperf]

theorem centralizer_quotient_out {G : Type} [Group G] [Finite G] (c : G)
    (L S E N : Subgroup G) (y₀ h : G)
    (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hS : Nat.card S = 2 ^ (Nat.card G).factorization 2) (hSL : S ≤ L)
    (hLc : ∀ ℓ ∈ L, ℓ * c = c * ℓ) (hLperf : ⁅L, L⁆ = L)
    (hLS : ∀ p : G, p * c = c * p → (∀ s ∈ S, p * s * p⁻¹ ∈ S) → p ∈ L)
    (hO : ∀ Q : Subgroup G, (∀ q ∈ Q, q * c = c * q) →
      (∀ g : G, g * c = c * g → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) → Odd (Nat.card Q) → Q = ⊥)
    (hcE : c ∈ E) (hEsq : ∀ y ∈ E, y * y = 1 ∨ y * y = c)
    (hL : L = Subgroup.normalizer (E : Set G))
    (hEcard : Nat.card E = 2 ^ 7) (hLcard : Nat.card L = 2 ^ 7 * 168)
    [(E.subgroupOf L).Normal]
    (hgl : Nonempty (↥L ⧸ E.subgroupOf L ≃* GL (Fin 3) (ZMod 2)))
    (hZLE : ∀ z ∈ L, (∀ ℓ ∈ L, ⁅z, ℓ⁆ ∈ E) → z ∈ E)
    (hNL : N ≤ L) (hy₀N : y₀ ∈ N)
    (hZN : ∀ y ∈ E, (∀ n ∈ N, ⁅y, n⁆ = 1 ∨ ⁅y, n⁆ = c) →
      y = 1 ∨ y = c ∨ y = y₀ ∨ y = y₀ * c)
    (hhc : h * c = c * h) (hy₀h : ⁅y₀, h⁆ ≠ 1 ∧ ⁅y₀, h⁆ ≠ c)
    (hnot : ∃ x ∈ E, h⁻¹ * x * h ∉ E) :
    CentralizerQuotientOut G c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemC : ∀ g : G, g ∈ Subgroup.centralizer ({c} : Set G) ↔ g * c = c * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := fun ℓ hℓ => (hmemC ℓ).2 (hLc ℓ hℓ)
  have hSC : S ≤ Subgroup.centralizer ({c} : Set G) := hSL.trans hLC
  have hEL : E ≤ L := by
    rw [hL]
    exact Subgroup.le_normalizer
  have hNC : N ≤ Subgroup.centralizer ({c} : Set G) := hNL.trans hLC
  let cC : ↥(Subgroup.centralizer ({c} : Set G)) := ⟨c, (hmemC c).2 rfl⟩
  let y₀C : ↥(Subgroup.centralizer ({c} : Set G)) := ⟨y₀, hNC hy₀N⟩
  let hC : ↥(Subgroup.centralizer ({c} : Set G)) := ⟨h, (hmemC h).2 hhc⟩
  have hcZ : cC ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hcC2 : cC * cC = 1 := Subtype.ext hc2
  have hcC1 : cC ≠ 1 := fun h1 => hc1 (congrArg Subtype.val h1)
  have hOC : ∀ Q : Subgroup ↥(Subgroup.centralizer ({c} : Set G)), Q.Normal →
      Odd (Nat.card Q) → Q = ⊥ := fun Q hQ hodd => by
    haveI := hQ
    exact eq_bot_of_normal_odd c hO Q hodd
  have hSyl : Nat.card (S.subgroupOf (Subgroup.centralizer ({c} : Set G))) =
      2 ^ (Nat.card ↥(Subgroup.centralizer ({c} : Set G))).factorization 2 :=
    Sylow.card_eq_multiplicity ((Sylow.ofCard S hS).subtype hSC)
  have hperf : commutator ↥(Subgroup.centralizer ({c} : Set G)) = ⊤ := by
    refine commutator_eq_top_of_normalizer_le (S.subgroupOf _) (L.subgroupOf _) hSyl
      (Subgroup.subgroupOf_mono _ hSL) (commutator_subgroupOf_eq_self hLC hLperf) fun p hp => ?_
    refine Subgroup.mem_subgroupOf.2 (hLS p ((hmemC p).1 p.2) fun s hs => ?_)
    exact Subgroup.mem_subgroupOf.1
      ((Subgroup.mem_normalizer_iff.1 hp ⟨s, hSC hs⟩).1 (Subgroup.mem_subgroupOf.2 hs))
  have hZLEC : ∀ z ∈ L.subgroupOf (Subgroup.centralizer ({c} : Set G)),
      (∀ ℓ ∈ L.subgroupOf (Subgroup.centralizer ({c} : Set G)),
        ⁅z, ℓ⁆ ∈ E.subgroupOf (Subgroup.centralizer ({c} : Set G))) →
      z ∈ E.subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    intro z hz hzℓ
    refine Subgroup.mem_subgroupOf.2 (hZLE z (Subgroup.mem_subgroupOf.1 hz) fun ℓ hℓ => ?_)
    exact Subgroup.mem_subgroupOf.1 (hzℓ ⟨ℓ, hLC hℓ⟩ (Subgroup.mem_subgroupOf.2 hℓ))
  have hZNC : ∀ y ∈ E.subgroupOf (Subgroup.centralizer ({c} : Set G)),
      (∀ n ∈ N.subgroupOf (Subgroup.centralizer ({c} : Set G)), ⁅y, n⁆ = 1 ∨ ⁅y, n⁆ = cC) →
      y = 1 ∨ y = cC ∨ y = y₀C ∨ y = y₀C * cC := by
    intro y hy hyn
    have key := hZN y (Subgroup.mem_subgroupOf.1 hy) fun n hn => by
      rcases hyn ⟨n, hNC hn⟩ (Subgroup.mem_subgroupOf.2 hn) with h1 | h1
      · exact Or.inl (congrArg Subtype.val h1)
      · exact Or.inr (congrArg Subtype.val h1)
    rcases key with k | k | k | k
    · exact Or.inl (Subtype.ext k)
    · exact Or.inr (Or.inl (Subtype.ext k))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext k)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext k)))
  have hsecond := second_center_le cC (L.subgroupOf _) (S.subgroupOf _) (E.subgroupOf _)
    (N.subgroupOf _) y₀C hC hcZ hcC2 hcC1 hOC hSyl (Subgroup.subgroupOf_mono _ hSL)
    (Subgroup.mem_subgroupOf.2 hcE) (Subgroup.subgroupOf_mono _ hEL) hZLEC hZNC
    ⟨fun h1 => hy₀h.1 (congrArg Subtype.val h1), fun h1 => hy₀h.2 (congrArg Subtype.val h1)⟩
  have hcenter : ∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)),
      (z : G) = 1 ∨ (z : G) = c := by
    intro z hz
    have hz' : z = 1 ∨ z = cC := hsecond z fun y => Or.inl
      (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz y).symm)
    rcases hz' with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  have hZZ : ∀ z : ↥(Subgroup.centralizer ({c} : Set G)),
      (∀ y : ↥(Subgroup.centralizer ({c} : Set G)),
        ⁅z, y⁆ ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G))) →
      z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)) := by
    intro z hz
    have hz' : z = 1 ∨ z = cC := hsecond z fun y => by
      rcases hcenter _ (hz y) with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    rcases hz' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hcZ
  obtain ⟨x, hx, hxn⟩ := hnot
  have hnot' : ∃ k : G, k * c = c * k ∧ ∃ x ∈ E, k * x * k⁻¹ ∉ E :=
    ⟨h⁻¹, (show Commute h c from hhc).inv_left, x, hx, by rwa [inv_inv]⟩
  have hZ2 := card_center_centralizer_eq_two c hc2 hc1 hcenter
  exact ⟨hcenter, hperf, hZ2, fusionSimple_quotient hperf hOC hZ2 hZZ,
    exists_E_quotient c E L hc2 hc1 hcE hEsq hcenter hL hLc hEcard hLcard hnot' hgl⟩

end CFSG.EvenSporadicStandard.M12Std.Yosh
