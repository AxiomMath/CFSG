module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalTwisted
public import CFSG.LieType.Chevalley.RootLocalComponentFree

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley Subgroup

@[expose] def CentralizerOTwoFree (C : Type*) [Group C] : Prop :=
  ∀ S : Subgroup C, Odd (Nat.card S) → ∀ N : Subgroup C,
    N ≤ centralizer (S : Set C) → (N.subgroupOf (centralizer (S : Set C))).Normal →
      IsPGroup 2 N → N = ⊥

theorem centralizerOTwoFree_of_subgroup {M : Type*} [Group M] (G : Subgroup M)
    (h : ∀ S : Subgroup M, S ≤ G → Odd (Nat.card S) → ∀ N : Subgroup M,
      N ≤ G ⊓ centralizer (S : Set M) → (N.subgroupOf (G ⊓ centralizer (S : Set M))).Normal →
        IsPGroup 2 N → N = ⊥) :
    CentralizerOTwoFree ↥G := by
  intro S hS N hNC hNn hN2
  have hS₀G : S.map G.subtype ≤ G := map_subtype_le S
  have hS₀ : Odd (Nat.card (S.map G.subtype)) := by
    rwa [Subgroup.card_map_of_injective G.subtype_injective]
  have hN₀C : N.map G.subtype ≤ G ⊓ centralizer ((S.map G.subtype : Subgroup M) : Set M) := by
    rintro _ ⟨n, hn, rfl⟩
    refine mem_inf.2 ⟨n.2, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 (hNC hn) s hs)
  have hCN := (normal_subgroupOf_iff_le_normalizer hNC).1 hNn
  have hCN₀ : G ⊓ centralizer ((S.map G.subtype : Subgroup M) : Set M) ≤
      normalizer ((N.map G.subtype : Subgroup M) : Set M) :=
    le_normalizer_of_conj_mem fun c hc y hy => by
      obtain ⟨n, hn, rfl⟩ := hy
      obtain ⟨hcG, hcS⟩ := mem_inf.1 hc
      have hc' : (⟨c, hcG⟩ : G) ∈ centralizer (S : Set G) :=
        mem_centralizer_iff.2 fun s hs => Subtype.ext (mem_centralizer_iff.1 hcS s ⟨s, hs, rfl⟩)
      exact ⟨_, (mem_normalizer_iff.1 (hCN hc') n).1 hn, rfl⟩
  have h0 := h _ hS₀G hS₀ _ hN₀C ((normal_subgroupOf_iff_le_normalizer hN₀C).2 hCN₀)
    (hN2.map _)
  rw [eq_bot_iff]
  intro n hn
  have h1 : (n : M) ∈ N.map G.subtype := ⟨n, hn, rfl⟩
  rw [h0, mem_bot] at h1
  exact mem_bot.2 (Subtype.ext h1)

variable {K : Type} [Field K]

theorem centralizerOTwoFree_adjointGroup
    [Finite K] [CharP K 2] {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    CentralizerOTwoFree ↥(adjointGroup τ K) :=
  centralizerOTwoFree_of_subgroup _ fun _ hSG hS _ hNC hNn hN2 =>
    eq_bot_of_normal_centralizer hτ hSG hS hNC hNn hN2

theorem centralizerOTwoFree_graphFixedRootGroupE6
    [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) :
    CentralizerOTwoFree ↥(graphFixedRootGroup .E6 K σ.toRingHom) :=
  centralizerOTwoFree_of_subgroup _ fun _ hSG hS _ hNC hNn hN2 =>
    eq_bot_of_normal_centralizer_twistedE6 σ hσ hSG hS hNC hNn hN2

theorem charTwo_of_involution
    [Finite K] [CharP K 2] (D : RootWeightDatum K)
    {x : D.group} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    CFSG.IsCharacteristicP 2 ↥(centralizer ({x} : Set D.group)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (zpowers x) := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hx : x ^ 2 = 1 := by rw [sq]; exact hx2
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hQ : zpowers x ≠ ⊥ := fun h => hx1 (zpowers_eq_bot.1 h)
  have hH : centralizer ({x} : Set D.group) = centralizer (zpowers x : Set D.group) := by
    rw [zpowers_eq_closure, centralizer_closure]
  exact (D.defining_characteristic_root_local_groups_component_free 2 _ hQ2 hQ _
    (Or.inr hH)).1

end CFSG.LieType.Chevalley.EvenOddRadical
