module

public import CFSG.GH74.GLS.Balance.PStarDefs
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem le_pPrimeCoreOf_of_normal_subnormal {X : Type} [Group X] [Finite X] {W M U : Subgroup X}
    (hMW : M ≤ W) (hMsub : (M.subgroupOf W).IsSubnormal) (hUM : U ≤ M)
    (hUn : M ≤ normalizer (U : Set X)) (hUodd : Odd (Nat.card U)) :
    U ≤ pPrimeCoreOf 2 W := by
  have hUW : U ≤ W := hUM.trans hMW
  set H : Subgroup ↥W := M.subgroupOf W with hH
  set UW : Subgroup ↥W := U.subgroupOf W with hUW'
  have hUWH : UW ≤ H := fun u hu => hUM hu
  set UH : Subgroup ↥H := UW.subgroupOf H with hUH
  have hUHnormal : UH.Normal := by
    refine ⟨fun u hu h => ?_⟩
    have hu' : ((u : ↥H) : X) ∈ U := hu
    have := (mem_normalizer_iff.mp (hUn h.2) (u : X)).mp hu'
    exact this
  have hUHodd : Odd (Nat.card UH) := by
    have e : Nat.card UH = Nat.card U := by
      rw [hUH, hUW', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUWH).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
    rw [e]; exact hUodd
  have h1 : UH ≤ pPrimeCore 2 ↥H := le_sSup ⟨hUHnormal, Nat.coprime_two_left.mpr hUHodd⟩
  have h2 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hMsub
  have h3 : UH.map H.subtype ≤ pPrimeCore 2 ↥W := (Subgroup.map_mono h1).trans h2
  have h4 : UH.map H.subtype = UW := Subgroup.map_subgroupOf_eq_of_le hUWH
  rw [h4] at h3
  intro u hu
  exact ⟨⟨u, hUW hu⟩, h3 (show (⟨u, hUW hu⟩ : ↥W) ∈ UW from hu), rfl⟩




theorem IsPStar.exists_mul_centralizer {X : Type} [Group X] [Finite X] {Y N Q : Subgroup X}
    (hY : IsPStar 2 ↥Y) (hNY : N ≤ Y) (hNn : (N.subgroupOf Y).Normal) (hQN : Q ≤ N)
    (hQ2 : IsPGroup 2 Q)
    (hQs : ∀ T : Subgroup X, T ≤ N → IsPGroup 2 T → Nat.card T ≤ Nat.card Q) :
    ∀ y ∈ Y, ∃ n ∈ N, ∃ c ∈ Y ⊓ centralizer (Q : Set X), y = n * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup ↥Y := N.subgroupOf Y with hN'
  set Q' : Subgroup ↥N' := (Q.subgroupOf Y).subgroupOf N' with hQ'
  have hQY : Q ≤ Y := hQN.trans hNY
  have hQN' : Q.subgroupOf Y ≤ N' := fun q hq => hQN hq
  have hmapQ' : Q'.map N'.subtype = Q.subgroupOf Y := Subgroup.map_subgroupOf_eq_of_le hQN'
  have hQ'2 : IsPGroup 2 Q' := by
    have h1 : IsPGroup 2 (Q.subgroupOf Y) := hQ2.comap_of_injective Y.subtype Y.subtype_injective
    exact h1.comap_of_injective N'.subtype N'.subtype_injective
  obtain ⟨S, hS⟩ := hQ'2.exists_le_sylow
  set T'' : Subgroup X := ((S : Subgroup ↥N').map N'.subtype).map Y.subtype with hT''
  have hT''N : T'' ≤ N := by
    rintro _ ⟨_, ⟨s, _, rfl⟩, rfl⟩
    exact s.2
  have hT''2 : IsPGroup 2 T'' := (S.isPGroup'.map N'.subtype).map Y.subtype
  have hQT'' : Q ≤ T'' := by
    intro q hq
    have hq' : (⟨⟨q, hQY hq⟩, hQN hq⟩ : ↥N') ∈ Q' := hq
    exact ⟨_, ⟨_, hS hq', rfl⟩, rfl⟩
  have hcard1 : Nat.card T'' ≤ Nat.card Q := hQs T'' hT''N hT''2
  have hcard2 : Nat.card Q ≤ Nat.card T'' := Subgroup.card_le_of_le hQT''
  have hT''Q : T'' = Q := (Subgroup.eq_of_le_of_card_ge hQT'' hcard1).symm
  have hSQ : (S : Subgroup ↥N').map N'.subtype = Q.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [← hT'', hT''Q, Subgroup.map_subgroupOf_eq_of_le hQY]
  have htop := hY.2 N' hNn S
  rw [hSQ] at htop
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥Y) ∈ N' ⊔ centralizer ((Q.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [htop]; exact Subgroup.mem_top _
  have : N'.Normal := hNn
  obtain ⟨n', hn', c', hc', hnc⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(n' : X), hn', (c' : X), ⟨c'.2, ?_⟩, ?_⟩
  · show (c' : X) ∈ centralizer (Q : Set X)
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : (⟨q, hQY hq⟩ : ↥Y) ∈ Q.subgroupOf Y := hq
    have := mem_centralizer_iff.mp hc' _ hq'
    exact congrArg Subtype.val this
  · exact (congrArg Subtype.val hnc).symm



omit [Finite X] in
theorem mem_sup_of_le_normalizer {N V₁ : Subgroup X} (h : V₁ ≤ normalizer (N : Set X)) {y : X} :
    y ∈ N ⊔ V₁ ↔ ∃ n ∈ N, ∃ v ∈ V₁, n * v = y := by
  constructor
  · intro hy
    rw [Subgroup.sup_eq_closure] at hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, V₁.one_mem, by simp⟩
      · exact ⟨1, N.one_mem, y, hy, by simp⟩
    · exact ⟨1, N.one_mem, 1, V₁.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨n₁, hn₁, v₁, hv₁, rfl⟩ ⟨n₂, hn₂, v₂, hv₂, rfl⟩
      refine ⟨n₁ * (v₁ * n₂ * v₁⁻¹), N.mul_mem hn₁ ?_, v₁ * v₂, V₁.mul_mem hv₁ hv₂, by group⟩
      exact (mem_normalizer_iff.mp (h hv₁) n₂).mp hn₂
    · rintro _ _ ⟨n, hn, v, hv, rfl⟩
      refine ⟨v⁻¹ * n⁻¹ * v, ?_, v⁻¹, V₁.inv_mem hv, by group⟩
      have h1 : v⁻¹ * n⁻¹ * (v⁻¹)⁻¹ ∈ N :=
        (mem_normalizer_iff.mp (h (V₁.inv_mem hv)) n⁻¹).mp (N.inv_mem hn)
      simpa using h1
  · rintro ⟨n, hn, v, hv, rfl⟩
    exact Subgroup.mul_mem_sup hn hv


end CFSG.GH74.GLS.Balance
