module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16R7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYProd

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem mem_normalizer_zpowers_of_conj {G : Type} [Group G] {g β : G}
    (h : g * β * g⁻¹ = β ∨ g * β * g⁻¹ = β⁻¹) :
    g ∈ normalizer ((zpowers β : Subgroup G) : Set G) := by
  have h1 : ∀ k : ℤ, g * β ^ k * g⁻¹ ∈ zpowers β := by
    intro k
    have : g * β ^ k * g⁻¹ = (g * β * g⁻¹) ^ k := by rw [← conj_zpow]
    rw [this]
    rcases h with h | h
    · rw [h]; exact zpow_mem (mem_zpowers β) k
    · rw [h]; exact zpow_mem (inv_mem (mem_zpowers β)) k
  have h2 : g⁻¹ * β * g ∈ zpowers β := by
    rcases h with h | h
    · have e : g * β = β * g := by
        calc g * β = (g * β * g⁻¹) * g := by group
          _ = β * g := by rw [h]
      have : g⁻¹ * β * g = β := by
        calc g⁻¹ * β * g = g⁻¹ * (β * g) := by group
          _ = g⁻¹ * (g * β) := by rw [e]
          _ = β := by group
      rw [this]; exact mem_zpowers β
    · have e1 : g⁻¹ * β⁻¹ * g = β := by
        calc g⁻¹ * β⁻¹ * g = g⁻¹ * (g * β * g⁻¹) * g := by rw [h]
          _ = β := by group
      have : g⁻¹ * β * g = β⁻¹ := by
        calc g⁻¹ * β * g = (g⁻¹ * β⁻¹ * g)⁻¹ := by group
          _ = β⁻¹ := by rw [e1]
      rw [this]; exact inv_mem (mem_zpowers β)
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact h1 k
  · intro hw
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hw
    have : w = (g⁻¹ * β * g) ^ k := by
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * β ^ k * g := by rw [← hk]
        _ = (g⁻¹ * β * g) ^ k := by
          have := conj_zpow (a := g⁻¹) (b := β) (i := k)
          simpa using this.symm
    rw [this]
    exact zpow_mem h2 k

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem exists_cent_64_v {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer ((zpowers β : Subgroup G) : Set G) ∧
      S ≤ P ∧ v ∈ P ∧ P ≤ centralizer ({v} : Set G) ∧ Nat.card ↥P = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := c.hyp.outerE.cfg
  have ht2 : t * t = 1 := hcfg.t_sq
  have hEB : ∀ w ∈ L ⊓ centralizer ({t} : Set G), ∀ s ∈ S, w * s = s * w := fun w hw s hs =>
    (mem_centralizer_iff.1 (c.EB_le_centS hw) s hs).symm
  have hvS : ∀ s ∈ S, v * s = s * v := fun s hs =>
    hEB v ⟨hD.v_L, mem_centralizer_singleton_iff.2 hD.v_t⟩ s hs
  have hv8 : orderOf v = 8 := by
    have h8 : orderOf v = 2 ^ (2 + 1) := by
      refine orderOf_eq_prime_pow (p := 2) ?_ ?_
      · intro h
        apply hcfg.t_ne
        rw [← hD.v4]
        simpa using h
      · simpa using hD.v8
    simpa using h8
  have htS : t ∈ S := c.t_mem_S
  have htv : t ∈ zpowers v := ⟨4, by simpa using hD.v4⟩
  have hSE : S ≤ centralizer ((zpowers v : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_left (show Commute v s from hvS s hs) k).eq
  have hint : ∀ w ∈ S, w ∈ zpowers v → w = 1 ∨ w = t := by
    intro w hwS hwv
    have hwL : w ∈ L := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hwv
      exact zpow_mem hD.v_L k
    exact c.hyp.wFacts.cent w hwL fun e he => (mem_centralizer_iff.1 (c.SC hwS) e he).symm
  have hcard := card_sup_commuting_two hSE hint ht2 hcfg.t_ne htS htv
  rw [Nat.card_zpowers, hv8, c.card16] at hcard
  refine ⟨S ⊔ zpowers v, IsPGroup.of_card (n := 6) (by omega), ?_, le_sup_left,
    mem_sup_right (mem_zpowers v), ?_, by omega⟩
  · refine sup_le (fun s hs => ?_) ?_
    · refine mem_normalizer_zpowers_of_conj (Or.inl ?_)
      have := c.BS β c.hyp.outerB.beta_mem s hs
      calc s * β * s⁻¹ = (β * s) * s⁻¹ := by rw [this]
        _ = β := by group
    · rw [zpowers_le]
      exact mem_normalizer_zpowers_of_conj (Or.inr hD.v_β)
  · refine sup_le (fun s hs => mem_centralizer_singleton_iff.2 (hvS s hs).symm) ?_
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
