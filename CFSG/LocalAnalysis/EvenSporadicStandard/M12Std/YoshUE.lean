module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

theorem ue_unique {Γ : Type*} [Group Γ] [Finite Γ] (S E D : Subgroup Γ) (c : Γ)
    (hES : E ≤ S) (hDS : D ≤ S)
    (hnorm : ∀ s ∈ S, ∀ x ∈ E, s * x * s⁻¹ ∈ E)
    (hcE : c ∈ E)
    (hS : Nat.card S = 1024) (hE : Nat.card E = 128) (hD : Nat.card D = 128)
    (hDsq : ∀ x ∈ D, x * x = 1 ∨ x * x = c)
    (hDcomm : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)
    (hC : ∃ s₁ ∈ S, ∃ s₂ ∈ S, ⁅s₁, s₂⁆ ∉ E)
    (hA : ∀ y ∈ S, y ∉ E → (y * y = 1 ∨ y * y = c) →
       Nat.card {x : Γ // x ∈ E ∧ (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)} ≤ 32)
    (hB : ∀ y₁ ∈ S, ∀ y₂ ∈ S, y₁ ∉ E → y₂ ∉ E →
       (y₁ * y₁ = 1 ∨ y₁ * y₁ = c) → (y₂ * y₂ = 1 ∨ y₂ * y₂ = c) →
       (∀ x ∈ E, ((⁅x, y₁⁆ = 1 ∨ ⁅x, y₁⁆ = c) ↔ (⁅x, y₂⁆ = 1 ∨ ⁅x, y₂⁆ = c))) →
       y₁⁻¹ * y₂ ∈ E) :
    D = E := by
  classical
  by_contra hne
  have hnle : ¬ D ≤ E := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hD, hE]))
  obtain ⟨y₀, hy₀D, hy₀E⟩ := SetLike.not_le_iff_exists.1 hnle
  obtain ⟨N, hNmem, hNcard⟩ : ∃ N : Subgroup S, (∀ s : S, s ∈ N ↔ (s : Γ) ∈ E) ∧
      Nat.card N = 128 := by
    refine ⟨E.subgroupOf S, fun s => Subgroup.mem_subgroupOf, ?_⟩
    rw [← hE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [hNmem] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hV : Nat.card (S ⧸ N) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hS, hNcard] at h
    omega
  let π : S →* S ⧸ N := QuotientGroup.mk' N
  have hπ : ∀ s : S, π s = 1 ↔ (s : Γ) ∈ E := fun s =>
    (QuotientGroup.eq_one_iff s).trans (hNmem s)
  let f : D →* S ⧸ N := π.comp (Subgroup.inclusion hDS)
  have hf : ∀ d : D, f d = 1 ↔ (d : Γ) ∈ E := fun d => hπ (Subgroup.inclusion hDS d)
  have hkr := Subgroup.card_ker_mul_card_range f
  rw [hD] at hkr
  have hrdvd : Nat.card f.range ∣ 8 := by
    have h := Subgroup.card_subgroup_dvd_card f.range
    rwa [hV] at h
  have hι : ∀ y ∈ D, ∃ ι : f.ker → {x : Γ // x ∈ E ∧ (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)},
      Function.Injective ι ∧ ∀ d, (ι d : Γ) = d.1.1 := by
    intro y hy
    refine ⟨fun d => ⟨d.1.1, (hf d.1).1 (MonoidHom.mem_ker.1 d.2),
      hDcomm _ d.1.2 y hy⟩, fun d d' h => ?_, fun d => rfl⟩
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hker_le : Nat.card f.ker ≤ 32 := by
    obtain ⟨ι, hιinj, -⟩ := hι y₀ hy₀D
    exact (Nat.card_le_card_of_injective ι hιinj).trans
      (hA y₀ (hDS hy₀D) hy₀E (hDsq y₀ hy₀D))
  have hr4 : 4 ≤ Nat.card f.range := by
    by_contra h
    have h3 : Nat.card f.range ≤ 3 := by omega
    have := Nat.mul_le_mul hker_le h3
    omega
  have hrle : Nat.card f.range ≤ 8 := Nat.le_of_dvd (by omega) hrdvd
  have hr : Nat.card f.range = 4 ∨ Nat.card f.range = 8 := by
    have key : ∀ r : ℕ, r ≤ 8 → r ∣ 8 → 4 ≤ r → r = 4 ∨ r = 8 := by decide
    exact key _ hrle hrdvd hr4
  rcases hr with hr4' | hr8
  ·
    have hk32 : Nat.card f.ker = 32 := by
      rw [hr4'] at hkr
      omega
    have hQ : ∀ y ∈ D, y ∉ E → ∀ x ∈ E, ((⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c) ↔ x ∈ D) := by
      intro y hyD hyE x hxE
      obtain ⟨ι, hιinj, hιval⟩ := hι y hyD
      have hbij : Function.Bijective ι := hιinj.bijective_of_nat_card_le
        (by rw [hk32]; exact hA y (hDS hyD) hyE (hDsq y hyD))
      refine ⟨fun hx => ?_, fun hx => hDcomm x hx y hyD⟩
      obtain ⟨d, hd⟩ := hbij.2 ⟨x, hxE, hx⟩
      have h1 : d.1.1 = x := by rw [← hιval d, hd]
      rw [← h1]
      exact d.1.2
    have hex : ∃ d₂ : D, f d₂ ≠ 1 ∧ f d₂ ≠ f ⟨y₀, hy₀D⟩ := by
      by_contra hcon
      push Not at hcon
      have hsub : (f.range : Set (S ⧸ N)) ⊆ {1, f ⟨y₀, hy₀D⟩} := by
        rintro _ ⟨d, rfl⟩
        by_cases h1 : f d = 1
        · exact Or.inl h1
        · exact Or.inr (hcon d h1)
      have h2 : ({1, f ⟨y₀, hy₀D⟩} : Set (S ⧸ N)).ncard ≤ 2 := by
        calc _ ≤ ({f ⟨y₀, hy₀D⟩} : Set (S ⧸ N)).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      have h3 := (Set.ncard_le_ncard hsub).trans h2
      have h4 : (f.range : Set (S ⧸ N)).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hr4'
      omega
    obtain ⟨d₂, hd₂1, hd₂2⟩ := hex
    have hy₂E : (d₂ : Γ) ∉ E := fun h => hd₂1 ((hf d₂).2 h)
    have hy₁₂ : y₀⁻¹ * (d₂ : Γ) ∉ E := by
      intro h
      apply hd₂2
      have h' := (hf (⟨y₀, hy₀D⟩⁻¹ * d₂)).2 (by simpa using h)
      rw [map_mul, map_inv, inv_mul_eq_one] at h'
      exact h'.symm
    exact hy₁₂ (hB y₀ (hDS hy₀D) d₂ (hDS d₂.2) hy₀E hy₂E (hDsq y₀ hy₀D) (hDsq d₂ d₂.2)
      (fun x hx => (hQ y₀ hy₀D hy₀E x hx).trans (hQ d₂ d₂.2 hy₂E x hx).symm))
  ·
    have htop : f.range = ⊤ :=
      Subgroup.eq_top_of_card_eq f.range (by rw [hr8, hV])
    have hsurj : ∀ s : S, ∃ d : D, f d = π s := fun s => by
      have : π s ∈ f.range := by
        rw [htop]
        exact Subgroup.mem_top _
      exact MonoidHom.mem_range.1 this
    obtain ⟨s₁, hs₁, s₂, hs₂, hcomm⟩ := hC
    obtain ⟨d₁, hd₁⟩ := hsurj ⟨s₁, hs₁⟩
    obtain ⟨d₂, hd₂⟩ := hsurj ⟨s₂, hs₂⟩
    apply hcomm
    have hmem : ((⁅d₁, d₂⁆ : D) : Γ) ∈ E := by
      have hc : ((⁅d₁, d₂⁆ : D) : Γ) = ⁅(d₁ : Γ), (d₂ : Γ)⁆ := rfl
      rw [hc]
      rcases hDcomm d₁ d₁.2 d₂ d₂.2 with h | h
      · rw [h]
        exact E.one_mem
      · rw [h]
        exact hcE
    have h1 : π ⁅(⟨s₁, hs₁⟩ : S), ⟨s₂, hs₂⟩⁆ = 1 :=
      calc π ⁅(⟨s₁, hs₁⟩ : S), ⟨s₂, hs₂⟩⁆
          = ⁅π ⟨s₁, hs₁⟩, π ⟨s₂, hs₂⟩⁆ := map_commutatorElement π _ _
        _ = ⁅f d₁, f d₂⁆ := by rw [hd₁, hd₂]
        _ = f ⁅d₁, d₂⁆ := (map_commutatorElement f d₁ d₂).symm
        _ = 1 := (hf _).2 hmem
    exact (hπ _).1 h1

end CFSG.EvenSporadicStandard.M12Std.Yosh
