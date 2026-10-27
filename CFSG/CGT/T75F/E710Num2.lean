module

public import CFSG.CGT.T75F.E710Num1
public import CFSG.CGT.T75F.E710QuotCores

public section

namespace CFSG.CGT.T75F

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

theorem exists_torus_generator {K : Type} [Group K] [Finite K]
    (hK : IsBenderGroup K) (Q : Sylow 2 K) :
    ∃ (q' : ℕ) (δ : K), 4 ≤ q' ∧ Nat.card (Subgroup.center (Q : Subgroup K)) = q' ∧
      (∀ g ∈ Subgroup.zpowers δ, g ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K)) ∧
      ∀ ω₁ ω₂ : K, (ω₁ ∈ Q ∧ ∀ y ∈ Q, Commute y ω₁) → ω₁ ≠ 1 →
        (ω₂ ∈ Q ∧ ∀ y ∈ Q, Commute y ω₂) → ω₂ ≠ 1 → ∃ i : ℕ, δ ^ i * ω₁ * (δ ^ i)⁻¹ = ω₂ := by
  obtain ⟨q', k, hBB, hq4, -⟩ := IsBenderGroup.exists_fusionBenderBorel hK
  obtain ⟨-, ⟨D', hcyc, -, -, hsup⟩, -, hcard, -⟩ := hBB Q
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hDle : D' ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := hsup ▸ le_sup_right
  have hzle : Subgroup.zpowers (g : K) ≤ D' := (Subgroup.zpowers_le).2 g.2
  refine ⟨q', (g : K), hq4, hcard, fun x hx => hDle (hzle hx), ?_⟩
  intro ω₁ ω₂ hω₁ hω₁1 hω₂ hω₂1
  obtain ⟨n, hn, hconj⟩ := IsBenderGroup.exists_normalizer_conj hK Q hω₁ hω₁1 hω₂ hω₂1
  have hn' : n ∈ D' ⊔ (Q : Subgroup K) := by rw [sup_comm, hsup]; exact hn
  obtain ⟨d, hd, u, hu, rfl⟩ := CFSG.Walter.mem_sup_of_le_normalizer hDle hn'
  have hcomm : u * ω₁ = ω₁ * u := (hω₁.2 u hu).eq
  have hd2 : d * ω₁ * d⁻¹ = ω₂ := by
    rw [← hconj]
    calc d * ω₁ * d⁻¹ = d * (ω₁ * u) * u⁻¹ * d⁻¹ := by group
      _ = d * (u * ω₁) * u⁻¹ * d⁻¹ := by rw [hcomm]
      _ = d * u * ω₁ * (d * u)⁻¹ := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨d, hd⟩)
  have hkd : (g : K) ^ k = d := by
    have := congrArg Subtype.val hk
    simpa using this
  have hpos : (0 : ℤ) < (orderOf (g : K) : ℤ) := by
    exact_mod_cast orderOf_pos (g : K)
  refine ⟨(k % (orderOf (g : K) : ℤ)).toNat, ?_⟩
  have h1 : (g : K) ^ (k % (orderOf (g : K) : ℤ)) = d := by rw [zpow_mod_orderOf, hkd]
  have h2 : (g : K) ^ ((k % (orderOf (g : K) : ℤ)).toNat) = d := by
    rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k hpos.ne')]
  rw [h2]
  exact hd2

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

structure Torus710 (M : Subgroup X) (q' : ℕ) (δ : X ⧸ Subgroup.center X) : Prop where
  four_le : 4 ≤ q'
  card : Nat.card (Mhat M) = q'
  normalizes : ∀ i : ℕ, ∀ ω ∈ Mhat M, δ ^ i * ω * (δ ^ i)⁻¹ ∈ Mhat M
  trans : ∀ ω₁ ∈ Mhat M, ω₁ ≠ 1 → ∀ ω₂ ∈ Mhat M, ω₂ ≠ 1 → ∃ i : ℕ, δ ^ i * ω₁ * (δ ^ i)⁻¹ = ω₂

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem mem_Mhat_iff (hB : IsBenderGroup (X ⧸ Subgroup.center X)) (S : Sylow 2 X) (hMS : M ≤ S)
    {ω : X ⧸ Subgroup.center X} :
    ω ∈ Mhat M ↔ ω ∈ (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) ∧
      ∀ y ∈ (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)), Commute y ω := by
  have hψ : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  let Ŝ : Sylow 2 (X ⧸ Subgroup.center X) := S.mapSurjective hψ
  have hŜ : (Ŝ : Subgroup (X ⧸ Subgroup.center X)) =
      (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) := Sylow.coe_mapSurjective hψ S
  constructor
  · intro hω
    have hωŜ : ω ∈ (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) := by
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hω
      exact Subgroup.mem_map.2 ⟨m, hMS hm, rfl⟩
    refine ⟨hωŜ, fun y hy => ?_⟩
    have hωŜ' : ω ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) := by rw [hŜ]; exact hωŜ
    have hy' : y ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) := by rw [hŜ]; exact hy
    exact (IsBenderGroup.commute_of_mul_self_eq_one hB Ŝ hωŜ' (h.Mhat_sq hω) y hy').symm
  · rintro ⟨hωŜ, hc⟩
    by_cases hω1 : ω = 1
    · rw [hω1]; exact Subgroup.one_mem _
    have hωŜ' : ω ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) := by rw [hŜ]; exact hωŜ
    have hω2 : ω * ω = 1 := by
      refine IsBenderGroup.mul_self_eq_one_of_commute hB Ŝ hωŜ' fun y hy => ?_
      have hy1 : y ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) := hy
      rw [hŜ] at hy1
      exact (hc y hy1).symm
    obtain ⟨β, -, hβM, hβ⟩ := h.exists_delta_of_involution hB S hMS hωŜ hω2 hω1
    exact Subgroup.mem_map.2 ⟨β, hβM, hβ⟩

theorem exists_torus (hB : IsBenderGroup (X ⧸ Subgroup.center X)) :
    ∃ (q' : ℕ) (δ : X ⧸ Subgroup.center X), Torus710 M q' δ := by
  obtain ⟨S, hMS⟩ := h.exists_sylow
  have hψ : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  let Ŝ : Sylow 2 (X ⧸ Subgroup.center X) := S.mapSurjective hψ
  have hŜ : (Ŝ : Subgroup (X ⧸ Subgroup.center X)) =
      (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) := Sylow.coe_mapSurjective hψ S
  have hmem : ∀ ω : X ⧸ Subgroup.center X, ω ∈ Mhat M ↔
      ω ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) ∧
        ∀ y ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)), Commute y ω := by
    intro ω
    rw [hŜ]
    exact h.mem_Mhat_iff hB S hMS
  obtain ⟨q', δ, hq4, hcard, hnorm, htrans⟩ := exists_torus_generator hB Ŝ
  refine ⟨q', δ, ⟨hq4, ?_, ?_, ?_⟩⟩
  ·
    rw [← hcard]
    have hz : ∀ z : ↥(Subgroup.center (Ŝ : Subgroup (X ⧸ Subgroup.center X))),
        ∀ y ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)),
        Commute y (((z : ↥(Ŝ : Subgroup (X ⧸ Subgroup.center X))) : X ⧸ Subgroup.center X)) := by
      intro z y hy
      have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    refine Nat.card_congr ?_
    exact
      { toFun := fun ω => ⟨⟨(ω : X ⧸ Subgroup.center X), ((hmem _).1 ω.2).1⟩,
          Subgroup.mem_center_iff.2 fun g => Subtype.ext ((((hmem _).1 ω.2).2 g g.2).eq)⟩
        invFun := fun z => ⟨((z : ↥(Ŝ : Subgroup (X ⧸ Subgroup.center X))) :
          X ⧸ Subgroup.center X), (hmem _).2 ⟨(z : ↥(Ŝ : Subgroup (X ⧸ Subgroup.center X))).2,
            hz z⟩⟩
        left_inv := fun ω => rfl
        right_inv := fun z => rfl }
  · intro i ω hω
    have hg := hnorm (δ ^ i) ((Subgroup.zpowers δ).pow_mem (Subgroup.mem_zpowers δ) i)
    obtain ⟨hωŜ, hωc⟩ := (hmem ω).1 hω
    refine (hmem _).2 ⟨(Subgroup.mem_normalizer_iff.1 hg ω).1 hωŜ, fun y hy => ?_⟩
    have hy' : (δ ^ i)⁻¹ * y * (δ ^ i)⁻¹⁻¹ ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) :=
      (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) y).1 hy
    have hc := (hωc _ hy').symm.eq
    rw [inv_inv] at hy'
    show y * (δ ^ i * ω * (δ ^ i)⁻¹) = δ ^ i * ω * (δ ^ i)⁻¹ * y
    rw [inv_inv] at hc
    calc y * (δ ^ i * ω * (δ ^ i)⁻¹)
        = δ ^ i * (((δ ^ i)⁻¹ * y * δ ^ i) * ω) * (δ ^ i)⁻¹ := by group
      _ = δ ^ i * (ω * ((δ ^ i)⁻¹ * y * δ ^ i)) * (δ ^ i)⁻¹ := by rw [hc]
      _ = δ ^ i * ω * (δ ^ i)⁻¹ * y := by group
  · intro ω₁ hω₁ hω₁1 ω₂ hω₂ hω₂1
    exact htrans ω₁ ω₂ ((hmem _).1 hω₁) hω₁1 ((hmem _).1 hω₂) hω₂1

end Endgame710

end CFSG.CGT.T75F
