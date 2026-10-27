module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Basis
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Excl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Rank
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Std
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Xfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

@[expose] def n24Conj6 (w : GL (Fin 6) (ZMod 2)) (H : Subgroup (GL (Fin 6) (ZMod 2))) :
    Subgroup (GL (Fin 6) (ZMod 2)) :=
  H.map (MulAut.conj w).toMonoidHom

theorem mem_n24Conj6 {w : GL (Fin 6) (ZMod 2)} {H : Subgroup (GL (Fin 6) (ZMod 2))}
    {x : GL (Fin 6) (ZMod 2)} : x ∈ n24Conj6 w H ↔ w⁻¹ * x * w ∈ H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have e : w⁻¹ * x * w = y := by
      rw [← hyx]
      show w⁻¹ * (w * y * w⁻¹) * w = y
      group
    rw [e]
    exact hy
  · intro h
    refine ⟨w⁻¹ * x * w, h, ?_⟩
    show w * (w⁻¹ * x * w) * w⁻¹ = x
    group

noncomputable def n24Conj6Equiv (w : GL (Fin 6) (ZMod 2))
    (H : Subgroup (GL (Fin 6) (ZMod 2))) : ↥H ≃* ↥(n24Conj6 w H) :=
  Subgroup.equivMapOfInjective H (MulAut.conj w).toMonoidHom (MulAut.conj w).injective

theorem nar24_mat_holds : Nar24Mat := by
  intro H D τ hs hnc h64 hDH hDiso hfpf hτ2 hτD hτH hcent
  have hcardD : Nat.card ↥D = 168 := by
    rw [Nat.card_congr hDiso.some.toEquiv]
    exact CFSG.ComponentClassification.GHarris.card_GL32_gh
  by_cases hτ1 : τ = 1
  ·
    subst hτ1
    have hN : (D.subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h1 := hcent (g : GL (Fin 6) (ZMod 2)) g.2 (by rw [mul_one, one_mul]) n hn
      simpa using h1
    haveI := hs
    haveI := hN
    rcases Subgroup.Normal.eq_bot_or_eq_top (D.subgroupOf H) with hb | ht
    · have hDb : D = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro d hd
        have hmem : (⟨d, hDH hd⟩ : ↥H) ∈ D.subgroupOf H := Subgroup.mem_subgroupOf.2 hd
        rw [hb, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      rw [hDb, Subgroup.card_bot] at hcardD
      omega
    · have hHD : H ≤ D := fun h hh => by
        have hmem : (⟨h, hh⟩ : ↥H) ∈ D.subgroupOf H := by rw [ht]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 hmem
      have h1 := Subgroup.card_dvd_of_le hHD
      rw [hcardD] at h1
      exact absurd (h64.trans h1) (by norm_num)
  ·
    have hτ1' : τ * τ = 1 := by rw [← pow_two]; exact hτ2
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := GL (Fin 3) (ZMod 2)) 7 (by
      rw [CFSG.ComponentClassification.GHarris.card_GL32_gh]
      norm_num)
    obtain ⟨x, hx⟩ : ∃ x : ↥D, orderOf x = 7 :=
      ⟨hDiso.some.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
    have hx7 : (x : GL (Fin 6) (ZMod 2)) ^ 7 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hx]
    have hx1 : (x : GL (Fin 6) (ZMod 2)) ≠ 1 := by
      intro h
      have h1 : orderOf (x : GL (Fin 6) (ZMod 2)) = 1 := by rw [h]; exact orderOf_one
      rw [Subgroup.orderOf_coe, hx] at h1
      omega
    have hxf := hfpf x x.2 hx7 hx1
    have hxτ : (x : GL (Fin 6) (ZMod 2)) * τ = τ * x := (hτD x x.2).symm
    obtain ⟨g, hg⟩ := n24_conj_z0 τ hτ1' (n24_rank_three τ x hτ1' hτ1 hxτ hx7 hxf)
    have hD₁iso : Nonempty (↥(n24Conj6 g D) ≃* GL (Fin 3) (ZMod 2)) :=
      ⟨(n24Conj6Equiv g D).symm.trans hDiso.some⟩
    have hD₁c : ∀ d ∈ n24Conj6 g D, d * z₀ = z₀ * d := by
      intro d hd
      rw [mem_n24Conj6] at hd
      have h1 := hτD _ hd
      rw [← hg]
      calc d * (g * τ * g⁻¹) = g * ((g⁻¹ * d * g) * τ) * g⁻¹ := by group
        _ = g * (τ * (g⁻¹ * d * g)) * g⁻¹ := by rw [← h1]
        _ = g * τ * g⁻¹ * d := by group
    obtain ⟨u, huz, hu⟩ := n24_std (n24Conj6 g D) hD₁iso hD₁c
    obtain ⟨w, hw⟩ : ∃ w : GL (Fin 6) (ZMod 2), w = u * g := ⟨_, rfl⟩
    have hwτ : w * τ * w⁻¹ = z₀ := by
      rw [hw]
      calc u * g * τ * (u * g)⁻¹ = u * (g * τ * g⁻¹) * u⁻¹ := by group
        _ = u * z₀ * u⁻¹ := by rw [hg]
        _ = z₀ := by rw [huz]; group
    have hwD : ∀ x : GL (Fin 6) (ZMod 2), x ∈ D ↔
        w * x * w⁻¹ ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range := by
      intro x
      have h1 : x ∈ D ↔ g * x * g⁻¹ ∈ n24Conj6 g D := by
        rw [mem_n24Conj6]
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e]
      rw [h1, hu, hw]
      have e : u * (g * x * g⁻¹) * u⁻¹ = u * g * x * (u * g)⁻¹ := by group
      rw [e]
    haveI : IsSimpleGroup ↥H := hs
    refine n24_excl (n24Conj6 w H) (n24Conj6Equiv w H).symm.isSimpleGroup ?_ ?_ ?_ ?_ ?_
    · intro hcomm
      apply hnc
      intro a b
      apply (n24Conj6Equiv w H).injective
      rw [map_mul, map_mul]
      exact hcomm _ _
    · rw [Nat.card_congr (n24Conj6Equiv w H).toEquiv.symm]
      exact h64
    · intro e he
      rw [mem_n24Conj6]
      apply hDH
      rw [hwD]
      have e1 : w * (w⁻¹ * e * w) * w⁻¹ = e := by group
      rw [e1]
      exact he
    · intro h hh
      rw [mem_n24Conj6] at hh ⊢
      have e1 : w⁻¹ * (z₀ * h * z₀⁻¹) * w = τ * (w⁻¹ * h * w) * τ⁻¹ := by
        rw [← hwτ]
        group
      rw [e1]
      exact hτH _ hh
    · intro c hc hcz d hd
      rw [mem_n24Conj6] at hc
      have hc0 : (w⁻¹ * c * w) * τ = τ * (w⁻¹ * c * w) := by
        have e1 : (w⁻¹ * c * w) * τ = w⁻¹ * (c * z₀) * w := by
          rw [← hwτ]
          group
        have e2 : τ * (w⁻¹ * c * w) = w⁻¹ * (z₀ * c) * w := by
          rw [← hwτ]
          group
        rw [e1, e2, hcz]
      have hd0 : w⁻¹ * d * w ∈ D := by
        rw [hwD]
        have e1 : w * (w⁻¹ * d * w) * w⁻¹ = d := by group
        rw [e1]
        exact hd
      have h3 := hcent _ hc hc0 _ hd0
      rw [hwD] at h3
      have e3 : w * ((w⁻¹ * c * w) * (w⁻¹ * d * w) * (w⁻¹ * c * w)⁻¹) * w⁻¹ = c * d * c⁻¹ := by
        group
      rw [e3] at h3
      exact h3

theorem nar24_holds : Nar24 :=
  nar24_of_mat nar24_mat_holds

end CFSG.OddStandard.HigherRank.YamadaG23
