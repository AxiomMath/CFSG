module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResI
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResC3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResE
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResH2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResHH2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLinkZ

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem false_of_resB_a7 (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)}
    (hB : BridgeB k p H P g J) (hIJ : barIn H I ≤ centralizer (J : Set (HBar H)))
    (hDS : ∀ {w : G}, (w = z ∨ w = t) → ∀ {W : Subgroup (HBar H)},
      W ≤ centralizer (barIn H (zpowers w) : Set (HBar H)) →
      W ≤ centralizer (barIn H I : Set (HBar H)) → Group.IsSolvable ↥W)
    (hDW : ∀ {w : G}, (w = z ∨ w = t) → ∀ {y : G}, y ∈ H → orderOf y = 2 → IsConj z y →
      y * w = w * y → y ≠ w →
      barIn H (zpowers y) ≤ centralizer (barIn H I : Set (HBar H)) → ¬ IsConj z (y * w))
    (hA7 : Nonempty ((↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7))) : False := by
  obtain ⟨e7⟩ := hA7
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', hM, -, hL⟩ := hB
  have := hM.normal
  have hq := hM.quasi
  have hJ : IsComponent J := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, _⟩ := hL
    exact hJ
  have hZJ := odd_card_center hL31 h hd hJ hIJ
  have hZK := LinkB.odd_center hq hL hZJ
  obtain ⟨e, ψ, hψ, hψγ, hψJ⟩ := exists_actUK hL31 h hd hJ hIJ hq hL
  set eY : (↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 7) := e.symm.trans e7 with heY
  set τ := Ivk8.autTransport (by norm_num : 5 ≤ 7) (by norm_num) eY with hτ
  have : Fact p.Prime := ⟨hM.prime⟩
  have hb : orderOf (actYHom (K := K) a) = p :=
    orderOf_eq_prime hM.actYHom_pow hM.actYHom_ne_one
  have hUH := U_le_H h hd.u
  have := hd.u.four.1
  have hsq : ∀ u : ↥(L52Two.U4 z t), u * u = 1 := fun u => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← sq]
    exact elemPow_eq_one_of_isElementaryAbelian (u : G) u.2
  set Xh : Subgroup (MulAut (↥K ⧸ center ↥K)) := P'.map (actYHom (K := K)) with hXh
  have hXp : IsPGroup p ↥Xh := hM.pgrp.map _
  have hX1 : Xh ≠ ⊥ := fun hbot => hM.actYHom_ne_one (by
    have : actYHom (K := K) a ∈ Xh := ⟨a, hM.a_mem, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this)
  have hD2 : ∀ d ∈ ψ.range, d * d = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_mul, hsq, map_one]
  have hD4 : Nat.card ψ.range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hd.u.four.2]
  have hDX : ∀ d ∈ ψ.range, ∀ x ∈ Xh, d * x * d⁻¹ ∈ Xh := by
    rintro _ ⟨u, rfl⟩ _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ, hψu⟩ := hψγ u
    rw [hψu, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨γ * x * γ⁻¹, (mem_normalizer_iff.mp hγ x).mp hx, rfl⟩
  have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
    have hdvd : p ∣ Nat.factorial 7 := by
      have h1 := orderOf_dvd_natCard (actYHom (K := K) a)
      rwa [hb, Nat.card_congr τ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h1
    have hp7 : p ≤ 7 := (hM.prime.dvd_factorial).mp hdvd
    have hp := hM.prime
    have hp2 := hM.odd
    interval_cases p <;> first | omega | norm_num at hp
  rcases hp357 with rfl | rfl | rfl
  · refine hM.false_of_hhobsAt (r := 2) (fun _ h2 => ?_) ?_
    · exact (Nat.not_even_iff_odd.mpr hZK) (even_iff_two_dvd.mpr h2)
    · rw [bAut_eq_actYHom]
      exact ResHH.hhobsAt_alt7 eY _ hb
  · obtain ⟨_, ⟨u₁, rfl⟩, hd1, hsw⟩ :=
      ResA7.exists_swap_of_four_five eY hXp hX1 hD2 hD4 hDX
    have hns := ResA7.not_isSolvable_fixed_of_isSwap eY hsw
    have hu₁1 : u₁ ≠ 1 := fun h1 => hd1 (by rw [h1, map_one])
    by_cases hu₁ : (u₁ : G) = z ∨ (u₁ : G) = t
    · obtain ⟨hN, hψu⟩ := hψJ u₁
      rw [hψu] at hns
      have hx2 : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨(u₁ : G), hUH u₁.2⟩ *
          QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨(u₁ : G), hUH u₁.2⟩ = 1 := by
        rw [← map_mul]
        have h1 : (⟨(u₁ : G), hUH u₁.2⟩ : ↥H) * ⟨(u₁ : G), hUH u₁.2⟩ = 1 := by
          have h0 : ((u₁ * u₁ : ↥(L52Two.U4 z t)) : G) = 1 := congrArg Subtype.val (hsq u₁)
          exact Subtype.ext h0
        rw [h1, map_one]
      apply not_isSolvable_inf_centralizer J e hN hx2 hZJ hns
      obtain ⟨h1, h2⟩ := inf_centralizer_le hIJ (hUH u₁.2)
      exact hDS hu₁ h1 h2
    ·
      obtain ⟨u₀, hu₀U, hu₀1, hu₀J⟩ := exists_U_mem_J hL31 h hd hJ hIJ
      set u₀' : ↥(L52Two.U4 z t) := ⟨u₀, hu₀U⟩ with hu₀'
      have hd₀i : ψ u₀' ∈ (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range := by
        obtain ⟨hN, hψu⟩ := hψJ u₀'
        rw [hψu, actJ_of_mem J hu₀J]
        exact ⟨e _, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e _).symm⟩
      have hne : (u₀ : G) ≠ u₁ := by
        intro h1
        obtain ⟨y, hy⟩ := hd₀i
        have h2 : u₀' = u₁ := Subtype.ext h1
        rw [h2] at hy
        have h3 := Ivk8.autTransport_conj (by norm_num : 5 ≤ 7) (by norm_num) eY y
        rw [hy] at h3
        obtain ⟨x₁, x₂, hx, hsw'⟩ := hsw
        have h4 := (eY y).2
        rw [← h3, hsw', Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hx] at h4
        exact absurd h4 (by decide)
      have hu₀zt : (u₀ : G) = z ∨ (u₀ : G) = t := by
        rcases (L52Two.mem_U4_iff hd.u.udata).mp hu₀U with h0 | h0 | h0 | h0
        · exact absurd (by rw [show u₀ = 1 from Subtype.ext h0, map_one]) hu₀1
        · exact Or.inl h0
        · exact Or.inr h0
        · exfalso
          rcases (L52Two.mem_U4_iff hd.u.udata).mp u₁.2 with h1 | h1 | h1 | h1
          · exact hu₁1 (Subtype.ext h1)
          · exact hu₁ (Or.inl h1)
          · exact hu₁ (Or.inr h1)
          · exact hne (h0.trans h1.symm)
      exact false_of_mem_J_a7 hL31 h hd hJ hIJ e7 hDW hu₀zt u₀.2 hu₀J hu₀1
  · exact ResA7.false_of_four_seven eY hXp hX1 hD2 hD4 hDX

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
