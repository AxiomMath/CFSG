module

public import CFSG.ClassicalInvolution.Q3.Q3ZBLoc
public import CFSG.ClassicalInvolution.Q3.Q3ZBModelQ
public import CFSG.ClassicalInvolution.Q3.WeakBalance

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
  CFSG.ClassicalInvolution.Q3.Q3ZA CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane IsHyperbolicPlane
  longBlock planeGroup_stdPlane longInv isHyperbolicPlane_stdPlane)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

section Hub

variable {G : Type} [Group G] {K : Subgroup G} {M : Subgroup G} {Λ : StatedSp 2 F3 →* G}

theorem odd_orderOf_of_cube {H : Type*} [Group H] {x : H} (h : x * x * x = 1) :
    Odd (orderOf x) := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact h)
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h2 | h2 <;> rw [h2] <;> decide

theorem IsHubLayer.mem_plane1 (hΛ : IsHubLayer (conjClass3 K) M Λ) :
    (planeGroup (stdPlane F3 2 1)).map Λ ∈ conjClass3 K := by
  obtain ⟨y, -, hy⟩ := map_planeGroup_eq_conj Λ (isHyperbolicPlane_stdPlane (K := F3) (n := 2) 1)
  rw [hy]
  exact conjInvariant_conjClass3 K y _ hΛ.mem_plane

theorem IsHubLayer.map_Qexp_le_locN (hΛ : IsHubLayer (conjClass3 K) M Λ) :
    Qexp.map Λ ≤ locN K (Λ tHub) := by
  have ha : ∀ y, Λ (longBlock F3 2 1 y) ∈ locN K (Λ tHub) := by
    intro y
    refine le_locN (hΛ.mem_plane1) ?_ ⟨longBlock F3 2 1 y, ?_, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, tHub, ← map_mul, ← map_mul,
        Q3Z.commutes_planeGroup_stdPlane _ (by rw [planeGroup_stdPlane]; exact ⟨uSL, rfl⟩) s hs]
    · rw [planeGroup_stdPlane]
      exact ⟨y, rfl⟩
  have hle : Qexp ≤ (locN K (Λ tHub)).comap Λ := by
    refine Qexp_le_of_conj (fun y => ha y) (fun c hc y => ?_)
    have hcomm : Λ c ∈ Subgroup.centralizer ({Λ tHub} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        mem_DHub.1 hc]
    have := conj_mem_locN hcomm (ha y)
    simpa using this
  intro x ⟨q, hq, hx⟩
  rw [← hx]
  exact hle hq

theorem IsHubLayer.map_DHub_le_locN (hΛ : IsHubLayer (conjClass3 K) M Λ)
    (hz : Λ (longInv F3 2 0) ∈ locN K (Λ tHub)) : DHub.map Λ ≤ locN K (Λ tHub) := by
  have ha : ∀ y, Λ (longBlock F3 2 1 y) ∈ locN K (Λ tHub) := by
    intro y
    refine le_locN (hΛ.mem_plane1) ?_ ⟨longBlock F3 2 1 y, ?_, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, tHub, ← map_mul, ← map_mul,
        Q3Z.commutes_planeGroup_stdPlane _ (by rw [planeGroup_stdPlane]; exact ⟨uSL, rfl⟩) s hs]
    · rw [planeGroup_stdPlane]
      exact ⟨y, rfl⟩
  have hle : DHub ≤ (locN K (Λ tHub)).comap Λ := by
    refine DHub_le_of_conj (fun y => ha y) (fun c hc y => ?_) hz
    have hcomm : Λ c ∈ Subgroup.centralizer ({Λ tHub} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_DHub.1 hc]
    have := conj_mem_locN hcomm (ha y)
    simpa using this
  rintro x ⟨q, hq, rfl⟩
  exact hle hq

theorem conj_map_Qexp_mem (hΛ : Function.Injective Λ) {g : G}
    (hg : ∀ s, g * Λ s * g⁻¹ ∈ Λ.range) (hg' : ∀ s, g⁻¹ * Λ s * g ∈ Λ.range)
    (hga : g * Λ tHub = Λ tHub * g) {q : StatedSp 2 F3} (hq : q ∈ Qexp) :
    g * Λ q * g⁻¹ ∈ Qexp.map Λ := by
  let S : Subgroup (StatedSp 2 F3) := (conjSub g (Qexp.map Λ)).comap Λ
  have hQcomm : ∀ q' ∈ Qexp, Λ q' * Λ tHub = Λ tHub * Λ q' := fun q' hq' => by
    rw [← map_mul, ← map_mul, mem_DHub.1 (Qexp_le_DHub hq')]
  have hSD : S ≤ DHub := by
    rintro s ⟨x, ⟨q', hq', rfl⟩, hx⟩
    rw [mem_DHub]
    apply hΛ
    rw [map_mul, map_mul, ← hx]
    have hc : Commute (g * Λ q' * g⁻¹) (Λ tHub) :=
      ((Commute.mul_left (show Commute g (Λ tHub) from hga) (show Commute (Λ q') (Λ tHub) from
        hQcomm q' hq')).mul_left (show Commute g (Λ tHub) from hga).inv_left)
    exact hc.eq
  have hodd : ∀ s ∈ S, Odd (orderOf s) := by
    rintro s ⟨x, ⟨q', hq', rfl⟩, hx⟩
    apply odd_orderOf_of_cube
    apply hΛ
    rw [map_mul, map_mul, map_one, ← hx]
    have h3 := congrArg Λ (Qexp_cube hq')
    rw [map_mul, map_mul, map_one] at h3
    calc g * Λ q' * g⁻¹ * (g * Λ q' * g⁻¹) * (g * Λ q' * g⁻¹)
        = g * (Λ q' * Λ q' * Λ q') * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  have hn : ∀ d ∈ DHub, ∀ s ∈ S, d * s * d⁻¹ ∈ S := by
    intro d hd s hs
    obtain ⟨x, ⟨q', hq', rfl⟩, hx⟩ := hs
    obtain ⟨δ, hδ⟩ := hg' d
    have hδD : δ ∈ DHub := by
      rw [mem_DHub]
      apply hΛ
      rw [map_mul, map_mul, hδ]
      have h1 : Commute (Λ d) (Λ tHub) := by
        show Λ d * Λ tHub = Λ tHub * Λ d
        rw [← map_mul, ← map_mul, mem_DHub.1 hd]
      have h2 : Commute (g⁻¹ * Λ d * g) (Λ tHub) :=
        ((show Commute g (Λ tHub) from hga).inv_left.mul_left h1).mul_left
          (show Commute g (Λ tHub) from hga)
      exact h2.eq
    refine ⟨Λ (δ * q' * δ⁻¹), ⟨δ * q' * δ⁻¹, conj_mem_Qexp hδD hq', rfl⟩, ?_⟩
    show g * Λ (δ * q' * δ⁻¹) * g⁻¹ = Λ (d * s * d⁻¹)
    have hdΛ : Λ d = g * Λ δ * g⁻¹ := by rw [hδ]; group
    have hsΛ : Λ s = g * Λ q' * g⁻¹ := hx.symm
    have hL : Λ (δ * q' * δ⁻¹) = Λ δ * Λ q' * (Λ δ)⁻¹ := by rw [map_mul, map_mul, map_inv]
    have hR : Λ (d * s * d⁻¹) = Λ d * Λ s * (Λ d)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [hL, hR, hsΛ, hdΛ]
    group
  have hSQ : S ≤ Qexp := le_Qexp_of_odd hSD hn hodd
  obtain ⟨s', hs'⟩ := hg q
  have hs'S : s' ∈ S := ⟨Λ q, ⟨q, hq, rfl⟩, hs'.symm⟩
  rw [← hs']
  exact ⟨s', hSQ hs'S, rfl⟩

theorem tHub_ne_one : tHub ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg (mat 2 F3) h) (Sum.inl 0)) (Sum.inr 0)
  simp [tHub, CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_longBlock,
    CFSG.LieType.Steinberg.Sp.blockMat, uSL] at h1

theorem mem_Qexp_of_mem_locR [Finite G] (hΛ : Function.Injective Λ)
    (hD : DHub.map Λ ≤ locN K (Λ tHub)) {s : StatedSp 2 F3} (hs : Λ s ∈ locR K (Λ tHub)) :
    s ∈ Qexp := by
  let S : Subgroup (StatedSp 2 F3) := (locR K (Λ tHub)).comap Λ
  have hSD : S ≤ DHub := fun s hs => by
    rw [mem_DHub]
    apply hΛ
    rw [map_mul, map_mul]
    exact commutes_of_mem_locR hs
  have hn : ∀ d ∈ DHub, ∀ s ∈ S, d * s * d⁻¹ ∈ S := fun d hd s hs => by
    show Λ (d * s * d⁻¹) ∈ locR K (Λ tHub)
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_locR (hD ⟨d, hd, rfl⟩) hs
  have hodd : ∀ s ∈ S, Odd (orderOf s) := fun s hs => by
    have := odd_orderOf_of_mem_locR hs
    rwa [orderOf_injective Λ hΛ s] at this
  exact le_Qexp_of_odd hSD hn hodd hs

end Hub

section MFO

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {M : Subgroup G} {Λ : StatedSp 2 F3 →* G}


theorem map_Qexp_le_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hΛ : IsHubLayer (conjClass3 K) M Λ) {w : G} (hw : IsCentralInvolution M w)
    (hwN : w ∈ locN K (Λ tHub)) : Qexp.map Λ ≤ locR K (Λ tHub) := by
  set a := Λ tHub with ha
  have hnc : a ∉ Subgroup.center G := by
    intro h
    have hcen : Subgroup.center G = ⊥ :=
      CFSG.ComponentClassification.Helpers.center_eq_bot G hctx.nab
    rw [hcen, Subgroup.mem_bot] at h
    exact tHub_ne_one (hΛ.inj (h.trans (map_one Λ).symm))
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw.sq) hw.ne_one
  have hSN : Qexp.map Λ ≤ locN K a ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine le_inf hΛ.map_Qexp_le_locN ?_
    rintro _ ⟨q, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hΛ.comm (Λ q) ⟨q, rfl⟩ w hw.mem)
  have hnorm : locN K a ⊓ Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.normalizer ((Qexp.map Λ : Subgroup G) : Set G) := by
    rintro g ⟨hgN, hgw⟩
    have hgw' : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.1 hgw
    have hgw'' : g⁻¹ * w = w * g⁻¹ := by
      calc g⁻¹ * w = g⁻¹ * (w * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * w) * g⁻¹ := by rw [hgw']
        _ = w * g⁻¹ := by group
    have h1 := hΛ.conj_mem_range hctx (conjSub_eq_of_centralizes hctx hΛ.mem_hub hw hgw')
    have h2 := hΛ.conj_mem_range hctx (conjSub_eq_of_centralizes hctx hΛ.mem_hub hw hgw'')
    simp only [inv_inv] at h2
    have hga : g * Λ tHub = Λ tHub * g :=
      Subgroup.mem_centralizer_singleton_iff.1 (locN_le_centralizer hgN)
    have hga' : g⁻¹ * Λ tHub = Λ tHub * g⁻¹ := by
      calc g⁻¹ * Λ tHub = g⁻¹ * (Λ tHub * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * Λ tHub) * g⁻¹ := by rw [hga]
        _ = Λ tHub * g⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact conj_map_Qexp_mem hΛ.inj h1 h2 hga hq
    · intro hx
      have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      obtain ⟨q, hq, hqx⟩ := hx
      rw [hx', ← hqx]
      have := conj_map_Qexp_mem hΛ.inj (by simpa using h2) (by simpa using h1) hga' hq
      simpa using this
  have hodd : Odd (Nat.card (Qexp.map Λ)) := by
    have hp : IsPGroup 3 ↥(Qexp.map Λ) := by
      intro x
      obtain ⟨_, ⟨q, hq, rfl⟩⟩ := x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      show (Λ q) ^ (3 ^ 1) = 1
      rw [pow_one, pow_three', ← map_mul, ← map_mul, Qexp_cube hq, map_one]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    rw [hn]
    exact Odd.pow (by decide)
  exact (le_oddCoreIn_of_normalizes hSN hnorm hodd).trans (hO a hnc w hwN hw2)

end MFO

end CFSG.ClassicalInvolution.Q3.Q3ZB
