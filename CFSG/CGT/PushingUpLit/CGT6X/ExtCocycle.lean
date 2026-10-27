module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

section Cocycle

variable {G V : Type*} [Group G] [CommGroup V] (ρ : G →* MulAut V)

@[expose] def IsCocycle (c : G → V) : Prop := ∀ g h : G, c (g * h) = c g * ρ g (c h)

@[expose] def IsCoboundary (c : G → V) : Prop := ∃ m : V, ∀ g : G, c g = ρ g m * m⁻¹

variable {ρ}

theorem isCocycle_cobdry (m : V) : IsCocycle ρ (fun g => ρ g m * m⁻¹) := by
  intro g h
  show ρ (g * h) m * m⁻¹ = (ρ g m * m⁻¹) * ρ g (ρ h m * m⁻¹)
  have e : ρ (g * h) m = ρ g (ρ h m) := by rw [map_mul]; rfl
  have e2 : ρ g (ρ h m * m⁻¹) = ρ g (ρ h m) * (ρ g m)⁻¹ := by
    rw [(ρ g).map_mul, (ρ g).map_inv]
  rw [e, e2]
  calc ρ g (ρ h m) * m⁻¹ = (ρ g m * (ρ g m)⁻¹) * (m⁻¹ * ρ g (ρ h m)) := by
        rw [mul_inv_cancel, one_mul, mul_comm]
    _ = _ := by ac_rfl

theorem IsCocycle.map_one {c : G → V} (hc : IsCocycle ρ c) : c 1 = 1 := by
  have h := hc 1 1
  rw [mul_one] at h
  simpa using h

theorem IsCocycle.mul {c c' : G → V} (hc : IsCocycle ρ c) (hc' : IsCocycle ρ c') :
    IsCocycle ρ (fun g => c g * c' g) := by
  intro g h
  simp only [hc g h, hc' g h, map_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem IsCocycle.inv {c : G → V} (hc : IsCocycle ρ c) : IsCocycle ρ (fun g => (c g)⁻¹) := by
  intro g h
  simp only [hc g h, mul_inv_rev, map_inv]
  simp only [mul_comm]

theorem IsCocycle.div_cobdry {c : G → V} (hc : IsCocycle ρ c) (m : V) :
    IsCocycle ρ (fun g => c g * (ρ g m * m⁻¹)⁻¹) :=
  hc.mul (isCocycle_cobdry m).inv

end Cocycle

section Odd

variable {G V : Type*} [Group G] [CommGroup V] {ρ : G →* MulAut V}

theorem pow_odd_eq_self (hV : ∀ v : V, v ^ 2 = 1) (v : V) {t : ℕ} (ht : Odd t) : v ^ t = v := by
  obtain ⟨k, rfl⟩ := ht
  rw [pow_succ, pow_mul, hV v, one_pow, one_mul]

theorem coboundary_of_vanish_on_odd_index (hV : ∀ v : V, v ^ 2 = 1) (H : Subgroup G)
    (hH : Odd H.index) {c : G → V} (hc : IsCocycle ρ c) (hvan : ∀ h ∈ H, c h = 1) :
    IsCoboundary ρ c := by
  classical
  have hfin : H.FiniteIndex := ⟨by rintro h; rw [h] at hH; exact (Nat.not_odd_zero hH)⟩
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hconst : ∀ (g : G) (h : G), h ∈ H → c (g * h) = c g := by
    intro g h hh
    rw [hc g h, hvan h hh, map_one, mul_one]
  let φ : G ⧸ H → V := fun q => c q.out
  have hφ : ∀ g : G, φ (g : G ⧸ H) = c g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    show c (g : G ⧸ H).out = c g
    rw [hh]
    exact hconst g h h.2
  set s : V := ∏ q : G ⧸ H, φ q with hs
  refine ⟨s⁻¹, fun x => ?_⟩
  have hperm : ∏ q : G ⧸ H, φ (x • q) = s := by
    exact Fintype.prod_equiv (MulAction.toPerm x) _ _ (fun q => rfl)
  have hstep : ∀ q : G ⧸ H, φ (x • q) = c x * ρ x (φ q) := by
    intro q
    have : x • q = ((x * q.out : G) : G ⧸ H) := by
      conv_lhs => rw [← Quotient.out_eq' q]
      rfl
    rw [this, hφ, hc x q.out]
  have hprod : s = c x ^ Fintype.card (G ⧸ H) * ρ x s := by
    calc s = ∏ q : G ⧸ H, φ (x • q) := hperm.symm
      _ = ∏ q : G ⧸ H, (c x * ρ x (φ q)) := Finset.prod_congr rfl fun q _ => hstep q
      _ = c x ^ Fintype.card (G ⧸ H) * ρ x s := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← map_prod]
  have hodd : Odd (Fintype.card (G ⧸ H)) := by
    have : H.index = Fintype.card (G ⧸ H) := by
      rw [Subgroup.index, Nat.card_eq_fintype_card]
    rwa [← this]
  rw [pow_odd_eq_self hV _ hodd] at hprod
  have hx : c x = s * (ρ x s)⁻¹ := by
    calc c x = (c x * ρ x s) * (ρ x s)⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = s * (ρ x s)⁻¹ := by rw [← hprod]
  rw [hx, map_inv, inv_inv]
  exact mul_comm _ _

theorem isCoboundary_of_div_cobdry {c : G → V} (m : V)
    (h : IsCoboundary ρ (fun g => c g * (ρ g m * m⁻¹)⁻¹)) : IsCoboundary ρ c := by
  obtain ⟨m', hm'⟩ := h
  refine ⟨m' * m, fun g => ?_⟩
  have h2 : c g = (ρ g m' * m'⁻¹) * (ρ g m * m⁻¹) := by
    have : c g * (ρ g m * m⁻¹)⁻¹ = ρ g m' * m'⁻¹ := hm' g
    calc c g = c g * (ρ g m * m⁻¹)⁻¹ * (ρ g m * m⁻¹) := (inv_mul_cancel_right _ _).symm
      _ = _ := by rw [this]
  rw [h2]
  simp only [map_mul, mul_inv_rev]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem coboundary_of_odd_card (hV : ∀ v : V, v ^ 2 = 1) (hG : Odd (Nat.card G)) {c : G → V}
    (hc : IsCocycle ρ c) : IsCoboundary ρ c := by
  refine coboundary_of_vanish_on_odd_index hV ⊥ (by rwa [Subgroup.index_bot]) hc ?_
  intro h hh
  rw [Subgroup.mem_bot.1 hh]
  exact hc.map_one

end Odd

end CFSG.CGT.PushingUpLit.CGT6X
