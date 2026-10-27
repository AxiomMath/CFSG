module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Heis

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

variable {V : Type} [CommGroup V] {G : Type} [Group G] (ρ : G →* MulAut V)

section Stab

theorem eq_eps_mul (hV : ∀ v : V, v ^ 2 = 1) (y : G) (w : V) :
    w = eps ρ y w * (ρ y w * ρ (y ^ 2) w) := by
  calc w = w * (ρ y w * ρ y w) * (ρ (y ^ 2) w * ρ (y ^ 2) w) := by
        rw [mul_self_eq_one' hV, mul_self_eq_one' hV, mul_one, mul_one]
    _ = eps ρ y w * (ρ y w * ρ (y ^ 2) w) := by
        simp only [eps]
        ac_rfl

theorem comp_mem_kerSub (hV : ∀ v : V, v ^ 2 = 1) {y : G} (hy : y ^ 3 = 1) (w : V) :
    ρ y w * ρ (y ^ 2) w ∈ kerSub ρ y := by
  rw [mem_kerSub, eps_mul, eps_rho_self ρ hy, eps_rho_sq ρ hy, mul_self_eq_one' hV]

theorem eps_comm {g y : G} (hgy : g * y = y * g) (w : V) :
    ρ g (eps ρ y w) = eps ρ y (ρ g w) := by
  have h2 : g * y ^ 2 = y ^ 2 * g := (Commute.pow_right (show Commute g y from hgy) 2).eq
  simp only [eps]
  rw [(ρ g).map_mul, (ρ g).map_mul, rho_rho, rho_rho, rho_rho, rho_rho, hgy, h2]

theorem mem_setStab_kerSub {g y : G} (hgy : g * y = y * g) : g ∈ setStab ρ (kerSub ρ y) := by
  intro w
  rw [mem_kerSub, mem_kerSub, ← eps_comm ρ hgy]
  exact (ρ g).map_eq_one_iff

theorem mem_setStab_fixSub {g y : G} (hgy : g * y = y * g) : g ∈ setStab ρ (fixSub ρ y) := by
  intro w
  rw [mem_fixSub, mem_fixSub, rho_rho, ← hgy, ← rho_rho]
  exact (ρ g).injective.eq_iff

theorem mem_setStab_inf {g : G} {A B : Subgroup V} (hA : g ∈ setStab ρ A)
    (hB : g ∈ setStab ρ B) : g ∈ setStab ρ (A ⊓ B) := by
  intro w
  simp only [Subgroup.mem_inf]
  exact and_congr (hA w) (hB w)

theorem mem_setStab_cen {e1 e2 g : G} (hg1 : g * e1 = e1 * g) (hg2 : g * e2 = e2 * g) :
    g ∈ setStab ρ (cen ρ e1 e2) :=
  mem_setStab_inf ρ (mem_setStab_fixSub ρ hg1) (mem_setStab_fixSub ρ hg2)

theorem commute_el_of {e1 e2 g : G} (hg1 : g * e1 = e1 * g) (hg2 : g * e2 = e2 * g)
    (x : ZMod 3 × ZMod 3) : g * el e1 e2 x = el e1 e2 x * g :=
  (Commute.mul_right (Commute.pow_right (show Commute g e1 from hg1) _)
    (Commute.pow_right (show Commute g e2 from hg2) _)).eq

theorem mem_setStab_piece {e1 e2 g : G} (h : Comm3 e1 e2) (hg1 : g * e1 = e1 * g)
    (hg2 : g * e2 = e2 * g) (i : Fin 4) : g ∈ setStab ρ (piece ρ e1 e2 i) := by
  have key : ∀ {g : G}, g * e1 = e1 * g → g * e2 = e2 * g →
      ∀ w ∈ piece ρ e1 e2 i, ρ g w ∈ piece ρ e1 e2 i := by
    intro g hg1 hg2 w hw
    have hA : ∀ w, ρ g (avgA ρ e1 e2 w) = avgA ρ e1 e2 (ρ g w) := by
      refine rho_avgA_conj ρ h (m1 := (1, 0)) (m2 := (0, 1)) (by decide) ?_ ?_
      · rw [el_10]
        exact mul_inv_eq_iff_eq_mul.2 hg1
      · rw [el_01]
        exact mul_inv_eq_iff_eq_mul.2 hg2
    exact piece_map ρ hA (Or.inl (mul_inv_eq_iff_eq_mul.2 (commute_el_of hg1 hg2 _))) hw
  exact mem_setStab_of ρ _ (key hg1 hg2)
    (key (show Commute g e1 from hg1).inv_left.eq (show Commute g e2 from hg2).inv_left.eq)

end Stab

section Dich

variable [Finite V]

theorem dich (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V) {z y x : G} (hzU : z ∈ setStab ρ U)
    (hyU : y ∈ setStab ρ U) (hxU : x ∈ setStab ρ U) (hz : z ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzy : z * y = y * z) (hxz : x * z = z * x) (hxy : x * y * x⁻¹ = z * y) :
    (∀ w ∈ U, ρ z w = w) ∨ 64 ≤ Nat.card U := by
  have hzW : z ∈ setStab ρ (U ⊓ kerSub ρ z) := mem_setStab_inf ρ hzU (mem_setStab_kerSub ρ rfl)
  have hyW : y ∈ setStab ρ (U ⊓ kerSub ρ z) :=
    mem_setStab_inf ρ hyU (mem_setStab_kerSub ρ hzy.symm)
  have hxW : x ∈ setStab ρ (U ⊓ kerSub ρ z) := mem_setStab_inf ρ hxU (mem_setStab_kerSub ρ hxz)
  have hfpf : ∀ w ∈ U ⊓ kerSub ρ z, ρ z w = w → w = 1 := by
    intro w hw hfix
    have hmem : w ∈ fixSub ρ z ⊓ kerSub ρ z := ⟨hfix, hw.2⟩
    rw [fixSub_inf_kerSub ρ hV z] at hmem
    exact hmem
  rcases heis_card_sub ρ hV (U ⊓ kerSub ρ z) hzW hyW hxW hz hy hzy hxz hxy hfpf with hbot | hcard
  · left
    intro w hw
    have hz1 : ρ z w ∈ U := (hzU w).2 hw
    have hz2 : ρ (z ^ 2) w ∈ U := ((Subgroup.pow_mem _ hzU 2) w).2 hw
    have hb : ρ z w * ρ (z ^ 2) w ∈ U ⊓ kerSub ρ z :=
      ⟨U.mul_mem hz1 hz2, comp_mem_kerSub ρ hV hz w⟩
    rw [hbot, Subgroup.mem_bot] at hb
    have hw' : w = eps ρ z w := by
      have := eq_eps_mul ρ hV z w
      rwa [hb, mul_one] at this
    calc ρ z w = ρ z (eps ρ z w) := congrArg (ρ z) hw'
      _ = eps ρ z w := rho_eps ρ hz w
      _ = w := hw'.symm
  · right
    exact hcard.trans (Subgroup.card_le_of_le inf_le_left)

end Dich

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
