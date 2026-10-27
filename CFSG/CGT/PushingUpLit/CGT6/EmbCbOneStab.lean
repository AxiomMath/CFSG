module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbStruct
import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneComp
import CFSG.CGT.PushingUpLit.CGT6.EmbCbPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

namespace CbData

variable (D : CbData Y t m X)

@[expose] def u₀ : V := D.w D.a * D.w D.b

omit [Finite V] in
omit [Finite V] in
omit [Finite V] in
theorem u₀_mem_commV (hV : ∀ v : V, v ^ 2 = 1) : D.u₀ ∈ commV (Subgroup.zpowers t) := by
  have h1 : t (D.w D.a) * (D.w D.a)⁻¹ ∈ commV (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, D.w D.a, rfl⟩
  have h2 : (D.w D.a)⁻¹ = D.w D.a := inv_eq_of_mul_eq_one_right (D.w_sq hV D.a)
  rw [D.htw, Equiv.swap_apply_left, h2, mul_comm] at h1
  exact h1

omit [Finite V] in
omit [Finite V] in
omit [Finite V] in
theorem u₀_ne_one (hV : ∀ v : V, v ^ 2 = 1) : D.u₀ ≠ 1 := by
  intro h
  have h2 : (D.w D.a)⁻¹ = D.w D.a := inv_eq_of_mul_eq_one_right (D.w_sq hV D.a)
  have h3 : D.w D.b = (D.w D.a)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h2] at h3
  exact D.hab (D.hwinj h3).symm

omit [Finite V] in
theorem fix_u₀ {y : MulAut V} (hy : y ∈ Y) (hYX : Y ≤ X) : y D.u₀ = D.u₀ := by
  have hmem : (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X := hy
  have h1 : D.θ ⟨y, hYX hy⟩ ∈ (Y.subgroupOf X).map D.θ.toMonoidHom := ⟨_, hmem, rfl⟩
  rw [D.hstab, mem_altStabilizer_iff] at h1
  have ha := h1 D.a (by simp)
  have hb := h1 D.b (by simp)
  show y (D.w D.a * D.w D.b) = D.w D.a * D.w D.b
  rw [map_mul, D.hwact y (hYX hy), D.hwact y (hYX hy), ha, hb]

omit [Finite V] in
theorem exists_move (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) :
    ∃ x ∈ X, x D.u₀ ≠ D.u₀ := by
  classical
  obtain ⟨j, l, r, n, hj, hl, -, -, hjl, -, -, -, -, -⟩ :=
    cbp_four_points ({D.a, D.b} : Finset (Fin (m + 2)))
      (by have := Finset.card_le_two (a := D.a) (b := D.b); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj hl
  obtain ⟨τ, hτa, hτb⟩ := cbp_exists_alt_pair (by omega : 4 ≤ m + 2) D.hab hjl
  have hx : (D.θ.symm τ : MulAut V) ∈ X := (D.θ.symm τ).2
  refine ⟨_, hx, fun hcon => ?_⟩
  have hθ : (D.θ ⟨(D.θ.symm τ : MulAut V), hx⟩ : Equiv.Perm (Fin (m + 2))) = (τ : Perm _) := by
    have : (⟨(D.θ.symm τ : MulAut V), hx⟩ : ↥X) = D.θ.symm τ := Subtype.ext rfl
    rw [this, D.θ.apply_symm_apply]
  have h1 : (D.θ.symm τ : MulAut V) D.u₀ = D.w j * D.w l := by
    show (D.θ.symm τ : MulAut V) (D.w D.a * D.w D.b) = _
    rw [map_mul, D.hwact _ hx, D.hwact _ hx, hθ, hτa, hτb]
  rw [h1] at hcon
  apply D.hw4 j l D.a D.b hjl hj.1 hj.2 hl.1 hl.2
    D.hab
  have hu : D.u₀ * D.u₀ = 1 := by
    show (D.w D.a * D.w D.b) * (D.w D.a * D.w D.b) = 1
    calc (D.w D.a * D.w D.b) * (D.w D.a * D.w D.b) = (D.w D.a * D.w D.a) * (D.w D.b * D.w D.b) := by
          ac_rfl
      _ = 1 := by rw [D.w_sq hV, D.w_sq hV, one_mul]
  calc D.w j * D.w l * D.w D.a * D.w D.b = (D.w j * D.w l) * D.u₀ := by
        show _ = (D.w j * D.w l) * (D.w D.a * D.w D.b)
        ac_rfl
    _ = D.u₀ * D.u₀ := by rw [hcon]
    _ = 1 := hu

end CbData

namespace OneCfg

variable {G T : Subgroup (MulAut V)} (c : OneCfg G T Y t m X) (D : CbData Y t m X)

include c in
theorem vecStab_normalizes_Y {g : MulAut V} (hg : g ∈ vecStab G D.u₀) :
    ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
  have hu := D.u₀_mem_commV c.hV
  have hu1 := D.u₀_ne_one c.hV
  obtain ⟨X'', hlift⟩ := c.cfg.exists_lift_vecStab c.hV c.hm c.hodd c.hY c.htG c.htT c.ht2 c.ht1
    hu hu1
  have hHG : vecStab G D.u₀ ≤ G := fun x hx => (mem_vecStab.mp hx).1
  have hYH : Y ≤ vecStab G D.u₀ := fun y hy =>
    mem_vecStab.mpr ⟨c.Y_le_G hy, D.fix_u₀ hy c.Y_le_X⟩
  by_cases hXY : X'' = Y
  · subst hXY
    exact c.cfg.normalizes_of_subnormal c.h2 c.hV c.hm c.hodd c.hY hHG hYH
      (hlift.2.2.1) g hg
  · exfalso
    have hcb := c.cfg.cbLift_of_lift c.h2 c.hV c.hm c.hodd c.hY c.htG c.htT c.ht2 c.ht1 hu hu1
      hlift hXY
    have hXe := c.huniq _ hcb
    subst hXe
    obtain ⟨x, hx, hxne⟩ := D.exists_move c.hV c.hm
    exact hxne (mem_vecStab.mp (hlift.2.1 hx)).2

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
