module

public import CFSG.CGT.M24S.NSTypeA2

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

set_option maxRecDepth 10000 in
theorem card_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem mb_lv_v₀ : ∀ cc : Fin 3 → ZMod 2, v₀ ⬝ᵥ cc = 0 → mb (lv cc v₀) = 1 := by
  decide

theorem commute_of_mem_cent {x : G} {g : ↥(H ⊓ Subgroup.centralizer ({x} : Set G))} :
    (g : G) * x = x * g :=
  Subgroup.mem_centralizer_singleton_iff.1 g.2.2

noncomputable def mbHom {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) :
    ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) →* Matrix (Fin 2) (Fin 2) (ZMod 2) where
  toFun g := mb (blk (c.mat g))
  map_one' := by rw [OneMemClass.coe_one, c.mat_one, blk_one, mb_one]
  map_mul' g g' := by
    have hg := stab_of_commute c hx hxv g.2.1 commute_of_mem_cent
    have hg' := stab_of_commute c hx hxv g'.2.1 commute_of_mem_cent
    rw [Subgroup.coe_mul, blk_mul_of_mem c hg.1 g'.2.1, mb_mul hg'.2]

noncomputable def psi {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) :
    ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) →* GL (Fin 2) (ZMod 2) :=
  (mbHom c hx hxv).toHomUnits

theorem coe_psi {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀)
    (g : ↥(H ⊓ Subgroup.centralizer ({x} : Set G))) :
    ((psi c hx hxv g : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      mb (blk (c.mat g)) := by
  unfold psi mbHom
  rfl

theorem ker_psi [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H) {x : G}
    (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hx2 : x ^ 2 = 1) :
    (psi c hx hxv).ker = (c.E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (H ⊓ Subgroup.centralizer ({x} : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, ← Units.val_eq_one,
    coe_psi]
  constructor
  · intro h
    exact ⟨mem_E_of_commute c hN hns hx hxv hx2 g.2.1 commute_of_mem_cent h, g.2.2⟩
  · rintro ⟨he, -⟩
    rw [c.blk_of_mem_E he, mb_one]

theorem exists_commute_lift [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hx2 : x ^ 2 = 1)
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB1 : B.det = 1) (hBv : vecMul v₀ B = v₀) :
    ∃ g' : G, g' ∈ H ∧ g' * x = x * g' ∧ mb (blk (c.mat g')) = mb B := by
  obtain ⟨g, hg, hgB⟩ := c.exists_mem_cent B hB1
  have hover : Over c v₀ x := ⟨hx, hxv, hx2⟩
  have hy : Over c v₀ (g * x * g⁻¹) :=
    ⟨c.conj_mem_E hg hx, top_conj_eq c hg hx hxv (by rw [hgB]; exact hBv),
      by rw [conj_pow, hx2, mul_one, mul_inv_cancel]⟩
  obtain ⟨s, hs, hys, hvs⟩ := exists_mul_of_over c hover hy
  obtain ⟨h, hh, hhB⟩ := c.exists_mem_cent (lv (tail (c.vec s)) v₀) (det_lv hvs)
  have hd := moves_of_ne_zero c hN hns (by decide) h hh _ hvs hhB _ hy
  have hT := mem_T_of_fix c hh hy.1 (by rw [hy.2.1, hhB]; exact vecMul_lv_self hvs)
  have hd' : tail (c.vec (s * ((g * x * g⁻¹)⁻¹ * h * (g * x * g⁻¹) * h⁻¹))) = 0 := by
    rw [c.vec_mul hs hT, GL4.tail_add]
    change tail (c.vec s) + disp c h (g * x * g⁻¹) = 0
    rw [hd, vec_add_self]
  have hhy : (h * g) * x * (h * g)⁻¹ =
      x * (s * ((g * x * g⁻¹)⁻¹ * h * (g * x * g⁻¹) * h⁻¹)) := by
    calc (h * g) * x * (h * g)⁻¹ =
        (g * x * g⁻¹) * ((g * x * g⁻¹)⁻¹ * h * (g * x * g⁻¹) * h⁻¹) := by group
      _ = _ := by rw [hys, mul_assoc]
  have hmb : mb (blk (c.mat (h * g))) = mb B := by
    rw [blk_mul_of_mem c hh hg.1, hhB, hgB, mb_mul hBv, mb_lv_v₀ _ hvs, one_mul]
  rcases eq_one_or_eq_t_of_tail_eq_zero c (T.mul_mem hs hT) hd' with h1 | h1
  · refine ⟨h * g, H.mul_mem hh.1 hg.1, ?_, hmb⟩
    have h2 : (h * g) * x * (h * g)⁻¹ = x := by rw [hhy, h1, mul_one]
    calc h * g * x = (h * g) * x * (h * g)⁻¹ * (h * g) := by group
      _ = x * (h * g) := by rw [h2]
  · obtain ⟨s₀, hs₀, hs₀x⟩ := exists_conj_eq_mul_t c hx hxv
    refine ⟨s₀ * (h * g), H.mul_mem (c.le hs₀) (H.mul_mem hh.1 hg.1), ?_, ?_⟩
    · have h2 : (h * g) * x * (h * g)⁻¹ = x * t := by rw [hhy, h1]
      have hs₀t : s₀ * t = t * s₀ := commute_of_mem_T c hs₀ c.mem
      have h3 : (s₀ * (h * g)) * x * (s₀ * (h * g))⁻¹ = x := by
        calc (s₀ * (h * g)) * x * (s₀ * (h * g))⁻¹ = s₀ * ((h * g) * x * (h * g)⁻¹) * s₀⁻¹ := by
              group
          _ = s₀ * x * s₀⁻¹ * (s₀ * t * s₀⁻¹) := by rw [h2]; group
          _ = x * t * t := by rw [hs₀x, hs₀t, mul_inv_cancel_right]
          _ = x := by rw [mul_assoc, ← pow_two, c.z_sq, mul_one]
      calc s₀ * (h * g) * x = (s₀ * (h * g)) * x * (s₀ * (h * g))⁻¹ * (s₀ * (h * g)) := by
            group
        _ = x * (s₀ * (h * g)) := by rw [h3]
    · rw [blk_mul_of_mem c (c.E_le (c.T_le_E hs₀)) (H.mul_mem hh.1 hg.1),
        (c.mat_eq_one_iff (c.le hs₀)).2 hs₀, blk_one, one_mul, hmb]

theorem psi_surjective [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H) {x : G}
    (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hx2 : x ^ 2 = 1) :
    Function.Surjective (psi c hx hxv) := by
  intro u
  have hdet : (u : Matrix (Fin 2) (Fin 2) (ZMod 2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
  obtain ⟨B, hB1, hBv, hBm⟩ := hasStabLift _ hdet
  obtain ⟨g', hg'H, hg'x, hmb⟩ := exists_commute_lift c hN hns hx hxv hx2 hB1 hBv
  refine ⟨⟨g', hg'H, Subgroup.mem_centralizer_singleton_iff.2 hg'x⟩, Units.ext ?_⟩
  rw [coe_psi]
  exact hmb.trans hBm

theorem card_centralizer_eq [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hx2 : x ^ 2 = 1) :
    Nat.card (H ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 384 := by
  have hle : c.E ⊓ Subgroup.centralizer ({x} : Set G) ≤ H ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ fun e he => c.mem_H_of_mem_E he
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (psi c hx hxv).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (psi_surjective c hN hns hx hxv hx2)).toEquiv, ker_psi c hN hns hx hxv hx2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_centralizer_E c hx hxv,
    card_GL_two] at h1
  rw [h1]

end CFSG.CGT.M24S.NSB
