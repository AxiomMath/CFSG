module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAEich

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {w u u' : V6} {x y k : G}

private theorem add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem EichActs.mem_range_of_eq_zero_or_eq (hC : centralizer (ι.range : Set G) ≤ ι.range)
    (hw : qm w = 0) (hx : EichActs ι w x u) (hu : u = 0 ∨ u = w) : x ∈ ι.range := by
  apply Acts.mem_range_of_one hC
  intro v
  have h := hx.2 v
  rcases hu with h0 | hw'
  · rw [h0, eichF_zero] at h
    simpa using h
  · rw [hw'] at h
    have hww : eichF w w v = v := by
      have h1 : eichF w w v = eichF w (0 + w) v := by rw [zero_add]
      rw [h1, eichF_add_w hw (bil_zero_left w), eichF_zero]
    rw [hww] at h
    simpa using h

theorem EichActs.inv_mul_mem_range (hC : centralizer (ι.range : Set G) ≤ ι.range) (hw : qm w = 0)
    (hx : EichActs ι w x u) (hy : EichActs ι w y u') (h : u + u' = 0 ∨ u + u' = w) :
    x⁻¹ * y ∈ ι.range :=
  EichActs.mem_range_of_eq_zero_or_eq hC hw (hx.inv.mul hy) h

theorem EichActs.comm_mem_range (hC : centralizer (ι.range : Set G) ≤ ι.range) (hw : qm w = 0)
    (hx : EichActs ι w x u) (hy : EichActs ι w y u') : x * y * x⁻¹ * y⁻¹ ∈ ι.range := by
  refine EichActs.mem_range_of_eq_zero_or_eq (u := (u + u') + u + u') hC hw ?_ ?_
  · exact ((hx.mul hy).mul hx.inv).mul hy.inv
  · left
    have h : (u + u') + u + u' = (u + u) + (u' + u') := by abel
    rw [h, add_self_eq_zero_V6 u, add_self_eq_zero_V6 u', add_zero]

theorem EichActs.sq_mul_coord (hx : EichActs ι w x u) (a : V6) :
    (x * coordElt ι a) ^ 2 =
      x ^ 2 * coordElt ι (bil a w • u + (bil a u + qm u * bil a w) • w) := by
  have hstep : (x * coordElt ι a) ^ 2
      = x * x * (x⁻¹ * coordElt ι a * x) * coordElt ι a := by
    rw [pow_two]; group
  have hxinv := hx.inv.2 a
  rw [inv_inv] at hxinv
  calc (x * coordElt ι a) ^ 2
      = x * x * (x⁻¹ * coordElt ι a * x) * coordElt ι a := hstep
    _ = x * x * coordElt ι (eichF w u a) * coordElt ι a := by rw [hxinv]
    _ = x * x * (coordElt ι (eichF w u a) * coordElt ι a) := by group
    _ = x * x * coordElt ι (eichF w u a + a) := by rw [coordElt_add]
    _ = x * x * coordElt ι (bil a w • u + (bil a u + qm u * bil a w) • w) := by
          rw [eichF_add_self]
    _ = x ^ 2 * coordElt ι (bil a w • u + (bil a u + qm u * bil a w) • w) := by rw [pow_two]

theorem EichActs.conj {g : Equiv.Perm V6} (hk : Acts ι k g) (hg : g ∈ OrthMinus) (hgw : g w = w)
    (hx : EichActs ι w x u) : EichActs ι w (k * x * k⁻¹) (g u) := by
  constructor
  · have h := bil_apply_of_mem_orthOf isQF_qm hg u w
    rw [hgw, hx.1] at h
    exact h
  · intro v
    have hk1 := hk.inv v
    rw [inv_inv] at hk1
    have hxv := hx.2 (g⁻¹ v)
    have hk2 := hk (eichF w u (g⁻¹ v))
    have hconj := eichF_conj (w := w) (u := u) hg hgw (g⁻¹ v)
    have hgg : g (g⁻¹ v) = v := by simp
    rw [hgg] at hconj
    calc (k * x * k⁻¹) * coordElt ι v * (k * x * k⁻¹)⁻¹
        = k * (x * (k⁻¹ * coordElt ι v * k) * x⁻¹) * k⁻¹ := by group
      _ = k * (x * coordElt ι (g⁻¹ v) * x⁻¹) * k⁻¹ := by rw [hk1]
      _ = k * coordElt ι (eichF w u (g⁻¹ v)) * k⁻¹ := by rw [hxv]
      _ = coordElt ι (g (eichF w u (g⁻¹ v))) := hk2
      _ = coordElt ι (eichF w (g u) v) := by rw [hconj]

theorem Acts.apply_coord_of_fix {g : Equiv.Perm V6} (hk : Acts ι k g) (hgw : g w = w) :
    k * coordElt ι w * k⁻¹ = coordElt ι w := by
  have h := hk w
  rw [hgw] at h
  exact h

end CFSG.EvenSporadicStandard.HNRecog.Harada
