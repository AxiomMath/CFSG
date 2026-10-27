module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Dec
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Conj

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem _root_.CFSG.CGT.PushingUpLit.CGT6.Sec5Hyp.zpowers_eq (h : Sec5Hyp V G T Y)
    {y : MulAut V} (hy : y ∈ Y) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = Y :=
  zpowers_eq_of_card_three h.ycard hy hy1

omit [Finite V] in
theorem stabV_of_commV_conjSub_eq {q : MulAut V} {Y : Subgroup (MulAut V)}
    (h : commV Y = commV (conjSub q Y)) : q ∈ stabV (commV Y) := by
  intro w
  constructor
  · intro hw
    have : q w ∈ commV (conjSub q Y) := h ▸ hw
    rw [mem_commV_conjSub] at this
    simpa using this
  · intro hw
    have : q w ∈ commV (conjSub q Y) := by
      rw [mem_commV_conjSub]
      simpa using hw
    exact h ▸ this

theorem _root_.CFSG.CGT.PushingUpLit.CGT6.Sec5Hyp.pair_orth (h : Sec5Hyp V G T Y)
    {y q : MulAut V} (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hqG : q ∈ G) (h3 : IsPGroup 3 ↥(Y ⊔ conjSub q Y)) (hne : q * y * q⁻¹ ∉ Y) :
    y * (q * y * q⁻¹) = (q * y * q⁻¹) * y ∧ ∀ u ∈ commV Y, (q * y * q⁻¹) u = u := by
  set y' : MulAut V := q * y * q⁻¹ with hy'
  have hyY' : y' ∈ conjSub q Y := conj_mem_conjSub hy
  have hU' : Nat.card (commV (conjSub q Y)) = 4 := by rw [card_commV_conjSub, h.ucard]
  have hcomm := commute_of_sup_three_group h.elem h.ucard.le hU'.le h3
  have hYsup : ∀ a ∈ Y, a ∈ Y ⊔ conjSub q Y := fun a ha => Subgroup.mem_sup_left ha
  have hY'sup : ∀ a ∈ conjSub q Y, a ∈ Y ⊔ conjSub q Y := fun a ha => Subgroup.mem_sup_right ha
  have hcY : ∀ a ∈ Y, a * y' = y' * a := fun a ha => hcomm a (hYsup a ha) y' (hY'sup _ hyY')
  have hcY' : ∀ b ∈ conjSub q Y, y * b = b * y := fun b hb =>
    hcomm y (hYsup y hy) b (hY'sup b hb)
  refine ⟨hcY y hy, ?_⟩
  have hy3 : y ^ 3 = 1 := h.pow_three hy
  have hy'3 : y' ^ 3 = 1 := by
    have : y' ^ 3 = q * y ^ 3 * q⁻¹ := conj_pow
    rw [this, hy3]; group
  have hy'1 : y' ≠ 1 := fun e => hy1 (by
    have : q * y * q⁻¹ = 1 := e
    simpa using this)
  have hzY : Subgroup.zpowers y = Y := h.zpowers_eq hy hy1
  have hcard' : Nat.card (conjSub q Y) = 3 := by rw [card_conjSub, h.ycard]
  have hzY' : Subgroup.zpowers y' = conjSub q Y := zpowers_eq_of_card_three hcard' hyY' hy'1
  set U : Subgroup V := commV Y with hUdef
  set U' : Subgroup V := commV (conjSub q Y) with hU'def
  have hUy' : ∀ w ∈ U, y' w ∈ U := fun w hw =>
    G6.apply_mem_commV (fun x hx => by
      have := hcY x hx
      have e : y' * x * y'⁻¹ = x := by rw [← this]; group
      rw [e]; exact hx) hw
  have hU'y : ∀ w ∈ U', y w ∈ U' := fun w hw =>
    G6.apply_mem_commV (fun x hx => by
      have := hcY' x hx
      have e : y * x * y⁻¹ = x := by rw [this]; group
      rw [e]; exact hx) hw
  have hfpf : ∀ u ∈ U, y u = u → u = 1 := fun u hu hyu => by
    rw [hUdef, ← hzY] at hu
    exact eq_one_of_mem_commV_of_fixed h.elem hy3 hu hyu
  have hgP : ∀ p ∈ U ⊓ U', y p ∈ U ⊓ U' := fun p hp =>
    ⟨commV_invariant hy hp.1, hU'y p hp.2⟩
  have hU4 : Nat.card U = 4 := h.ucard
  rcases klein_inv hU4 inf_le_left hy3 hgP hfpf with hbot | htop
  · intro u hu
    have hs : normHom y' u ∈ U := by
      rw [normHom_apply]
      exact U.mul_mem (U.mul_mem hu (hUy' u hu)) (hUy' _ (hUy' u hu))
    have hw : u * (normHom y' u)⁻¹ ∈ U ⊓ U' := by
      refine Subgroup.mem_inf.mpr ⟨U.mul_mem hu (U.inv_mem hs), ?_⟩
      rw [hU'def, ← hzY']
      exact mul_inv_normHom_mem_commV h.elem u
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hw
    have hfix := apply_normHom hy'3 u
    rw [← hw] at hfix
    exact hfix
  · exfalso
    have hle : U ≤ U' := htop ▸ inf_le_right
    have hUU' : U = U' := Subgroup.eq_of_le_of_card_ge hle (by rw [hU', hU4])
    have hstab : q ∈ stabV U := stabV_of_commV_conjSub_eq hUU'
    have hnorm := h.normalizer_of_stabV ⟨hqG, hstab⟩
    exact hne ((Subgroup.mem_normalizer_iff.mp hnorm y).mp hy)

end CFSG.CGT.PushingUpLit.CGT6E
