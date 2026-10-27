module

public import CFSG.CGT.Foote82.T66.CaseIIAlt
public import CFSG.CGT.Foote82.T66.CaseIIHeart

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel CFSG.QuasithinUnique
open Equiv Equiv.Perm

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def hmk (y : Fin 6 → ZMod 2) (hy : ∑ i, y i = 0) : altHeart 6 :=
  ((⟨y, hy⟩ : evenWeight 6) : altHeart 6)

theorem mem_zmultiples_allOnes_iff (y : Fin 6 → ZMod 2) :
    y ∈ AddSubgroup.zmultiples (allOnes 6) ↔ IsTriv y := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have e : k • allOnes 6 = fun _ => (k : ZMod 2) := by
      funext i
      simp [allOnes]
    rw [e]
    rcases zmod2_cases (k : ZMod 2) with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨0, zero_zsmul _⟩
    · exact ⟨1, one_zsmul _⟩

theorem isTriv_neg_iff (y : Fin 6 → ZMod 2) : IsTriv (-y) ↔ IsTriv y := by
  have : -y = y := by
    funext i
    exact ZMod.neg_eq_self_mod_two (y i)
  rw [this]

theorem hmk_eq_hmk_iff {x y : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    hmk x hx = hmk y hy ↔ IsTriv (x - y) := by
  rw [hmk, hmk, QuotientAddGroup.eq]
  change (-(⟨x, hx⟩ : evenWeight 6) + ⟨y, hy⟩ : evenWeight 6) ∈
    (AddSubgroup.zmultiples (allOnes 6)).addSubgroupOf (evenWeight 6) ↔ _
  rw [AddSubgroup.mem_addSubgroupOf, mem_zmultiples_allOnes_iff]
  have e : ((-(⟨x, hx⟩ : evenWeight 6) + ⟨y, hy⟩ : evenWeight 6) : Fin 6 → ZMod 2) =
      -(x - y) := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  rw [e, isTriv_neg_iff]

theorem hmk_eq_zero_iff {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) :
    hmk x hx = 0 ↔ IsTriv x := by
  have h0 : ∑ i, (0 : Fin 6 → ZMod 2) i = 0 := by simp
  have : (0 : altHeart 6) = hmk 0 h0 := by
    rw [hmk]
    exact (QuotientAddGroup.mk_zero _).symm
  rw [this, hmk_eq_hmk_iff, show x - 0 = x from funext fun i => sub_zero (x i)]

theorem sum_sub_eq_zero {x y : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    ∑ i, (x - y) i = 0 := by
  have h := Finset.sum_sub_distrib (s := Finset.univ) (f := x) (g := y)
  refine h.trans ?_
  exact (congrArg₂ (fun a b : ZMod 2 => a - b) hx hy).trans (sub_zero 0)

theorem hmk_sub {x y : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    hmk x hx - hmk y hy = hmk (x - y) (sum_sub_eq_zero hx hy) := by
  rw [hmk, hmk, hmk, ← QuotientAddGroup.mk_sub]
  rfl

theorem sum_pv_eq_zero (σ : Perm (Fin 6)) {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) :
    ∑ i, pv σ x i = 0 := by rw [sum_pv, hx]

theorem hmk_congr {y y' : Fin 6 → ZMod 2} (h : y = y') (hy : ∑ i, y i = 0) (hy' : ∑ i, y' i = 0) :
    hmk y hy = hmk y' hy' := by
  subst h
  rfl

theorem exists_hmk (y : altHeart 6) : ∃ x : Fin 6 → ZMod 2, ∃ hx : ∑ i, x i = 0, y = hmk x hx := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hx' : ∑ i, x i = 0 := hx
  exact ⟨x, hx', rfl⟩

theorem dt₀_cycleType : dt₀.cycleType = {2, 2} := by
  have h1 : (swap (0 : Fin 6) 1).IsCycle := isCycle_swap (by decide)
  have h2 : (swap (2 : Fin 6) 3).IsCycle := isCycle_swap (by decide)
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 6) 1) (swap 2 3) := by
    rw [disjoint_iff_disjoint_support]
    decide
  rw [dt₀, hd.cycleType_mul, h1.cycleType, h2.cycleType, card_support_swap (by decide),
    card_support_swap (by decide)]
  rfl

theorem d3₀_cycleType : d3₀.cycleType = {3, 3} := by
  have h1 : (swap (0 : Fin 6) 1 * swap 1 2).IsThreeCycle := card_support_eq_three_iff.mp (by decide)
  have h2 : (swap (3 : Fin 6) 4 * swap 4 5).IsThreeCycle := card_support_eq_three_iff.mp (by decide)
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 6) 1 * swap 1 2) (swap 3 4 * swap 4 5) := by
    rw [disjoint_iff_disjoint_support]
    decide
  rw [d3₀, hd.cycleType_mul, h1, h2]
  rfl

structure AD (L : Subgroup (GLV V)) (α : ↥L →* ↥(alternatingGroup (Fin 6)))
    (β : ↥(commSpace L ⊤) →+ altHeart 6) : Prop where
  α_surj : Function.Surjective α
  β_surj : Function.Surjective β
  β_ker : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup
  rel : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
    ∀ x : evenWeight 6, β w = (x : altHeart 6) →
      β w' = (evenWeightPerm (α ℓ : Perm (Fin 6)) x : altHeart 6)

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem Ctx.exists_ad (c : Ctx G L z v H₁ ψ) (hs : CaseIISplit) : ∃ α β, AD L α β := by
  obtain ⟨α, hα, β, hβ, hk, hr⟩ := c.isAltNaturalModule hs
  exact ⟨α, β, hα, hβ, hk, hr⟩

namespace AD

variable {α : ↥L →* ↥(alternatingGroup (Fin 6))} {β : ↥(commSpace L ⊤) →+ altHeart 6}
  (d : AD L α β)
include d

theorem conj_mem (ℓ : ↥L) (w : ↥(commSpace L ⊤)) : (ℓ : GLV V) w ∈ commSpace L ⊤ :=
  invariant_commSpace (fun _ ha _ hb => L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha))
    (invariant_top L) ℓ ℓ.2 w w.2

theorem sub_mem (ℓ : ↥L) (w : V) : (ℓ : GLV V) w - w ∈ commSpace L ⊤ :=
  sub_mem_commSpace ℓ.2 Submodule.mem_top

theorem beta_eq_zero_iff (w : ↥(commSpace L ⊤)) : β w = 0 ↔ (w : V) ∈ fixedSpace L := by
  rw [← AddMonoidHom.mem_ker, d.β_ker]
  rfl

theorem beta_sub (ℓ : ↥L) (w : ↥(commSpace L ⊤)) {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0)
    (hβw : β w = hmk x hx) :
    β ⟨(ℓ : GLV V) w - w, d.sub_mem ℓ w⟩ =
      hmk (pv (α ℓ : Perm (Fin 6)) x - x) (sum_sub_eq_zero (sum_pv_eq_zero _ hx) hx) := by
  have e : (⟨(ℓ : GLV V) w - w, d.sub_mem ℓ w⟩ : ↥(commSpace L ⊤)) =
      ⟨(ℓ : GLV V) w, d.conj_mem ℓ w⟩ - w := rfl
  have h1 := d.rel ℓ w ⟨(ℓ : GLV V) w, d.conj_mem ℓ w⟩ rfl ⟨x, hx⟩ hβw
  rw [e, map_sub, h1, hβw]
  rw [← hmk_sub (sum_pv_eq_zero _ hx) hx]
  rfl

theorem beta_conj (ℓ : ↥L) (w : ↥(commSpace L ⊤)) {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0)
    (hβw : β w = hmk x hx) :
    β ⟨(ℓ : GLV V) w, d.conj_mem ℓ w⟩ = hmk (pv (α ℓ : Perm (Fin 6)) x) (sum_pv_eq_zero _ hx) :=
  d.rel ℓ w ⟨(ℓ : GLV V) w, d.conj_mem ℓ w⟩ rfl ⟨x, hx⟩ hβw

theorem α_injective (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) : Function.Injective α := by
  obtain ⟨e⟩ := hL
  exact (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 d.α_surj

theorem exists_two_comm (ℓ : ↥L) (hσ : (α ℓ : Perm (Fin 6)).cycleType = {2, 2}) :
    ∃ w₁ w₂ : ↥(commSpace L ⊤), (ℓ : GLV V) w₁ - w₁ ≠ 0 ∧ (ℓ : GLV V) w₂ - w₂ ≠ 0 ∧
      (ℓ : GLV V) w₁ - w₁ ≠ (ℓ : GLV V) w₂ - w₂ := by
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 6), π * dt₀ * π⁻¹ = (α ℓ : Perm (Fin 6)) :=
    isConj_iff.1 (isConj_iff_cycleType_eq.2 (dt₀_cycleType.trans hσ.symm))
  have hx : ∀ k, ∑ i, pv π (dtx k) i = 0 := fun k => sum_pv_eq_zero π (dtx_sum k)
  obtain ⟨w₁, hw₁⟩ := d.β_surj (hmk _ (hx 0))
  obtain ⟨w₂, hw₂⟩ := d.β_surj (hmk _ (hx 1))
  have hc : ∀ k, pv (α ℓ : Perm (Fin 6)) (pv π (dtx k)) - pv π (dtx k) =
      pv π (pv dt₀ (dtx k) - dtx k) := fun k => by rw [← hπ, pv_conj]
  have hb₁ := d.beta_sub ℓ w₁ (hx 0) hw₁
  have hb₂ := d.beta_sub ℓ w₂ (hx 1) hw₂
  have hne : ∀ k, ¬ IsTriv (pv (α ℓ : Perm (Fin 6)) (pv π (dtx k)) - pv π (dtx k)) := by
    intro k
    rw [hc, isTriv_pv_iff]
    exact dt_three.1 k
  refine ⟨w₁, w₂, ?_, ?_, ?_⟩
  · intro h0
    have : β ⟨(ℓ : GLV V) w₁ - w₁, d.sub_mem ℓ w₁⟩ = 0 := by
      rw [show (⟨(ℓ : GLV V) w₁ - w₁, d.sub_mem ℓ w₁⟩ : ↥(commSpace L ⊤)) = 0 from
        Subtype.ext h0, map_zero]
    rw [hb₁, hmk_eq_zero_iff] at this
    exact hne 0 this
  · intro h0
    have : β ⟨(ℓ : GLV V) w₂ - w₂, d.sub_mem ℓ w₂⟩ = 0 := by
      rw [show (⟨(ℓ : GLV V) w₂ - w₂, d.sub_mem ℓ w₂⟩ : ↥(commSpace L ⊤)) = 0 from
        Subtype.ext h0, map_zero]
    rw [hb₂, hmk_eq_zero_iff] at this
    exact hne 1 this
  · intro h12
    have : β ⟨(ℓ : GLV V) w₁ - w₁, d.sub_mem ℓ w₁⟩ = β ⟨(ℓ : GLV V) w₂ - w₂, d.sub_mem ℓ w₂⟩ := by
      congr 1
      exact Subtype.ext h12
    rw [hb₁, hb₂, hmk_eq_hmk_iff, hc, hc, ← pv_sub, isTriv_pv_iff] at this
    exact dt_three.2 0 1 (by decide) this

theorem eq_zero_of_fixed (ℓ : ↥L) (hσ : (α ℓ : Perm (Fin 6)).cycleType = {3, 3})
    (w : ↥(commSpace L ⊤)) (hw : β ⟨(ℓ : GLV V) w, d.conj_mem ℓ w⟩ = β w) : β w = 0 := by
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 6), π * d3₀ * π⁻¹ = (α ℓ : Perm (Fin 6)) :=
    isConj_iff.1 (isConj_iff_cycleType_eq.2 (d3₀_cycleType.trans hσ.symm))
  obtain ⟨x, hx, hβw⟩ := exists_hmk (β w)
  rw [d.beta_conj ℓ w hx hβw, hβw, hmk_eq_hmk_iff] at hw
  have hx' : x = pv π (pv π⁻¹ x) := by rw [← pv_mul, mul_inv_cancel, pv_one_left]
  rw [hx', ← hπ, pv_conj, isTriv_pv_iff] at hw
  have h0 := d3_no_fixed (pv π⁻¹ x) (sum_pv_eq_zero _ hx) hw
  rw [hβw, hmk_eq_zero_iff, hx', isTriv_pv_iff]
  exact h0

theorem exists_fixed (ℓ : ↥L) (hℓ : (α ℓ : Perm (Fin 6)) = c3₀) :
    ∃ w : ↥(commSpace L ⊤), β w ≠ 0 ∧ β ⟨(ℓ : GLV V) w, d.conj_mem ℓ w⟩ = β w := by
  obtain ⟨hs, hnt, hfix⟩ := c3_fixed
  obtain ⟨w, hw⟩ := d.β_surj (hmk c3x hs)
  refine ⟨w, ?_, ?_⟩
  · rw [hw, Ne, hmk_eq_zero_iff]
    exact hnt
  · rw [d.beta_conj ℓ w hs hw, hw]
    simp only [hℓ, hfix]

end AD

end CaseII

end CFSG.CGT.Foote82
