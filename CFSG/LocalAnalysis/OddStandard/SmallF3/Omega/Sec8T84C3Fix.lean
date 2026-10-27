module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Ctx
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

open CFSG.GH74.GLS.Bg.TwoGroups.L218

variable {V : Type} [CommGroup V] [Finite V] {u : MulAut V} {H : Subgroup (MulAut V)}
  {Bv : Subgroup V}

theorem exists_fixed_of_invariant (F : Ctx V u H Bv) {W : Subgroup V}
    (hW : ∀ w ∈ W, u w ∈ W) (hne : W ≠ ⊥) : ∃ w ∈ W, w ≠ 1 ∧ u w = w := by
  by_contra h
  have hbot : W ⊓ fixE u = ⊥ := by
    by_contra hb
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
    exact h ⟨(x : V), x.2.1, (fun hx1 => hxne (Subtype.ext hx1)),
      (mem_fixE u (x : V)).mp x.2.2⟩
  have hcard := card_le_fixE_sq_sub F.sq u F.u_sq W hW
  rw [hbot, Subgroup.card_bot, one_pow] at hcard
  exact hne (Subgroup.eq_bot_of_card_le W hcard)

theorem bv_le_of_invariant (F : Ctx V u H Bv) {W : Subgroup V}
    (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) (hne : W ≠ ⊥) : Bv ≤ W := by
  intro b hb
  obtain ⟨w0, hw0W, hw0ne, hw0fix⟩ :=
    exists_fixed_of_invariant F (hW u F.u_mem) hne
  have hw0Bv : w0 ∈ Bv := (F.fix w0).mp hw0fix
  by_cases hb1 : b = 1
  · rw [hb1]; exact W.one_mem
  · obtain ⟨a, ha, haeq⟩ := F.trans w0 hw0Bv hw0ne b hb hb1
    rw [← haeq]
    exact hW a ha w0 hw0W

theorem eq_one_of_fixed_of_mem_closure (hsq : ∀ v : V, v * v = 1) {Q : Subgroup (MulAut V)}
    (hodd : Odd (Nat.card Q)) {w : V} (hfix : ∀ q ∈ Q, q w = w)
    (hw : w ∈ Subgroup.closure {x : V | ∃ q ∈ Q, ∃ e : V, x = q e * e⁻¹}) : w = 1 := by
  classical
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by
    intro h
    rw [h] at hodd
    exact absurd hodd (by decide))
  haveI : Fintype Q := Fintype.ofFinite Q
  let N : V →* V :=
    { toFun := fun v => ∏ σ : Q, (σ : MulAut V) v
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul]
        exact Finset.prod_mul_distrib }
  have hNinv : ∀ (τ : Q) (v : V), N ((τ : MulAut V) v) = N v := by
    intro τ v
    show ∏ σ : Q, (σ : MulAut V) ((τ : MulAut V) v) = ∏ σ : Q, (σ : MulAut V) v
    exact Fintype.prod_equiv (Equiv.mulRight τ) _ _ (fun σ => by simp [MulAut.mul_apply])
  have hNker : Subgroup.closure {x : V | ∃ q ∈ Q, ∃ e : V, x = q e * e⁻¹} ≤ N.ker := by
    rw [Subgroup.closure_le]
    rintro x ⟨σ, hσ, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
    rw [hNinv ⟨σ, hσ⟩ v, mul_inv_cancel]
  have hNw : N w = w ^ Nat.card Q := by
    show ∏ σ : Q, (σ : MulAut V) w = w ^ Nat.card Q
    have : ∀ σ : Q, (σ : MulAut V) w = w := fun σ => hfix σ σ.2
    simp only [this, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have h1 : N w = 1 := hNker hw
  obtain ⟨m, hm⟩ := hodd
  have hw' : w ^ Nat.card Q = w := by
    rw [hm, pow_succ, pow_mul, pow_two, hsq w, one_pow, one_mul]
  rw [← hw', ← hNw, h1]

theorem fixed_eq_one (F : Ctx V u H Bv) {Q : Subgroup (MulAut V)} (hQ : Q ≠ ⊥)
    (hodd : Odd (Nat.card Q)) (hQn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) :
    ∀ e : V, (∀ q ∈ Q, q e = e) → e = 1 := by
  classical
  set W1 : Subgroup V :=
    { carrier := {e : V | ∀ q ∈ Q, q e = e}
      one_mem' := fun q _ => map_one q
      mul_mem' := fun ha hb q hq => by rw [map_mul, ha q hq, hb q hq]
      inv_mem' := fun ha q hq => by rw [map_inv, ha q hq] } with hW1def
  set W2 : Subgroup V :=
    Subgroup.closure {x : V | ∃ q ∈ Q, ∃ e : V, x = q e * e⁻¹} with hW2def
  have hW1inv : ∀ h ∈ H, ∀ e ∈ W1, h e ∈ W1 := by
    intro h hh e he
    rw [hW1def] at he ⊢
    intro q hq
    have hq' : h⁻¹ * q * h ∈ Q := by
      have := hQn h⁻¹ (H.inv_mem hh) q hq
      simpa using this
    have hstep : q (h e) = h ((h⁻¹ * q * h) e) := by
      simp [MulAut.mul_apply]
    rw [hstep, he (h⁻¹ * q * h) hq']
  have hW2inv : ∀ h ∈ H, ∀ e ∈ W2, h e ∈ W2 := by
    intro h hh e he
    have hmap : Subgroup.map (h : MulAut V).toMonoidHom W2 ≤ W2 := by
      rw [hW2def, MonoidHom.map_closure, Subgroup.closure_le]
      rintro x ⟨y, ⟨q, hq, e, rfl⟩, rfl⟩
      have hmem : (h : MulAut V) (q e * e⁻¹) ∈
          {x : V | ∃ q ∈ Q, ∃ e : V, x = q e * e⁻¹} :=
        ⟨h * q * h⁻¹, hQn h hh q hq, h e, by simp [MulAut.mul_apply]⟩
      exact Subgroup.subset_closure hmem
    exact hmap (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)
  intro e0 he0
  by_contra he0ne
  have he0W1 : e0 ∈ W1 := by rw [hW1def]; exact he0
  have hW1ne : W1 ≠ ⊥ := by
    intro h
    have : e0 = 1 := by
      have : e0 ∈ (⊥ : Subgroup V) := h ▸ he0W1
      simpa using this
    exact he0ne this
  have hB1 : Bv ≤ W1 := bv_le_of_invariant F hW1inv hW1ne
  obtain ⟨q1, hq1ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
  have hq1ne' : (q1 : MulAut V) ≠ 1 := fun h => hq1ne (Subtype.ext h)
  obtain ⟨e1, he1⟩ : ∃ e1 : V, (q1 : MulAut V) e1 ≠ e1 := by
    by_contra h
    push Not at h
    exact hq1ne' (MulEquiv.ext fun x => by simpa using h x)
  have hxW2 : (q1 : MulAut V) e1 * e1⁻¹ ∈ W2 := by
    rw [hW2def]
    exact Subgroup.subset_closure (k := {x : V | ∃ q ∈ Q, ∃ e : V, x = q e * e⁻¹})
      ⟨(q1 : MulAut V), q1.2, e1, rfl⟩
  have hxne : (q1 : MulAut V) e1 * e1⁻¹ ≠ 1 := by
    intro h
    exact he1 (by
      have h2 := congrArg (fun y => y * e1) h
      simpa [mul_assoc, inv_mul_cancel, mul_one] using h2)
  have hW2ne : W2 ≠ ⊥ := by
    intro h
    have : (q1 : MulAut V) e1 * e1⁻¹ ∈ (⊥ : Subgroup V) := h ▸ hxW2
    exact hxne (by simpa using this)
  have hB2 : Bv ≤ W2 := bv_le_of_invariant F hW2inv hW2ne
  have hBne : Bv ≠ ⊥ := by
    intro h
    have : Nat.card Bv = 1 := by rw [h]; exact Subgroup.card_bot
    rw [F.card_B] at this
    norm_num at this
  obtain ⟨b, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbVne : (b : V) ≠ 1 := fun h => hbne (Subtype.ext h)
  have hbW1 : (b : V) ∈ W1 := hB1 b.2
  have hbW2 : (b : V) ∈ W2 := hB2 b.2
  rw [hW1def] at hbW1
  rw [hW2def] at hbW2
  exact hbVne (eq_one_of_fixed_of_mem_closure F.sq hodd hbW1 hbW2)

end C10

end CFSG.OddStandard.SmallF3.Omega
