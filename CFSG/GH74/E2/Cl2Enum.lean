module

public import CFSG.GH74.E2.Cl2E2
public import CFSG.GH74.E2.Cl2Tensor

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

section Aux

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

namespace Enum

theorem abInv (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : AbInv2 a b (dsub Q) :=
  ⟨h.dsub_comm hQ, h.dsub_inva, h.dsub_invb⟩

theorem eps_eq_of_fix {n : Q} (hn : n * n = 1) (ha : a n = n) : eps a n = n := by
  unfold eps
  rw [ha, ha, hn, one_mul]

theorem N_comm (h : Cl3 Q a b N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun _ hx y _ =>
  (Subgroup.mem_center_iff.1 (h.N_central hx) y).symm

theorem conj_N (h : Cl3 Q a b N) (g : Q) {n : Q} (hn : n ∈ N) : g * n * g⁻¹ = n := by
  have := Subgroup.mem_center_iff.1 (h.N_central hn) g
  calc g * n * g⁻¹ = (n * g) * g⁻¹ := by rw [this]
    _ = n := by group

theorem N_abInv (h : Cl3 Q a b N) : AbInv2 a b N :=
  ⟨N_comm h, h.N_inva, h.N_invb⟩

theorem eps_eq_one (h : Cl3 Q a b N) (hfpf : ∀ n ∈ N, a n = n → n = 1) {n : Q} (hn : n ∈ N) :
    eps a n = 1 := by
  have ha3 := h.bpair.a_cube
  have h1 := h.N_inva n hn
  have h2 := h.N_inva _ h1
  have hmem : eps a n ∈ N := N.mul_mem (N.mul_mem hn h1) h2
  apply hfpf _ hmem
  have h3 : a (a (a n)) = n := Cl2Wt.cube_apply ha3 n
  unfold eps
  rw [map_mul, map_mul, h3]
  calc a n * a (a n) * n = n * (a n * a (a n)) := (N_comm h _ (N.mul_mem h1 h2) n hn)
    _ = n * a n * a (a n) := by rw [mul_assoc]

end Enum

end Aux

section Enum

variable {Q : Type*} [Group Q] [Finite Q] {a b : MulAut Q} {N : Subgroup Q}

namespace Enum

abbrev W (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : Wt → Subgroup Q := wsub a b (dsub Q) (abInv hQ h)

abbrev E (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : Subgroup Q := omega1 (dsub Q) (abInv hQ h).comm

abbrev WE (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : Wt → Subgroup Q :=
  wsub a b (E hQ h) (abInv hQ h).omega1

theorem E_card_le (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : Nat.card (E hQ h) ≤ 16 := by
  have := FourGen.relIndex_le h.four (H := E hQ h) (R := ⊥)
    (fun x _ r hr => by
      rw [Subgroup.mem_bot] at hr
      rw [hr]
      simp)
    (fun x hx => by
      rw [Subgroup.mem_bot]
      exact hx.2)
  rwa [Subgroup.relIndex_bot_left] at this

theorem prod_le (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) :
    Nat.card (WE hQ h .w0) * Nat.card (WE hQ h .wa) * Nat.card (WE hQ h .wb) *
      Nat.card (WE hQ h .wp) * Nat.card (WE hQ h .wm) ≤ 16 := by
  have := wsub_card hQ h.bpair.a_cube h.bpair.b_cube h.bpair.comm (abInv hQ h).omega1
  rw [← this]
  exact E_card_le hQ h

theorem pos (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (w : Wt) : 1 ≤ Nat.card (WE hQ h w) :=
  Nat.card_pos

omit [Finite Q] in
theorem eq_one_of_bot (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {w : Wt} {y : Q}
    (hw : W hQ h w = ⊥) (hy : y ∈ W hQ h w) : y = 1 := by
  rw [hw] at hy
  exact Subgroup.mem_bot.1 hy

theorem card_eq (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) :
    Nat.card (E hQ h) = Nat.card (WE hQ h .w0) * Nat.card (WE hQ h .wa) *
      Nat.card (WE hQ h .wb) * Nat.card (WE hQ h .wp) * Nat.card (WE hQ h .wm) :=
  wsub_card hQ h.bpair.a_cube h.bpair.b_cube h.bpair.comm (abInv hQ h).omega1

theorem card_ge (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {w : Wt} (hne : W hQ h w ≠ ⊥) :
    2 ≤ Nat.card (WE hQ h w) ∧ (w ≠ Wt.w0 → 4 ≤ Nat.card (WE hQ h w)) := by
  have ha3 := h.bpair.a_cube
  have hb3 := h.bpair.b_cube
  have hab := h.bpair.comm
  have hne' : WE hQ h w ≠ ⊥ := wsub_omega1_ne_bot hQ ha3 hb3 hab (abInv hQ h) hne
  have h1 : Nat.card (WE hQ h w) ≠ 1 := fun e => hne' (Subgroup.card_eq_one.1 e)
  refine ⟨by have := pos hQ h w; omega, fun hw => ?_⟩
  exact wsub_card_ge_four hQ ha3 hb3 hab (abInv hQ h).omega1 (fun x hx => hx.2) hw hne'

theorem prod_ge (x0 xa xb xp xm y0 ya yb yp ym : ℕ) (h0 : y0 ≤ x0) (ha : ya ≤ xa) (hb : yb ≤ xb)
    (hp : yp ≤ xp) (hm : ym ≤ xm) : y0 * ya * yb * yp * ym ≤ x0 * xa * xb * xp * xm :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 ha) hb) hp) hm

end Enum

theorem Cl3.N_type (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) :
    NTypeA a b N ∨ NTypeB a b N ∨ NTypeP a b N ∨ NTypeM a b N := by
  have ha3 := h.bpair.a_cube
  have hb3 := h.bpair.b_cube
  have hab := h.bpair.comm
  have hN := Enum.N_abInv h
  have hWN : ∀ w, wsub a b N hN w = ⊥ ∨ wsub a b N hN w = N := fun w =>
    h.N_simple _ (wsub_le hN w) (fun x hx => (wsub_inv hQ ha3 hb3 hab hN w hx).1)
      (fun x hx => (wsub_inv hQ ha3 hb3 hab hN w hx).2)
  obtain ⟨w, hw⟩ : ∃ w, wsub a b N hN w = N := by
    by_contra hcon
    have hcon' : ∀ w, wsub a b N hN w ≠ N := fun w hw => hcon ⟨w, hw⟩
    apply h.N_ne
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
      wsub_decomp hQ ha3 hb3 hab hN hn
    have e : ∀ w, ∀ y ∈ wsub a b N hN w, y = 1 := fun w y hy => by
      rcases hWN w with h0 | h0
      · rw [h0] at hy
        exact Subgroup.mem_bot.1 hy
      · exact absurd h0 (hcon' w)
    rw [e _ x0 hx0, e _ xa hxa, e _ xb hxb, e _ xp hxp, e _ xm hxm]
    simp
  have hmem : ∀ n ∈ N, n ∈ wsub a b N hN w := fun n hn => by
    rw [hw]
    exact hn
  have hsq := h.N_elem
  cases w with
  | w0 =>
    exfalso
    apply h.N_ne
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨-, h1, h2⟩ := (mem_wsub_w0 hN).1 (hmem n hn)
    exact Subgroup.mem_bot.2 (Cl3.N_fixed_free hQ h hn h1 h2)
  | wa =>
    left
    refine ⟨fun n hn => ((mem_wsub_wa hN).1 (hmem n hn)).2.1, fun n hn han => ?_⟩
    have h1 := ((mem_wsub_wa hN).1 (hmem n hn)).2.2
    rw [← Enum.eps_eq_of_fix (hsq n hn) han]
    exact h1
  | wb =>
    right
    left
    refine ⟨fun n hn => ((mem_wsub_wb hN).1 (hmem n hn)).2.1, fun n hn hbn => ?_⟩
    have h1 := ((mem_wsub_wb hN).1 (hmem n hn)).2.2
    rw [← Enum.eps_eq_of_fix (hsq n hn) hbn]
    exact h1
  | wp =>
    right
    right
    left
    refine ⟨fun n hn => ((mem_wsub_wp hN).1 (hmem n hn)).2.1, fun n hn han => ?_⟩
    have h1 := ((mem_wsub_wp hN).1 (hmem n hn)).2.2
    rw [← Enum.eps_eq_of_fix (hsq n hn) han]
    exact h1
  | wm =>
    right
    right
    right
    refine ⟨fun n hn => ((mem_wsub_wm hN).1 (hmem n hn)).2.1, fun n hn han => ?_⟩
    have h1 := ((mem_wsub_wm hN).1 (hmem n hn)).2.2
    rw [← Enum.eps_eq_of_fix (hsq n hn) han]
    exact h1

omit [Finite Q] in
theorem Cl3.NTypeM_toP (_hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hM : NTypeM a b N) :
    NTypeP a b⁻¹ N := by
  have hb3 := h.bpair.b_cube
  refine ⟨fun n hn => ?_, hM.2⟩
  have h3 : b (b (b n)) = n := Cl2Wt.cube_apply hb3 n
  have hinv : b⁻¹ n = b (b n) := by
    have := MulAut.inv_apply_self Q b (b (b n))
    rw [h3] at this
    exact this
  have hn' : b⁻¹ n ∈ N := by
    rw [hinv]
    exact h.N_invb _ (h.N_invb n hn)
  have := hM.1 (b⁻¹ n) hn'
  rwa [MulAut.apply_inv_self] at this

theorem Cl3.cases_alpha (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hA : NTypeA a b N) :
    CaseAHyp Q a b N ∨ CaseBHyp Q a b N ∨ CaseBHyp Q a b⁻¹ N := by
  have ha3 := h.bpair.a_cube
  have hb3 := h.bpair.b_cube
  have hab := h.bpair.comm
  have hAi := Enum.abInv hQ h
  have hNA := h.N_le_dsub hQ
  have hcomm : ∀ y, a (b y) = b (a y) := fun y => by
    have := congrArg (fun f : MulAut Q => f y) hab
    simpa [MulAut.mul_apply] using this
  have F1 : ∀ n ∈ N, n ∈ Enum.W hQ h .wa := fun n hn =>
    (mem_wsub_wa hAi).2 ⟨hNA hn, hA.1 n hn, Enum.eps_eq_one h hA.2 hn⟩
  have F2 : ∀ u ∈ Enum.W hQ h .wa, u ∈ N := fun u hu => by
    obtain ⟨hu1, hu2, hu3⟩ := (mem_wsub_wa hAi).1 hu
    exact Cl3.E2_a hQ h hu1 (by rw [hu2, mul_inv_cancel]; exact N.one_mem)
      (by rw [hu3]; exact N.one_mem)
  have F3 : Enum.W hQ h .wb = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := (mem_wsub_wb hAi).1 hu
    have huN : u ∈ N := Cl3.E2_b hQ h hu1 (by rw [hu2, mul_inv_cancel]; exact N.one_mem)
      (by rw [hu3]; exact N.one_mem)
    exact Subgroup.mem_bot.2 (hA.2 u huN hu2)
  have hwa : Enum.W hQ h .wa ≠ ⊥ := by
    intro hbot
    apply h.N_ne
    rw [eq_bot_iff]
    intro n hn
    have := F1 n hn
    rw [hbot] at this
    exact this
  have hca : 4 ≤ Nat.card (Enum.WE hQ h .wa) := (Enum.card_ge hQ h hwa).2 (by decide)
  have hpr := Enum.prod_le hQ h
  have hpos := Enum.pos hQ h
  have hbinv : ∀ n ∈ N, b⁻¹ n = n := fun n hn => by
    calc b⁻¹ n = b⁻¹ (b n) := by rw [hA.1 n hn]
      _ = n := MulAut.inv_apply_self Q b n
  have hfixa : ∀ (hW0 : Enum.W hQ h .w0 = ⊥) (u : Q), u ∈ dsub Q → a u = u → u = 1 := by
    intro hW0 u hu hau
    obtain ⟨x0, hx0, xb, hxb, rfl⟩ := fix_a_decomp hQ ha3 hb3 hab hAi hu hau
    rw [Enum.eq_one_of_bot hQ h hW0 hx0, Enum.eq_one_of_bot hQ h F3 hxb, one_mul]
  by_cases hp : Enum.W hQ h .wp = ⊥
  · by_cases hm : Enum.W hQ h .wm = ⊥
    ·
      left
      refine ⟨hA, fun u hu => ?_⟩
      obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
        wsub_decomp hQ ha3 hb3 hab hAi hu
      have e2 : xb = 1 := Enum.eq_one_of_bot hQ h F3 hxb
      have e3 : xp = 1 := Enum.eq_one_of_bot hQ h hp hxp
      have e4 : xm = 1 := Enum.eq_one_of_bot hQ h hm hxm
      subst e2 e3 e4
      simp only [mul_one]
      have hx0a : a x0 = x0 := ((mem_wsub_w0 hAi).1 hx0).2.1
      have hx0b : b x0 = x0 := ((mem_wsub_w0 hAi).1 hx0).2.2
      have hxaN : xa ∈ N := F2 xa hxa
      refine ⟨?_, ?_⟩
      · have hm' : a xa * xa⁻¹ ∈ N := N.mul_mem (h.N_inva xa hxaN) (N.inv_mem hxaN)
        have e : a (x0 * xa) * (x0 * xa)⁻¹ = x0 * (a xa * xa⁻¹) * x0⁻¹ := by
          rw [map_mul, hx0a]
          group
        rw [e, Enum.conj_N h x0 hm']
        exact hm'
      · rw [map_mul, hx0b, hA.1 xa hxaN, mul_inv_cancel]
        exact N.one_mem
    ·
      right
      right
      have hcm : 4 ≤ Nat.card (Enum.WE hQ h .wm) := (Enum.card_ge hQ h hm).2 (by decide)
      have hW0 : Enum.W hQ h .w0 = ⊥ := by
        by_contra hne
        have h2 := (Enum.card_ge hQ h hne).1
        have := Enum.prod_ge _ _ _ _ _ 2 4 1 1 4 h2 hca (hpos .wb) (hpos .wp) hcm
        exact absurd (this.trans hpr) (by norm_num)
      refine ⟨⟨fun n hn => hbinv n hn, hA.2⟩, fun u hu => ?_, fun u hu hau => hfixa hW0 u hu hau⟩
      obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
        wsub_decomp hQ ha3 hb3 hab hAi hu
      have e0 : x0 = 1 := Enum.eq_one_of_bot hQ h hW0 hx0
      have e2 : xb = 1 := Enum.eq_one_of_bot hQ h F3 hxb
      have e3 : xp = 1 := Enum.eq_one_of_bot hQ h hp hxp
      subst e0 e2 e3
      simp only [one_mul, mul_one]
      have hxaN : xa ∈ N := F2 xa hxa
      have hxm1 : a (b xm) = xm := ((mem_wsub_wm hAi).1 hxm).2.1
      have hb1 : b⁻¹ xm = a xm :=
        calc b⁻¹ xm = b⁻¹ (a (b xm)) := by rw [hxm1]
          _ = b⁻¹ (b (a xm)) := by rw [hcomm]
          _ = a xm := MulAut.inv_apply_self Q b _
      rw [map_mul, map_mul, hbinv xa hxaN, hb1]
      have e : xa * a xm * (a xa * a xm)⁻¹ = xa * (a xa)⁻¹ := by group
      rw [e]
      exact N.mul_mem hxaN (N.inv_mem (h.N_inva xa hxaN))
  ·
    right
    left
    have hcp : 4 ≤ Nat.card (Enum.WE hQ h .wp) := (Enum.card_ge hQ h hp).2 (by decide)
    have hW0 : Enum.W hQ h .w0 = ⊥ := by
      by_contra hne
      have h2 := (Enum.card_ge hQ h hne).1
      have := Enum.prod_ge _ _ _ _ _ 2 4 1 4 1 h2 hca (hpos .wb) hcp (hpos .wm)
      exact absurd (this.trans hpr) (by norm_num)
    have hWm : Enum.W hQ h .wm = ⊥ := by
      by_contra hne
      have h2 := (Enum.card_ge hQ h hne).2 (by decide)
      have := Enum.prod_ge _ _ _ _ _ 1 4 1 4 4 (hpos .w0) hca (hpos .wb) hcp h2
      exact absurd (this.trans hpr) (by norm_num)
    refine ⟨hA, fun u hu => ?_, fun u hu hau => hfixa hW0 u hu hau⟩
    obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
      wsub_decomp hQ ha3 hb3 hab hAi hu
    have e0 : x0 = 1 := Enum.eq_one_of_bot hQ h hW0 hx0
    have e2 : xb = 1 := Enum.eq_one_of_bot hQ h F3 hxb
    have e4 : xm = 1 := Enum.eq_one_of_bot hQ h hWm hxm
    subst e0 e2 e4
    simp only [one_mul, mul_one]
    have hxaN : xa ∈ N := F2 xa hxa
    have hxpe : a xp = b xp := ((mem_wsub_wp hAi).1 hxp).2.1
    rw [map_mul, map_mul, hA.1 xa hxaN, ← hxpe]
    have e : xa * a xp * (a xa * a xp)⁻¹ = xa * (a xa)⁻¹ := by group
    rw [e]
    exact N.mul_mem hxaN (N.inv_mem (h.N_inva xa hxaN))

theorem Cl3.cases_plus (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hP : NTypeP a b N) :
    CaseCHyp Q a b N ∨ CaseDHyp Q a b N := by
  have ha3 := h.bpair.a_cube
  have hb3 := h.bpair.b_cube
  have hab := h.bpair.comm
  have hAi := Enum.abInv hQ h
  have hNA := h.N_le_dsub hQ
  have F1 : ∀ n ∈ N, n ∈ Enum.W hQ h .wp := fun n hn =>
    (mem_wsub_wp hAi).2 ⟨hNA hn, hP.1 n hn, Enum.eps_eq_one h hP.2 hn⟩
  have F2a : Enum.W hQ h .wa = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := (mem_wsub_wa hAi).1 hu
    have huN : u ∈ N := Cl3.E2_a hQ h hu1 (by rw [hu2, mul_inv_cancel]; exact N.one_mem)
      (by rw [hu3]; exact N.one_mem)
    have hau : a u = u := by rw [hP.1 u huN, hu2]
    exact Subgroup.mem_bot.2 (hP.2 u huN hau)
  have F2b : Enum.W hQ h .wb = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := (mem_wsub_wb hAi).1 hu
    have huN : u ∈ N := Cl3.E2_b hQ h hu1 (by rw [hu2, mul_inv_cancel]; exact N.one_mem)
      (by rw [hu3]; exact N.one_mem)
    exact Subgroup.mem_bot.2 (hP.2 u huN hu2)
  have hwp : Enum.W hQ h .wp ≠ ⊥ := by
    intro hbot
    apply h.N_ne
    rw [eq_bot_iff]
    intro n hn
    have := F1 n hn
    rw [hbot] at this
    exact this
  obtain ⟨u0, hu0, hu01, hu02, hu03⟩ := Cl3.tensor_plus hQ h hP
  have hwm : Enum.W hQ h .wm ≠ ⊥ := by
    intro hbot
    apply hu01
    have : u0 ∈ Enum.W hQ h .wm := (mem_wsub_wm hAi).2 ⟨hu0, hu02, hu03⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have hcp : 4 ≤ Nat.card (Enum.WE hQ h .wp) := (Enum.card_ge hQ h hwp).2 (by decide)
  have hcm : 4 ≤ Nat.card (Enum.WE hQ h .wm) := (Enum.card_ge hQ h hwm).2 (by decide)
  have hpr := Enum.prod_le hQ h
  have hpos := Enum.pos hQ h
  have hW0 : Enum.W hQ h .w0 = ⊥ := by
    by_contra hne
    have h2 := (Enum.card_ge hQ h hne).1
    have := Enum.prod_ge _ _ _ _ _ 2 1 1 4 4 h2 (hpos .wa) (hpos .wb) hcp hcm
    exact absurd (this.trans hpr) (by norm_num)
  have hrel : 16 ≤ (sqsub (dsub Q)).relIndex (dsub Q) := by
    rw [← omega1_card_eq_relIndex_sqsub hAi.comm]
    show 16 ≤ Nat.card (Enum.E hQ h)
    have hc := Enum.card_eq hQ h
    have h16 : 1 * 1 * 1 * 4 * 4 ≤ Nat.card (Enum.WE hQ h .w0) * Nat.card (Enum.WE hQ h .wa) *
        Nat.card (Enum.WE hQ h .wb) * Nat.card (Enum.WE hQ h .wp) *
          Nat.card (Enum.WE hQ h .wm) :=
      Enum.prod_ge _ _ _ _ _ 1 1 1 4 4 (hpos .w0) (hpos .wa) (hpos .wb) hcp hcm
    omega
  have hMa : ∀ x ∈ N ⊓ sqsub (dsub Q), a x ∈ N ⊓ sqsub (dsub Q) := by
    intro x hx
    refine ⟨h.N_inva x hx.1, ?_⟩
    obtain ⟨u, hu, hxu⟩ := (mem_sqsub_iff hAi.comm).1 hx.2
    exact (mem_sqsub_iff hAi.comm).2 ⟨a u, h.dsub_inva u hu, by rw [hxu, map_mul]⟩
  have hMb : ∀ x ∈ N ⊓ sqsub (dsub Q), b x ∈ N ⊓ sqsub (dsub Q) := by
    intro x hx
    refine ⟨h.N_invb x hx.1, ?_⟩
    obtain ⟨u, hu, hxu⟩ := (mem_sqsub_iff hAi.comm).1 hx.2
    exact (mem_sqsub_iff hAi.comm).2 ⟨b u, h.dsub_invb u hu, by rw [hxu, map_mul]⟩
  have hfa : ∀ u ∈ dsub Q, a u = u → u = 1 := by
    intro u hu hau
    obtain ⟨x0, hx0, xb, hxb, rfl⟩ := fix_a_decomp hQ ha3 hb3 hab hAi hu hau
    rw [Enum.eq_one_of_bot hQ h hW0 hx0, Enum.eq_one_of_bot hQ h F2b hxb, one_mul]
  have hfb : ∀ u ∈ dsub Q, b u = u → u = 1 := by
    intro u hu hbu
    obtain ⟨x0, hx0, xa, hxa, rfl⟩ := fix_b_decomp hQ ha3 hb3 hab hAi hu hbu
    rw [Enum.eq_one_of_bot hQ h hW0 hx0, Enum.eq_one_of_bot hQ h F2a hxa, one_mul]
  rcases h.N_simple (N ⊓ sqsub (dsub Q)) inf_le_left hMa hMb with hM | hM
  · left
    refine ⟨hP, fun n hn ⟨u, hu, hnu⟩ => ?_, hfa, hfb, hrel⟩
    have hmem : n ∈ N ⊓ sqsub (dsub Q) := ⟨hn, (mem_sqsub_iff hAi.comm).2 ⟨u, hu, hnu⟩⟩
    rw [hM] at hmem
    exact Subgroup.mem_bot.1 hmem
  · right
    refine ⟨hP, fun n hn => ?_, hfa, hfb, hrel⟩
    have hmem : n ∈ N ⊓ sqsub (dsub Q) := by
      rw [hM]
      exact hn
    exact (mem_sqsub_iff hAi.comm).1 hmem.2

theorem Cl3.cases (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) :
    ∃ a' b' : MulAut Q, Cl3 Q a' b' N ∧
      (CaseAHyp Q a' b' N ∨ CaseBHyp Q a' b' N ∨ CaseCHyp Q a' b' N ∨ CaseDHyp Q a' b' N) := by
  rcases Cl3.N_type hQ h with hA | hB | hP | hM
  · rcases Cl3.cases_alpha hQ h hA with hc | hc | hc
    · exact ⟨a, b, h, Or.inl hc⟩
    · exact ⟨a, b, h, Or.inr (Or.inl hc)⟩
    · exact ⟨a, b⁻¹, h.inv_right, Or.inr (Or.inl hc)⟩
  · have h' := h.swap
    have hA : NTypeA b a N := hB
    rcases Cl3.cases_alpha hQ h' hA with hc | hc | hc
    · exact ⟨b, a, h', Or.inl hc⟩
    · exact ⟨b, a, h', Or.inr (Or.inl hc)⟩
    · exact ⟨b, a⁻¹, h'.inv_right, Or.inr (Or.inl hc)⟩
  · rcases Cl3.cases_plus hQ h hP with hc | hc
    · exact ⟨a, b, h, Or.inr (Or.inr (Or.inl hc))⟩
    · exact ⟨a, b, h, Or.inr (Or.inr (Or.inr hc))⟩
  · rcases Cl3.cases_plus hQ h.inv_right (Cl3.NTypeM_toP hQ h hM) with hc | hc
    · exact ⟨a, b⁻¹, h.inv_right, Or.inr (Or.inr (Or.inl hc))⟩
    · exact ⟨a, b⁻¹, h.inv_right, Or.inr (Or.inr (Or.inr hc))⟩

end Enum

end CFSG.GH74.E2
