module

public import CFSG.CGT.Stroth76.Lemma7OneData
public import CFSG.CGT.Stroth76.TFacts
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

@[expose] def upar (p : Tc) : ZMod 2 := p.2.2.2

theorem upar_tmul (p q : Tc) : upar (tmul p q) = upar p + upar q := rfl

theorem wpar_sig2 : ∀ p : Tc, wpar (sig2 p) = wpar p := by decide +kernel
theorem upar_sig2 : ∀ p : Tc, upar (sig2 p) = upar p := by decide +kernel

theorem sm2_snd (a b : Sc) :
    (sm2 a b).2 = tmul (if b.1 = 1 then sig2 a.2 else a.2) b.2 := by
  simp only [sm2, smulC, ite_self, IdxTwo.tmul_zero_left]

theorem sm2_fst (a b : Sc) : (sm2 a b).1 = a.1 + b.1 := rfl

theorem wpar_sm2 (a b : Sc) : wpar (sm2 a b).2 = wpar a.2 + wpar b.2 := by
  rw [sm2_snd, wpar_tmul]
  split_ifs <;> simp [wpar_sig2]

theorem upar_sm2 (a b : Sc) : upar (sm2 a b).2 = upar a.2 + upar b.2 := by
  rw [sm2_snd, upar_tmul]
  split_ifs <;> simp [upar_sig2]

@[expose] def notInvXYCheck (p : Tc) : Bool :=
  !(tmul ((0, 1, 0), 0) p == tmul p ((0, 3, 0), 0) && tmul ((0, 0, 1), 0) p == tmul p ((0, 0, 3), 0))

theorem notInvXYCheck_all : ∀ p : Tc, notInvXYCheck p = true := by decide +kernel

@[expose] def chi1 (r : Sc) : ZMod 2 := wpar r.2
@[expose] def chi3 (r : Sc) : ZMod 2 := wpar r.2 + upar r.2
@[expose] def chi4 (r : Sc) : ZMod 2 := wpar r.2 + upar r.2 + r.1

theorem chi1_sm2 (a b : Sc) : chi1 (sm2 a b) = chi1 a + chi1 b := by
  simp only [chi1, wpar_sm2]
theorem chi3_sm2 (a b : Sc) : chi3 (sm2 a b) = chi3 a + chi3 b := by
  simp only [chi3, wpar_sm2, upar_sm2]; ring
theorem chi4_sm2 (a b : Sc) : chi4 (sm2 a b) = chi4 a + chi4 b := by
  simp only [chi4, wpar_sm2, upar_sm2, sm2_fst]; ring

theorem card_chi1 : Fintype.card {r : Sc // chi1 r = 0} = 2 ^ 8 := by decide +kernel
theorem card_chi3 : Fintype.card {r : Sc // chi3 r = 0} = 2 ^ 8 := by decide +kernel
theorem card_chi4 : Fintype.card {r : Sc // chi4 r = 0} = 2 ^ 8 := by decide +kernel

theorem inS1_iff (r : Sc) : inS1 r = true ↔ chi1 r = 0 := by
  obtain ⟨e, ⟨i, j, l⟩, a, b, c⟩ := r
  simp only [inS1, chi1, wpar, beq_iff_eq]
theorem inS3_iff (r : Sc) : inS3 r = true ↔ chi3 r = 0 := by
  obtain ⟨e, ⟨i, j, l⟩, a, b, c⟩ := r
  simp only [inS3, chi3, wpar, upar, beq_iff_eq]
  revert i c; decide
theorem inS4_iff (r : Sc) : inS4 r = true ↔ chi4 r = 0 := by
  obtain ⟨e, ⟨i, j, l⟩, a, b, c⟩ := r
  simp only [inS4, chi4, wpar, upar, beq_iff_eq]
  revert e i c; decide

section Main

variable {G : Type*} [Group G] [Finite G] (K : Config G)

theorem tElt_x_inv : tElt K ((0, 3, 0), 0) = K.x⁻¹ := by rw [tElt_ev, K.ev_030]
theorem tElt_y_inv : tElt K ((0, 0, 3), 0) = K.y⁻¹ := by
  rw [tElt_ev, K.y_inv_eq]
  simp [Config.ev, show (3 : ZMod 4).val = 3 from rfl]
theorem tElt_xyuv' : tElt K ((0, 1, 1), (1, 0, 0)) = K.x * K.y * K.uv := tElt_xyuvC K
theorem tElt_xinv_t : tElt K ((0, 3, 0), (0, 1, 0)) = K.x⁻¹ * K.t := by
  rw [show ((0, 3, 0), (0, 1, 0)) = tmul ((0, 3, 0), 0) (0, (0, 1, 0)) from rfl, tElt_mul,
    tElt_x_inv, tElt_gen_t]

@[expose] def idxTwo2 {s : G} (hs2 : s ^ 2 = 1) (hsw : s⁻¹ * K.w * s = K.w)
    (hsx : s⁻¹ * K.x * s = K.x⁻¹) (hsy : s⁻¹ * K.y * s = K.y⁻¹)
    (hsuv : s⁻¹ * K.uv * s = K.x * K.y * K.uv) (hst : s⁻¹ * K.t * s = K.x⁻¹ * K.t)
    (hsu : s⁻¹ * K.u * s = K.u) (hsT : s ∉ Tsub K) : IdxTwo K where
  s := s
  iw := ((1, 0, 0), 0)
  ix := ((0, 3, 0), 0)
  iy := ((0, 0, 3), 0)
  iuv := ((0, 1, 1), (1, 0, 0))
  it := ((0, 3, 0), (0, 1, 0))
  iu := (0, (0, 0, 1))
  z := (0, 0)
  hw := by rw [tElt_w, hsw]
  hx := by rw [tElt_x_inv, hsx]
  hy := by rw [tElt_y_inv, hsy]
  huv := by rw [tElt_xyuv', hsuv]
  ht := by rw [tElt_xinv_t, hst]
  hu := by rw [tElt_gen_u, hsu]
  hz := by rw [tElt_zero, ← pow_two, hs2]
  hsT := hsT

theorem s_not_mem_T {s : G} (hsx : s⁻¹ * K.x * s = K.x⁻¹) (hsy : s⁻¹ * K.y * s = K.y⁻¹) :
    s ∉ Tsub K := by
  intro hs
  obtain ⟨p, rfl⟩ := exists_tElt K hs
  have hx : tmul ((0, 1, 0), 0) p = tmul p ((0, 3, 0), 0) := tElt_injective K (by
    rw [tElt_mul, tElt_mul, tElt_x, tElt_x_inv, ← hsx]; group)
  have hy : tmul ((0, 0, 1), 0) p = tmul p ((0, 0, 3), 0) := tElt_injective K (by
    rw [tElt_mul, tElt_mul, tElt_y, tElt_y_inv, ← hsy]; group)
  have := notInvXYCheck_all p
  simp only [notInvXYCheck, hx, hy, beq_self_eq_true, Bool.and_self, Bool.not_true] at this
  exact Bool.false_ne_true this

variable {K}

@[expose] def charSub (D : IdxTwo K) (hD : ∀ a b, D.smul a b = sm2 a b) (χ : Sc → ZMod 2)
    (hχ : ∀ a b, χ (sm2 a b) = χ a + χ b) : Subgroup G where
  carrier := {g | ∃ r, χ r = 0 ∧ D.sElt r = g}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨sm2 a b, by rw [hχ, ha, hb, add_zero], by rw [← hD, D.sElt_mul]⟩
  one_mem' := ⟨(0, (0, 0)), by
      have h := hχ (0, (0, 0)) (0, (0, 0))
      have h0 : sm2 (0, (0, 0)) (0, (0, 0)) = (0, (0, 0)) := by decide
      rw [h0] at h
      generalize χ (0, (0, 0)) = a at h
      revert a; decide,
    by rw [D.sElt_zero_fst, tElt_zero]⟩
  inv_mem' := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨r', hr'⟩ := D.exists_sElt (D.Ssub.inv_mem (D.sElt_mem r))
    refine ⟨r', ?_, hr'⟩
    have h1 : sm2 r r' = (0, (0, 0)) := D.sElt_injective (by
      rw [← hD, D.sElt_mul, hr', mul_inv_cancel, D.sElt_zero_fst, tElt_zero])
    have h0 : χ (0, (0, 0)) = 0 := by
      have h := hχ (0, (0, 0)) (0, (0, 0))
      have h0 : sm2 (0, (0, 0)) (0, (0, 0)) = (0, (0, 0)) := by decide
      rw [h0] at h
      generalize χ (0, (0, 0)) = a at h
      revert a; decide
    have h2 := hχ r r'
    rw [h1, h0, hr, zero_add] at h2
    exact h2.symm

theorem charSub_le (D : IdxTwo K) (hD) (χ) (hχ) : charSub D hD χ hχ ≤ D.Ssub := by
  rintro _ ⟨r, -, rfl⟩
  exact D.sElt_mem r

theorem card_charSub (D : IdxTwo K) (hD) (χ : Sc → ZMod 2) (hχ) [DecidablePred (fun r => χ r = 0)] :
    Nat.card (charSub D hD χ hχ) = Fintype.card {r : Sc // χ r = 0} := by
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun r : {r : Sc // χ r = 0} => (⟨D.sElt r, ⟨r, r.2, rfl⟩⟩ : charSub D hD χ hχ)) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (D.sElt_injective (congrArg Subtype.val h))
  · rintro ⟨g, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

theorem not_mem_charSub (D : IdxTwo K) (hD) (χ) (hχ) {r : Sc} (hr : χ r ≠ 0) :
    D.sElt r ∉ charSub D hD χ hχ := by
  rintro ⟨r', hr', he⟩
  exact hr (D.sElt_injective he ▸ hr')

theorem isConj_of_mem_tab (D : IdxTwo K) (hD : ∀ a b, D.smul a b = sm2 a b)
    {tab : List (Sc × Sc × Sc)} {targets : List Sc} (hchk : checkTab tab targets = true)
    {e : Sc × Sc × Sc} (he : e ∈ tab) :
    IsConj (D.sElt e.1) (D.sElt e.2.2) ∧ e.2.2 ∈ targets := by
  have h := List.all_eq_true.1 hchk e he
  simp only [Bool.and_eq_true, conjChk, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨isConj_iff.2 ⟨(D.sElt e.2.1)⁻¹, ?_⟩, h2⟩
  have h3 : D.sElt e.1 * D.sElt e.2.1 = D.sElt e.2.1 * D.sElt e.2.2 := by
    rw [← D.sElt_mul, ← D.sElt_mul, hD, hD, h1]
  rw [inv_inv, ← mul_inv_eq_iff_eq_mul.2 h3.symm] at *
  group

end Main

theorem zc2_central : ∀ r : Sc, sm2 r zc2 = sm2 zc2 r := by decide +kernel

theorem q1_sq_mem_A : ∀ r : Sc, (!inQ1 r || ((sm2 r r).1 == 0 && (sm2 r r).2.2 == 0)) = true := by
  decide +kernel

theorem q1_comm_mem_A : ∀ r : Sc,
    (!(inQ1 r && sm2 r (0, ((0, 2, 0), 0)) == sm2 (0, ((0, 2, 0), 0)) r &&
      sm2 r (0, ((0, 1, 1), 0)) == sm2 (0, ((0, 1, 1), 0)) r) || (r.1 == 0 && r.2.2 == 0)) = true := by
  decide +kernel

theorem q1_comm_w : ∀ r : Sc, (!inQ1 r || sm2 r wc2 == sm2 wc2 r) = true := by decide +kernel

theorem wxuv_wu_ord : (let p := sm2 (0, ((1, 1, 0), (1, 0, 0))) (0, ((1, 0, 0), (0, 0, 1)))
    sm2 (sm2 p p) (sm2 p p) != one2) = true := by decide

theorem comm_facts :
    (sm2 (0, ((1, 1, 0), (1, 0, 0))) (1, ((0, 0, 0), (0, 0, 1))) ==
        sm2 (1, ((0, 0, 0), (0, 0, 1))) (0, ((1, 1, 0), (1, 0, 0))) &&
      sm2 (0, ((1, 0, 0), (0, 0, 1))) (1, ((0, 0, 0), (0, 0, 1))) ==
        sm2 (1, ((0, 0, 0), (0, 0, 1))) (0, ((1, 0, 0), (0, 0, 1)))) = true := by decide

end CFSG.CGT.Stroth76
