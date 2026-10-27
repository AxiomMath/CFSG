module

public import Certificates.Data.Kernel.IdxFourTcosetK
public import CFSG.Certificates.Kernel.IdxFourLbarSound
public import CFSG.GF2Type.Smith1979.IdxFourModelSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KC.IF4T

open Module CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.StepA CFSG.RankThree.OrthogonalInvolutions
open CFSG.GF2Type.Smith1979.IdxFour

theorem beq_land_one (x : ℕ) : Nat.beq (x &&& 1) 1 = x.testBit 0 := by
  rw [Nat.and_one_is_mod]
  exact beq_mod_two x

theorem par6_eq (x : ℕ) : par6 x = (x.testBit 0 ^^ (x.testBit 1 ^^ (x.testBit 2 ^^
    (x.testBit 3 ^^ (x.testBit 4 ^^ (x.testBit 5 ^^ false)))))) := by
  change (Nat.beq (x &&& 1) 1 ^^ (Nat.beq ((x >>> 1) &&& 1) 1 ^^
    (Nat.beq ((x >>> 1 >>> 1) &&& 1) 1 ^^ (Nat.beq ((x >>> 1 >>> 1 >>> 1) &&& 1) 1 ^^
    (Nat.beq ((x >>> 1 >>> 1 >>> 1 >>> 1) &&& 1) 1 ^^
    (Nat.beq ((x >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) &&& 1) 1 ^^ false)))))) = _
  simp only [beq_land_one, Nat.testBit_shiftRight, Nat.add_zero] <;> rfl

theorem q0K_eq (n : ℕ) : q0K n = q0b n := by
  change par6 (n ||| n >>> 6) = _
  rw [par6_eq]
  simp only [Nat.testBit_or, Nat.testBit_shiftRight]
  simp [q0b, List.range_succ, Bool.xor_assoc, Nat.add_comm]

theorem f0K_eq (m n : ℕ) : f0K m n = f0b m n := by
  change par6 ((m &&& n >>> 6) ^^^ (m >>> 6 &&& n)) = _
  rw [par6_eq]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight]
  simp [f0b, List.range_succ, Bool.xor_assoc]

theorem thK_eq (n : ℕ) : thK n = theta0N n := rfl

theorem q0_eq_zero_of_q0K {x : ℕ} (h : q0K x = false) : q0 (vecOf x) = 0 := by
  rw [q0_vecOf, ← q0K_eq, h]
  rfl

theorem q0_eq_one_of_q0K {x : ℕ} (h : q0K x = true) : q0 (vecOf x) = 1 := by
  rw [q0_vecOf, ← q0K_eq, h]
  rfl

theorem f0_eq_one_of_f0K {x y : ℕ} (h : f0K x y = true) : f0 (vecOf x) (vecOf y) = 1 := by
  rw [f0_vecOf, ← f0K_eq, h]
  rfl

theorem thPow_spec {n : ℕ} (hn : n < 4096) :
    ∀ i : ℕ, thPow i n < 4096 ∧ vecOf (thPow i n) = (thetaU ^ i) (vecOf n)
  | 0 => ⟨hn, by rw [pow_zero]; rfl⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := thPow_spec hn i
    change thK (thPow i n) < 4096 ∧ vecOf (thK (thPow i n)) = _
    rw [thK_eq, vecOf_theta0N h1, h2, pow_succ', LinearEquiv.mul_apply, thetaU_apply]
    exact ⟨theta0N_lt h1, rfl⟩

theorem fld_xor (a b c : ℕ) : fld (a ^^^ b) c = fld a c ^^^ fld b c := by
  change ((a ^^^ b) >>> (12 * c)) &&& 4095 =
    ((a >>> (12 * c)) &&& 4095) ^^^ ((b >>> (12 * c)) &&& 4095)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases (4095 : ℕ).testBit i <;> simp

theorem linP_xor (a b : ℕ) (v : V12) : linP (a ^^^ b) v = linP a v + linP b v := by
  simp only [linP_apply, fld_xor, vecOf_xor, smul_add, Finset.sum_add_distrib]

theorem linP_zero (v : V12) : linP 0 v = 0 := by
  have h : ∀ j : Fin 12, fld 0 j = 0 := fun j => by
    change ((0 : ℕ) >>> (12 * (j : ℕ))) &&& 4095 = 0
    rw [Nat.zero_shiftRight, Nat.zero_and]
  simp only [linP_apply, h, vecOf_zero, smul_zero, Finset.sum_const_zero]

theorem fld_zero' (m : ℕ) : fld m 0 = m &&& 4095 := by
  change (m >>> (12 * 0)) &&& 4095 = _
  rw [Nat.mul_zero, Nat.shiftRight_zero]

theorem ap12k_lt_of {p : ℕ} : ∀ (k m x : ℕ), (∀ j < k, fld m j < 2 ^ p) → ap12k k m x < 2 ^ p
  | 0, _, _, _ => Nat.two_pow_pos p
  | k + 1, m, x, h => by
    change (bif Nat.beq (Nat.land x 1) 1 then Nat.land m 4095 else 0) ^^^
      ap12k k (m >>> 12) (x >>> 1) < 2 ^ p
    refine Nat.xor_lt_two_pow ?_ (ap12k_lt_of k _ _ fun j hj => ?_)
    · cases Nat.beq (Nat.land x 1) 1
      · exact Nat.two_pow_pos p
      · have := h 0 (Nat.succ_pos k)
        rwa [fld_zero'] at this
    · rw [fld_shiftRight]
      exact h (j + 1) (by omega)

theorem ap12_lt_of {p m : ℕ} (h : ∀ j < 12, fld m j < 2 ^ p) (x : ℕ) : ap12 m x < 2 ^ p :=
  ap12k_lt_of 12 m x h

theorem linP_single (m : ℕ) (j : Fin 12) : linP m (Pi.single j 1) = vecOf (fld m j) := by
  rw [linP_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem anyD_spec_aux (Dm v : ℕ) : ∀ n : ℕ,
    Nat.rec (motive := fun _ => Bool) false (fun c ih => f0K v (fld Dm c) || ih) n = true →
      ∃ c < n, f0K v (fld Dm c) = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    change (f0K v (fld Dm n) || Nat.rec (motive := fun _ => Bool) false
      (fun c ih => f0K v (fld Dm c) || ih) n) = true at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact ⟨n, Nat.lt_succ_self n, h⟩
    · obtain ⟨c, hc, hc'⟩ := anyD_spec_aux Dm v n h
      exact ⟨c, Nat.lt_succ_of_lt hc, hc'⟩

theorem anyD_spec {Dm v : ℕ} (h : anyD Dm v = true) : ∃ c < 5, f0K v (fld Dm c) = true :=
  anyD_spec_aux Dm v 5 h

theorem ptOK_spec {Cm Dm Rm w k : ℕ} (h : ptOK Cm Dm Rm w k = true) :
    (q0K (ap12 Cm k) = true ∧ anyD Dm (ap12 Cm k) = true) ∨
      ∃ i a b, ap12 Cm k = thPow i (ap12 Dm a) ^^^ ap12 Rm b ∧
        (i = 0 ∨ anyD Dm (ap12 Cm k) = true) := by
  unfold ptOK at h
  cases hw : Nat.beq w 0
  · rw [hw] at h
    simp only [cond_false, Bool.and_eq_true, Nat.beq_eq, Bool.or_eq_true] at h
    exact Or.inr ⟨_, _, _, h.1, h.2⟩
  · rw [hw] at h
    simp only [cond_true, Bool.and_eq_true] at h
    exact Or.inl h

theorem ptsOK_spec {Cm Dm Rm : ℕ} : ∀ {ws : List ℕ} {k0 : ℕ}, ptsOK Cm Dm Rm ws k0 = true →
    ∀ j < ws.length, ptOK Cm Dm Rm (ws.getD j 0) (k0 + j) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | w :: ws, k0, h, j, hj => by
    change (ptOK Cm Dm Rm w k0 && ptsOK Cm Dm Rm ws (Nat.succ k0)) = true at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := ptsOK_spec h.2 j (by simpa using hj)
      rwa [Nat.succ_add, ← Nat.add_succ] at this

theorem tOK_spec {LP : List ℕ} {VP m Cm E K Um F Am : ℕ} {ws : List ℕ}
    (h : tOK LP VP m Cm E K Um F Am ws = true) :
    mulP Cm E ^^^ mulP K (subP LP m ^^^ idP) = idP ∧
      mulP (mulP (subP LP m ^^^ idP) Um) F = subP LP m ^^^ idP ∧
      mulP (subP LP m ^^^ idP) (mulP VP Am) = 0 ∧
      (∀ j < 12, fld E j < 256 ∧ fld F j < 16) ∧
      (∀ b < 16, q0K (ap12 (mulP (subP LP m ^^^ idP) Um) b) = false) ∧ ws.length = 256 ∧
      ptsOK Cm (mulP VP Am) (mulP (subP LP m ^^^ idP) Um) ws 0 = true := by
  unfold tOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, Nat.blt_eq, lenN_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem modelInner_of_tOK {t : V12 ≃ₗ[ZMod 2] V12} {LP : List ℕ} {VP m Cm E K Um F Am : ℕ}
    {ws : List ℕ} {Vt : Submodule (ZMod 2) V12} (ht : IsP t (subP LP m))
    (hθ : thetaU * t = t * thetaU) (hVP : ∀ u, linP VP u ∈ Vt)
    (h : tOK LP VP m Cm E K Um F Am ws = true) : ModelInner Vt t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := tOK_spec h
  set N := subP LP m ^^^ idP with hNdef
  set Rm := mulP N Um with hRm
  set Dm := mulP VP Am with hDm
  have hN : ∀ v, linP N v = t v - v := fun v => by
    rw [hNdef, linP_xor, ← ht, linP_idP, vec_sub_eq_add]
  have hfix : ∀ v, v ∈ fixSpace t ↔ linP N v = 0 := fun v => by
    rw [mem_fixSpace, hN, sub_eq_zero]
  have hC : ∀ v, v ∈ fixSpace t → ap12 E (codeOf v) < 256 ∧ v = vecOf (ap12 Cm (ap12 E (codeOf v))) := by
    intro v hv
    refine ⟨ap12_lt_of (p := 8) (fun j hj => (h4 j hj).1) _, ?_⟩
    have e := linP_idP v
    rw [← h1, linP_xor, linP_mulP, linP_mulP, (hfix v).1 hv, map_zero, add_zero] at e
    rw [vecOf_ap12, vecOf_ap12, vecOf_codeOf, e]
  have hR : ∀ v, ap12 F (codeOf v) < 16 ∧ t v - v = vecOf (ap12 Rm (ap12 F (codeOf v))) := by
    intro v
    refine ⟨ap12_lt_of (p := 4) (fun j hj => (h4 j hj).2) _, ?_⟩
    rw [← hN, ← h2, linP_mulP, vecOf_ap12, vecOf_ap12, vecOf_codeOf]
  have hRcomm : ∀ y, vecOf (ap12 Rm y) ∈ commSpace t := fun y => by
    rw [vecOf_ap12, hRm, linP_mulP, hN]
    exact sub_mem_commSpace t _
  have hD : ∀ y, vecOf (ap12 Dm y) ∈ Vt ⊓ fixSpace t := fun y => by
    refine Submodule.mem_inf.2 ⟨?_, (hfix _).2 ?_⟩
    · rw [vecOf_ap12, hDm, linP_mulP]
      exact hVP _
    · rw [vecOf_ap12, ← linP_mulP, h3, linP_zero]
  have hDcol : ∀ c < 5, vecOf (fld Dm c) ∈ Vt ⊓ fixSpace t := fun c hc => by
    have := hD (2 ^ c)
    have e : vecOf (2 ^ c) = Pi.single (⟨c, by omega⟩ : Fin 12) 1 := by
      funext j
      rw [vecOf, Pi.single_apply, Nat.testBit_two_pow]
      by_cases hj : (j : ℕ) = c
      · have hj' : j = ⟨c, by omega⟩ := Fin.ext hj
        simp [hj, hj']
      · have hj' : j ≠ ⟨c, by omega⟩ := fun e => hj (by rw [e])
        simp [hj', Ne.symm hj]
    rwa [vecOf_ap12, e, linP_single] at this
  have hpts : ∀ k < 256, ptOK Cm Dm Rm (ws.getD k 0) k = true := fun k hk => by
    have := ptsOK_spec h7 k (by omega)
    rwa [Nat.zero_add] at this
  have hanyD : ∀ v, anyD Dm v = true → ∃ p ∈ Vt ⊓ fixSpace t, f0 (vecOf v) p = 1 := by
    intro v hv
    obtain ⟨c, hc, hc'⟩ := anyD_spec hv
    exact ⟨_, hDcol c hc, f0_eq_one_of_f0K hc'⟩
  refine ⟨hθ, ?_, ?_, ?_, ?_⟩
  ·
    have hcard : Nat.card (fixSpace t) ≤ 2 ^ 8 := by
      let f : fixSpace t → Fin 256 := fun v => ⟨ap12 E (codeOf v.1), (hC v.1 v.2).1⟩
      have hf : Function.Injective f := fun a b e => Subtype.ext (by
        have := congrArg (fun k : Fin 256 => vecOf (ap12 Cm k.1)) e
        simp only [f] at this
        rw [(hC a.1 a.2).2, (hC b.1 b.2).2, this])
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_eq_fintype_card (α := Fin 256), Fintype.card_fin] at this
    have hp := FiniteField.pow_finrank_eq_natCard 2 ↥(fixSpace t)
    by_contra hlt
    have h9 : 2 ^ 9 ≤ 2 ^ finrank (ZMod 2) ↥(fixSpace t) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hp] at h9
    omega
  ·
    intro r hr
    obtain ⟨v, rfl⟩ := mem_commSpace.1 hr
    obtain ⟨hb, e⟩ := hR v
    rw [e]
    exact q0_eq_zero_of_q0K (h5 _ hb)
  ·
    intro w hw horth
    obtain ⟨hk, e⟩ := hC w hw
    rcases ptOK_spec (hpts _ hk) with ⟨-, hD'⟩ | ⟨i, a, b, ev, hi⟩
    · obtain ⟨p, hp, hfp⟩ := hanyD _ hD'
      rw [← e, horth p hp] at hfp
      exact absurd hfp (by decide)
    · rcases hi with rfl | hi
      · refine ⟨_, hD a, _, hRcomm b, ?_⟩
        rw [e, ev, vecOf_xor]
        rfl
      · obtain ⟨p, hp, hfp⟩ := hanyD _ hi
        rw [← e, horth p hp] at hfp
        exact absurd hfp (by decide)
  ·
    intro v hv hq
    obtain ⟨hk, e⟩ := hC v hv
    rcases ptOK_spec (hpts _ hk) with ⟨hq', -⟩ | ⟨i, a, b, ev, -⟩
    · have := q0_eq_one_of_q0K hq'
      rw [← e, hq] at this
      exact absurd this (by decide)
    · refine ⟨i, _, hD a, _, hRcomm b, ?_⟩
      rw [e, ev, vecOf_xor, (thPow_spec (ap12_lt _ _) i).2]

end CFSG.KC.IF4T

end
