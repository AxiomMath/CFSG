module

public import Certificates.Data.Kernel.Misc.Ree2
public import Certificates.Data.Kernel.Misc.Ree
import CFSG.Certificates.Kernel.Misc.Ree2Field
import CFSG.Certificates.Kernel.Misc.Ree2Mat
import CFSG.Certificates.Kernel.Misc.Ree2Bez

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.Walter.Ree.Bombieri

@[expose] noncomputable def zetaL (q1 ZT c0 c1 : Nat) : Nat :=
  addL q1 ZT (nat_lit 0) (mulL q1 c1 (mulL q1 c0 c0))

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bezOK_eq (q1 ZT D : ℕ) (s p t : List ℕ) (P1 g0 n₀ k : ℕ) :
    bezOK q1 ZT D s p t P1 g0 n₀ k =
      bezRange q1 ZT D (packL s) (packL p) (packL t) P1 (lenL s) (lenL t) g0 n₀ k := by
  simp only [bezOK, strictB_eq]

theorem entry_sound {m F g dg q1 hf ET ZT Fl G M15 ML nb : ℕ} {k lam : ℕ} {neg : Bool}
    {W xs p p' s t : List ℕ} {g0 : ℕ}
    (hhead : headOK m F g dg q1 hf ET ZT 399 = true)
    (hchain : chainOK m F g dg q1 ET 0 q1 = true)
    (hzech : zechOK q1 ET ZT 0 q1 = true)
    (hlanes : Nat.beq Fl (lanesOf m F) = true)
    (hsetup : CFSG.KC.Misc.Ree.setupK m Fl G M15 ML = true)
    (hroot : CFSG.KC.Misc.Ree.rootK m G M15 ML nb = true)
    (hk : k ≤ 3) (hW : lenL W = k + 1) (hWl : logsOK q1 W = true)
    (hq : qOK q1 hf ZT (cpt q1 W k lam neg 0) (cpt q1 W k lam neg 1) (cpt q1 W k lam neg 2)
      (cpt q1 W k lam neg 3) (cpt q1 W k lam neg 4) = true)
    (hpts : ptsOK 114 400 xs = true)
    (hint : interpOK q1 hf ZT shapeL atomL coefL (cpt q1 W k lam neg 0) (cpt q1 W k lam neg 1)
      (cpt q1 W k lam neg 2) (cpt q1 W k lam neg 3) (cpt q1 W k lam neg 4) xs p p' 0 115 = true)
    (hsize : sizeOK q1 114 p p' s t g0 = true)
    (hbez : bezOK q1 ZT 114 s p t
      (p1Pack q1 114 (zetaL q1 ZT (cpt q1 W k lam neg 0) (cpt q1 W k lam neg 1)) p') g0 0 343 =
        true) :
    Elim.Hs k lam neg ≠ 0 := by
  have _ := hk
  have _ := hW
  obtain ⟨γ, E, hdist, hD⟩ := field_env hhead hchain hzech hlanes hsetup hroot
  unfold sizeOK at hsize
  simp only [bA] at hsize
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := hsize
  have hpl : p.length = 115 := by
    have := Nat.eq_of_beq_eq_true s1; rw [lenL_eq] at this; exact this
  have hlc : nthL q1 p 114 ≠ q1 := Nat.ne_of_beq_eq_false (bNot.mp s2)
  have hp'l : p'.length ≤ 115 := by
    have := Nat.le_of_ble_eq_true s3; rw [lenL_eq] at this; exact this
  have hsl : s.length ≤ 228 := by
    have := Nat.le_of_ble_eq_true s4; rw [lenL_eq] at this; exact this
  have hsl0 : 0 < s.length := by
    rw [Nat.blt_eq, lenL_eq] at s5; exact s5
  have htl : t.length ≤ 114 := by
    have := Nat.le_of_ble_eq_true s6; rw [lenL_eq] at this; exact this
  have htl0 : 0 < t.length := by
    rw [Nat.blt_eq, lenL_eq] at s7; exact s7
  have hg0 : g0 < q1 := by rw [Nat.blt_eq] at s8; exact s8
  have hq65 : q1 < 65535 := by rw [Nat.blt_eq] at s9; exact s9
  have hpv := logsOK_iff.mp s10
  have hp'v := logsOK_iff.mp s11
  have hsv := logsOK_iff.mp s12
  have htv := logsOK_iff.mp s13
  have hhf := E.hf_lt
  have hD114 : Elim.D = 114 := rfl
  set c : ℕ → ℕ := cpt q1 W k lam neg with hcdef
  have hWv : ∀ x ∈ W, x ≤ q1 := logsOK_iff.mp hWl
  set w : Fin (k + 1) → GaloisField 3 m := fun i => phi q1 γ (W.getD i q1) with hw
  set cK : Fin 5 → GaloisField 3 m :=
    fun j => w ⟨substIdx k neg j, substIdx_lt k neg j⟩ ^ 3 ^ substExp k lam neg j with hcK
  have hc : ∀ j : ℕ, c j ≤ q1 ∧ phi q1 γ (c j) =
      w ⟨substIdx k neg j, substIdx_lt k neg j⟩ ^ 3 ^ substExp k lam neg j := by
    intro j
    simp only [hcdef, cpt]
    rw [nthL_eq]
    exact E.powL_spec (getD_le hWv le_rfl _) _
  have hcl : ∀ j, c j ≤ q1 := fun j => (hc j).1
  have hc0 : phi q1 γ (c 0) = cK 0 := (hc 0).2
  have hc1 : phi q1 γ (c 1) = cK 1 := (hc 1).2
  have hc2 : phi q1 γ (c 2) = cK 2 := (hc 2).2
  have hc3 : phi q1 γ (c 3) = cK 3 := (hc 3).2
  have hc4 : phi q1 γ (c 4) = cK 4 := (hc 4).2
  set f5 := Elim.evA5 cK with hf5
  have hρ : ∀ i, cvars q1 (c 0) (c 1) (c 2) (c 3) (c 4) i ≤ q1 := by
    intro i
    unfold cvars
    rw [varsL_eq]
    split_ifs <;> first | exact hcl _ | exact le_rfl
  have hQ : ∀ ε : ℤ, Bool.rec (motive := fun _ => Bool) true false
      (Nat.beq (evalL q1 hf ZT (cvars q1 (c 0) (c 1) (c 2) (c 3) (c 4)) (fun _ => q1)
        (Elim.qExpr ε)) q1) = true → f5 (Elim.Qε ε) ≠ 0 := by
    intro ε hε
    have hne := Nat.ne_of_beq_eq_false (bNot.mp hε)
    obtain ⟨h1, h2⟩ := E.evalL_spec hρ (fun _ => le_rfl) (Elim.qExpr ε)
    have h3 := E.phi_ne_zero h1 hne
    rw [h2] at h3
    rw [hf5, Elim.evA5_Qε]
    convert h3 using 1
    simp only [Elim.qExpr, PE.eval_sub, PE.eval_mul, PE.eval_add, PE.eval_pow, PE.eval_var,
      PE.eval_const, PE.eval_one, Function.comp_apply]
    have e0 : phi q1 γ (cvars q1 (c 0) (c 1) (c 2) (c 3) (c 4) 0) = cK 0 := hc0
    have e1 : phi q1 γ (cvars q1 (c 0) (c 1) (c 2) (c 3) (c 4) 1) = cK 1 := hc1
    have e2 : phi q1 γ (cvars q1 (c 0) (c 1) (c 2) (c 3) (c 4) 2) = cK 2 := hc2
    rw [e0, e1, e2]
  unfold qOK at hq
  rw [bA, bA] at hq
  obtain ⟨hq0, hq1, hq2⟩ := hq
  obtain ⟨hxl, hxR, hxs⟩ := ptsOK_spec hpts
  set x : ℕ → ℕ := fun i => xs.getD i q1 with hx
  have hxlt : ∀ i < 115, x i < 400 := by
    intro i hi
    simp only [hx]
    rw [getD_of_lt _ (by omega)]
    exact hxR _ (List.getElem_mem _)
  have hxmono : ∀ i j, i < j → j < 115 → x i < x j := by
    intro i j hij hj
    simp only [hx]
    rw [getD_of_lt _ (by omega), getD_of_lt _ (by omega)]
    exact List.pairwise_iff_getElem.mp hxs i j (by omega) (by omega) hij
  have hpow : ∀ a b, a < b → b < 400 → γ ^ a ≠ γ ^ b := by
    intro a b hab hb h
    apply hdist (b - a) (by omega) (by omega)
    have e : γ ^ b = γ ^ a * γ ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [e] at h
    exact mul_left_cancel₀ (pow_ne_zero a E.ne_zero) (h.symm.trans (mul_one _).symm)
  have hinj : Function.Injective (fun i : Fin 115 => phi q1 γ (x i)) := by
    intro i j hij
    simp only at hij
    rw [phi_lt (by have := hxlt i i.2; omega), phi_lt (by have := hxlt j j.2; omega)] at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hpow _ _ (hxmono _ _ h j.2) (hxlt j j.2) hij
    · exact hpow _ _ (hxmono _ _ h i.2) (hxlt i i.2) hij.symm
  unfold interpOK at hint
  rw [allFrom_iff] at hint
  have hpt : ∀ i < 115,
      detL q1 hf ZT shapeL atomL coefL (c 0) (c 1) (c 2) (c 3) (x i) = hornerL q1 ZT p (x i) ∧
      detL q1 hf ZT shapeL atomL coefL (c 1) (c 2) (c 3) (c 4) (x i) =
        hornerL q1 ZT p' (x i) := by
    intro i hi
    have := hint i (Nat.zero_le _) (by omega)
    rw [sB, bA, nthL_eq] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hxq : ∀ i < 115, x i ≤ q1 := fun i hi => by have := hxlt i hi; omega
  have hA : Elim.P.map f5 = polyL q1 γ p := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun i => ?_) ?_
    · obtain ⟨h1, -⟩ := hpt i i.2
      obtain ⟨h2, h3⟩ := E.hornerL_spec (hxq i i.2) hpv
      have h4 := E.detL_spec hq65 (hcl 0) (hcl 1) (hcl 2) (hcl 3) (hxq i i.2) (by omega)
      rw [Polynomial.eval_map, hf5, Elim.eval_P, ← hc0, ← hc1, ← hc2, ← hc3, ← h4.2, h1, h3]
    · simp only [Fintype.card_fin]
      refine max_lt ((Polynomial.natDegree_map_le).trans_lt ?_) ?_
      · have := Elim.natDegree_P; omega
      · have := natDegree_polyL_le (q1 := q1) (γ := γ) p; omega
  have hA' : Elim.P'.map f5 = polyL q1 γ p' := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun i => ?_) ?_
    · obtain ⟨-, h1⟩ := hpt i i.2
      obtain ⟨h2, h3⟩ := E.hornerL_spec (hxq i i.2) hp'v
      have h4 := E.detL_spec hq65 (hcl 1) (hcl 2) (hcl 3) (hcl 4) (hxq i i.2) (by omega)
      rw [Polynomial.eval_map, hf5, Elim.eval_P', ← hc1, ← hc2, ← hc3, ← hc4, ← h4.2, h1, h3]
    · simp only [Fintype.card_fin]
      refine max_lt ((Polynomial.natDegree_map_le).trans_lt ?_) ?_
      · have := Elim.natDegree_P'; omega
      · have := natDegree_polyL_le (q1 := q1) (γ := γ) p'; omega
  have hlc' : (Elim.P.map f5).coeff Elim.D ≠ 0 := by
    rw [hA, coeff_polyL, ← nthL_eq]
    exact E.phi_ne_zero (by rw [nthL_eq]; exact getD_le hpv le_rfl _) hlc
  have hnatA : (Elim.P.map f5).natDegree = Elim.D :=
    le_antisymm ((Polynomial.natDegree_map_le).trans Elim.natDegree_P)
      (Polynomial.le_natDegree_of_ne_zero hlc')
  set ζ := zetaL q1 ZT (c 0) (c 1) with hζdef
  have hζ : ζ ≤ q1 ∧ phi q1 γ ζ = 1 + cK 1 * cK 0 ^ 2 := by
    obtain ⟨h1, h2⟩ := E.mulL_spec (hcl 0) (hcl 0)
    obtain ⟨h3, h4⟩ := E.mulL_spec (hcl 1) h1
    obtain ⟨h5, h6⟩ := E.addL_spec (Nat.zero_le q1) h3
    refine ⟨h5, ?_⟩
    change phi q1 γ (addL q1 ZT 0 (mulL q1 (c 1) (mulL q1 (c 0) (c 0)))) = _
    rw [h6, h4, h2, E.phi_zero, hc0, hc1]
    ring
  set P1v := p1Pack q1 114 ζ p' with hP1v
  have hP1f := E.getP_p1Pack (D := 114) hq65 hp'v hζ.1
  have hP1l : ∀ n, getP P1v n ≤ q1 := by
    intro n
    rw [hP1f]
    split_ifs
    · exact (E.mulL_spec (getD_le hp'v le_rfl _) (E.powL_spec hζ.1 _).1).1
    · exact le_rfl
    · exact Nat.zero_le _
  have h16 : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ q1) → ∀ x ∈ l, x < 2 ^ 16 :=
    fun hl x hx => (hl x hx).trans_lt (by omega)
  have hSp : ∀ i, getP (packL s) i = s.getD i 0 := getP_packL (h16 hsv)
  have hPp : ∀ i, getP (packL p) i = p.getD i 0 := getP_packL (h16 hpv)
  have hTp : ∀ i, getP (packL t) i = t.getD i 0 := getP_packL (h16 htv)
  have hSl : ∀ i, getP (packL s) i ≤ q1 := fun i => by rw [hSp]; exact getD_le hsv (Nat.zero_le _) i
  have hPl : ∀ i, getP (packL p) i ≤ q1 := fun i => by rw [hPp]; exact getD_le hpv (Nat.zero_le _) i
  have hTl : ∀ i, getP (packL t) i ≤ q1 := fun i => by rw [hTp]; exact getD_le htv (Nat.zero_le _) i
  set P1K : Polynomial (GaloisField 3 m) := ∑ n ∈ Finset.range 229,
    Polynomial.C (phi q1 γ (getP P1v n)) * Polynomial.X ^ n with hP1K
  have hP1Kc : ∀ j, P1K.coeff j = if j ≤ 228 then phi q1 γ (getP P1v j) else 0 := by
    intro j
    simp only [hP1K, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have hcoefL : ∀ {l : List ℕ} (B : ℕ), (∀ i, getP (packL l) i = l.getD i 0) →
      ∀ i, (polyL q1 γ l).coeff i = if i < l.length then phi q1 γ (getP (packL l) i) else 0 := by
    intro l B hl i
    rw [coeff_polyL]
    split_ifs with h
    · rw [hl, getD_of_lt _ h, getD_of_lt _ h]
    · rw [getD_ge _ (by omega), phi_q1]
  have hPc : ∀ j, (polyL q1 γ p).coeff j = if j ≤ 114 then phi q1 γ (getP (packL p) j) else 0 := by
    intro j
    rw [hcoefL 0 hPp j, hpl]
    simp only [Nat.lt_succ_iff]
  have hbez' : polyL q1 γ s * polyL q1 γ p + polyL q1 γ t * P1K = Polynomial.C (phi q1 γ g0) := by
    ext n
    rw [Polynomial.coeff_add, Polynomial.coeff_C]
    by_cases hn : n < 343
    · rw [bezOK_eq] at hbez
      unfold bezRange at hbez
      rw [allFrom_iff] at hbez
      have hb := Nat.eq_of_beq_eq_true (hbez n (Nat.zero_le _) (by omega))
      unfold bezCoef at hb
      rw [sN, sN, nIf_eq, nbeq, lenL_eq, lenL_eq] at hb
      simp only [decide_eq_true_eq] at hb
      have hb' : addL q1 ZT (convAt q1 ZT (packL s) (packL p) n (n - 114) (min n (s.length - 1)))
          (convAt q1 ZT (packL t) P1v n (n - 228) (min n (t.length - 1))) =
            if n = 0 then g0 else q1 := hb
      have hc1 := E.convAt_spec hSl hPl n (n - 114) (min n (s.length - 1))
      have hc2 := E.convAt_spec hTl hP1l n (n - 228) (min n (t.length - 1))
      have h3 := congrArg (phi q1 γ) hb'
      rw [(E.addL_spec hc1.1 hc2.1).2, hc1.2, hc2.2] at h3
      rw [coeff_mul_window (hcoefL 0 hSp) hPc hsl0, coeff_mul_window (hcoefL 0 hTp) hP1Kc htl0,
        h3]
      split_ifs
      · rfl
      · exact phi_q1
    · have hd1 : (polyL q1 γ s * polyL q1 γ p).natDegree < n := by
        refine Polynomial.natDegree_mul_le.trans_lt ?_
        have := natDegree_polyL_le (q1 := q1) (γ := γ) s
        have := natDegree_polyL_le (q1 := q1) (γ := γ) p
        omega
      have hP1d : P1K.natDegree ≤ 228 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [hP1Kc, ite_eq_right (by omega)]
      have hd2 : (polyL q1 γ t * P1K).natDegree < n := by
        refine Polynomial.natDegree_mul_le.trans_lt ?_
        have := natDegree_polyL_le (q1 := q1) (γ := γ) t
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd1,
        Polynomial.coeff_eq_zero_of_natDegree_lt hd2, ite_eq_right (by omega), add_zero]
  have hP1eq : P1K = Elim.P1.map f5 := by
    ext n
    rw [hP1Kc, Polynomial.coeff_map, Elim.coeff_P1, map_sum]
    have h1 : ∀ j ∈ Finset.range (Elim.D + 1),
        f5 (if n = 2 * Elim.D - 2 * j then Elim.P'.coeff j * Elim.ζA ^ j else 0) =
          if n = 2 * Elim.D - 2 * j then
            phi q1 γ (p'.getD j q1) * (1 + cK 1 * cK 0 ^ 2) ^ j else 0 := by
      intro j _
      split_ifs
      · rw [map_mul, map_pow, ← Polynomial.coeff_map, hA', coeff_polyL, hf5, Elim.evA5_ζA]
      · exact map_zero _
    rw [Finset.sum_congr rfl h1, sum_shift_eq, hP1f]
    have hD114 : Elim.D = 114 := rfl
    rw [hD114]
    by_cases h2 : n ≤ 228
    · rw [ite_eq_left h2, ite_eq_left (by omega : n ≤ 2 * 114)]
      by_cases h3 : n % 2 = 0
      · rw [ite_eq_left h3, ite_eq_left ⟨by omega, h3⟩,
          (E.mulL_spec (getD_le hp'v le_rfl _) (E.powL_spec hζ.1 _).1).2,
          (E.powL_spec hζ.1 _).2, hζ.2]
      · rw [ite_eq_right h3, ite_eq_right (by omega), phi_q1]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]
  rw [← hA, hP1eq] at hbez'
  have hg0' : phi q1 γ g0 ≠ 0 := E.phi_ne_zero hg0.le (ne_of_lt hg0)
  have hcop : IsCoprime (Elim.P.map f5) (Elim.P1.map f5) := by
    refine ⟨Polynomial.C (phi q1 γ g0)⁻¹ * polyL q1 γ s,
      Polynomial.C (phi q1 γ g0)⁻¹ * polyL q1 γ t, ?_⟩
    calc Polynomial.C (phi q1 γ g0)⁻¹ * polyL q1 γ s * Elim.P.map f5 +
          Polynomial.C (phi q1 γ g0)⁻¹ * polyL q1 γ t * Elim.P1.map f5 =
        Polynomial.C (phi q1 γ g0)⁻¹ * (polyL q1 γ s * Elim.P.map f5 +
          polyL q1 γ t * Elim.P1.map f5) := by ring
      _ = 1 := by rw [hbez', ← Polynomial.C_mul, inv_mul_cancel₀ hg0', Polynomial.C_1]
  have hH0 : f5 Elim.H0 ≠ 0 := by
    rw [Elim.H0_eq, ← Polynomial.resultant_map_map]
    have hk : 2 * Elim.D = (Elim.P1.map f5).natDegree + (2 * Elim.D - (Elim.P1.map f5).natDegree) :=
      by
        have := (Polynomial.natDegree_map_le (f := f5) (p := Elim.P1)).trans Elim.natDegree_P1
        omega
    rw [hk, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl]
    refine mul_ne_zero (pow_ne_zero _ hlc') ?_
    have : Elim.D = (Elim.P.map f5).natDegree := hnatA.symm
    rw [this]
    exact Polynomial.resultant_ne_zero _ _ hcop
  intro h0
  have hval := congrArg (MvPolynomial.eval₂ (castThree (GaloisField 3 m)) w) h0
  rw [MvPolynomial.eval₂_zero, Elim.eval₂_Hs, Elim.evA5_H] at hval
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hQ 0 hq0) (hQ 1 hq1)) (hQ (-1) hq2)) hH0 hval

theorem allFrom_append {f : ℕ → Bool} {a b c : ℕ} (h1 : allFrom a b f = true)
    (h2 : allFrom c (b + a) f = true) : allFrom (a + c) b f = true := by
  induction a generalizing b with
  | zero =>
    simpa using h2
  | succ a ih =>
    have e : a + 1 + c = (a + c) + 1 := by omega
    rw [e]
    change Bool.rec false (allFrom (a + c) (b + 1) f) (f b) = true
    change Bool.rec false (allFrom a (b + 1) f) (f b) = true at h1
    cases hb : f b
    · rw [hb] at h1
      exact absurd h1 Bool.false_ne_true
    · rw [hb] at h1
      exact ih h1 (by rw [show b + 1 + a = b + (a + 1) by omega]; exact h2)

theorem chainOK_append {m F g dg q1 ET a b c : ℕ} (h1 : chainOK m F g dg q1 ET b a = true)
    (h2 : chainOK m F g dg q1 ET (b + a) c = true) : chainOK m F g dg q1 ET b (a + c) = true :=
  allFrom_append h1 h2

theorem zechOK_append {q1 ET ZT a b c : ℕ} (h1 : zechOK q1 ET ZT b a = true)
    (h2 : zechOK q1 ET ZT (b + a) c = true) : zechOK q1 ET ZT b (a + c) = true :=
  allFrom_append h1 h2

theorem interpOK_append {q1 hf ZT S : ℕ} {AL CL : List PE} {c0 c1 c2 c3 c4 : ℕ}
    {xs p p' : List ℕ} {a b c : ℕ}
    (h1 : interpOK q1 hf ZT S AL CL c0 c1 c2 c3 c4 xs p p' b a = true)
    (h2 : interpOK q1 hf ZT S AL CL c0 c1 c2 c3 c4 xs p p' (b + a) c = true) :
    interpOK q1 hf ZT S AL CL c0 c1 c2 c3 c4 xs p p' b (a + c) = true :=
  allFrom_append h1 h2

theorem bezOK_append {q1 ZT D : ℕ} {s p t : List ℕ} {P1 g0 a b c : ℕ}
    (h1 : bezOK q1 ZT D s p t P1 g0 b a = true)
    (h2 : bezOK q1 ZT D s p t P1 g0 (b + a) c = true) :
    bezOK q1 ZT D s p t P1 g0 b (a + c) = true := by
  rw [bezOK_eq] at h1 h2 ⊢
  exact allFrom_append h1 h2

theorem allFrom_zero {f : ℕ → Bool} {b : ℕ} : allFrom 0 b f = true := rfl

theorem chainOK_zero {m F g dg q1 ET b : ℕ} : chainOK m F g dg q1 ET b 0 = true := rfl

theorem zechOK_zero {q1 ET ZT b : ℕ} : zechOK q1 ET ZT b 0 = true := rfl

theorem interpOK_zero {q1 hf ZT S : ℕ} {AL CL : List PE} {c0 c1 c2 c3 c4 : ℕ}
    {xs p p' : List ℕ} {b : ℕ} :
    interpOK q1 hf ZT S AL CL c0 c1 c2 c3 c4 xs p p' b 0 = true := rfl

theorem bezOK_zero {q1 ZT D : ℕ} {s p t : List ℕ} {P1 g0 b : ℕ} :
    bezOK q1 ZT D s p t P1 g0 b 0 = true := by
  rw [bezOK_eq]
  rfl

end CFSG.KC.Misc.Ree2

end
