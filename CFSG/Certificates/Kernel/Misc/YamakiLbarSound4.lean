module

public import CFSG.Certificates.Kernel.Misc.YamakiLbarSound3

public section

namespace CFSG.KC.YamakiLbar

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiLbar
  CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KC.Misc.Spec Matrix
  CFSG.KD.YamakiA0
open CFSG.KD.Sp62 (MULF ONE)
open CFSG.KC.Sp62 (MULF_lt pkMat_MULF pkMat_inj)

variable {R Q W : ℕ → ℕ}

theorem arr2_get0 (x y : Array ℕ) : (#[x, y] : Array (Array ℕ))[0]! = x := rfl

theorem arr2_get1 (x y : Array ℕ) : (#[x, y] : Array (Array ℕ))[1]! = y := rfl

theorem beq_self (x : ℕ) : Nat.beq x x = true := by rw [Nat.beq_eq]

theorem beq_false {x y : ℕ} (h : ¬x = y) : Nat.beq x y = false := by
  cases e : Nat.beq x y
  · rfl
  · rw [Nat.beq_eq] at e
    exact absurd e h

section Norm

variable (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hA : a0TabK R 64 = true)
  (hc : coordK R Q = true) (hg : glK R Q = true) (hl : lbTabK Q = true)

include hG hA hc in
theorem img_fold2 (T : Array (Array ℕ)) (Λ : ℕ → ℕ) {v : ℕ} (hv : v < 64) :
    ∀ J : List ℕ, (∀ m ∈ J, T[m]! = phiA Q (Λ m)) →
      J.foldr (fun m acc => ((z6MulTab ())[(T[m]!)[v]!]!)[acc]!) 0 =
        psc Q (J.foldr (fun m a => Nat.xor (MULF (crd Q v) (Λ m)) a) 0)
  | [], _ => by
    rw [List.foldr_nil, List.foldr_nil, psc_zero hA hc]
  | m :: J, hJ => by
    have ih := img_fold2 T Λ hv J fun x hx => hJ x (List.mem_cons_of_mem _ hx)
    have hlt : ∀ J : List ℕ, J.foldr (fun m a => Nat.xor (MULF (crd Q v) (Λ m)) a) 0 < 64 := by
      intro J
      induction J with
      | nil => norm_num
      | cons x J ihJ => exact xor_lt64 (vec_lt (crd_lt hA hc hv) _) ihJ
    rw [List.foldr_cons, List.foldr_cons, ih, hJ m List.mem_cons_self, phiA_get _ hv,
      z6MulTab_psc hG hA hc (vec_lt (crd_lt hA hc hv) _) (hlt J)]
    rfl

include hG hA hc hg hl in
theorem norm_v (hrep : repK Q = true) (hia : iaK Q = true) (hib : ibK Q = true)
    (hcand : candK Q W = true) {ia ib A B : ℕ} (hia' : ia < 168) (hib' : ib < 168)
    (hAe : lbL Q ia = A) (hBe : lbL Q ib = B) {T : Array (Array ℕ)}
    (hT : ∀ m ∈ [0, 2, 3, 5, 8, 14], T[m]! = phiA Q (lamOf A B m))
    (hAA : MULF A A = ONE) (hBB : MULF (MULF B B) B = ONE) {v : ℕ} (hv : v < 64) :
    (z6FEqn (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v)
        (z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v)) &&
      (!z6Valid (z6MulTab ()) (z6GsL ()) #[phiA Q A, phiA Q B]
          (z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v)) ||
        ((z6EnumL ()).lookup
          (z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v))).isSome)) = true := by
  have hcl : crd Q v < 64 := crd_lt hA hc hv
  have hAl : A < 2 ^ 36 := hAe ▸ lbL_lt hl ia hia'
  have hBl : B < 2 ^ 36 := hBe ▸ lbL_lt hl ib hib'
  have himg : z6Img (z6MulTab ()) T v =
      #[psc Q (MULF (crd Q v) (sOf A B 0)), psc Q (MULF (crd Q v) (sOf A B 1)),
        psc Q (MULF (crd Q v) (sOf A B 2)), psc Q (MULF (crd Q v) (sOf A B 3)),
        psc Q (MULF (crd Q v) (sOf A B 4)), psc Q (MULF (crd Q v) (sOf A B 5))] := by
    unfold z6Img
    rw [List.map_congr_left fun J hJ => img_fold2 hG hA hc T (lamOf A B) hv J fun m hm => hT m (by
      simp only [z6J, List.mem_cons, List.not_mem_nil, or_false] at hJ
      rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢ <;> omega)]
    simp only [z6J, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nxor_zero]
    congr 1
    simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;>
      simp only [sOf, lamOf, List.getD_cons_zero, List.getD_cons_succ, mulF_nxor]
  have himg_get : ∀ j < 6, (z6Img (z6MulTab ()) T v)[j]! =
      psc Q (MULF (2 ^ j) (gOf (crd Q v) A B)) := by
    intro j hj
    rw [himg, row_gOf hcl A B hj]
    interval_cases j <;> rfl
  obtain ⟨hE, -, -, hBt, -⟩ := enumA0_inv hG hA
  have hpar : ∀ k, 0 < k → k < 64 → (enumA0 ()).parent[k]! = recF R 12 0 (k - 1) ∧
      (enumA0 ()).gen[k]! = recF R 12 1 (k - 1) := fun k h1 h2 => hE.2.2.2.2.1 k h2 h1
  obtain ⟨hFs, hF0, hFk⟩ := z6BuildF_facts (z6MulTab ()) (enumA0 ())
    (z6Img (z6MulTab ()) T v) fun k h1 h2 => by
      rw [(hpar k h1 h2).1]
      have := (hBt (k - 1) (by omega)).1
      omega
  have hFv : ∀ k < 64, (z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v))[k]! =
      psc Q (MULF (crd Q k) (gOf (crd Q v) A B)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => rw [hF0, (coord_facts hc).1, zero_mulF, psc_zero hA hc]
      | succ t =>
        obtain ⟨p1, p2, -⟩ := hBt t (by omega)
        rw [hFk (t + 1) (by omega) hk, (hpar (t + 1) (by omega) hk).1,
          (hpar (t + 1) (by omega) hk).2, Nat.add_sub_cancel, ih _ (by omega) (by omega),
          himg_get _ p2, z6MulTab_psc hG hA hc (vec_lt (crd_lt hA hc (by omega)) _)
            (vec_lt (pow_lt64 p2) _), ← xor_mulF, ← crd_succ hA hc (by omega)]
  have hFG : z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v) =
      phiA Q (gOf (crd Q v) A B) :=
    ext64 hFs (size_phiA _) fun k hk => by rw [hFv k hk, phiA_get _ hk]
  have hFE : z6FEqn (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v)
      (z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v)) = true := by
    unfold z6FEqn
    simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true]
    refine ⟨⟨hFs, ?_⟩, fun k hk => ?_⟩
    · rw [Array.getElem?_eq_getElem (by omega), ← getElem!_pos _ 0 (by omega), hF0]
    · by_cases h0 : k = 0
      · exact Or.inl h0
      · exact Or.inr (hFk k (Nat.pos_of_ne_zero h0) hk)
  rw [hFE, Bool.true_and]
  rcases Bool.eq_false_or_eq_true
    (z6Valid (z6MulTab ()) (z6GsL ()) #[phiA Q A, phiA Q B]
      (z6BuildF (z6MulTab ()) (enumA0 ()) (z6Img (z6MulTab ()) T v))) with hval | hval
  swap
  · rw [hval]
    rfl
  rw [hval, Bool.not_true, Bool.false_or]
  unfold z6Valid z6IsNorm z6IsPerm at hval
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at hval
  obtain ⟨⟨hN, -, hP⟩, -⟩ := hval
  rw [hFG] at hN hP
  rw [z6GsL_eq hG hA hc hg hl] at hN
  have hN0 := hN 0 (by simp)
  have hN1 := hN 1 (by simp)
  rw [arr2_get0, arr2_get0, compA_phiA hA hc, compA_phiA hA hc] at hN0
  rw [arr2_get1, arr2_get1, compA_phiA hA hc, compA_phiA hA hc] at hN1
  have hI0 := phiA_inj hA hc (MULF_lt _ _) (MULF_lt _ _) hN0
  have hI1 := phiA_inj hA hc (MULF_lt _ _) (MULF_lt _ _) hN1
  have hker : ∀ x < 64, 0 < x → MULF x (gOf (crd Q v) A B) ≠ 0 := by
    intro x hx hx0 hz
    have hpx := psc_lt hA hc hx
    have hne : psc Q x ≠ 0 := fun h => by
      have := crd_psc hA hc hx
      rw [h, (coord_facts hc).1] at this
      omega
    have e1 : (phiA Q (gOf (crd Q v) A B))[psc Q x]! = 0 := by
      rw [phiA_psc hA hc _ hx, hz, psc_zero hA hc]
    exact (hP (psc Q x) hpx).2 0 (Nat.pos_of_ne_zero hne)
      (by rw [e1, phiA_zero hA hc])
  have hc0 : crd Q v ≠ 0 := by
    intro h
    apply hker 1 (by norm_num) (by norm_num)
    have := row_gOf hcl A B (j := 0) (by norm_num)
    rw [pow_zero] at this
    rw [this, h, zero_mulF]
  have hro := CFSG.KC.G2Three.allBelow_g2 hrep (by norm_num) (crd Q v - 1) (by omega)
  rw [show Nat.succ (crd Q v - 1) = crd Q v by omega] at hro
  unfold repOne at hro
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hro
  obtain ⟨⟨⟨⟨hρ, hs⟩, hs'⟩, hss⟩, hrepc⟩ := hro
  generalize Q (Nat.add 739 (crd Q v)) = ρ at hρ hrepc
  generalize Q (Nat.add 803 (crd Q v)) = s at hs hss hrepc
  generalize Q (Nat.add 867 (crd Q v)) = s' at hs' hss
  have hSS : pkMat 6 (lbL Q s) * pkMat 6 (lbL Q s') = 1 := by
    rw [← pkMat_MULF, hss, pkMat_ONE]
  have hSS' : pkMat 6 (lbL Q s') * pkMat 6 (lbL Q s) = 1 := mul_eq_one_comm.1 hSS
  have hcan : ∀ X, pkMat 6 (lbL Q s) * (pkMat 6 (lbL Q s') * X) = X := by
    intro X
    rw [← mul_assoc, hSS, one_mul]
  obtain ⟨u1, hu1, eu1⟩ := lbL_mul hl s' hs' ia hia'
  obtain ⟨ua, hua, eua⟩ := lbL_mul hl u1 hu1 s hs
  obtain ⟨u2, hu2, eu2⟩ := lbL_mul hl s' hs' ib hib'
  obtain ⟨ub, hub, eub⟩ := lbL_mul hl u2 hu2 s hs
  rw [eu1, hAe] at eua
  rw [eu2, hBe] at eub
  have hAm : pkMat 6 A * pkMat 6 A = 1 := by rw [← pkMat_MULF, hAA, pkMat_ONE]
  have hBm : pkMat 6 B * pkMat 6 B * pkMat 6 B = 1 := by
    rw [← pkMat_MULF, ← pkMat_MULF, hBB, pkMat_ONE]
  have hA2 : MULF (lbL Q ua) (lbL Q ua) = ONE := by
    rw [eua]
    refine pkMat_inj (MULF_lt _ _) ONE_lt ?_
    simp only [pkMat_MULF, pkMat_ONE, mul_assoc, hcan]
    rw [← mul_assoc (pkMat 6 A) (pkMat 6 A), hAm, one_mul, hSS']
  have hB3 : MULF (MULF (lbL Q ub) (lbL Q ub)) (lbL Q ub) = ONE := by
    rw [eub]
    refine pkMat_inj (MULF_lt _ _) ONE_lt ?_
    simp only [pkMat_MULF, pkMat_ONE, mul_assoc, hcan]
    rw [← mul_assoc (pkMat 6 B) (pkMat 6 B), ← mul_assoc (pkMat 6 B * pkMat 6 B), hBm, one_mul,
      hSS']
  have ea := CFSG.KC.G2Three.allBelow_g2 hia (by norm_num) ua hua
  rw [hA2, beq_self] at ea
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ea
  have eb := CFSG.KC.G2Three.allBelow_g2 hib (by norm_num) ub hub
  rw [hB3, beq_self] at eb
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at eb
  generalize Q (Nat.add 399 ua) = i at ea
  generalize Q (Nat.add 567 ub) = l at eb
  unfold candK at hcand
  simp only [Bool.and_eq_true, Nat.beq_eq] at hcand
  obtain ⟨htr0, hall⟩ := hcand
  have hp := CFSG.KC.G2Three.allBelow_g2 hall (by norm_num) (57 * i + l) (by omega)
  have hdiv : Nat.div (57 * i + l) 57 = i := by
    change (57 * i + l) / 57 = i
    omega
  have hmod : Nat.mod (57 * i + l) 57 = l := by
    change (57 * i + l) % 57 = l
    omega
  rw [hdiv, hmod, ea.2, eb.2, eua, eub] at hp
  unfold candP at hp
  simp only [boolN_eq] at hp
  have hr : MULF (crd Q v) (lbL Q s) < 64 := vec_lt hcl _
  have hG' := gOf_conj (A := A) (B := B) hcl hr hSS
  have hI0' : MULF (Q 0) (MULF (gOf (crd Q v) A B) (lbL Q s)) =
      MULF (MULF (gOf (crd Q v) A B) (lbL Q s)) (MULF (MULF (lbL Q s') A) (lbL Q s)) := by
    refine pkMat_inj (MULF_lt _ _) (MULF_lt _ _) ?_
    have hm := congrArg (pkMat 6) hI0
    simp only [pkMat_MULF] at hm ⊢
    simp only [mul_assoc, hcan]
    rw [← mul_assoc, hm, mul_assoc]
  have hI1' : MULF (Q 11) (MULF (gOf (crd Q v) A B) (lbL Q s)) =
      MULF (MULF (gOf (crd Q v) A B) (lbL Q s)) (MULF (MULF (lbL Q s') B) (lbL Q s)) := by
    refine pkMat_inj (MULF_lt _ _) (MULF_lt _ _) ?_
    have hm := congrArg (pkMat 6) hI1
    simp only [pkMat_MULF] at hm ⊢
    simp only [mul_assoc, hcan]
    rw [← mul_assoc, hm, mul_assoc]
  have hker' : ∀ x < 64, 0 < x → MULF x (MULF (gOf (crd Q v) A B) (lbL Q s)) ≠ 0 := by
    intro x hx hx0 hz
    apply hker x hx hx0
    have : MULF (MULF x (MULF (gOf (crd Q v) A B) (lbL Q s))) (lbL Q s') = 0 := by
      rw [hz, zero_mulF]
    rwa [mulF_assoc, mulF_assoc, hss, mulF_one (gOf_lt hcl _ _)] at this
  have htr : trK (MULF (MULF (MULF (lbL Q s') A) (lbL Q s)) (MULF (MULF (lbL Q s') B) (lbL Q s))) =
      1 := by
    rw [trK_conj hker' (M := MULF (Q 0) (Q 11)) ?_]
    · exact htr0
    · rw [mulF_assoc (Q 0) (Q 11), hI1', ← mulF_assoc (Q 0), hI0', mulF_assoc]
  rw [htr, beq_self, Bool.not_true, Bool.false_or] at hp
  have hρ' := CFSG.KC.G2Three.allBelow_g2 hp (by norm_num) ρ hρ
  have hρ'' : candG Q (W (Nat.add (Nat.mul 4 (57 * i + l)) ρ))
      (MULF (MULF (lbL Q s') A) (lbL Q s)) (MULF (MULF (lbL Q s') B) (lbL Q s))
      (gOf (Q (Nat.add 735 ρ)) (MULF (MULF (lbL Q s') A) (lbL Q s))
        (MULF (MULF (lbL Q s') B) (lbL Q s))) = true := hρ'
  rw [← hrepc, ← hG'] at hρ''
  unfold candG at hρ''
  rw [hI0', hI1', beq_self, beq_self, Bool.and_true, Bool.not_true, Bool.false_or] at hρ''
  unfold witOK at hρ''
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hρ''
  generalize W (Nat.add (Nat.mul 4 (57 * i + l)) ρ) = w at hρ''
  rcases hρ'' with ⟨⟨hw0, hw1⟩, hwG⟩ | ⟨⟨hw0, hw1⟩, hwz⟩
  · obtain ⟨u, hu, eu⟩ := lbL_mul hl (Nat.pred w) (by rw [Nat.pred_eq_sub_one]; omega) s' hs'
    have hGu : gOf (crd Q v) A B = lbL Q u := by
      rw [eu, hwG, mulF_assoc, hss, mulF_one (gOf_lt hcl _ _)]
    rw [hFG, hGu, enumL_lookup hG hA hc hg hl hu]
    rfl
  · exact absurd hwz (hker' (Nat.sub w 1000) (by change w - 1000 < 64; omega)
      (by change 0 < w - 1000; omega))

include hG hA hc hg hl in
theorem z6NormCheck_of (hrep : repK Q = true) (hia : iaK Q = true) (hib : ibK Q = true)
    (htree : treeK Q = true) (hcand : candK Q W = true) : z6NormCheck () = true := by
  obtain ⟨hE, -⟩ := enumL_inv hG hA hc hg hl
  obtain ⟨-, -, hB, -⟩ := lb_facts hl
  unfold treeK at htree
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Nat.beq_eq, Bool.and_true] at htree
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a7, b7⟩, ⟨a8, b8⟩, ⟨a13, b13⟩⟩ := htree
  unfold z6NormCheck
  simp only [allLt_iff]
  intro ia hia' ib hib'
  rw [enumL_get hG hA hc hg hl hia', enumL_get hG hA hc hg hl hib', arr2_get0, arr2_get1,
    compA_phiA hA hc, compA_phiA hA hc, compA_phiA hA hc, ← phiA_one hA hc,
    decide_phiA hA hc (MULF_lt _ _) ONE_lt, decide_phiA hA hc (MULF_lt _ _) ONE_lt]
  have hAl := lbL_lt hl ia hia'
  have hBl := lbL_lt hl ib hib'
  by_cases ha : MULF (lbL Q ia) (lbL Q ia) = ONE
  swap
  · rw [beq_false ha]
    rfl
  by_cases hb : MULF (MULF (lbL Q ib) (lbL Q ib)) (lbL Q ib) = ONE
  swap
  · rw [beq_false hb]
    simp
  rw [Nat.beq_eq.mpr ha, Nat.beq_eq.mpr hb, Bool.not_true, Bool.false_or, Bool.false_or]
  have hsz : (z6EnumL ()).elems.size = 168 := hE.1
  obtain ⟨hTs, hT0, hTm⟩ := buildF_facts (z6EnumL ())
    #[phiA Q (lbL Q ia), phiA Q (lbL Q ib)] (by rw [hsz]; norm_num) fun i h1 h2 => by
      rw [hsz] at h2
      rw [(hE.2.2.2.2.1 i h2 h1).1]
      have := (hB (i - 1) (by omega)).1
      omega
  have hTn : ∀ e < 167, (buildF (z6EnumL ()) #[phiA Q (lbL Q ia), phiA Q (lbL Q ib)])[e + 1]! =
      compA (buildF (z6EnumL ()) #[phiA Q (lbL Q ia), phiA Q (lbL Q ib)])[recF Q 140 0 e]!
        (#[phiA Q (lbL Q ia), phiA Q (lbL Q ib)])[recF Q 140 1 e]! := by
    intro e he
    have := hTm (e + 1) (by omega) (by rw [hsz]; omega)
    rwa [(hE.2.2.2.2.1 (e + 1) (by omega) (by omega)).1,
      (hE.2.2.2.2.1 (e + 1) (by omega) (by omega)).2, Nat.add_sub_cancel] at this
  generalize hT : buildF (z6EnumL ()) #[phiA Q (lbL Q ia), phiA Q (lbL Q ib)] = T at hTs hT0 hTm hTn ⊢
  have hT0' : T[0]! = phiA Q ONE := by rw [hT0, phiA_one hA hc]
  have hT1 : T[1]! = phiA Q (lbL Q ia) := by
    have := hTn 0 (by norm_num)
    rw [a0, b0, hT0', arr2_get0, compA_phiA hA hc, mulF_one hAl] at this
    exact this
  have hT2 : T[2]! = phiA Q (lbL Q ib) := by
    have := hTn 1 (by norm_num)
    rw [a1, b1, hT0', arr2_get1, compA_phiA hA hc, mulF_one hBl] at this
    exact this
  have hT3 : T[3]! = phiA Q (MULF (lbL Q ib) (lbL Q ia)) := by
    have := hTn 2 (by norm_num)
    rw [a2, b2, hT1, arr2_get1, compA_phiA hA hc] at this
    exact this
  have hT4 : T[4]! = phiA Q (MULF (lbL Q ia) (lbL Q ib)) := by
    have := hTn 3 (by norm_num)
    rw [a3, b3, hT2, arr2_get0, compA_phiA hA hc] at this
    exact this
  have hT5 : T[5]! = phiA Q (MULF (lbL Q ib) (lbL Q ib)) := by
    have := hTn 4 (by norm_num)
    rw [a4, b4, hT2, arr2_get1, compA_phiA hA hc] at this
    exact this
  have hT8 : T[8]! = phiA Q (MULF (lbL Q ib) (MULF (lbL Q ia) (lbL Q ib))) := by
    have := hTn 7 (by norm_num)
    rw [a7, b7, hT4, arr2_get1, compA_phiA hA hc] at this
    exact this
  have hT9 : T[9]! = phiA Q (MULF (lbL Q ia) (MULF (lbL Q ib) (lbL Q ib))) := by
    have := hTn 8 (by norm_num)
    rw [a8, b8, hT5, arr2_get0, compA_phiA hA hc] at this
    exact this
  have hT14 : T[14]! =
      phiA Q (MULF (lbL Q ib) (MULF (lbL Q ia) (MULF (lbL Q ib) (lbL Q ib)))) := by
    have := hTn 13 (by norm_num)
    rw [a13, b13, hT9, arr2_get1, compA_phiA hA hc] at this
    exact this
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold z6TEqn
    simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true]
    refine ⟨⟨hTs, ?_⟩, fun m hm => ?_⟩
    · rw [Array.getElem?_eq_getElem (by rw [hTs, hsz]; norm_num), ← getElem!_pos T 0
        (by rw [hTs, hsz]; norm_num), hT0]
    · by_cases h0 : m = 0
      · exact Or.inl h0
      · exact Or.inr (hTm m (Nat.pos_of_ne_zero h0) hm)
  · rw [allLt_iff]
    intro v hv
    exact norm_v hG hA hc hg hl hrep hia hib hcand hia' hib' rfl rfl (fun m hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hT0'
      · exact hT2
      · exact hT3
      · exact hT5
      · exact hT8
      · exact hT14) ha hb hv

include hG hA hc hg hl in
theorem cert550104_of (hm : lbMemK Q = true) (ho : orbK Q = true) (hrep : repK Q = true)
    (hia : iaK Q = true) (hib : ibK Q = true) (htree : treeK Q = true)
    (hcand : candK Q W = true) :
    (z6LbarCheck () = true) ∧ (z6OrbCheck () = true) ∧ (z6NormCheck () = true) :=
  ⟨z6LbarCheck_of hG hA hc hg hl hm, z6OrbCheck_of hG hA hc hg hl ho,
    z6NormCheck_of hG hA hc hg hl hrep hia hib htree hcand⟩

end Norm

end CFSG.KC.YamakiLbar

end
