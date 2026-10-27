module

public import CFSG.Certificates.Kernel.Hall82K.SoundAff

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.CGT.Hall82

theorem u0K_eq : u0K = hallU0List := rfl

theorem kK_eq : kK = hallKList := rfl

theorem u0K_lt : ∀ u ∈ u0K, u < 64 := by decide +kernel

theorem fullK_testBit : ∀ k < 64, fullK.testBit k = true := by decide +kernel

theorem orb_mask_iff : ∀ k : Fin 64, Nat.land 146 (Nat.shiftLeft 1 k.val) = 0 ↔ ¬ IsHallOrb k := by
  unfold IsHallOrb
  decide +kernel

theorem codeA_transl5 : codeA ⇑(transl 5) = trK 5 := codeA_transl 5

theorem lor36_m36' {L : ℕ} (hL : L < 2 ^ 36) (u : ℕ) :
    Nat.land (Nat.lor L (Nat.shiftLeft u 36)) m36K = L := lor36_m36 hL u

theorem lor36_shr' {L : ℕ} (hL : L < 2 ^ 36) (u : ℕ) :
    Nat.shiftRight (Nat.lor L (Nat.shiftLeft u 36)) 36 = u := lor36_shr hL u

theorem apL_lor36' {L : ℕ} (hL : L < 2 ^ 36) (u v : ℕ) :
    apL (Nat.lor L (Nat.shiftLeft u 36)) v = apL L v := apL_lor36 hL u v

theorem eq_codeA_iff {g h : Equiv.Perm (Fin 64)} (hg : IsAff g) (hh : IsAff h) :
    g = h ↔ codeA g = codeA h :=
  ⟨fun e => e ▸ rfl, fun e => Equiv.ext fun v => congrFun (codeA_inj hg hh e) v⟩

section X1

variable (hrm : zipArrK rmK hallRMArr = true)
  (hinv : allL (fun r => Nat.beq (compL r r) idK) rmK = true)

include hrm hinv in
theorem xcode_mul_of (hmul : x1MulK = true) :
    ∀ x ∈ hallX1, ∀ y ∈ hallX1, xcode (x * y) = xorF (xcode x) (xcode y) := by
  intro x hx y hy
  have hxa := (x1_code hrm hinv hx).1
  have hya := (x1_code hrm hinv hy).1
  have h1 := allX1_code hrm hinv hmul hx
  have h2 : Nat.beq (xcodeK (compA (codeA x) (codeA y))) (Nat.xor (xcodeK (codeA x))
      (xcodeK (codeA y))) = true := allX1_code hrm hinv h1 hy
  rw [nbeq_iff, compA_codeA_mul hxa hya, xcodeK_codeA, xcodeK_codeA, xcodeK_codeA] at h2
  exact Fin.ext h2

include hrm hinv in
theorem xcode_eq_zero_of (hz : x1ZeroK = true) :
    ∀ x ∈ hallX1, xcode x = 0 ↔ x = 1 ∨ x = transl 5 := by
  intro x hx
  have hxa := (x1_code hrm hinv hx).1
  have h : beqB (Nat.beq (xcodeK (codeA x)) 0)
      (bor (Nat.beq (codeA x) idK) (Nat.beq (codeA x) (trK 5))) = true := allX1_code hrm hinv hz hx
  rw [beqB_eq_true, nbeq_iff, bor_eq_true, nbeq_iff, nbeq_iff, xcodeK_codeA] at h
  rw [eq_codeA_iff hxa isAff_one, eq_codeA_iff hxa (isAff_transl 5), codeA_one, codeA_transl5,
    ← h]
  exact Fin.ext_iff

include hrm hinv in
theorem xcode_surj_of (hs : x1SurjK = true) : ∀ k, ∃ x ∈ hallX1, xcode x = k := by
  intro k
  have hb := fullK_testBit k.val k.2
  rw [← nbeq_iff.1 hs, testBit_orL] at hb
  obtain ⟨u, hu, hb⟩ := hb
  rw [testBit_orL] at hb
  obtain ⟨r, hr, hb⟩ := hb
  change (1 <<< _).testBit _ = true at hb
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hb
  obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hr
  have hu64 := u0K_lt u hu
  refine ⟨transl ⟨u, hu64⟩ * hallRMPerm ⟨e, he⟩, ⟨⟨u, hu64⟩, hu, ⟨e, he⟩, rfl⟩, Fin.ext ?_⟩
  rw [← xcodeK_codeA, codeA_transl_mul hrm hinv, List.getD_eq_getElem _ _ he]
  exact hb

include hrm hinv in
theorem xcode_sq_of (hq0 : q0BridgeK = true) (hsq : x1SqK = true) :
    ∀ x ∈ hallX1, x * x = transl 5 ↔ hallQ0 (xcode x) = true := by
  intro x hx
  have hxa := (x1_code hrm hinv hx).1
  have h : beqB (Nat.beq (compA (codeA x) (codeA x)) (trK 5))
      (Nat.beq (bitN q0K (xcodeK (codeA x))) 1) = true := allX1_code hrm hinv hsq hx
  have hq : beqB (hallQ0List.getD (xcode x).val false) (Nat.beq (bitN q0K (xcode x).val) 1) =
      true := allN_iff.1 hq0 _ (xcode x).2
  rw [beqB_eq_true, nbeq_iff, nbeq_iff, compA_codeA_mul hxa hxa, xcodeK_codeA] at h
  rw [beqB_eq_true, nbeq_iff] at hq
  rw [eq_codeA_iff (isAff_mul hxa hxa) (isAff_transl 5), codeA_transl5, h, ← hq]
  rfl

include hrm hinv in
theorem xcode_orb_of (horb : x1OrbK = true) :
    ∀ x ∈ hallX1, IsHallOrb (xcode x) → ∃ h, IsOvalVec h ∧ x = transl h := by
  intro x hx ho
  have hxa := (x1_code hrm hinv hx).1
  have h : bor (Nat.beq (Nat.land 146 (Nat.shiftLeft 1 (xcodeK (codeA x)))) 0)
      (band (Nat.beq (Nat.land (codeA x) m36K) idK) (memL (Nat.shiftRight (codeA x) 36) kK)) =
      true := allX1_code hrm hinv horb hx
  rw [bor_eq_true, band_eq_true, nbeq_iff, nbeq_iff, memL_iff, xcodeK_codeA, codeA_m36,
    codeA_shr] at h
  rcases h with h | ⟨hl, hk⟩
  · exact absurd ho ((orb_mask_iff _).1 h)
  · have hid : linPart x = id := codeL_inj hxa (fun _ _ => rfl) (hl.trans codeL_id.symm)
    refine ⟨x 0, hk, Equiv.ext fun v => ?_⟩
    rw [eq_linPart x v, hid]
    rfl

end X1

theorem hallRIdx_rmK : ∀ i : Fin 3, rmK.getD (hallRIdx i).val 0 =
    [45451591809, 51811205313, 34628702724].getD i.val 0 := by
  decide +kernel

section Lift

variable (hrm : zipArrK rmK hallRMArr = true)
  (hinv : allL (fun r => Nat.beq (compL r r) idK) rmK = true)

include hrm hinv in
theorem codeA_hallXi (a : Fin 3 → Fin 64) (i : Fin 3) :
    codeA ⇑(hallXi a i) = xiK ([45451591809, 51811205313, 34628702724].getD i.val 0) (a i).val := by
  unfold hallXi
  rw [codeA_transl_mul hrm hinv, hallRIdx_rmK]
  rfl

include hrm hinv in
theorem isAff_hallXi (a : Fin 3 → Fin 64) (i : Fin 3) : IsAff (hallXi a i) :=
  isAff_transl_mul hrm hinv _ _

include hrm hinv in
theorem hallXi_inv (a : Fin 3 → Fin 64) (i : Fin 3) :
    (hallXi a i)⁻¹ = hallRMPerm (hallRIdx i) * transl (a i) := by
  unfold hallXi
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (transl_mul_self (a i)),
    inv_eq_of_mul_eq_one_right (hallRMPerm_mul_self hrm hinv _)]

include hrm hinv in
theorem codeA_hallXi_inv (a : Fin 3 → Fin 64) (i : Fin 3) :
    codeA ⇑((hallXi a i)⁻¹) = invIK (codeA (hallXi a i)) := by
  have hl : (hallRIdx i).val < rmK.length := (hallRIdx i).2
  have hmem : rmK.getD (hallRIdx i).val 0 ∈ rmK := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hlt := rmK_lt _ hmem
  rw [hallXi_inv hrm hinv, codeA_mul_transl hrm hinv]
  unfold hallXi
  rw [codeA_transl_mul hrm hinv]
  unfold invIK
  rw [lor36_m36' hlt, apL_lor36' hlt, lor36_shr' hlt]

include hrm hinv in
theorem isAff_hallXi_inv (a : Fin 3 → Fin 64) (i : Fin 3) : IsAff ⇑((hallXi a i)⁻¹) := by
  rw [hallXi_inv hrm hinv]
  exact isAff_mul (isAff_hallRMPerm hrm hinv _) (isAff_transl _)

theorem oneOr5_of {z : ℕ} (h : z = idK ∨ z = trK 5) : oneOr5 z = true := by
  unfold oneOr5
  rw [bor_eq_true, nbeq_iff, nbeq_iff]
  exact h

include hrm hinv in
theorem sqOK_of {a : Fin 3 → Fin 64} {i : Fin 3}
    (h : hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5) :
    sqOK (xiK ([45451591809, 51811205313, 34628702724].getD i.val 0) (a i).val) = true := by
  unfold sqOK
  rw [← codeA_hallXi hrm hinv, compA_codeA_mul (isAff_hallXi hrm hinv a i)
    (isAff_hallXi hrm hinv a i)]
  apply oneOr5_of
  rcases h with h | h
  · left
    rw [h, codeA_one]
  · right
    rw [h, codeA_transl5]

include hrm hinv in
theorem commOK_of {a : Fin 3 → Fin 64} {i j : Fin 3}
    (h : hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
      hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5) :
    commOK (xiK ([45451591809, 51811205313, 34628702724].getD i.val 0) (a i).val)
      (xiK ([45451591809, 51811205313, 34628702724].getD j.val 0) (a j).val) = true := by
  have hi := isAff_hallXi hrm hinv a i
  have hj := isAff_hallXi hrm hinv a j
  have hi' := isAff_hallXi_inv hrm hinv a i
  have hj' := isAff_hallXi_inv hrm hinv a j
  unfold commOK
  rw [← codeA_hallXi hrm hinv, ← codeA_hallXi hrm hinv, ← codeA_hallXi_inv hrm hinv,
    ← codeA_hallXi_inv hrm hinv, compA_codeA_mul hi hj, compA_codeA_mul hi' hj',
    compA_codeA_mul (isAff_mul hi hj) (isAff_mul hi' hj'), ← mul_assoc]
  apply oneOr5_of
  rcases h with h | h
  · left
    rw [h, codeA_one]
  · right
    rw [h, codeA_transl5]

theorem liftK_spec {r0 r1 r2 : ℕ} (h : liftK r0 r1 r2 = true) {a0 a1 a2 : ℕ} (h0 : a0 < 64)
    (h1 : a1 < 64) (h2 : a2 < 64) (s0 : sqOK (xiK r0 a0) = true) (s1 : sqOK (xiK r1 a1) = true)
    (s2 : sqOK (xiK r2 a2) = true) (c01 : commOK (xiK r0 a0) (xiK r1 a1) = true)
    (c02 : commOK (xiK r0 a0) (xiK r2 a2) = true) (c12 : commOK (xiK r1 a1) (xiK r2 a2) = true) :
    inU a0 = true ∧ inU a1 = true ∧ inU a2 = true := by
  have k0 := allN_iff.1 h a0 h0
  rw [bor_eq_true, bnot_eq_true, s0] at k0
  have k1 := allN_iff.1 (k0.resolve_left (by simp)) a1 h1
  rw [bor_eq_true, bnot_eq_true, band_eq_true.2 ⟨s1, c01⟩] at k1
  have k2 := allN_iff.1 (k1.resolve_left (by simp)) a2 h2
  rw [bor_eq_true, bnot_eq_true, band_eq_true.2 ⟨s2, band_eq_true.2 ⟨c02, c12⟩⟩] at k2
  have k3 := k2.resolve_left (by simp)
  rw [band_eq_true, band_eq_true] at k3
  exact k3

include hrm hinv in
theorem lift_of (hl : liftK 45451591809 51811205313 34628702724 = true) :
    ∀ a : Fin 3 → Fin 64,
      (∀ i j, hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
        hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5) →
      (∀ i, hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5) →
      (∀ s ∈ hexaM, s 5 = 5 → ∀ i, ∃ u, InHallU u ∧ ∃ e, s * hallXi a i * s⁻¹ =
        transl u * hallXProd a e) →
      ∀ i, InHallU (a i) := by
  intro a hc hs _ i
  have k := liftK_spec hl (a 0).2 (a 1).2 (a 2).2 (sqOK_of hrm hinv (hs 0))
    (sqOK_of hrm hinv (hs 1)) (sqOK_of hrm hinv (hs 2)) (commOK_of hrm hinv (hc 0 1))
    (commOK_of hrm hinv (hc 0 2)) (commOK_of hrm hinv (hc 1 2))
  unfold inU at k
  rw [memL_iff, memL_iff, memL_iff] at k
  unfold InHallU
  fin_cases i
  · exact k.1
  · exact k.2.1
  · exact k.2.2

end Lift

end CFSG.KC.Hall82K
