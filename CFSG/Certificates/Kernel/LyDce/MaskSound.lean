module

public import Certificates.Data.Kernel.LyDce.CoverWalk
public import CFSG.Certificates.Kernel.LyBase.Sound

public section

namespace CFSG.KC.LyDce

open Equiv Pointwise CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.Benes
  CFSG.KC.YModel.Sem CFSG.KC.LyBenes CFSG.KC.LyBase

variable {n : Nat}

@[expose] def IsMask (M : Nat) (S : Set (Fin n)) : Prop :=
  ∀ q, M.testBit q = true ↔ ∃ h : q < n, (⟨q, h⟩ : Fin n) ∈ S

theorem IsMask.mem {M : Nat} {S : Set (Fin n)} (h : IsMask M S) (a : Fin n) :
    M.testBit a = true ↔ a ∈ S := by
  rw [h a]
  exact ⟨fun ⟨_, ha⟩ => ha, fun ha => ⟨a.2, ha⟩⟩

theorem IsMask.testBit_ge {M : Nat} {S : Set (Fin n)} (h : IsMask M S) {q : Nat} (hq : n ≤ q) :
    M.testBit q = false := by
  cases e : M.testBit q with
  | false => rfl
  | true =>
    obtain ⟨hq', _⟩ := (h q).1 e
    omega

theorem IsMask.eq {M M' : Nat} {S : Set (Fin n)} (h : IsMask M S) (h' : IsMask M' S) :
    M = M' := by
  apply Nat.eq_of_testBit_eq
  intro q
  apply Bool.eq_iff_iff.2
  rw [h q, h' q]

theorem IsMask.lt {M : Nat} {S : Set (Fin n)} (h : IsMask M S) : M < 2 ^ n :=
  lt_of_testBit_ge fun _ hq => h.testBit_ge hq

theorem mem_inv_smul {g : Perm (Fin n)} {S : Set (Fin n)} (a : Fin n) :
    a ∈ g⁻¹ • S ↔ g a ∈ S := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Perm.smul_def]

theorem testBit_maskOf (q : Nat) : ∀ O : List Nat, (maskOf O).testBit q = decide (q ∈ O)
  | [] => by
    change (0 : Nat).testBit q = _
    simp
  | a :: O => by
    change (strictN (maskOf O) fun x => Nat.lor x (Nat.shiftLeft 1 a)).testBit q = _
    rw [strictN_eq, nlor, nshl, Nat.one_shiftLeft, Nat.testBit_or, testBit_maskOf q O,
      Nat.testBit_two_pow]
    by_cases h : q = a
    · subst h
      simp
    · have h' : a ≠ q := fun e => h e.symm
      simp [h, h']

theorem isMask_maskOf {O : List Nat} (hO : ∀ a ∈ O, a < n) :
    IsMask (maskOf O) {a : Fin n | (a : Nat) ∈ O} := by
  intro q
  rw [testBit_maskOf, decide_eq_true_iff]
  exact ⟨fun hq => ⟨hO q hq, hq⟩, fun ⟨_, hq⟩ => hq⟩

theorem salt0_lt : salt0 < 2 ^ 131072 := by decide +kernel

theorem IsMask.land_ones {M : Nat} {S : Set (Fin n)} (h : IsMask M S) :
    Nat.land M (ones n) = M := by
  rw [nland, ones_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h.lt]

theorem IsMask.keyOf_eq {M : Nat} {S : Set (Fin 66825)} (h : IsMask M S) (P : Nat) :
    keyOf P M = M % P := by
  unfold keyOf
  rw [h.land_ones]
  rfl

theorem shiftRight_saltOf (M : Nat) : saltOf M >>> 131072 = M := by
  apply Nat.eq_of_testBit_eq
  intro q
  have hs : salt0.testBit (131072 + q) = false :=
    Nat.testBit_lt_two_pow (lt_two_pow_mono salt0_lt (by omega))
  change (Nat.lor (Nat.shiftLeft M 131072) salt0 >>> 131072).testBit q = _
  rw [Nat.testBit_shiftRight, nlor, nshl, Nat.testBit_or, Nat.testBit_shiftLeft, hs,
    Bool.or_false, Nat.add_sub_cancel_left]
  simp

theorem testBit_net2 {N : Nat} (hv : StagesValid 17 N) (X : Nat) :
    (∀ r < 2 ^ 17, (net2 N X).testBit (131072 + r) =
      X.testBit (131072 + benesPerm 17 N r)) ∧
    (∀ q, 262144 ≤ q → (net2 N X).testBit q = X.testBit q) := by
  have e : net2 N X = netApply 17 131072 (repU 131072 2) N X := by
    change netsApply 17 131072 (repU 131072 2) [N] X = _
    rw [netsApply_cons]
    rfl
  have h := testBit_netApply (k := 17) (W := 131072) (P := 2) (by norm_num) hv X
  rw [e]
  refine ⟨fun r hr => ?_, fun q hq => h.2 q (by omega)⟩
  have := h.1 1 (by decide) r (by simpa using hr)
  simpa using this

theorem le_benesPerm {N : Nat} {g : Perm (Fin n)} (hv : StagesValid 17 N) (hN : NRep 17 n N g)
    {r : Nat} (hr : n ≤ r) : n ≤ benesPerm 17 N r := by
  by_contra hlt
  have hlt' : benesPerm 17 N r < n := by omega
  have e : benesPerm 17 N (g⁻¹ ⟨benesPerm 17 N r, hlt'⟩ : Fin n) = benesPerm 17 N r := by
    rw [hN, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  have e2 := congrArg (benesInv 17 N) e
  rw [benesInv_benesPerm hv, benesInv_benesPerm hv] at e2
  have := (g⁻¹ ⟨benesPerm 17 N r, hlt'⟩).2
  omega

theorem isMask_net2 {N : Nat} {g : Perm (Fin n)} (hn : n ≤ 2 ^ 17) (hv : StagesValid 17 N)
    (hN : NRep 17 n N g) {X : Nat} {S : Set (Fin n)} (hX : IsMask (X >>> 131072) S) :
    IsMask (net2 N X >>> 131072) (g⁻¹ • S) := by
  intro q
  rw [Nat.testBit_shiftRight]
  by_cases hq : q < 2 ^ 17
  · rw [(testBit_net2 hv X).1 q hq, ← Nat.testBit_shiftRight]
    by_cases hqn : q < n
    · have e : benesPerm 17 N q = (g ⟨q, hqn⟩ : Nat) := hN ⟨q, hqn⟩
      rw [e, hX.mem, ← mem_inv_smul]
      exact ⟨fun h => ⟨hqn, h⟩, fun ⟨_, h⟩ => h⟩
    · rw [hX.testBit_ge (le_benesPerm hv hN (by omega))]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨h, _⟩ => absurd h hqn⟩
  · rw [(testBit_net2 hv X).2 _ (by omega), ← Nat.testBit_shiftRight,
      hX.testBit_ge (by omega)]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨h, _⟩ => absurd h (by omega)⟩

theorem smul_eq_of_netsApply {Ns : List Nat} {g : Perm (Fin n)} (hn : n ≤ 2 ^ 17)
    (hv : ∀ N ∈ Ns, StagesValid 17 N) (hg : ∀ a : Fin n, compN 17 Ns a = (g a : Nat)) {M : Nat}
    {S : Set (Fin n)} (hM : IsMask M S) (h : netsApply 17 131072 1 Ns M = M) : g • S = S := by
  ext x
  have hb := testBit_netsApply17 hv M (p := (g⁻¹ x : Fin n)) (by have := (g⁻¹ x).2; omega)
  rw [h, hg, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at hb
  rw [Set.mem_smul_set_iff_inv_smul_mem, Perm.smul_def, ← hM.mem, ← hM.mem, hb]

theorem strictBN_eq (y : Nat) (k : Nat → Bool) : strictBN y k = k y := by
  cases y <;> rfl

theorem lineS_sound {P K Tc Td l X Xc Xd : Nat} (h : lineS P K Tc Td l X Xc Xd = true) :
    keyS P X = fldW 48 K l ∧ fldW 16 Tc l < nL ∧ fldW 16 Td l < nL ∧
      keyS P Xc = fldW 48 K (fldW 16 Tc l) ∧ keyS P Xd = fldW 48 K (fldW 16 Td l) := by
  have h' : andB (Nat.beq (keyS P X) (fldW 48 K l))
      (strictBN (fldW 16 Tc l) fun a => strictBN (fldW 16 Td l) fun b =>
        andB (andB (Nat.blt a nL) (Nat.blt b nL))
          (andB (Nat.beq (keyS P Xc) (fldW 48 K a)) (Nat.beq (keyS P Xd) (fldW 48 K b)))) =
      true := h
  obtain ⟨h1, h2⟩ := andB_true h'
  rw [strictBN_eq, strictBN_eq] at h2
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h3
  obtain ⟨h7, h8⟩ := andB_true h4
  exact ⟨Nat.eq_of_beq_eq_true h1, by simpa [Nat.blt_eq] using h5,
    by simpa [Nat.blt_eq] using h6, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8⟩

theorem fixOK_sound {NS : Nat → Nat} {M₀ : Nat} : ∀ {G : List (List Nat)},
    fixOK NS M₀ G = true → ∀ g ∈ G, netsApply 17 131072 1 ((jwOf g).map NS) M₀ = M₀
  | [], _, _, hg => absurd hg List.not_mem_nil
  | g' :: G, h, g, hg => by
    have h' : andB (Nat.beq (netsApply 17 131072 1 ((jwOf g').map NS) M₀) M₀)
        (fixOK NS M₀ G) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases List.mem_cons.1 hg with rfl | hg
    · exact Nat.eq_of_beq_eq_true h1
    · exact fixOK_sound h2 g hg

theorem allFix_sound {cF dF : Nat → Nat} {G : List (List Nat)} {b : Nat} :
    ∀ {ws : List (List Nat)}, allFix cF dF G b ws = true →
      ∀ w ∈ ws, fixAll cF dF [b] (expandG G w) = true
  | [], _, _, hw => absurd hw List.not_mem_nil
  | w' :: ws, h, w, hw => by
    have h' : andB (fixAll cF dF [b] (expandG G w')) (allFix cF dF G b ws) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h1
    · exact allFix_sound h2 w hw

end CFSG.KC.LyDce

end
