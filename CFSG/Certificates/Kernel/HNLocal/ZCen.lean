module

public import Certificates.Data.Kernel.HNLocalZ
public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.HNLocal.Cen

public section

namespace CFSG.KS.HNLocal

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord Matrix

variable {L H CM RM ONE LV HV : Nat}

@[expose] def bitsE (x : Nat) : Nat → Nat := fun i => x / 2 ^ i % 2

private theorem ksZC_ne {x y : Nat} (h : notB (Nat.beq x y) = true) : x ≠ y := by
  intro hxy
  subst hxy
  rw [Nat.beq_refl] at h
  exact absurd h (by simp [notB])

private theorem ksZC_div_self {x k : Nat} (hx : x < 2 ^ k) : x / 2 ^ k % 2 = 0 := by
  rw [Nat.div_eq_of_lt hx]

private theorem ksZC_div_add {x k i : Nat} (hi : i < k) :
    (x + 2 ^ k) / 2 ^ i % 2 = x / 2 ^ i % 2 := by
  have h2 : (2 : Nat) ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i),
    show (2 : Nat) ^ (k - i) = 2 * 2 ^ (k - i - 1) by
      rw [← Nat.pow_succ']
      congr 1
      omega,
    Nat.add_mul_mod_self_left]

private theorem ksZC_div_add_self {x k : Nat} (hx : x < 2 ^ k) :
    (x + 2 ^ k) / 2 ^ k % 2 = 1 := by
  rw [show x + 2 ^ k = x + 2 ^ k * 1 by rw [Nat.mul_one],
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hx, Nat.zero_add]

private theorem ksZC_row_mul {A B : Matrix (Fin 133) (Fin 133) (ZMod 5)} {b : Nat} (hb : b < 133) :
    (fun j => A ⟨b, hb⟩ j) ᵥ* B = fun j => (A * B) ⟨b, hb⟩ j := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply]

private theorem ksZC_evMem {EV e : Nat} (h : evMem EV e = true) : ∃ s < 4, e = evAt EV s := by
  unfold evMem at h
  cases h0 : Nat.beq e (evAt EV 0)
  · rw [h0] at h
    dsimp only at h
    cases h1 : Nat.beq e (evAt EV 1)
    · rw [h1] at h
      dsimp only at h
      cases h2 : Nat.beq e (evAt EV 2)
      · rw [h2] at h
        dsimp only at h
        exact ⟨3, by omega, Nat.eq_of_beq_eq_true h⟩
      · rw [h2] at h
        dsimp only at h
        exact ⟨2, by omega, Nat.eq_of_beq_eq_true h2⟩
    · rw [h1] at h
      dsimp only at h
      exact ⟨1, by omega, Nat.eq_of_beq_eq_true h1⟩
  · rw [h0] at h
    dsimp only at h
    exact ⟨0, by omega, Nat.eq_of_beq_eq_true h0⟩

private theorem ksZC_rowA {PC : Nat → Nat} {M b j : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) (hM : Canon 5 133 13 M)
    (hb : b < 133) (hj : j < 14) :
    CenPf.VCanon 5 133 13 (vecR 5 13 1729 133 9 LV HV RM (rowL RM M b) (PC j)) ∧
      CenPf.toVec 5 133 13 (vecR 5 13 1729 133 9 LV HV RM (rowL RM M b) (PC j)) =
        fun t => (OM M * OM (PC j)) ⟨b, hb⟩ t := by
  have hr : CenPf.VCanon 5 133 13 (rowL RM M b) ∧
      CenPf.toVec 5 133 13 (rowL RM M b) = fun t => OM M ⟨b, hb⟩ t :=
    CenPf.row_spec (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9) hc hM hb
  obtain ⟨hv, hto⟩ := CenPf.vecR_sound (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9)
    hc hr.1 (hPC j hj)
  refine ⟨hv, ?_⟩
  rw [hto, hr.2]
  exact ksZC_row_mul (A := OM M) (B := OM (PC j)) hb

private theorem ksZC_rowB {PC : Nat → Nat} {M b j : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) (hM : Canon 5 133 13 M)
    (hb : b < 133) (hj : j < 14) :
    CenPf.VCanon 5 133 13 (vecR 5 13 1729 133 9 LV HV RM (rowL RM (PC j) b) M) ∧
      CenPf.toVec 5 133 13 (vecR 5 13 1729 133 9 LV HV RM (rowL RM (PC j) b) M) =
        fun t => (OM (PC j) * OM M) ⟨b, hb⟩ t := by
  have hr : CenPf.VCanon 5 133 13 (rowL RM (PC j) b) ∧
      CenPf.toVec 5 133 13 (rowL RM (PC j) b) = fun t => OM (PC j) ⟨b, hb⟩ t :=
    CenPf.row_spec (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9) hc (hPC j hj) hb
  obtain ⟨hv, hto⟩ := CenPf.vecR_sound (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9)
    hc hr.1 hM
  refine ⟨hv, ?_⟩
  rw [hto, hr.2]
  exact ksZC_row_mul (A := OM (PC j)) (B := OM M) hb

private theorem ksZC_rowC {PC : Nat → Nat} {Z M b j : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) (hZ : Canon 5 133 13 Z)
    (hM : Canon 5 133 13 M) (hb : b < 133) (hj : j < 14) :
    CenPf.VCanon 5 133 13
        (vecR 5 13 1729 133 9 LV HV RM (vecR 5 13 1729 133 9 LV HV RM (rowL RM Z b) (PC j)) M) ∧
      CenPf.toVec 5 133 13
          (vecR 5 13 1729 133 9 LV HV RM (vecR 5 13 1729 133 9 LV HV RM (rowL RM Z b) (PC j)) M) =
        fun t => ((OM Z * OM (PC j)) * OM M) ⟨b, hb⟩ t := by
  have hr : CenPf.VCanon 5 133 13 (rowL RM Z b) ∧
      CenPf.toVec 5 133 13 (rowL RM Z b) = fun t => OM Z ⟨b, hb⟩ t :=
    CenPf.row_spec (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9) hc hZ hb
  obtain ⟨hv1, ht1⟩ := CenPf.vecR_sound (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9)
    hc hr.1 (hPC j hj)
  have hin : CenPf.toVec 5 133 13
      (vecR 5 13 1729 133 9 LV HV RM (rowL RM Z b) (PC j)) =
      fun t => (OM Z * OM (PC j)) ⟨b, hb⟩ t := by
    rw [ht1, hr.2]
    exact ksZC_row_mul (A := OM Z) (B := OM (PC j)) hb
  obtain ⟨hv2, ht2⟩ := CenPf.vecR_sound (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9)
    hc hv1 hM
  refine ⟨hv2, ?_⟩
  rw [ht2, hin]
  exact ksZC_row_mul (A := OM Z * OM (PC j)) (B := OM M) hb

private theorem ksZC_elem_ok {PC TG : Nat → Nat} {Z EV M idx : Nat} {eZ e : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) (hZ : Canon 5 133 13 Z)
    (hZeq : OM Z = nfE PC 14 eZ) (hM : Canon 5 133 13 M)
    (hOM : OM M = nfE PC 14 e) (hbits : ∀ i < 14, idx / 2 ^ i % 2 = e i)
    (h : zElemOK (vecR 5 13 1729 133 9 LV HV RM) PC RM Z EV M idx (TG idx) = true) :
    (∃ s < 4, ∀ i < 14, e i = bitsE (evAt EV s) i) ∨
      ∃ j < 14, nfE PC 14 e * OM (PC j) ≠ OM (PC j) * nfE PC 14 e ∧
        nfE PC 14 e * OM (PC j) ≠ nfE PC 14 eZ * OM (PC j) * nfE PC 14 e := by
  unfold zElemOK at h
  generalize Nat.land (TG idx) 3 = kd at h
  generalize Nat.land (Nat.shiftRight (TG idx) 2) 15 = j at h
  generalize Nat.shiftRight (TG idx) 6 = b at h
  beta_reduce at h
  cases hk0 : Nat.beq kd 0
  · rw [hk0] at h
    dsimp only at h
    cases hk1 : Nat.beq kd 1
    · rw [hk1] at h
      dsimp only at h
      exact absurd h (by simp)
    · rw [hk1] at h
      dsimp only at h
      obtain ⟨hj, h⟩ := CenPf.andT h
      obtain ⟨hb, h⟩ := CenPf.andT h
      rw [CenPf.letB_eq] at h
      obtain ⟨hne1, hne2⟩ := CenPf.andT h
      have hj' : j < 14 := Nat.le_of_ble_eq_true hj
      have hb' : b < 133 := Nat.le_of_ble_eq_true hb
      have hA := ksZC_rowA hc hPC hM hb' hj'
      have hB := ksZC_rowB hc hPC hM hb' hj'
      have hC := ksZC_rowC hc hPC hZ hM hb' hj'
      refine Or.inr ⟨j, hj', ?_, ?_⟩
      · intro heq
        rw [← hOM] at heq
        refine ksZC_ne hne1 (CenPf.vec_inj (by norm_num) hA.1 hB.1 ?_)
        rw [hA.2, hB.2]
        funext t; rw [heq]
      · intro heq
        rw [← hOM, ← hZeq] at heq
        refine ksZC_ne hne2 (CenPf.vec_inj (by norm_num) hA.1 hC.1 ?_)
        rw [hA.2, hC.2]
        funext t; rw [heq]
  · rw [hk0] at h
    dsimp only at h
    obtain ⟨s, hs, hidx⟩ := ksZC_evMem h
    refine Or.inl ⟨s, hs, fun i hi => ?_⟩
    rw [← hbits i hi, hidx]
    rfl

private theorem ksZC_zcen_succ {mul vm : Nat → Nat → Nat} {PC TG : Nat → Nat}
    {RM Z EV n k M idx : Nat}
    (h : zcen mul vm PC TG RM Z EV (n + 1) k M idx = true) :
    zcen mul vm PC TG RM Z EV n (k + 1) M idx = true ∧
      zcen mul vm PC TG RM Z EV n (k + 1) (mul M (PC k)) (idx + 1 <<< k) = true := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (letB (mul M (PC k)) (fun M' => zcen mul vm PC TG RM Z EV n (Nat.succ k) M'
        (Nat.add idx (Nat.shiftLeft (nat_lit 1) k))))
      (zcen mul vm PC TG RM Z EV n (Nat.succ k) M idx) = true := h
  obtain ⟨h1, h2⟩ := CenPf.bAndT h'
  rw [CenPf.letB_eq] at h2
  exact ⟨h1, h2⟩

private theorem ksZC_zcen_step {PC TG : Nat → Nat} {Z EV : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) {eZ : Nat → Nat} {n : Nat}
    (ih : ∀ k M idx, k + n = 14 → Canon 5 133 13 M →
      zcen (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC TG RM Z EV
        n k M idx = true →
      ∀ e : Nat → Nat, (∀ i, e i < 2) → OM M = nfE PC k e → idx < 2 ^ k →
        (∀ i < k, idx / 2 ^ i % 2 = e i) →
        (∃ s < 4, ∀ i < 14, e i = bitsE (evAt EV s) i) ∨
        ∃ j < 14, nfE PC 14 e * OM (PC j) ≠ OM (PC j) * nfE PC 14 e ∧
          nfE PC 14 e * OM (PC j) ≠ nfE PC 14 eZ * OM (PC j) * nfE PC 14 e) :
    ∀ k M idx, k + (n + 1) = 14 → Canon 5 133 13 M →
      zcen (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC TG RM Z EV
        (n + 1) k M idx = true →
      ∀ e : Nat → Nat, (∀ i, e i < 2) → OM M = nfE PC k e → idx < 2 ^ k →
        (∀ i < k, idx / 2 ^ i % 2 = e i) →
        (∃ s < 4, ∀ i < 14, e i = bitsE (evAt EV s) i) ∨
        ∃ j < 14, nfE PC 14 e * OM (PC j) ≠ OM (PC j) * nfE PC 14 e ∧
          nfE PC 14 e * OM (PC j) ≠ nfE PC 14 eZ * OM (PC j) * nfE PC 14 e := by
  intro k M idx hkn hM h e he hOM hidx hbits
  obtain ⟨h1, h2⟩ := ksZC_zcen_succ h
  have hkn' : k + 1 + n = 14 := by omega
  rcases Nat.lt_or_ge (e k) 1 with hk | hk
  · have hk0 : e k = 0 := by omega
    refine ih (k + 1) M idx hkn' hM h1 e he ?_ ?_ ?_
    · rw [CenPf.nfE_succ, hk0, pow_zero, mul_one]
      exact hOM
    · rw [Nat.pow_succ]
      omega
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
      · exact hbits i hlt
      · rw [ksZC_div_self hidx, hk0]
  · have hk1 : e k = 1 := by have := he k; omega
    obtain ⟨hM', hOM'⟩ := mulR_sound hc hM (hPC k (by omega))
    refine ih (k + 1) (mulR 5 13 1729 133 9 L H CM RM M (PC k)) (idx + 1 <<< k) hkn' hM' h2
      e he ?_ ?_ ?_
    · rw [CenPf.nfE_succ, hk1, pow_one, ← hOM]
      exact hOM'
    · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
      omega
    · intro i hi
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
      · rw [ksZC_div_add (x := idx) hlt]
        exact hbits i hlt
      · rw [ksZC_div_add_self hidx, hk1]

private theorem ksZC_zcen_ok {PC TG : Nat → Nat} {Z EV : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) (hZ : Canon 5 133 13 Z)
    {eZ : Nat → Nat} (hZeq : OM Z = nfE PC 14 eZ) :
    ∀ n k M idx, k + n = 14 → Canon 5 133 13 M →
      zcen (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC TG RM Z EV
        n k M idx = true →
      ∀ e : Nat → Nat, (∀ i, e i < 2) → OM M = nfE PC k e → idx < 2 ^ k →
        (∀ i < k, idx / 2 ^ i % 2 = e i) →
        (∃ s < 4, ∀ i < 14, e i = bitsE (evAt EV s) i) ∨
        ∃ j < 14, nfE PC 14 e * OM (PC j) ≠ OM (PC j) * nfE PC 14 e ∧
          nfE PC 14 e * OM (PC j) ≠ nfE PC 14 eZ * OM (PC j) * nfE PC 14 e := by
  intro n
  induction n with
  | zero =>
    intro k M idx hkn hM h e he hOM hidx hbits
    have hk : k = 14 := by omega
    rw [hk] at hOM hbits
    exact ksZC_elem_ok hc hPC hZ hZeq hM hOM hbits h
  | succ n ih => exact ksZC_zcen_step hc hPC ih

theorem zcenAt_sound {PC TG : Nat → Nat} {ez EV m k n : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < 14, Canon 5 133 13 (PC i)) (hkn : k + n = 14) (hm : m < 2 ^ k)
    (h : zcenAt (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC TG ONE RM ez
      EV m k n = true) :
    ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < k, e i = m / 2 ^ i % 2) →
      (∃ s < 4, ∀ i < 14, e i = bitsE (evAt EV s) i) ∨
      ∃ j < 14, nfE PC 14 e * ordMat 5 133 13 1729 (PC j) ≠
          ordMat 5 133 13 1729 (PC j) * nfE PC 14 e ∧
        nfE PC 14 e * ordMat 5 133 13 1729 (PC j) ≠
          nfE PC 14 (bitsE ez) * ordMat 5 133 13 1729 (PC j) * nfE PC 14 e := by
  intro e he hek
  have h' : zcen (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC TG RM
      (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE ez 14) EV n k
      (nfPre (mulR 5 13 1729 133 9 L H CM RM) PC ONE m k) m = true := by
    unfold zcenAt at h
    simpa only [CenPf.letB_eq] using h
  obtain ⟨hZc, hZe⟩ := CenPf.nfPre_ok hc ez 14 (fun i hi => hPC i (by omega))
  obtain ⟨hMc, hMe⟩ := CenPf.nfPre_ok hc m k (fun i hi => hPC i (by omega))
  refine ksZC_zcen_ok hc hPC hZc hZe n k _ m hkn hMc h' e he ?_ hm ?_
  · rw [hMe]
    exact CenPf.nfE_congr PC k fun i hi => (hek i hi).symm
  · exact fun i hi => (hek i hi).symm

end CFSG.KS.HNLocal

end
