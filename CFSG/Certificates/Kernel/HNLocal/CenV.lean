module

public import Certificates.Data.Kernel.HNLocalV
public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.HNLocal.Cen

public section

namespace CFSG.KS.HNLocal

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord Matrix

variable {L H CM RM ONE LV HV : Nat}

private theorem cenV_div_add {x k i : Nat} (hi : i < k) :
    (x + 2 ^ k) / 2 ^ i % 2 = x / 2 ^ i % 2 := by
  have h2 : (2 : Nat) ^ k = 2 ^ i * (2 * 2 ^ (k - i - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]
    congr 1
    omega
  rw [h2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.add_mul_mod_self_left]

private theorem cenV_div_add_self {x k : Nat} (hx : x < 2 ^ k) :
    (x + 2 ^ k) / 2 ^ k % 2 = 1 := by
  rw [show x + 2 ^ k = x + 2 ^ k * 1 by rw [Nat.mul_one],
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hx, Nat.zero_add]

private theorem cenV_vec (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) {v M : Nat}
    (hv : CenPf.VCanon 5 133 13 v) (hM : Canon 5 133 13 M) :
    CenPf.VCanon 5 133 13 (vecR 5 13 1729 133 9 LV HV RM v M) ∧
      CenPf.toVec 5 133 13 (vecR 5 13 1729 133 9 LV HV RM v M) = CenPf.toVec 5 133 13 v ᵥ* OM M :=
  CenPf.vecR_sound (p := 5) (w := 13) (S := 1729) (d := 133) (T := 9) hc hv hM

private theorem wordV_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    {PC : Nat → Nat} {v : Nat} (hv : CenPf.VCanon 5 133 13 v) (m : Nat) :
    ∀ k, (∀ i < k, Canon 5 133 13 (PC i)) →
      CenPf.VCanon 5 133 13 (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k) ∧
        CenPf.toVec 5 133 13 (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k) =
          CenPf.toVec 5 133 13 v ᵥ* nfE PC k (fun i => m / 2 ^ i % 2)
  | 0, _ => ⟨hv, by rw [CenPf.nfE_zero, Matrix.vecMul_one]; rfl⟩
  | k + 1, hPC => by
    obtain ⟨ih1, ih2⟩ := wordV_ok hc hv m k (fun i hi => hPC i (by omega))
    have e1 : wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m (k + 1) =
        Bool.rec (motive := fun _ => Nat) (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k)
          (vecR 5 13 1729 133 9 LV HV RM (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k) (PC k))
          (Nat.beq (Nat.land (Nat.shiftRight m k) 1) 1) := by
      have e0 : wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m (k + 1) =
          CFSG.KC.Loop.strictN (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k) (fun a =>
            Bool.rec (motive := fun _ => Nat) a (vecR 5 13 1729 133 9 LV HV RM a (PC k))
              (Nat.beq (Nat.land (Nat.shiftRight m k) 1) 1)) := rfl
      rw [e0, CenPf.strictN_eq]
    have hland : Nat.land (Nat.shiftRight m k) 1 = m / 2 ^ k % 2 := by
      change (m >>> k) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    rw [e1, hland, CenPf.nfE_succ]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with hb | hb
    · rw [hb]
      refine ⟨ih1, ?_⟩
      change CenPf.toVec 5 133 13 (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k) = _
      simp only [pow_zero, mul_one, ih2]
    · rw [hb]
      obtain ⟨h1, h2⟩ := cenV_vec hc ih1 (hPC k (by omega))
      refine ⟨h1, ?_⟩
      change CenPf.toVec 5 133 13 (vecR 5 13 1729 133 9 LV HV RM
        (wordV (vecR 5 13 1729 133 9 LV HV RM) PC v m k) (PC k)) = _
      simp only [pow_one, h2, ih2, Matrix.vecMul_vecMul]

private theorem cenV_beq {u w : Nat} {G : Matrix (Fin 133) (Fin 133) (ZMod 5)}
    (hu : CenPf.VCanon 5 133 13 u) (hw : CenPf.VCanon 5 133 13 w)
    (hwG : CenPf.toVec 5 133 13 w = CenPf.toVec 5 133 13 u ᵥ* G ᵥ* G) (hsq : G * G = 1) :
    Nat.beq w u = true := by
  have e : w = u := CenPf.vec_inj (by norm_num) hw hu
    (by rw [hwG, Matrix.vecMul_vecMul, hsq, Matrix.vecMul_one])
  rw [e]
  exact Nat.beq_refl u

private theorem elemV_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    {PC : Nat → Nat} {nb U v e tg : Nat} (hPC : ∀ i < nb, Canon 5 133 13 (PC i))
    (hU : CenPf.VCanon 5 133 13 U) (hv : CenPf.VCanon 5 133 13 v)
    (hvg : CenPf.toVec 5 133 13 v = CenPf.toVec 5 133 13 U ᵥ* nfE PC nb (fun i => e / 2 ^ i % 2))
    (h : elemV (vecR 5 13 1729 133 9 LV HV RM) PC nb U v e tg = true) :
    nfE PC nb (fun i => e / 2 ^ i % 2) * nfE PC nb (fun i => e / 2 ^ i % 2) ≠ 1 := by
  intro hsq
  obtain ⟨hw1, hw2⟩ := wordV_ok hc hv e nb hPC
  have hb := cenV_beq hU hw1 (by rw [hw2, hvg]) hsq
  unfold elemV at h
  rw [hb] at h
  have h' : letB (Nat.land (Nat.shiftRight tg 2) 255) (fun a =>
      andB (Nat.blt a 133) (notB (Nat.beq (wordV (vecR 5 13 1729 133 9 LV HV RM) PC
        (wordV (vecR 5 13 1729 133 9 LV HV RM) PC (unitV a) e nb) e nb) (unitV a)))) = true := h
  rw [CenPf.letB_eq] at h'
  generalize Nat.land (Nat.shiftRight tg 2) 255 = a at h'
  obtain ⟨ha, hn⟩ := CenPf.andT h'
  have ha' : a < 133 := Nat.le_of_ble_eq_true ha
  obtain ⟨hu1, -⟩ := CenPf.unit_spec (p := 5) (w := 13) (d := 133) (by norm_num) (by norm_num) ha'
  have hu1' : CenPf.VCanon 5 133 13 (unitV a) := hu1
  obtain ⟨hx1, hx2⟩ := wordV_ok hc hu1' e nb hPC
  obtain ⟨hy1, hy2⟩ := wordV_ok hc hx1 e nb hPC
  rw [cenV_beq hu1' hy1 (by rw [hy2, hx2]) hsq] at hn
  exact absurd hn (by simp [CFSG.KC.Ord.notB])

private theorem cenV_succ {vm : Nat → Nat → Nat} {PC TG : Nat → Nat} {nb U n k v idx : Nat}
    (h : cenV vm PC TG nb U (n + 1) k v idx = true) :
    cenV vm PC TG nb U n (k + 1) v idx = true ∧
      cenV vm PC TG nb U n (k + 1) (vm v (PC k)) (idx + 1 <<< k) = true := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (letB (vm v (PC k)) (fun v' => cenV vm PC TG nb U n (Nat.succ k) v'
        (Nat.add idx (Nat.shiftLeft (nat_lit 1) k))))
      (cenV vm PC TG nb U n (Nat.succ k) v idx) = true := h
  obtain ⟨h1, h2⟩ := CenPf.bAndT h'
  rw [CenPf.letB_eq] at h2
  exact ⟨h1, h2⟩

private theorem cenV_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    {PC TG : Nat → Nat} {nb U : Nat} (hPC : ∀ i < nb, Canon 5 133 13 (PC i))
    (hU : CenPf.VCanon 5 133 13 U) :
    ∀ n k v idx, k + n = nb → CenPf.VCanon 5 133 13 v →
      cenV (vecR 5 13 1729 133 9 LV HV RM) PC TG nb U n k v idx = true →
      ∀ e : Nat → Nat, (∀ i, e i < 2) →
        CenPf.toVec 5 133 13 v = CenPf.toVec 5 133 13 U ᵥ* nfE PC k e → idx < 2 ^ k →
        (∀ i < k, idx / 2 ^ i % 2 = e i) → nfE PC nb e * nfE PC nb e ≠ 1
  | 0, k, v, idx, hkn, hv, h, e, _, hvg, _, hbits => by
    rw [Nat.add_zero] at hkn
    subst hkn
    have hcg : nfE PC k e = nfE PC k (fun i => idx / 2 ^ i % 2) :=
      CenPf.nfE_congr PC k fun i hi => (hbits i hi).symm
    rw [hcg] at hvg ⊢
    exact elemV_ok hc hPC hU hv hvg h
  | n + 1, k, v, idx, hkn, hv, h, e, he, hvg, hidx, hbits => by
    obtain ⟨h1, h2⟩ := cenV_succ h
    have hkn' : k + 1 + n = nb := by omega
    rcases Nat.lt_or_ge (e k) 1 with hk | hk
    · have hk0 : e k = 0 := by omega
      refine cenV_ok hc hPC hU n (k + 1) v idx hkn' hv h1 e he ?_ ?_ ?_
      · rw [CenPf.nfE_succ, hk0, pow_zero, mul_one]
        exact hvg
      · rw [Nat.pow_succ]
        omega
      · intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
        · exact hbits i hlt
        · rw [Nat.div_eq_of_lt hidx, hk0]
    · have hk1 : e k = 1 := by have := he k; omega
      obtain ⟨hv', hvg'⟩ := cenV_vec hc hv (hPC k (by omega))
      refine cenV_ok hc hPC hU n (k + 1) _ (idx + 1 <<< k) hkn' hv' h2 e he ?_ ?_ ?_
      · rw [CenPf.nfE_succ, hk1, pow_one, hvg', hvg, Matrix.vecMul_vecMul]
      · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
        omega
      · intro i hi
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
        · rw [cenV_div_add (x := idx) hlt]
          exact hbits i hlt
        · rw [cenV_div_add_self hidx, hk1]

theorem cenVAt_sound {PC TG : Nat → Nat} {a0 m k n : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < k + n, Canon 5 133 13 (PC i)) (ha0 : a0 < 133) (hm : m < 2 ^ k)
    (h : cenVAt (vecR 5 13 1729 133 9 LV HV RM) PC TG a0 m k n = true) :
    ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < k, e i = m / 2 ^ i % 2) →
      nfE PC (k + n) e * nfE PC (k + n) e ≠ 1 := by
  intro e he hek
  have h' : cenV (vecR 5 13 1729 133 9 LV HV RM) PC TG (k + n) (unitV a0) n k
      (wordV (vecR 5 13 1729 133 9 LV HV RM) PC (unitV a0) m k) m = true := by
    unfold cenVAt at h
    rw [CenPf.letB_eq] at h
    exact h
  obtain ⟨hu1, -⟩ := CenPf.unit_spec (p := 5) (w := 13) (d := 133) (by norm_num) (by norm_num) ha0
  have hu1' : CenPf.VCanon 5 133 13 (unitV a0) := hu1
  obtain ⟨hv1, hv2⟩ := wordV_ok hc hu1' m k (fun i hi => hPC i (by omega))
  refine cenV_ok hc hPC hu1' n k _ m rfl hv1 h' e he ?_ hm (fun i hi => (hek i hi).symm)
  rw [hv2, CenPf.nfE_congr PC k fun i hi => (hek i hi).symm]

end CFSG.KS.HNLocal

end
