module

public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.HNLocal.Cen
import all CFSG.Certificates.Kernel.HNLocal.CenV

public section

namespace CFSG.KS.HNLocal

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord Matrix

variable {L H CM RM ONE LV HV : Nat}

private theorem memND_sound {e : Nat} : ∀ {D : List Nat}, memND e D = true → e ∈ D
  | [], h => absurd h (by simp [memND])
  | d :: D, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memND e D) true (Nat.beq e d) = true := h
    cases hb : Nat.beq e d
    · rw [hb] at h'
      exact List.mem_cons_of_mem _ (memND_sound h')
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

private theorem cenVD_succ {vm : Nat → Nat → Nat} {PC TG : Nat → Nat} {D : List Nat}
    {nb U n k v idx : Nat} (h : cenVD vm PC TG D nb U (n + 1) k v idx = true) :
    cenVD vm PC TG D nb U n (k + 1) v idx = true ∧
      cenVD vm PC TG D nb U n (k + 1) (vm v (PC k)) (idx + 1 <<< k) = true := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (letB (vm v (PC k)) (fun v' => cenVD vm PC TG D nb U n (Nat.succ k) v'
        (Nat.add idx (Nat.shiftLeft (nat_lit 1) k))))
      (cenVD vm PC TG D nb U n (Nat.succ k) v idx) = true := h
  obtain ⟨h1, h2⟩ := CenPf.bAndT h'
  rw [CenPf.letB_eq] at h2
  exact ⟨h1, h2⟩

private theorem cenVD_ok (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    {PC TG : Nat → Nat} {D : List Nat} {nb U : Nat} (hPC : ∀ i < nb, Canon 5 133 13 (PC i))
    (hU : CenPf.VCanon 5 133 13 U) :
    ∀ n k v idx, k + n = nb → CenPf.VCanon 5 133 13 v →
      cenVD (vecR 5 13 1729 133 9 LV HV RM) PC TG D nb U n k v idx = true →
      ∀ e : Nat → Nat, (∀ i, e i < 2) →
        CenPf.toVec 5 133 13 v = CenPf.toVec 5 133 13 U ᵥ* nfE PC k e → idx < 2 ^ k →
        (∀ i < k, idx / 2 ^ i % 2 = e i) →
        nfE PC nb e * nfE PC nb e ≠ 1 ∨ ∃ d ∈ D, ∀ i < nb, e i = d / 2 ^ i % 2
  | 0, k, v, idx, hkn, hv, h, e, _, hvg, _, hbits => by
    rw [Nat.add_zero] at hkn
    subst hkn
    have h' : Bool.rec (motive := fun _ => Bool)
        (elemV (vecR 5 13 1729 133 9 LV HV RM) PC k U v idx (TG idx)) true (memND idx D) = true := h
    cases hm : memND idx D
    · rw [hm] at h'
      have hcg : nfE PC k e = nfE PC k (fun i => idx / 2 ^ i % 2) :=
        CenPf.nfE_congr PC k fun i hi => (hbits i hi).symm
      rw [hcg] at hvg ⊢
      exact Or.inl (elemV_ok hc hPC hU hv hvg h')
    · exact Or.inr ⟨idx, memND_sound hm, fun i hi => (hbits i hi).symm⟩
  | n + 1, k, v, idx, hkn, hv, h, e, he, hvg, hidx, hbits => by
    obtain ⟨h1, h2⟩ := cenVD_succ h
    have hkn' : k + 1 + n = nb := by omega
    rcases Nat.lt_or_ge (e k) 1 with hk | hk
    · have hk0 : e k = 0 := by omega
      refine cenVD_ok hc hPC hU n (k + 1) v idx hkn' hv h1 e he ?_ ?_ ?_
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
      refine cenVD_ok hc hPC hU n (k + 1) _ (idx + 1 <<< k) hkn' hv' h2 e he ?_ ?_ ?_
      · rw [CenPf.nfE_succ, hk1, pow_one, hvg', hvg, Matrix.vecMul_vecMul]
      · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
        omega
      · intro i hi
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
        · rw [cenV_div_add (x := idx) hlt]
          exact hbits i hlt
        · rw [cenV_div_add_self hidx, hk1]

theorem cenVDAt_sound {PC TG : Nat → Nat} {D : List Nat} {a0 m k n : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < k + n, Canon 5 133 13 (PC i)) (ha0 : a0 < 133) (hm : m < 2 ^ k)
    (h : cenVDAt (vecR 5 13 1729 133 9 LV HV RM) PC TG D a0 m k n = true) :
    ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < k, e i = m / 2 ^ i % 2) →
      nfE PC (k + n) e * nfE PC (k + n) e ≠ 1 ∨
        ∃ d ∈ D, ∀ i < k + n, e i = d / 2 ^ i % 2 := by
  intro e he hek
  have h' : cenVD (vecR 5 13 1729 133 9 LV HV RM) PC TG D (k + n) (unitV a0) n k
      (wordV (vecR 5 13 1729 133 9 LV HV RM) PC (unitV a0) m k) m = true := by
    unfold cenVDAt at h
    rw [CenPf.letB_eq] at h
    exact h
  obtain ⟨hu1, -⟩ := CenPf.unit_spec (p := 5) (w := 13) (d := 133) (by norm_num) (by norm_num) ha0
  have hu1' : CenPf.VCanon 5 133 13 (unitV a0) := hu1
  obtain ⟨hv1, hv2⟩ := wordV_ok hc hu1' m k (fun i hi => hPC i (by omega))
  refine cenVD_ok hc hPC hu1' n k _ m rfl hv1 h' e he ?_ hm (fun i hi => (hek i hi).symm)
  rw [hv2, CenPf.nfE_congr PC k fun i hi => (hek i hi).symm]

theorem cenDL_sound {PC RP TG : Nat → Nat} {np k : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < k, Canon 5 133 13 (PC i)) (hRP : ∀ a < np, Canon 5 133 13 (RP a)) :
    ∀ {D : List Nat},
      cenDL (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np ONE RM k D
        = true →
      ∀ d ∈ D, ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < k, e i = d / 2 ^ i % 2) →
        nfE PC k e = 1 ∨ nfE PC k e * nfE PC k e ≠ 1 ∨
          ∃ a < np, ∃ q, q % 2 = 1 ∧ (nfE PC k e * OM (RP a)) ^ q = 1
  | [], _, d, hd => absurd hd List.not_mem_nil
  | d0 :: D, h, d, hd => by
    have h' : bAnd(Nat.blt d0 (Nat.shiftLeft 1 k),
        bAnd(cenAt (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np
          ONE RM d0 k 0,
          cenDL (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np ONE RM
            k D)) = true := h
    obtain ⟨hlt, h'⟩ := CenPf.bAndT h'
    obtain ⟨hcen, hrest⟩ := CenPf.bAndT h'
    rcases List.mem_cons.1 hd with rfl | hd
    · have hlt' : d < 2 ^ k := by
        have h1 : d.succ ≤ 1 <<< k := Nat.le_of_ble_eq_true hlt
        rw [Nat.shiftLeft_eq, Nat.one_mul] at h1
        exact h1
      exact CenPf.cenAt_sound' (n := 0) hc hPC hRP hlt' hcen
    · exact cenDL_sound hc hPC hRP hrest d hd

end CFSG.KS.HNLocal

end
