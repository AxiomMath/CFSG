module

public import Certificates.Data.Kernel.Spor.PEnumB
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Certificates.Data.Kernel.Spor.MulHQ
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.J2ModelsSound

public section

namespace CFSG.KS.PEnumB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem agreeC_iff (w m : Nat) (bs : List Nat) (X P Q : Nat) :
    agreeC w m bs X P Q = true ↔ ∀ b ∈ bs, pg w m X b = pg w m P (pg w m Q b) := by
  induction bs with
  | nil => simp [agreeC]
  | cons b bs ih =>
    change Bool.rec (motive := fun _ => Bool) false (agreeC w m bs X P Q)
      (Nat.beq (pg w m X b) (pg w m P (pg w m Q b))) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons, Nat.beq_eq]

theorem agreeC3_iff (w m : Nat) (bs : List Nat) (X A B C : Nat) :
    agreeC3 w m bs X A B C = true ↔ ∀ b ∈ bs, pg w m X b = pg w m A (pg w m B (pg w m C b)) := by
  induction bs with
  | nil => simp [agreeC3]
  | cons b bs ih =>
    change Bool.rec (motive := fun _ => Bool) false (agreeC3 w m bs X A B C)
      (Nat.beq (pg w m X b) (pg w m A (pg w m B (pg w m C b)))) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons, Nat.beq_eq]

structure BaseFaith (n w : Nat) (bs : List Nat) (M : Nat → Prop) : Prop where
  n_lt : n < 2 ^ 32
  bs_lt : ∀ b ∈ bs, b < n
  canon : ∀ X, M X → canonK n w (mask w) (n * w) X = true
  eq : ∀ X Y, M X → M Y → (∀ b ∈ bs, pg w (mask w) X b = pg w (mask w) Y b) → X = Y
  comp : ∀ X Y, M X → M Y → M (pcomp n w (mask w) X Y)
  id : M (pidn n w)

variable {n w : Nat} {bs : List Nat} {M : Nat → Prop}

theorem BaseFaith.eq_comp (hF : BaseFaith n w bs M) {X P Q : Nat} (hX : M X) (hP : M P) (hQ : M Q)
    (h : agreeC w (mask w) bs X P Q = true) : X = pcomp n w (mask w) P Q :=
  hF.eq _ _ hX (hF.comp _ _ hP hQ) fun b hb => by
    rw [(agreeC_iff _ _ _ _ _ _).1 h b hb, PF.pg_pcomp hF.n_lt (hF.bs_lt b hb)]

theorem BaseFaith.agreeC_comp (hF : BaseFaith n w bs M) (P Q : Nat) :
    agreeC w (mask w) bs (pcomp n w (mask w) P Q) P Q = true :=
  (agreeC_iff _ _ _ _ _ _).2 fun b hb => PF.pg_pcomp hF.n_lt (hF.bs_lt b hb)

theorem BaseFaith.agreeC_eq (hF : BaseFaith n w bs M) {X P Q : Nat} (hX : M X) (hP : M P)
    (hQ : M Q) :
    agreeC w (mask w) bs X P Q = Nat.beq X (pcomp n w (mask w) P Q) := by
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq]
  constructor
  · exact hF.eq_comp hX hP hQ
  · rintro rfl
    exact hF.agreeC_comp P Q

theorem BaseFaith.agreeC3_eq (hF : BaseFaith n w bs M) {X A B C : Nat} (hX : M X) (hA : M A)
    (hB : M B) (hC : M C) :
    agreeC3 w (mask w) bs X A B C = Nat.beq X (pcomp n w (mask w) (pcomp n w (mask w) A B) C) := by
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, agreeC3_iff]
  constructor
  · intro h
    refine hF.eq _ _ hX (hF.comp _ _ (hF.comp _ _ hA hB) hC) fun b hb => ?_
    have hb' := hF.bs_lt b hb
    rw [h b hb, PF.pg_pcomp hF.n_lt hb']
    have hc := (PF.canon_facts (hF.canon _ hC)).2.2.2 b hb'
    rw [PF.pg_pcomp hF.n_lt hc]
  · rintro rfl b hb
    have hb' := hF.bs_lt b hb
    rw [PF.pg_pcomp hF.n_lt hb']
    have hc := (PF.canon_facts (hF.canon _ hC)).2.2.2 b hb'
    rw [PF.pg_pcomp hF.n_lt hc]

theorem penumPtB_spec {m k cnt i : Nat} {GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtB n w m bs GI k cnt T PL POS SRT SRI i = true) :
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧ T i = pcomp n w m (T (parOf PL i)) (GI (labOf PL i))) ∧
    (∀ j < k, r32 POS (i * k + j) < cnt ∧ agreeC w m bs (T (r32 POS (i * k + j))) (T i) (GI j) = true) := by
  unfold penumPtB at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨ht, hpos, -⟩ := h
  refine ⟨fun hi => ?_, fun j hj => ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq] at ht
    exact ⟨ht.1, ht.2.1, Nat.eq_of_beq_eq_true ht.2.2.1⟩
  · have hq := CFSG.KS.Raw.Orb.allN_iff.1 hpos j hj
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Nat.mul_eq, Nat.add_eq,
      Bool.and_eq_true, Nat.blt_eq] at hq
    exact ⟨hq.1, hq.2.1⟩

theorem penumB_mem (hF : BaseFaith n w bs M) {k cnt cap : Nat} {GI T PL POS SRT SRI : Nat → Nat}
    (hGI : ∀ j < k, M (GI j)) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtB n w (mask w) bs GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, M (T i) := by
  have h0 : T 0 = pidn n w := by
    unfold penumHdK at hh
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hh
    exact Nat.eq_of_beq_eq_true hh.2.2.1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [h0]
      exact hF.id
    · obtain ⟨hp, hl, e⟩ := (penumPtB_spec (hb i hi)).1 hi0
      rw [e]
      exact hF.comp _ _ (ih _ hp (by omega)) (hGI _ hl)

theorem allN_congr {k : Nat} {f g : Nat → Bool} (h : ∀ j < k, f j = g j) : allN k f = allN k g := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.KS.Raw.Orb.allN_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact ⟨fun h' j hj => (h j hj) ▸ h' j hj, fun h' j hj => (h j hj).symm ▸ h' j hj⟩

theorem penumPtK_eq_B (hF : BaseFaith n w bs M) {k cnt i : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hT : ∀ x < cnt, M (T x)) (hGI : ∀ j < k, M (GI j)) (hG : ∀ j < k, G j = pidn n w)
    (hi : i < cnt) :
    penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i =
      penumPtB n w (mask w) bs GI k cnt T PL POS SRT SRI i := by
  unfold penumPtK penumPtB
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq]
  rw [hF.canon _ (hT i hi), Bool.true_and]
  congr 1
  · congr 1
    cases hp : Nat.blt (parOf PL i) i
    · simp
    · cases hl : Nat.blt (labOf PL i) k
      · simp
      · have hp' : parOf PL i < i := Nat.blt_eq.mp hp
        have hl' : labOf PL i < k := Nat.blt_eq.mp hl
        have e0 : stepK n w (mask w) true G GI (labOf PL i) (T (parOf PL i)) =
            pcomp n w (mask w) (pcomp n w (mask w) (G (labOf PL i)) (T (parOf PL i)))
              (GI (labOf PL i)) := rfl
        have e : stepK n w (mask w) true G GI (labOf PL i) (T (parOf PL i)) =
            pcomp n w (mask w) (T (parOf PL i)) (GI (labOf PL i)) := by
          rw [e0, hG _ hl', CFSG.KC.J2Models.pcomp_idL (hF.canon _ (hT _ (by omega)))]
        rw [e]
  · congr 1
    apply allN_congr
    intro j hj
    cases hq : Nat.blt (r32 POS (Nat.add (Nat.mul i k) j)) cnt
    · simp
    · have hq' := Nat.blt_eq.mp hq
      have e0 : stepK n w (mask w) true G GI j (T i) =
          pcomp n w (mask w) (pcomp n w (mask w) (G j) (T i)) (GI j) := rfl
      have e : stepK n w (mask w) true G GI j (T i) = pcomp n w (mask w) (T i) (GI j) := by
        rw [e0, hG _ hj, CFSG.KC.J2Models.pcomp_idL (hF.canon _ (hT i hi))]
      rw [e, hF.agreeC_eq (hT _ hq') (hT i hi) (hGI j hj)]

theorem penumPtK_of_B (hF : BaseFaith n w bs M) {k cnt cap : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} (hGI : ∀ j < k, M (GI j)) (hG : ∀ j < k, G j = pidn n w)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtB n w (mask w) bs GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true :=
  fun i hi => by
    rw [penumPtK_eq_B hF (penumB_mem hF hGI hh hb) hGI hG hi]
    exact hb i hi

theorem hsortPtK_of_V {m cnt : Nat} {T HV HS HSI : Nat → Nat}
    (hv : ∀ i < cnt, hvK n w m T HV i = true) (hs : ∀ i < cnt, hsortVK cnt HV HS HSI i = true) :
    ∀ i < cnt, hsortPtK n w m cnt T HS HSI i = true := by
  have hsl : ∀ i < cnt, r32 HS i < cnt := fun i hi => by
    have h := hs i hi
    unfold hsortVK at h
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
      Nat.blt_eq] at h
    exact h.1
  have he : ∀ s < cnt, hkeyK n w m (T s) = HV s := fun s hs' => by
    have h := hv s hs'
    unfold hvK at h
    exact Nat.eq_of_beq_eq_true h
  intro i hi
  have h := hs i hi
  unfold hsortVK at h
  unfold hsortPtK
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at h ⊢
  rw [he _ (hsl i hi)]
  by_cases h1 : i + 1 < cnt
  · rw [he _ (hsl _ h1)]
    exact h
  · have e : Nat.blt (Nat.succ i) cnt = false := by
      cases e : Nat.blt (Nat.succ i) cnt
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h1
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bIf_eq, e] at h ⊢
    simpa using h

theorem div_lt_of {c cnt K : Nat} (hc : c < cnt * K) : c / K < cnt := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      simp at hc
    · exact h
  exact (Nat.div_lt_iff_lt_mul hK).2 hc

theorem mod_lt_of {c cnt K : Nat} (hc : c < cnt * K) : c % K < K := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      simp at hc
    · exact h
  exact Nat.mod_lt c hK

theorem findPtK_prod_of_B (hF : BaseFaith n w bs M) {cnt K c : Nat} {T S POS : Nat → Nat}
    (hT : ∀ x < cnt, M (T x)) (hS : ∀ j < K, M (S j)) (hc : c < cnt * K)
    (h : findProdB cnt w (mask w) bs K T S POS c = true) :
    findPtK cnt T (prodQK n w (mask w) K T S) POS c = true := by
  unfold findProdB at h
  unfold findPtK prodQK
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h ⊢
  obtain ⟨hq, ha⟩ := h
  refine ⟨hq, ?_⟩
  have hq' := Nat.blt_eq.mp hq
  rw [← hF.agreeC_eq (hT _ hq') (hT (Nat.div c K) (div_lt_of hc)) (hS (Nat.mod c K) (mod_lt_of hc))]
  exact ha

theorem findPtK_conj_of_B (hF : BaseFaith n w bs M) {cnt K c : Nat} {T C CI POS : Nat → Nat}
    (hT : ∀ x < cnt, M (T x)) (hC : ∀ j < K, M (C j)) (hCI : ∀ j < K, M (CI j)) (hc : c < cnt * K)
    (h : findConjB cnt w (mask w) bs K T C CI POS c = true) :
    findPtK cnt T (conjQK n w (mask w) K T C CI) POS c = true := by
  unfold findConjB at h
  unfold findPtK conjQK
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h ⊢
  obtain ⟨hq, ha⟩ := h
  refine ⟨hq, ?_⟩
  have hq' := Nat.blt_eq.mp hq
  rw [← hF.agreeC3_eq (hT _ hq') (hC (Nat.mod c K) (mod_lt_of hc)) (hT (Nat.div c K) (div_lt_of hc))
    (hCI (Nat.mod c K) (mod_lt_of hc))]
  exact ha

end CFSG.KS.PEnumB

end
