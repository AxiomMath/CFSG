module

public import Certificates.Data.Kernel.Spor.MulHQI
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.J2ModelsSound

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

variable {n w k K nc cnt : Nat} {T S C CI PL CL NP : Nat → Nat}

theorem strictN_eq' (y : Nat) (f : Nat → Nat) : strictN y f = f y := by
  cases y <;> rfl
theorem pc_assoc {p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := CFSG.KS.PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0)
    (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 (hrr i hi),
    CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 hi]

theorem conj_mul {c ci a b : Nat} (hc : canonK n w (mask w) (n * w) c = true)
    (hci : canonK n w (mask w) (n * w) ci = true) (hinv : invEqK n w (mask w) (n * w) c ci = true)
    (hb : canonK n w (mask w) (n * w) b = true) :
    pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) c a) ci)
        (pcomp n w (mask w) (pcomp n w (mask w) c b) ci) =
      pcomp n w (mask w) (pcomp n w (mask w) c (pcomp n w (mask w) a b)) ci := by
  obtain ⟨hn, hw, -, -⟩ := CFSG.KS.PF.canon_facts hc
  obtain ⟨-, -, -, hcr⟩ := CFSG.KS.PF.canon_facts hc
  obtain ⟨-, -, -, hcir⟩ := CFSG.KS.PF.canon_facts hci
  obtain ⟨-, -, -, hbr⟩ := CFSG.KS.PF.canon_facts hb
  obtain ⟨-, -, f⟩ := CFSG.KS.Raw.Orb.permOK_facts hinv
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0)
    (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  have h1 := hcir i hi
  have h2 := hbr _ h1
  have h3 := hcr _ h2
  rw [CFSG.KS.PF.pg_pcomp (p := pcomp n w (mask w) (pcomp n w (mask w) c a) ci) hn32 hi,
    CFSG.KS.PF.pg_pcomp (p := pcomp n w (mask w) c b) (q := ci) hn32 hi,
    CFSG.KS.PF.pg_pcomp (p := c) (q := b) hn32 h1,
    CFSG.KS.PF.pg_pcomp (p := pcomp n w (mask w) c a) (q := ci) hn32 h3,
    (f _ h2).2,
    CFSG.KS.PF.pg_pcomp (p := c) (q := a) hn32 h2,
    CFSG.KS.PF.pg_pcomp (p := pcomp n w (mask w) c (pcomp n w (mask w) a b)) (q := ci) hn32 hi,
    CFSG.KS.PF.pg_pcomp (p := c) (q := pcomp n w (mask w) a b) hn32 h1,
    CFSG.KS.PF.pg_pcomp (p := a) (q := b) hn32 h1]

theorem walk_spec (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hS : ∀ l < k, canonK n w (mask w) (n * w) (S l) = true) (hT0 : T 0 = pidn n w)
    (hcl : ∀ x < cnt, ∀ l < k, r32 CL (x * K + l) < cnt ∧
      T (r32 CL (x * K + l)) = pcomp n w (mask w) (T x) (S l))
    (hpar : ∀ i < cnt, i ≠ 0 →
      parOf PL i < i ∧ labOf PL i < k ∧ r32 CL (parOf PL i * K + labOf PL i) = i) :
    ∀ f a b, a < cnt → b < cnt → walkK K cnt PL CL f a b < cnt →
      T (walkK K cnt PL CL f a b) = pcomp n w (mask w) (T a) (T b) := by
  intro f
  induction f with
  | zero =>
    intro a b _ _ h
    exact absurd h (Nat.lt_irrefl cnt)
  | succ f ih =>
    intro a b ha hb h
    by_cases hb0 : b = 0
    · subst hb0
      have e : walkK K cnt PL CL (f + 1) a 0 = a := rfl
      rw [e, hT0, CFSG.KC.J2Models.pcomp_idR (hT a ha)]
    · obtain ⟨hp, hl, e3⟩ := hpar b hb hb0
      have hbz : Nat.beq b 0 = false := by
        cases e' : Nat.beq b 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e') hb0
      have e : walkK K cnt PL CL (f + 1) a b = strictN (walkK K cnt PL CL f a (parOf PL b))
          (fun a' => nIf(Nat.blt a' cnt, r32 CL (Nat.add (Nat.mul a' K) (labOf PL b)), cnt)) := by
        have e0 : walkK K cnt PL CL (f + 1) a b = nIf(Nat.beq b 0, a,
            strictN (walkK K cnt PL CL f a (parOf PL b))
              (fun a' => nIf(Nat.blt a' cnt, r32 CL (Nat.add (Nat.mul a' K) (labOf PL b)), cnt))) :=
          rfl
        rw [e0, hbz]
      have IH := ih a (parOf PL b) ha (by omega)
      rw [e, strictN_eq'] at h ⊢
      generalize walkK K cnt PL CL f a (parOf PL b) = a' at h IH ⊢
      cases hab : Nat.blt a' cnt
      · rw [hab] at h
        exact absurd h (Nat.lt_irrefl cnt)
      · have ha' : a' < cnt := Nat.blt_eq.mp hab
        change T (r32 CL (a' * K + labOf PL b)) = _
        have hTb := (hcl _ (Nat.lt_trans hp hb) _ hl).2
        rw [e3] at hTb
        rw [(hcl a' ha' _ hl).2, IH ha', hTb, pc_assoc (hT a ha) (hS _ hl)]

theorem findPt_of_nq (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hS : ∀ l < k, canonK n w (mask w) (n * w) (S l) = true) (hT0 : T 0 = pidn n w)
    (hcl : ∀ x < cnt, ∀ l < k, r32 CL (x * K + l) < cnt ∧
      T (r32 CL (x * K + l)) = pcomp n w (mask w) (T x) (S l))
    (hpar : ∀ i < cnt, i ≠ 0 →
      parOf PL i < i ∧ labOf PL i < k ∧ r32 CL (parOf PL i * K + labOf PL i) = i)
    (hC : ∀ j < nc, canonK n w (mask w) (n * w) (C j) = true ∧
      canonK n w (mask w) (n * w) (CI j) = true ∧ invEqK n w (mask w) (n * w) (C j) (CI j) = true)
    (h0 : ∀ j < nc, findPtK cnt T (conjQK n w (mask w) nc T C CI) NP j = true)
    (hG : nqGK n w (mask w) k nc cnt T S C CI CL NP = true)
    (hW : ∀ i < cnt, nqWK K nc cnt PL CL NP i = true) :
    ∀ c < cnt * nc, findPtK cnt T (conjQK n w (mask w) nc T C CI) NP c = true := by
  have fpt : ∀ c, findPtK cnt T (conjQK n w (mask w) nc T C CI) NP c = true ↔
      r32 NP c < cnt ∧ T (r32 NP c) = conjQK n w (mask w) nc T C CI c := by
    intro c
    unfold findPtK
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq]
    exact ⟨fun h => ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩, fun h => ⟨h.1, by rw [h.2]; exact Nat.beq_refl _⟩⟩
  have cq : ∀ i j, j < nc → conjQK n w (mask w) nc T C CI (i * nc + j) =
      pcomp n w (mask w) (pcomp n w (mask w) (C j) (T i)) (CI j) := by
    intro i j hj
    have hnc : 0 < nc := by omega
    have hd : (i * nc + j) / nc = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnc, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hm : (i * nc + j) % nc = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    change pcomp n w (mask w) (pcomp n w (mask w) (C ((i * nc + j) % nc)) (T ((i * nc + j) / nc)))
      (CI ((i * nc + j) % nc)) = _
    rw [hd, hm]
  have hGs : ∀ l < k, ∀ j < nc, r32 NP (r32 CL l * nc + j) < cnt ∧
      T (r32 NP (r32 CL l * nc + j)) = pcomp n w (mask w) (pcomp n w (mask w) (C j) (S l)) (CI j) := by
    intro l hl j hj
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hG l hl) j hj
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
    exact ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2⟩
  have key : ∀ i < cnt, ∀ j < nc, r32 NP (i * nc + j) < cnt ∧
      T (r32 NP (i * nc + j)) = pcomp n w (mask w) (pcomp n w (mask w) (C j) (T i)) (CI j) := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro hi j hj
      by_cases hi0 : i = 0
      · subst hi0
        have e : 0 * nc + j = j := by rw [Nat.zero_mul, Nat.zero_add]
        obtain ⟨h1, h2⟩ := (fpt j).1 (h0 j hj)
        rw [e]
        refine ⟨h1, ?_⟩
        rw [h2, ← cq 0 j hj, e]
      · obtain ⟨hp, hl, e3⟩ := hpar i hi hi0
        have hiz : Nat.beq i 0 = false := by
          cases e' : Nat.beq i 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e') hi0
        have hw1 := hW i hi
        unfold nqWK at hw1
        rw [hiz] at hw1
        change strictB (parOf PL i) _ = true at hw1
        rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq,
          CFSG.KS.Raw.Orb.allN_iff] at hw1
        have hw2 := hw1 j hj
        rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hw2
        obtain ⟨hv, hveq⟩ := hw2
        have hv' : r32 NP (i * nc + j) < cnt := Nat.blt_eq.mp hv
        have hveq' : r32 NP (i * nc + j) = walkK K cnt PL CL cnt (r32 NP (parOf PL i * nc + j))
            (r32 NP (r32 CL (labOf PL i) * nc + j)) := Nat.eq_of_beq_eq_true hveq
        obtain ⟨hpa, hpb⟩ := ih _ hp (Nat.lt_trans hp hi) j hj
        obtain ⟨hga, hgb⟩ := hGs _ hl j hj
        refine ⟨hv', ?_⟩
        have hw := walk_spec hT hS hT0 hcl hpar cnt _ _ hpa hga (by rw [← hveq']; exact hv')
        have hTi := (hcl _ (Nat.lt_trans hp hi) _ hl).2
        rw [e3] at hTi
        rw [hveq', hw, hpb, hgb, conj_mul (hC j hj).1 (hC j hj).2.1 (hC j hj).2.2 (hS _ hl), hTi]
  intro c hc
  have hnc : 0 < nc := by
    rcases Nat.eq_zero_or_pos nc with h0' | h0'
    · subst h0'
      rw [Nat.mul_zero] at hc
      exact absurd hc (Nat.not_lt_zero _)
    · exact h0'
  have hc' : c / nc < cnt := (Nat.div_lt_iff_lt_mul hnc).2 hc
  have e : c / nc * nc + c % nc = c := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod c nc
  obtain ⟨h1, h2⟩ := key (c / nc) hc' (c % nc) (Nat.mod_lt c hnc)
  rw [e] at h1 h2
  refine (fpt c).2 ⟨h1, ?_⟩
  rw [h2, ← cq (c / nc) (c % nc) (Nat.mod_lt c hnc), e]

end CFSG.KS.MulH

end
