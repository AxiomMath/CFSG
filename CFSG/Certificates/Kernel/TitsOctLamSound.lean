module

public import Certificates.Data.Kernel.TitsOctLamK
public import CFSG.Certificates.Kernel.TitsOctSound
public import CFSG.Certificates.Kernel.SporCov.BaseFix

public section

namespace CFSG.KC.TitsOctLamSound

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsOctLamK
  CFSG.KC.TwoF4LieSound CFSG.KC.TitsOctSound

variable {lp : ℕ → ℕ}

theorem midL_iff {LAY x : ℕ} : midL LAY x = true ↔ 0 < layAt LAY x ∧ layAt LAY x < 8 := by
  unfold midL
  rw [bAnd_eq', blt_d, blt_d]
  simp

theorem layCnt_eq (LAY c : ℕ) :
    layCnt LAY c = ((Finset.range 1755).filter (fun x => layAt LAY x = c)).card := by
  rw [Finset.card_filter, layCnt, CFSG.KD.SporCov.sumBelow_specF _ (by norm_num)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [nIf_d, beq_d]
  simp

theorem lamCnt_eq (L0 LJ : ℕ) :
    lamCnt L0 LJ = ((Finset.range 1755).filter
      (fun x => layAt L0 x = 8 ∧ 0 < layAt LJ x ∧ layAt LJ x < 8)).card := by
  rw [Finset.card_filter, lamCnt, CFSG.KD.SporCov.sumBelow_specF _ (by norm_num)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [nIf_d, bAnd_eq', beq_d]
  by_cases h : layAt L0 x = 8 <;> by_cases h' : midL LJ x = true <;> simp_all [midL_iff]

theorem recPK_sound {A : ℕ → ℕ} {k root cnt LAY l ORD PR LB PS : ℕ}
    (h : recPK A k root cnt LAY l ORD PR LB PS = true) :
    fw 13 ORD 0 = root ∧ root < 1755 ∧
    (∀ i < cnt, fw 13 ORD i < 1755 ∧ (i ≠ 0 → fw 11 PR i < i ∧ fw 3 LB i < k ∧
      gp (A (fw 3 LB i)) (fw 13 ORD (fw 11 PR i)) = fw 13 ORD i)) ∧
    ∀ x < 1755, layAt LAY x = l → fw 13 PS x < cnt ∧ fw 13 ORD (fw 13 PS x) = x := by
  unfold recPK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  obtain ⟨h0, hr, hst, hcov⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, by simpa [blt_d] using hr, fun i hi => ?_,
    fun x hx hl => ?_⟩
  · have hi' := hst i hi
    by_cases hi0 : i = 0
    · simp only [bIf_d, blt_d, beq_d, hi0, decide_true, if_true, Bool.and_true,
        decide_eq_true_eq] at hi'
      rw [hi0]
      exact ⟨hi'.1, fun h => absurd rfl h⟩
    · simp only [bIf_d, bAnd_eq', blt_d, beq_d, hi0, decide_false, Bool.false_eq_true, if_false,
        Bool.and_eq_true, decide_eq_true_eq] at hi'
      exact ⟨hi'.1, fun _ => hi'.2⟩
  · have hx' := hcov x hx
    simp only [bIf_d, bAnd_eq', blt_d, beq_d, hl, decide_true, if_true, Bool.and_eq_true,
      decide_eq_true_eq] at hx'
    exact hx'

theorem recP_reach {X V : Type*} [Group X] [MulAction X V] {c : ℕ → V} {a : ℕ → X} {S : Set X}
    {A : ℕ → ℕ} {k root cnt LAY l ORD PR LB PS : ℕ} (ha : ∀ j < k, a j ∈ S)
    (hact : ∀ j < k, ∀ y < 1755, a j • c y = c (gp (A j) y))
    (h : recPK A k root cnt LAY l ORD PR LB PS = true) :
    ∀ x < 1755, layAt LAY x = l → ∃ g ∈ Subgroup.closure S, g • c root = c x := by
  obtain ⟨h0, -, hst, hcov⟩ := recPK_sound h
  have key : ∀ i < cnt, ∃ g ∈ Subgroup.closure S, g • c root = c (fw 13 ORD i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        exact ⟨1, Subgroup.one_mem _, by rw [one_smul, h0]⟩
      · obtain ⟨hpi, hlb, hav⟩ := (hst i hi).2 hi0
        obtain ⟨g, hg, e⟩ := ih _ hpi (by omega)
        refine ⟨a (fw 3 LB i) * g,
          Subgroup.mul_mem _ (Subgroup.subset_closure (ha _ hlb)) hg, ?_⟩
        rw [mul_smul, e, hact _ hlb _ (hst _ (by omega)).1, hav]
  intro x hx hl
  obtain ⟨hq, e⟩ := hcov x hx hl
  obtain ⟨g, hg, e'⟩ := key _ hq
  exact ⟨g, hg, by rw [e', e]⟩

theorem cmpK_sound {L0 LX LY : ℕ} (h : cmpK L0 LX LY = true) :
    ∀ c < 1755, layAt L0 c = 8 → (midL LY c = true ↔ midL LX c = false) := by
  intro c hc h8
  unfold cmpK at h
  have hc' := allN_iff'.1 h c hc
  clear h
  simp only [bIf_d, beq_d, h8, decide_true, if_true] at hc'
  cases hY : midL LY c <;> cases hX : midL LX c <;> simp_all

theorem walkK_sound {L0 LX : ℕ} {P : List ℕ} (h : walkK lp L0 LX P = true) :
    0 < P.length ∧ P.length ≤ 8 ∧ (∀ i, i + 1 < P.length →
      adjK lp (P.getD i 0) (P.getD (i + 1) 0) = true) ∧
    P.getLastD 0 < 1755 ∧ layAt L0 (P.getLastD 0) = 8 ∧ midL LX (P.getLastD 0) = true := by
  have key : ∀ Q : List ℕ, adjP lp Q = true → ∀ i, i + 1 < Q.length →
      adjK lp (Q.getD i 0) (Q.getD (i + 1) 0) = true := by
    intro Q
    induction Q with
    | nil => intro _ i hi; simp at hi
    | cons a t ih =>
      intro hQ i hi
      change bAnd(List.rec (motive := fun _ => Bool) true (fun b _ _ => adjK lp a b) t,
        adjP lp t) = true at hQ
      rw [bAnd_eq', Bool.and_eq_true] at hQ
      cases i with
      | zero =>
        cases t with
        | nil => simp at hi
        | cons b t' => simpa using hQ.1
      | succ i => simpa using ih hQ.2 i (by simpa using hi)
  unfold walkK at h
  simp only [bAnd_eq', Bool.and_eq_true, strictB_eq', blt_d, ble_d, beq_d,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, key P h3, h4, h5, h6⟩

theorem starts_sound {L0 xp : ℕ} {W : List (List ℕ)} (h : starts L0 xp W = true) :
    ∀ y < 1755, layAt L0 y = 2 → y ≠ xp → ∃ P ∈ W, P.headD 0 = y := by
  intro y hy h2 hne
  unfold starts at h
  have hW := allN_iff'.1 h y hy
  clear h
  simp only [bIf_d, beq_d, h2, hne, decide_true, decide_false, Bool.false_eq_true, if_true,
    if_false] at hW
  induction W with
  | nil => simp at hW
  | cons P W ih =>
    by_cases hP : P.headD 0 = y
    · exact ⟨P, List.mem_cons_self, hP⟩
    · have hP' : ¬ P.head?.getD 0 = y := by simpa using hP
      obtain ⟨Q, hQ, e⟩ := ih (by simpa [hP'] using hW)
      exact ⟨Q, List.mem_cons_of_mem _ hQ, e⟩

end CFSG.KC.TitsOctLamSound

end
