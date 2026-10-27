module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenFin
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenAbs
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.SolMax.SwapP2.ExactAbs Subgroup

open scoped commutatorElement

namespace ChainData

variable (n : ℕ)

theorem rep_gs {cd : ChainData} (h : cd.check n = true) {i : ℕ} (hi : i < cd.S.size) :
    Rep n cd.S[i]! (cd.gs n i) := ((cd.check_sound n h).1 i hi).1

theorem rep_inv_gs {cd : ChainData} (h : cd.check n = true) {i : ℕ} (hi : i < cd.S.size) :
    Rep n (rawInvs n cd.S)[i]! (cd.gs n i)⁻¹ := ((cd.check_sound n h).1 i hi).2

theorem k_le_size {cd : ChainData} (h : cd.check n = true) : cd.k ≤ cd.S.size := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

theorem n_pos {cd : ChainData} (h : cd.check n = true) : 1 ≤ n := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

@[expose] def origsOK (H amb : ChainData) (ws : List (List ℤ)) : Bool :=
  decide (ws.length = H.k) && (List.range H.k).all fun i =>
    lettersOK amb.S.size ws[i]! && eqA n H.S[i]! (amb.wordArr n ws[i]!)

theorem origsOK_eq {H amb : ChainData} {ws : List (List ℤ)} (hH : H.check n = true)
    (ha : amb.check n = true) (h : origsOK n H amb ws = true) :
    ∀ i < H.k, H.gs n i = amb.val n ws[i]! ∧ lettersOK amb.S.size ws[i]! = true := by
  simp only [origsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, h⟩ := h
  intro i hi
  obtain ⟨hl, he⟩ := h i hi
  refine ⟨?_, hl⟩
  exact (eqA_iff (rep_gs n hH (hi.trans_le (k_le_size n hH))) (amb.rep_wordArr n ha hl)).1 he

theorem sub_le_of_origsOK {H amb : ChainData} {ws : List (List ℤ)} (hH : H.check n = true)
    (ha : amb.check n = true) (h : origsOK n H amb ws = true) : H.sub n ≤ amb.sub n := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, hi, rfl⟩
  have := origsOK_eq n hH ha h i hi
  change H.gs n i ∈ amb.sub n
  rw [this.1]
  exact amb.val_mem_sub n ha _

end ChainData


structure Ctx where
  chP : ChainData
  chN : ChainData
  normW : List (List ℤ)
  transW : List (List ℤ)
  stabLetters : List ℕ
  deriving Inhabited

namespace Ctx

variable (n : ℕ) (c : Ctx)

@[expose] def b0 : ℕ := c.chP.base[0]!

@[expose] def ok : Bool :=
  c.chP.check n && c.chN.check n && decide (c.chP.k ≤ c.chN.k) && decide (0 < c.chP.base.length) &&
    (List.range c.chP.k).all (fun i => c.chN.S[i]! == c.chP.S[i]!) &&
    (List.range (c.chN.k - c.chP.k)).all (fun a => (List.range c.chP.k).all (fun p =>
      lettersOK c.chP.S.size c.normW[a * c.chP.k + p]! &&
      eqA n (conjArr n c.chN.S[c.chP.k + a]! (rawInvs n c.chN.S)[c.chP.k + a]! c.chP.S[p]!)
        (c.chP.wordArr n c.normW[a * c.chP.k + p]!))) &&
    decide (c.transW.length = n) &&
    (List.range n).all (fun ω => lettersOK c.chP.S.size c.transW[ω]! &&
      (c.chP.wordArr n c.transW[ω]!)[c.b0]! == ω) &&
    c.stabLetters.all (fun j => decide (0 < j) && decide (j ≤ c.chP.S.size) &&
      (c.chP.S[j - 1]!)[c.b0]! == c.b0) &&
    (List.range n).all (fun ω => ω == c.b0 ||
      c.stabLetters.any (fun j => (c.chP.S[j - 1]!)[ω]! != ω)) &&
    decide (c.b0 < n)


end Ctx

theorem eq_one_of_commute_transitive {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} (b : Fin n)
    (hT : ∀ ω, ∃ p ∈ P, p b = ω) (hF : ∀ ω, ω ≠ b → ∃ v ∈ P, v b = b ∧ v ω ≠ ω)
    {x : Equiv.Perm (Fin n)} (hx : ∀ p ∈ P, x * p = p * x) : x = 1 := by
  have hxb : x b = b := by
    by_contra hne
    obtain ⟨v, hv, hvb, hvω⟩ := hF (x b) hne
    apply hvω
    have := congrArg (fun f : Equiv.Perm (Fin n) => f b) (hx v hv)
    simp only [Equiv.Perm.mul_apply, hvb] at this
    exact this.symm
  refine Equiv.ext fun ω => ?_
  obtain ⟨p, hp, rfl⟩ := hT ω
  have := congrArg (fun f : Equiv.Perm (Fin n) => f b) (hx p hp)
  simp only [Equiv.Perm.mul_apply, hxb] at this
  simpa using this

namespace Ctx

variable (n : ℕ) (c : Ctx)

theorem sound (h : c.ok n = true) :
    c.chP.check n = true ∧ c.chN.check n = true ∧
    c.chP.sub n ≤ c.chN.sub n ∧
    (∀ μ ∈ c.chN.sub n, ∀ x, x ∈ c.chP.sub n ↔ μ * x * μ⁻¹ ∈ c.chP.sub n) ∧
    (∀ x ∈ c.chN.sub n, (∀ p ∈ c.chP.sub n, x * p = p * x) → x = 1) ∧
    Nat.card (c.chP.sub n) = c.chP.order n ∧ Nat.card (c.chN.sub n) = c.chN.order n := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, hN⟩, hkk⟩, hbl⟩, horig⟩, hnormW⟩, htl⟩, htrans⟩, hstab1⟩, hstab2⟩, hb0⟩ := h
  have hPs := c.chP.check_sound n hP
  have hNs := c.chN.check_sound n hN
  have hkP := ChainData.k_le_size n hP
  have hkN := ChainData.k_le_size n hN
  have hoeq : ∀ i < c.chP.k, c.chN.gs n i = c.chP.gs n i := by
    intro i hi
    have := horig i hi
    unfold ChainData.gs
    rw [this]
  have hPN : c.chP.sub n ≤ c.chN.sub n := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, hi, rfl⟩
    have : c.chP.gs n i = c.chN.gs n i := (hoeq i hi).symm
    change c.chP.gs n i ∈ c.chN.sub n
    rw [this]
    exact Subgroup.subset_closure ⟨i, hi.trans_le hkk, rfl⟩
  have hnorm : ∀ μ ∈ c.chN.sub n, ∀ x, x ∈ c.chP.sub n ↔ μ * x * μ⁻¹ ∈ c.chP.sub n := by
    refine normalizes_of_gens (Γ := Equiv.Perm (Fin n)) (P := c.chP.sub n) (N := c.chN.sub n)
      (ng := {g | ∃ i < c.chN.k, g = permOfArr n c.chN.S[i]!})
      (pg := {g | ∃ i < c.chP.k, g = permOfArr n c.chP.S[i]!}) rfl rfl ?_
    rintro g ⟨i, hi, rfl⟩ q ⟨j, hj, rfl⟩
    have hjP : c.chP.gs n j ∈ c.chP.sub n := Subgroup.subset_closure ⟨j, hj, rfl⟩
    by_cases hiP : i < c.chP.k
    · have hgi : c.chN.gs n i ∈ c.chP.sub n := by
        rw [hoeq i hiP]; exact Subgroup.subset_closure ⟨i, hiP, rfl⟩
      exact (c.chP.sub n).mul_mem ((c.chP.sub n).mul_mem hgi hjP) ((c.chP.sub n).inv_mem hgi)
    · have hia : i - c.chP.k < c.chN.k - c.chP.k := by omega
      obtain ⟨hl, he⟩ := hnormW (i - c.chP.k) hia j hj
      have hidx : c.chP.k + (i - c.chP.k) = i := by omega
      rw [hidx] at he
      have hiS : i < c.chN.S.size := hi.trans_le hkN
      have hrep := rep_conjArr (ChainData.rep_gs n hN hiS) (ChainData.rep_inv_gs n hN hiS)
        (ChainData.rep_gs n hP (hj.trans_le hkP))
      have heq := (eqA_iff hrep (c.chP.rep_wordArr n hP hl)).1 he
      change c.chN.gs n i * c.chP.gs n j * (c.chN.gs n i)⁻¹ ∈ c.chP.sub n
      rw [heq]
      exact c.chP.val_mem_sub n hP _
  have hb0' : c.b0 < n := hb0
  have hcent : ∀ x ∈ c.chN.sub n, (∀ p ∈ c.chP.sub n, x * p = p * x) → x = 1 := by
    intro x _ hx
    refine eq_one_of_commute_transitive (P := c.chP.sub n) ⟨c.b0, hb0'⟩ ?_ ?_ hx
    · intro ω
      refine ⟨c.chP.val n c.transW[ω.val]!, c.chP.val_mem_sub n hP _, ?_⟩
      obtain ⟨hl, he⟩ := htrans ω.val ω.2
      have hr := c.chP.rep_wordArr n hP hl
      apply Fin.ext
      have := hr ⟨c.b0, hb0'⟩
      rw [← this]
      exact he
    · intro ω hω
      have hne : ω.val ≠ c.b0 := fun hh => hω (Fin.ext hh)
      have hs := hstab2 ω.val ω.2
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at hs
      rcases hs with hs | ⟨j, hj, hjn⟩
      · exact absurd hs hne
      · obtain ⟨⟨hj0, hjle⟩, hjb⟩ := hstab1 j hj
        have hjS : j - 1 < c.chP.S.size := by omega
        refine ⟨c.chP.gs n (j - 1), hPs.2.1 (j - 1) hjS, ?_, ?_⟩
        · apply Fin.ext
          rw [← (ChainData.rep_gs n hP hjS) ⟨c.b0, hb0'⟩]
          exact hjb
        · intro hcontra
          apply hjn
          have := congrArg Fin.val hcontra
          rw [← (ChainData.rep_gs n hP hjS) ω] at this
          exact this
  exact ⟨hP, hN, hPN, hnorm, hcent, hPs.2.2, hNs.2.2⟩

end Ctx


@[expose] def winv (w : List ℤ) : List ℤ := w.reverse.map fun l => -l

structure CoverCert where
  ws : List (List ℤ)
  cj : List (ℕ × List ℤ)
  deriving Inhabited

@[expose] def CoverCert.ok (n : ℕ) (T K : ChainData) (cc : CoverCert) (nrep : ℕ)
    (repA : ℕ → Array ℕ) : Bool :=
  T.check n && K.check n && cc.ws.all (lettersOK T.S.size) &&
    strictInc (cc.ws.map fun w => hashN n (T.wordArr n w)) &&
    decide (cc.ws.length = T.order n) && decide (cc.cj.length = cc.ws.length) &&
    (List.range cc.ws.length).all fun i =>
      !(eqA n (compA n (T.wordArr n cc.ws[i]!) (T.wordArr n cc.ws[i]!)) (idA n)) ||
      eqA n (T.wordArr n cc.ws[i]!) (idA n) ||
      (decide (1 ≤ (cc.cj[i]!).1 ∧ (cc.cj[i]!).1 ≤ nrep) && lettersOK K.S.size (cc.cj[i]!).2 &&
        invPair n (K.wordArr n (cc.cj[i]!).2) (K.wordArr n (winv (cc.cj[i]!).2)) &&
        eqA n (conjArr n (K.wordArr n (cc.cj[i]!).2) (K.wordArr n (winv (cc.cj[i]!).2))
          (T.wordArr n cc.ws[i]!)) (repA (cc.cj[i]!).1))


theorem lettersOK_winv {j : ℕ} {w : List ℤ} (h : lettersOK j w = true) :
    lettersOK j (winv w) = true := by
  simp only [lettersOK, winv, List.all_eq_true, List.mem_map, List.mem_reverse] at h ⊢
  rintro l ⟨l', hl', rfl⟩
  have := h l' hl'
  simpa using this

theorem CoverCert.sound (n : ℕ) (T K : ChainData) (cc : CoverCert) (nrep : ℕ)
    (repA : ℕ → Array ℕ) (repP : ℕ → Equiv.Perm (Fin n))
    (hrep : ∀ k, 1 ≤ k → k ≤ nrep → Rep n (repA k) (repP k)) (h : cc.ok n T K nrep repA = true) :
    ∀ t ∈ T.sub n, t * t = 1 → t = 1 ∨
      ∃ μ ∈ K.sub n, ∃ k, 1 ≤ k ∧ k ≤ nrep ∧ μ * t * μ⁻¹ = repP k := by
  simp only [CoverCert.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hT, hK⟩, hl⟩, hs⟩, hlen⟩, hcj⟩, hall⟩ := h
  have hl' : ∀ w ∈ cc.ws, lettersOK T.S.size w = true := fun w hw => by
    simpa using (List.all_eq_true.1 hl) w hw
  intro t ht ht2
  obtain ⟨w, hw, rfl⟩ := elems_cover T n hT cc.ws hl hs hlen t ht
  obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.1 hw
  have hwi : cc.ws[i]! = w := by rw [getElem!_pos cc.ws i hi]; exact hiw
  have hi' := (List.all_eq_true.1 hall) i (List.mem_range.2 hi)
  rw [hwi] at hi'
  have hrepw := T.rep_wordArr n hT (hl' w hw)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at hi'
  rcases hi' with (h1 | h2) | ⟨⟨⟨⟨hj1, hlet⟩, hinv⟩, heq⟩⟩
  · exfalso
    have : eqA n (compA n (T.wordArr n w) (T.wordArr n w)) (idA n) = true :=
      (eqA_iff (rep_compA hrepw hrepw) (rep_idA (n := n))).2 ht2
    rw [this] at h1
    exact Bool.noConfusion h1
  · left
    exact (eqA_iff hrepw (rep_idA (n := n))).1 h2
  · right
    have hcl := hlet
    have hrK := K.rep_wordArr n hK hcl
    have hrKi := K.rep_wordArr n hK (lettersOK_winv hcl)
    have hinvE := rep_inv_of_invPair hrK hrKi hinv
    have hrc := rep_conjArr hrK hrKi hrepw
    have hrj := hrep _ hj1.1 hj1.2
    have := (eqA_iff hrc hrj).1 heq
    refine ⟨K.val n (cc.cj[i]!).2, K.val_mem_sub n hK _, (cc.cj[i]!).1, hj1.1, hj1.2, ?_⟩
    rw [← this, hinvE]


theorem getElem!_mem_toList (S : Array (Array ℕ)) {i : ℕ} (hi : i < S.size) : S[i]! ∈ S.toList := by
  rw [getElem!_pos S i hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

theorem getElem!_map_inv (n : ℕ) (S : Array (Array ℕ)) {i : ℕ} (hi : i < S.size) :
    (S.map (invCand n))[i]! = invCand n S[i]! := by
  rw [getElem!_pos (S.map (invCand n)) i (by simpa using hi), Array.getElem_map,
    getElem!_pos S i hi]

theorem wordA_closure {n : ℕ} (S : Array (Array ℕ)) (T : Set (Equiv.Perm (Fin n)))
    (hS : ∀ a ∈ S.toList, ∃ x ∈ T, Rep n a x ∧ Rep n (invCand n a) x⁻¹) :
    ∀ w : List ℤ, lettersOK S.size w = true →
      ∃ x ∈ Subgroup.closure T, Rep n (wordA n S (S.map (invCand n)) w) x := by
  intro w
  induction w with
  | nil => intro _; exact ⟨1, Subgroup.one_mem _, rep_idA⟩
  | cons l w ih =>
    intro hw
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw'⟩ := hw
    obtain ⟨y, hy, hry⟩ := ih (by simpa [lettersOK, List.all_eq_true] using hw')
    have hidx : l.natAbs - 1 < S.size := by omega
    obtain ⟨x, hxT, hrx, hrxi⟩ := hS _ (getElem!_mem_toList S hidx)
    have hxcl : x ∈ Subgroup.closure T := Subgroup.subset_closure hxT
    have hwd : wordA n S (S.map (invCand n)) (l :: w) =
        compA n (letterA S (S.map (invCand n)) l) (wordA n S (S.map (invCand n)) w) := rfl
    rw [hwd]
    by_cases hpos : 0 < l
    · have hlet : letterA S (S.map (invCand n)) l = S[l.natAbs - 1]! := by
        unfold letterA
        rw [if_pos hpos]
        congr 2
        omega
      refine ⟨x * y, Subgroup.mul_mem _ hxcl hy, ?_⟩
      rw [hlet]
      exact rep_compA hrx hry
    · have hlet : letterA S (S.map (invCand n)) l = invCand n S[l.natAbs - 1]! := by
        unfold letterA
        rw [if_neg hpos]
        have : (-l).toNat - 1 = l.natAbs - 1 := by omega
        rw [this]
        exact getElem!_map_inv n S hidx
      refine ⟨x⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _ hxcl) hy, ?_⟩
      rw [hlet]
      exact rep_compA hrxi hry


@[expose] def powA (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | k + 1 => compA n t (powA n t k)

theorem rep_powA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    ∀ k, Rep n (powA n t k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA (n := n)
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA h (rep_powA h k)

structure GenCert where
  Aw : List (List ℤ)
  ka : List ℕ
  Bw : List (List ℤ)
  kb : List ℕ
  pw : List (List ℤ)
  deriving Inhabited

namespace GenCert

variable (n : ℕ) (g : GenCert)

@[expose] def AB (chP chC : ChainData) : Array (Array ℕ) :=
  (g.Aw.map (chC.wordArr n) ++ g.Bw.map (chP.wordArr n)).toArray

@[expose] def ok (chP chC : ChainData) (nuA enuA : Array ℕ) : Bool :=
  let AB := g.AB n chP chC
  let ABi := AB.map (invCand n)
  g.Aw.all (lettersOK chC.S.size) && g.Bw.all (lettersOK chP.S.size) &&
    decide (g.ka.length = g.Aw.length) && decide (g.kb.length = g.Bw.length) &&
    (List.range g.Aw.length).all (fun i =>
      decide (g.ka[i]! % 2 = 1) &&
        eqA n (compA n nuA (chC.wordArr n g.Aw[i]!)) (compA n (chC.wordArr n g.Aw[i]!) nuA) &&
        eqA n (powA n (chC.wordArr n g.Aw[i]!) g.ka[i]!) (idA n)) &&
    (List.range g.Bw.length).all (fun i =>
      decide (g.kb[i]! % 2 = 1) &&
        eqA n (compA n enuA (chP.wordArr n g.Bw[i]!)) (compA n (chP.wordArr n g.Bw[i]!) enuA) &&
        eqA n (powA n (chP.wordArr n g.Bw[i]!) g.kb[i]!) (idA n)) &&
    decide (g.pw.length = chP.k) &&
    (List.range AB.size).all (fun j => isInvA n AB[j]! ABi[j]!) &&
    (List.range chP.k).all (fun i =>
      lettersOK AB.size g.pw[i]! && eqA n chP.S[i]! (wordA n AB ABi g.pw[i]!))

end GenCert


theorem GenCert.sound (n : ℕ) (g : GenCert) (chP chC : ChainData) (nuA enuA : Array ℕ)
    (ν E : Equiv.Perm (Fin n)) (hP : chP.check n = true) (hC : chC.check n = true)
    (hCP : chC.sub n ≤ chP.sub n) (hν : Rep n nuA ν) (hE : Rep n enuA E)
    (h : g.ok n chP chC nuA enuA = true) :
    chP.sub n ≤ Subgroup.closure ({x | x ∈ chP.sub n ∧ ν * x = x * ν ∧ Odd (orderOf x)} ∪
      {x | x ∈ chP.sub n ∧ E * x = x * E ∧ Odd (orderOf x)}) := by
  simp only [GenCert.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hAl, hBl⟩, hka⟩, hkb⟩, hA⟩, hB⟩, hpwl⟩, hinv⟩, hpw⟩ := h
  have hodd : ∀ {x : Equiv.Perm (Fin n)} {k : ℕ}, k % 2 = 1 → x ^ k = 1 → Odd (orderOf x) := by
    intro x k hk hxk
    exact Odd.of_dvd_nat (Nat.odd_iff.2 hk) (orderOf_dvd_of_pow_eq_one hxk)
  have hS : ∀ a ∈ (g.AB n chP chC).toList, ∃ x ∈ ({x | x ∈ chP.sub n ∧ ν * x = x * ν ∧
        Odd (orderOf x)} ∪ {x | x ∈ chP.sub n ∧ E * x = x * E ∧ Odd (orderOf x)}),
      Rep n a x ∧ Rep n (invCand n a) x⁻¹ := by
    intro a ha
    obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 ha
    have hjsz : j < (g.AB n chP chC).size := by simpa using hj
    have hinvj := hinv j hjsz
    have haj : (g.AB n chP chC)[j]! = a := by rw [getElem!_pos _ j hjsz]; simpa using hja
    rw [getElem!_map_inv n _ hjsz, haj] at hinvj
    have hmem : a ∈ g.Aw.map (chC.wordArr n) ∨ a ∈ g.Bw.map (chP.wordArr n) := by
      have : a ∈ (g.AB n chP chC).toList := ha
      simpa [GenCert.AB, List.mem_append] using this
    rcases hmem with hmA | hmB
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hmA
      obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.1 hw
      have hwi : g.Aw[i]! = w := by rw [getElem!_pos g.Aw i hi]; exact hiw
      have hlet : lettersOK chC.S.size w = true := hAl w hw
      have hr := chC.rep_wordArr n hC hlet
      obtain ⟨⟨hodd1, hcomm⟩, hpow⟩ := hA i (by
        have : g.Aw.length = g.ka.length := hka.symm
        omega)
      rw [hwi] at hcomm hpow
      refine ⟨chC.val n w, Or.inl ⟨hCP (chC.val_mem_sub n hC w), ?_, ?_⟩, hr, ?_⟩
      · exact (eqA_iff (rep_compA hν hr) (rep_compA hr hν)).1 hcomm
      · have := (eqA_iff (rep_powA hr _) (rep_idA (n := n))).1 hpow
        exact hodd hodd1 this
      · exact rep_inv_of_isInvA hr hinvj
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hmB
      obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.1 hw
      have hwi : g.Bw[i]! = w := by rw [getElem!_pos g.Bw i hi]; exact hiw
      have hlet : lettersOK chP.S.size w = true := hBl w hw
      have hr := chP.rep_wordArr n hP hlet
      obtain ⟨⟨hodd1, hcomm⟩, hpow⟩ := hB i (by
        have : g.Bw.length = g.kb.length := hkb.symm
        omega)
      rw [hwi] at hcomm hpow
      refine ⟨chP.val n w, Or.inr ⟨chP.val_mem_sub n hP w, ?_, ?_⟩, hr, ?_⟩
      · exact (eqA_iff (rep_compA hE hr) (rep_compA hr hE)).1 hcomm
      · have := (eqA_iff (rep_powA hr _) (rep_idA (n := n))).1 hpow
        exact hodd hodd1 this
      · exact rep_inv_of_isInvA hr hinvj
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, hi, rfl⟩
  obtain ⟨hl, he⟩ := hpw i hi
  obtain ⟨y, hy, hry⟩ := wordA_closure (g.AB n chP chC) _ hS _ hl
  have hP' : Rep n chP.S[i]! (chP.gs n i) :=
    ChainData.rep_gs n hP (hi.trans_le (ChainData.k_le_size n hP))
  have := (eqA_iff hP' hry).1 he
  show chP.gs n i ∈ _
  rw [this]
  exact hy


@[expose] def bfsAux (n : ℕ) (S Sinv : Array (Array ℕ)) :
    List (ℕ × ℤ) → Array (Array ℕ) → Array (Array ℕ)
  | [], L => L
  | (p, l) :: rest, L =>
    bfsAux n S Sinv rest
      (L.push (conjArr n (letterA S Sinv l) (letterA S Sinv (-l)) L[p]!))

@[expose] def bfsOK (j : ℕ) : List (ℕ × ℤ) → ℕ → Bool
  | [], _ => true
  | (p, l) :: rest, sz => decide (p < sz) && lettersOK j [l] && bfsOK j rest (sz + 1)

theorem bfsAux_size (n : ℕ) (S Sinv : Array (Array ℕ)) :
    ∀ (par : List (ℕ × ℤ)) (L : Array (Array ℕ)), (bfsAux n S Sinv par L).size = L.size + par.length
  | [], L => by simp [bfsAux]
  | (p, l) :: rest, L => by
    simp only [bfsAux, List.length_cons]
    rw [bfsAux_size n S Sinv rest, Array.size_push]
    omega

theorem bfsAux_sound (n : ℕ) (cd : ChainData) (hcd : cd.check n = true)
    (ν : Equiv.Perm (Fin n)) :
    ∀ (par : List (ℕ × ℤ)) (L : Array (Array ℕ)),
      (∀ m < L.size, ∃ h ∈ cd.sub n, Rep n L[m]! (h * ν * h⁻¹)) →
      bfsOK cd.S.size par L.size = true →
      ∀ m < (bfsAux n cd.S (rawInvs n cd.S) par L).size,
        ∃ h ∈ cd.sub n, Rep n (bfsAux n cd.S (rawInvs n cd.S) par L)[m]! (h * ν * h⁻¹)
  | [], L, hL, _ => by simpa [bfsAux] using hL
  | (p, l) :: rest, L, hL, hok => by
    simp only [bfsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hp, hl⟩, hrest⟩ := hok
    have hl' : l ≠ 0 ∧ l.natAbs ≤ cd.S.size := by
      simpa [lettersOK] using hl
    obtain ⟨g, hg, hrg⟩ : ∃ g ∈ cd.sub n, Rep n (letterA cd.S (rawInvs n cd.S) l) g ∧
        Rep n (letterA cd.S (rawInvs n cd.S) (-l)) g⁻¹ := by
      have h1 := rep_letterA (S := cd.S) (Sinv := rawInvs n cd.S) (gs := fun h => cd.gs n h)
        (j := cd.S.size) (fun h hh => ((cd.check_sound n hcd).1 h hh).1)
        (fun h hh => ((cd.check_sound n hcd).1 h hh).2) hl'
      have h2 := rep_letterA (S := cd.S) (Sinv := rawInvs n cd.S) (gs := fun h => cd.gs n h)
        (j := cd.S.size) (fun h hh => ((cd.check_sound n hcd).1 h hh).1)
        (fun h hh => ((cd.check_sound n hcd).1 h hh).2) (l := -l)
        ⟨by simpa using hl'.1, by simpa using hl'.2⟩
      have hmem : cd.gs n (l.natAbs - 1) ∈ cd.sub n :=
        (cd.check_sound n hcd).2.1 _ (by omega)
      by_cases hpos : 0 < l
      · refine ⟨cd.gs n (l.natAbs - 1), hmem, ?_, ?_⟩
        · simpa [hpos] using h1
        · have hn : ¬ l < 0 := by omega
          simpa [hn] using h2
      · refine ⟨(cd.gs n (l.natAbs - 1))⁻¹, cd.sub n |>.inv_mem hmem, ?_, ?_⟩
        · simpa [hpos] using h1
        · have hn : l < 0 := by omega
          simpa [hn] using h2
    refine bfsAux_sound n cd hcd ν rest _ ?_ (by rw [Array.size_push]; exact hrest)
    intro m hm
    rw [Array.size_push] at hm
    by_cases hmlt : m < L.size
    · rw [getElem!_pos _ m (by simpa [Array.size_push] using Nat.lt_succ_of_lt hmlt),
        Array.getElem_push_lt hmlt, ← getElem!_pos L m hmlt]
      exact hL m hmlt
    · have hmeq : m = L.size := by omega
      subst hmeq
      obtain ⟨h0, hh0, hr0⟩ := hL p hp
      refine ⟨g * h0, Subgroup.mul_mem _ hg hh0, ?_⟩
      rw [getElem!_pos _ L.size (by simp [Array.size_push]), Array.getElem_push_eq]
      have := rep_conjArr hrg.1 hrg.2 hr0
      convert this using 1
      group


theorem conjList_sound (n : ℕ) (cd : ChainData) (hcd : cd.check n = true)
    (ν : Equiv.Perm (Fin n)) (seed : Array ℕ) (hseed : Rep n seed ν) (par : List (ℕ × ℤ))
    (ord : List ℕ) (hbfs : bfsOK cd.S.size par 1 = true)
    (hord : ord.all (fun m => decide (m < par.length + 1)) = true)
    (hs : strictInc (ord.map fun m =>
      hashN n ((bfsAux n cd.S (rawInvs n cd.S) par #[seed])[m]!)) = true) :
    ∃ Ys : List (Equiv.Perm (Fin n)), Ys.Nodup ∧ Ys.length = ord.length ∧
      ∀ y ∈ Ys, ∃ g ∈ cd.sub n, g * ν * g⁻¹ = y := by
  classical
  set L := bfsAux n cd.S (rawInvs n cd.S) par #[seed] with hL
  have hsize : L.size = par.length + 1 := by
    rw [hL, bfsAux_size]; simp [add_comm]
  have hrep : ∀ m < L.size, ∃ h ∈ cd.sub n, Rep n L[m]! (h * ν * h⁻¹) :=
    bfsAux_sound n cd hcd ν par #[seed]
      (by
        intro m hm
        have : m = 0 := by simpa using hm
        subst this
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        simpa using hseed) hbfs
  choose! f hfmem hfrep using hrep
  have hordlt : ∀ m ∈ ord, m < L.size := fun m hm => by
    have := (List.all_eq_true.1 hord) m hm
    rw [hsize]; simpa using this
  refine ⟨ord.map fun m => f m * ν * (f m)⁻¹, ?_, by simp, ?_⟩
  · have hmap : (ord.map fun m => f m * ν * (f m)⁻¹).map (hashP n) =
        ord.map fun m => hashN n L[m]! := by
      rw [List.map_map]
      refine List.map_congr_left fun m hm => ?_
      exact (hashN_eq_hashP (hfrep m (hordlt m hm))).symm
    have hp := strictInc_pairwise _ hs
    rw [← hmap] at hp
    exact List.Nodup.of_map _ (List.Pairwise.imp (fun hab => ne_of_lt hab) hp)
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
    exact ⟨f m, hfmem m (hordlt m hm), rfl⟩

@[expose] def bfsCheck (n : ℕ) (S : Array (Array ℕ)) (seed : Array ℕ) (par : List (ℕ × ℤ))
    (ord : List ℕ) : Bool :=
  let L := bfsAux n S (rawInvs n S) par #[seed]
  bfsOK S.size par 1 && ord.all (fun m => decide (m < par.length + 1)) &&
    strictInc (ord.map fun m => hashN n L[m]!)

theorem conjList_sound' (n : ℕ) (cd : ChainData) (hcd : cd.check n = true)
    (ν : Equiv.Perm (Fin n)) (seed : Array ℕ) (hseed : Rep n seed ν) (par : List (ℕ × ℤ))
    (ord : List ℕ) (hb : bfsCheck n cd.S seed par ord = true) :
    ∃ Ys : List (Equiv.Perm (Fin n)), Ys.Nodup ∧ Ys.length = ord.length ∧
      ∀ y ∈ Ys, ∃ g ∈ cd.sub n, g * ν * g⁻¹ = y := by
  simp only [bfsCheck, Bool.and_eq_true] at hb
  exact conjList_sound n cd hcd ν seed hseed par ord hb.1.1 hb.1.2 hb.2


@[expose] def commArr (n : ℕ) (a b ai bi : Array ℕ) : Array ℕ :=
  compA n (compA n a b) (compA n ai bi)

structure RepCert where
  nuW : List ℤ
  chC : ChainData
  cgW : List (List ℤ)
  par : List (ℕ × ℤ)
  ord : List ℕ
  chX : ChainData
  xgW : List (List ℤ)
  xnorm : List (List (List ℤ))
  xcomm : List (List (List ℤ))
  chT : ChainData
  tgW : List (List ℤ)
  sylA : ℕ
  sylM : ℕ
  tel : CoverCert
  epsW : List (List ℤ)
  gens : List GenCert
  deriving Inhabited

namespace RepCert

variable (n : ℕ) (ctx : Ctx) (r : RepCert)

@[expose] def nuA : Array ℕ := ctx.chN.wordArr n r.nuW

@[expose] def epsA (k : ℕ) : Array ℕ := r.chX.wordArr n (r.epsW[k - 1]!)

@[expose] def okC : Bool :=
  lettersOK ctx.chN.S.size r.nuW &&
    eqA n (compA n (r.nuA n ctx) (r.nuA n ctx)) (idA n) &&
    r.chC.check n && ChainData.origsOK n r.chC ctx.chP r.cgW &&
    (List.range r.chC.k).all (fun i =>
      eqA n (compA n (r.nuA n ctx) r.chC.S[i]!) (compA n r.chC.S[i]! (r.nuA n ctx)))

@[expose] def okE : Bool :=
  bfsCheck n ctx.chP.S (r.nuA n ctx) r.par r.ord &&
    decide (ctx.chP.order n ≤ r.ord.length * r.chC.order n)

@[expose] def okX : Bool :=
  let Ci := rawInvs n r.chC.S
  r.chX.check n && ChainData.origsOK n r.chX r.chC r.xgW &&
    (List.range r.chC.k).all (fun i => (List.range r.chX.k).all (fun j =>
      lettersOK r.chX.S.size ((r.xnorm[i]!)[j]!) &&
        eqA n (conjArr n r.chC.S[i]! Ci[i]! r.chX.S[j]!)
          (r.chX.wordArr n ((r.xnorm[i]!)[j]!)))) &&
    (List.range r.chC.k).all (fun i => (List.range r.chC.k).all (fun i' =>
      lettersOK r.chX.S.size ((r.xcomm[i]!)[i']!) &&
        eqA n (commArr n r.chC.S[i]! r.chC.S[i']! Ci[i]! Ci[i']!)
          (r.chX.wordArr n ((r.xcomm[i]!)[i']!))))

@[expose] def okT : Bool :=
  r.chT.check n && ChainData.origsOK n r.chT r.chX r.tgW &&
    decide (r.chT.order n = 2 ^ r.sylA) && decide (r.chX.order n = 2 ^ r.sylA * r.sylM) &&
    decide (r.sylM % 2 = 1) &&
    r.epsW.all (lettersOK r.chX.S.size) &&
    r.tel.ok n r.chT r.chC r.epsW.length (r.epsA n)

@[expose] def okG : Bool :=
  decide (r.gens.length = r.epsW.length) &&
    (List.range r.epsW.length).all (fun l =>
      (r.gens[l]!).ok n ctx.chP r.chC (r.nuA n ctx) (compA n (r.epsA n (l + 1)) (r.nuA n ctx)))

@[expose] def ok : Bool := r.okC n ctx && r.okE n ctx && r.okX n && r.okT n && r.okG n ctx

theorem sound_C (hP : ctx.chP.check n = true) (hN : ctx.chN.check n = true)
    (h : r.okC n ctx = true) :
    r.chC.check n = true ∧ r.chC.sub n ≤ ctx.chP.sub n ∧
      Rep n (r.nuA n ctx) (ctx.chN.val n r.nuW) ∧
      ctx.chN.val n r.nuW * ctx.chN.val n r.nuW = 1 ∧
      (∀ g ∈ r.chC.sub n, ctx.chN.val n r.nuW * g = g * ctx.chN.val n r.nuW) := by
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hl, hnu2⟩, hCc⟩, horig⟩, hcomm⟩ := h
  have hν : Rep n (r.nuA n ctx) (ctx.chN.val n r.nuW) := ctx.chN.rep_wordArr n hN hl
  have hgens : ∀ g ∈ {g | ∃ i < r.chC.k, g = permOfArr n r.chC.S[i]!},
      ctx.chN.val n r.nuW * g = g * ctx.chN.val n r.nuW := by
    rintro g ⟨i, hi, rfl⟩
    have hi' : i < r.chC.S.size := hi.trans_le (ChainData.k_le_size n hCc)
    have hrep := ChainData.rep_gs n hCc hi'
    exact (eqA_iff (rep_compA hν hrep) (rep_compA hrep hν)).1 (hcomm i hi)
  have hcl : r.chC.sub n ≤ Subgroup.centralizer {ctx.chN.val n r.nuW} := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hgens g hg).symm
  refine ⟨hCc, ChainData.sub_le_of_origsOK n hCc hP horig, hν,
    (eqA_iff (rep_compA hν hν) (rep_idA (n := n))).1 hnu2, fun g hg => ?_⟩
  have := hcl hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

theorem sound_E {ν : Equiv.Perm (Fin n)} (hP : ctx.chP.check n = true) (hC : r.chC.check n = true)
    (hCP : r.chC.sub n ≤ ctx.chP.sub n) (hν : Rep n (r.nuA n ctx) ν)
    (hcomm : ∀ g ∈ r.chC.sub n, ν * g = g * ν) (h : r.okE n ctx = true) :
    ∀ g ∈ ctx.chP.sub n, ν * g = g * ν → g ∈ r.chC.sub n := by
  simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hb, hcard⟩ := h
  obtain ⟨Ys, hnd, hlen, hconj⟩ := conjList_sound' n ctx.chP hP ν (r.nuA n ctx) hν r.par r.ord hb
  have hCs := (r.chC.check_sound n hC).2.2
  have hPs := (ctx.chP.check_sound n hP).2.2
  have hcgP : {g | ∃ i < r.chC.k, g = permOfArr n r.chC.S[i]!} ⊆ ctx.chP.sub n := fun g hg =>
    hCP (Subgroup.subset_closure hg)
  exact mem_closure_of_commutes (P := ctx.chP.sub n) ν Ys hnd hconj
    {g | ∃ i < r.chC.k, g = permOfArr n r.chC.S[i]!} hcgP
    (fun c hc => hcomm c (Subgroup.subset_closure hc))
    (by rw [hlen]; change Nat.card (ctx.chP.sub n) ≤ r.ord.length * Nat.card (r.chC.sub n)
        rw [hCs, hPs]; exact hcard)

theorem sound_X (hC : r.chC.check n = true) (h : r.okX n = true) :
    r.chX.check n = true ∧ r.chX.sub n ≤ r.chC.sub n ∧
      ⁅r.chC.sub n, r.chC.sub n⁆ ≤ r.chX.sub n := by
  simp only [okX, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hX, horig⟩, hnormW⟩, hcommW⟩ := h
  have hXC : r.chX.sub n ≤ r.chC.sub n := ChainData.sub_le_of_origsOK n hX hC horig
  refine ⟨hX, hXC, ?_⟩
  refine commutator_le_of_gen (cg := {g | ∃ i < r.chC.k, g = permOfArr n r.chC.S[i]!}) rfl hXC ?_ ?_
  · rintro c ⟨i, hi, rfl⟩ x hx
    have hiS : i < r.chC.S.size := hi.trans_le (ChainData.k_le_size n hC)
    have hgen : ∀ j < r.chX.k, permOfArr n r.chC.S[i]! * permOfArr n r.chX.S[j]! *
        (permOfArr n r.chC.S[i]!)⁻¹ ∈ r.chX.sub n := by
      intro j hj
      obtain ⟨hl, he⟩ := hnormW i hi j hj
      have hjS : j < r.chX.S.size := hj.trans_le (ChainData.k_le_size n hX)
      have hrep := rep_conjArr (ChainData.rep_gs n hC hiS) (ChainData.rep_inv_gs n hC hiS)
        (ChainData.rep_gs n hX hjS)
      have heq := (eqA_iff hrep (r.chX.rep_wordArr n hX hl)).1 he
      change r.chC.gs n i * r.chX.gs n j * (r.chC.gs n i)⁻¹ ∈ r.chX.sub n
      rw [heq]
      exact r.chX.val_mem_sub n hX _
    change x ∈ Subgroup.closure {g | ∃ i < r.chX.k, g = permOfArr n r.chX.S[i]!} at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact hgen j hj
    | one => simpa using (r.chX.sub n).one_mem
    | mul a b _ _ ha hb =>
      have e : permOfArr n r.chC.S[i]! * (a * b) * (permOfArr n r.chC.S[i]!)⁻¹ =
          (permOfArr n r.chC.S[i]! * a * (permOfArr n r.chC.S[i]!)⁻¹) *
          (permOfArr n r.chC.S[i]! * b * (permOfArr n r.chC.S[i]!)⁻¹) := by group
      rw [e]
      exact (r.chX.sub n).mul_mem ha hb
    | inv a _ ha =>
      have e : permOfArr n r.chC.S[i]! * a⁻¹ * (permOfArr n r.chC.S[i]!)⁻¹ =
          (permOfArr n r.chC.S[i]! * a * (permOfArr n r.chC.S[i]!)⁻¹)⁻¹ := by group
      rw [e]
      exact (r.chX.sub n).inv_mem ha
  · rintro c ⟨i, hi, rfl⟩ c' ⟨i', hi', rfl⟩
    have hiS : i < r.chC.S.size := hi.trans_le (ChainData.k_le_size n hC)
    have hiS' : i' < r.chC.S.size := hi'.trans_le (ChainData.k_le_size n hC)
    obtain ⟨hl, he⟩ := hcommW i hi i' hi'
    have hrep : Rep n (commArr n r.chC.S[i]! r.chC.S[i']! (rawInvs n r.chC.S)[i]!
        (rawInvs n r.chC.S)[i']!)
        (r.chC.gs n i * r.chC.gs n i' * ((r.chC.gs n i)⁻¹ * (r.chC.gs n i')⁻¹)) :=
      rep_compA (rep_compA (ChainData.rep_gs n hC hiS) (ChainData.rep_gs n hC hiS'))
        (rep_compA (ChainData.rep_inv_gs n hC hiS) (ChainData.rep_inv_gs n hC hiS'))
    have heq := (eqA_iff hrep (r.chX.rep_wordArr n hX hl)).1 he
    change ⁅r.chC.gs n i, r.chC.gs n i'⁆ ∈ r.chX.sub n
    have e : ⁅r.chC.gs n i, r.chC.gs n i'⁆ =
        r.chC.gs n i * r.chC.gs n i' * ((r.chC.gs n i)⁻¹ * (r.chC.gs n i')⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, heq]
    exact r.chX.val_mem_sub n hX _

theorem factorization_two_pow_mul_odd (a m : ℕ) (hm : m % 2 = 1) :
    (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  omega

@[expose] def epsSet : Set (Equiv.Perm (Fin n)) :=
  {ε | ∃ k, 1 ≤ k ∧ k ≤ r.epsW.length ∧ ε = r.chX.val n (r.epsW[k - 1]!)}

theorem sound_T (hX : r.chX.check n = true) (hC : r.chC.check n = true)
    (hXC : r.chX.sub n ≤ r.chC.sub n) (h : r.okT n = true) :
    (∀ k, 1 ≤ k → k ≤ r.epsW.length → lettersOK r.chX.S.size (r.epsW[k - 1]!) = true) ∧
    ∀ e ∈ r.chX.sub n, e * e = 1 → e ≠ 1 →
      ∃ c ∈ r.chC.sub n, ∃ ε ∈ r.epsSet n, c * e * c⁻¹ = ε := by
  simp only [okT, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hT, horig⟩, hTord⟩, hXord⟩, hodd⟩, heps⟩, htel⟩ := h
  have hepsl : ∀ k, 1 ≤ k → k ≤ r.epsW.length → lettersOK r.chX.S.size (r.epsW[k - 1]!) = true := by
    intro k hk1 hk2
    have hmem : r.epsW[k - 1]! ∈ r.epsW := by
      rw [getElem!_pos r.epsW (k - 1) (by omega)]
      exact List.getElem_mem _
    exact List.all_eq_true.1 heps _ hmem
  refine ⟨hepsl, ?_⟩
  have hrep : ∀ k, 1 ≤ k → k ≤ r.epsW.length →
      Rep n (r.epsA n k) (r.chX.val n (r.epsW[k - 1]!)) := fun k hk1 hk2 =>
    r.chX.rep_wordArr n hX (hepsl k hk1 hk2)
  have hcov := CoverCert.sound n r.chT r.chC r.tel r.epsW.length (r.epsA n)
    (fun k => r.chX.val n (r.epsW[k - 1]!)) hrep htel
  have hTN : r.chT.sub n ≤ r.chX.sub n := ChainData.sub_le_of_origsOK n hT hX horig
  have hcardT : Nat.card (r.chT.sub n) = 2 ^ (Nat.card (r.chX.sub n)).factorization 2 := by
    rw [(r.chT.check_sound n hT).2.2, (r.chX.check_sound n hX).2.2, hTord, hXord,
      factorization_two_pow_mul_odd _ _ hodd]
  have hcov' := cover_of_sylow (N := r.chX.sub n) (T := r.chT.sub n) (K := r.chC.sub n) hXC hTN
    hcardT (r.epsSet n) (by
      intro t ht ht2
      rcases hcov t ht ht2 with h1 | ⟨μ, hμ, k, hk1, hk2, hμt⟩
      · exact Or.inl h1
      · exact Or.inr ⟨μ, hμ, _, ⟨k, hk1, hk2, rfl⟩, hμt⟩)
  intro e he he2 he1
  rcases hcov' e he he2 with h1 | ⟨μ, hμ, ρ, hρ, hμe⟩
  · exact absurd h1 he1
  · exact ⟨μ, hμ, ρ, hρ, hμe⟩

theorem sound_G {ν : Equiv.Perm (Fin n)} (hP : ctx.chP.check n = true)
    (hC : r.chC.check n = true) (hX : r.chX.check n = true)
    (hCP : r.chC.sub n ≤ ctx.chP.sub n) (hν : Rep n (r.nuA n ctx) ν)
    (hepsl : ∀ k, 1 ≤ k → k ≤ r.epsW.length → lettersOK r.chX.S.size (r.epsW[k - 1]!) = true)
    (h : r.okG n ctx = true) :
    ∀ ε ∈ r.epsSet n, ctx.chP.sub n ≤ Subgroup.closure
      ({x | x ∈ ctx.chP.sub n ∧ ν * x = x * ν ∧ Odd (orderOf x)} ∪
       {x | x ∈ ctx.chP.sub n ∧ (ε * ν) * x = x * (ε * ν) ∧ Odd (orderOf x)}) := by
  simp only [okG, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  rintro _ ⟨k, hk1, hk2, rfl⟩
  have hk := hall (k - 1) (by omega)
  have hkk : k - 1 + 1 = k := by omega
  rw [hkk] at hk
  have hrep : Rep n (r.epsA n k) (r.chX.val n (r.epsW[k - 1]!)) :=
    r.chX.rep_wordArr n hX (hepsl k hk1 hk2)
  exact GenCert.sound n (r.gens[k - 1]!) ctx.chP r.chC (r.nuA n ctx)
    (compA n (r.epsA n k) (r.nuA n ctx)) ν (r.chX.val n (r.epsW[k - 1]!) * ν) hP hC hCP hν
    (rep_compA hrep hν) hk

theorem good (hctx : ctx.ok n = true) (h : r.ok n ctx = true) :
    RepGood (ctx.chP.sub n) (ctx.chN.val n r.nuW) := by
  obtain ⟨hP, hN, -⟩ := Ctx.sound n ctx hctx
  simp only [ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hC', hE'⟩, hX'⟩, hT'⟩, hG'⟩ := h
  obtain ⟨hC, hCP, hν, -, hcomm⟩ := r.sound_C n ctx hP hN hC'
  have hexact := r.sound_E n ctx hP hC hCP hν hcomm hE'
  obtain ⟨hX, hXC, hcc⟩ := r.sound_X n hC hX'
  obtain ⟨hepsl, hcov⟩ := r.sound_T n hX hC hXC hT'
  exact ⟨r.chC.sub n, r.chX.sub n, r.epsSet n, hCP, hcomm, hexact, hXC, hcc, hcov,
    r.sound_G n ctx hP hC hX hCP hν hepsl hG'⟩

theorem okC_of_ok (h : r.ok n ctx = true) : r.okC n ctx = true := by
  simp only [ok, Bool.and_eq_true] at h
  exact h.1.1.1.1

end RepCert


structure FCCert where
  ctx : Ctx
  chTN : ChainData
  tnW : List (List ℤ)
  sylA : ℕ
  sylM : ℕ
  tel : CoverCert
  reps : List RepCert
  deriving Inhabited

namespace FCCert

variable (n : ℕ) (c : FCCert)

@[expose] def repA (j : ℕ) : Array ℕ := (c.reps[j - 1]!).nuA n c.ctx

@[expose] def okTN : Bool :=
  c.chTN.check n && ChainData.origsOK n c.chTN c.ctx.chN c.tnW &&
    decide (c.chTN.order n = 2 ^ c.sylA) && decide (c.ctx.chN.order n = 2 ^ c.sylA * c.sylM) &&
    decide (c.sylM % 2 = 1) && c.tel.ok n c.chTN c.ctx.chN c.reps.length (c.repA n)

@[expose] def ok : Bool :=
  c.ctx.ok n && c.okTN n && c.reps.all (fun r => r.ok n c.ctx)

@[expose] def repSet : Set (Equiv.Perm (Fin n)) :=
  {ν | ∃ j, 1 ≤ j ∧ j ≤ c.reps.length ∧ ν = c.ctx.chN.val n (c.reps[j - 1]!).nuW}

theorem sound (h : c.ok n = true) : FCHyp (c.ctx.chP.sub n) (c.ctx.chN.sub n) := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hctx, hTN⟩, hreps⟩ := h
  obtain ⟨hP, hN, -⟩ := Ctx.sound n c.ctx hctx
  simp only [okTN, Bool.and_eq_true, decide_eq_true_eq] at hTN
  obtain ⟨⟨⟨⟨⟨hT, horig⟩, hTord⟩, hNord⟩, hodd⟩, htel⟩ := hTN
  have hrmem : ∀ j, 1 ≤ j → j ≤ c.reps.length → c.reps[j - 1]! ∈ c.reps := by
    intro j hj1 hj2
    rw [getElem!_pos c.reps (j - 1) (by omega)]
    exact List.getElem_mem _
  have hCj : ∀ j, 1 ≤ j → j ≤ c.reps.length → ∀ r, r = c.reps[j - 1]! →
      r.chC.check n = true ∧ r.chC.sub n ≤ c.ctx.chP.sub n ∧
      Rep n (r.nuA n c.ctx) (c.ctx.chN.val n r.nuW) ∧
      c.ctx.chN.val n r.nuW * c.ctx.chN.val n r.nuW = 1 ∧
      (∀ g ∈ r.chC.sub n, c.ctx.chN.val n r.nuW * g = g * c.ctx.chN.val n r.nuW) := by
    intro j hj1 hj2 r hr
    subst hr
    exact RepCert.sound_C n c.ctx _ hP hN (RepCert.okC_of_ok n c.ctx _ (hreps _ (hrmem j hj1 hj2)))
  have hcov := CoverCert.sound n c.chTN c.ctx.chN c.tel c.reps.length (c.repA n)
    (fun j => c.ctx.chN.val n (c.reps[j - 1]!).nuW)
    (fun j hj1 hj2 => (hCj j hj1 hj2 _ rfl).2.2.1) htel
  have hTN' : c.chTN.sub n ≤ c.ctx.chN.sub n := ChainData.sub_le_of_origsOK n hT hN horig
  have hcardT : Nat.card (c.chTN.sub n) = 2 ^ (Nat.card (c.ctx.chN.sub n)).factorization 2 := by
    rw [(c.chTN.check_sound n hT).2.2, (c.ctx.chN.check_sound n hN).2.2, hTord, hNord,
      RepCert.factorization_two_pow_mul_odd _ _ hodd]
  have hcov' := cover_of_sylow (N := c.ctx.chN.sub n) (T := c.chTN.sub n) (K := c.ctx.chN.sub n)
    le_rfl hTN' hcardT (c.repSet n) (by
      intro t ht ht2
      rcases hcov t ht ht2 with h1 | ⟨μ, hμ, k, hk1, hk2, hμt⟩
      · exact Or.inl h1
      · exact Or.inr ⟨μ, hμ, _, ⟨k, hk1, hk2, rfl⟩, hμt⟩)
  refine ⟨c.repSet n, ?_, hcov'⟩
  rintro _ ⟨j, hj1, hj2, rfl⟩
  exact ⟨c.ctx.chN.val_mem_sub n hN _, (hCj j hj1 hj2 _ rfl).2.2.2.1,
    RepCert.good n c.ctx _ hctx (hreps _ (hrmem j hj1 hj2))⟩

theorem ctx_ok (h : c.ok n = true) : c.ctx.ok n = true := by
  simp only [ok, Bool.and_eq_true] at h
  exact h.1.1

end FCCert

theorem coreStmt_of_cert (n : ℕ) (c : FCCert) (hc : c.ok n = true) {S : Type*} [Group S]
    (e : S ≃* c.ctx.chP.sub n) (hperf : ⁅c.ctx.chP.sub n, c.ctx.chP.sub n⁆ = c.ctx.chP.sub n)
    (hAut : ∀ τ : MulAut S, τ * τ = 1 → ∃ σ : MulAut S, ∃ ν ∈ c.ctx.chN.sub n,
      ∀ s : S, ((e ((σ * τ * σ⁻¹) s) : c.ctx.chP.sub n) : Equiv.Perm (Fin n)) =
        ν * (e s : Equiv.Perm (Fin n)) * ν⁻¹) : CoreStmt S := by
  obtain ⟨-, -, hPN, hnorm, hcent, -, -⟩ := Ctx.sound n c.ctx (c.ctx_ok n hc)
  exact coreStmt_of_perm (c.ctx.chP.sub n) (c.ctx.chN.sub n) e hPN hnorm hperf hcent hAut
    (FCCert.sound n c hc)

end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
