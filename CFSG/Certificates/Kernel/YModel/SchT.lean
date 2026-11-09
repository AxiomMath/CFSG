module

public import Certificates.Data.Kernel.YModel.ModelT
public import CFSG.YGroups.Exact.Model
public import CFSG.Certificates.Kernel.YModel.SchCard
public import CFSG.Certificates.Kernel.BenesSound
public import CFSG.Certificates.Kernel.YModel.Sound

public section

namespace CFSG.KC.YModel.Sch

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel CFSG.KC.YModel.Sem

theorem apK_eq (k N X : Nat) : apK k N X = netApply k (2 ^ k) (repU (2 ^ k) k) N X := by
  unfold apK
  rw [wid_eq]

theorem land_mask_lt (P w : Nat) : Nat.land P (Nat.sub (Nat.shiftLeft 1 w) 1) < 2 ^ w := by
  have : Nat.sub (Nat.shiftLeft 1 w) 1 < 2 ^ w := by
    rw [shl1]
    exact Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos
  exact Nat.and_lt_two_pow P this

theorem tauOK_spec {k w Z a p : Nat} {U TT NT : Nat → Nat} (h : tauOK k w U TT NT Z a p = true) :
    StagesValid k (NT a) ∧
      ((ptL (TT a) = 0 ∧ apK k (NT a) (idP k) = idP k) ∨
        (ptL (TT a) ≠ 0 ∧ p < Z ∧ ptL (TT a) = ptL (TT p) + 1 ∧
          ptP (TT a) = catW w (Nat.land (ptP (TT a)) (Nat.sub (Nat.shiftLeft 1 w) 1)) 1
            (ptP (TT p)) ∧
          apK k (NT a) (idP k) = apK k (NT p)
            (apK k (codeNet k U (Nat.land (ptP (TT a)) (Nat.sub (Nat.shiftLeft 1 w) 1))) (idP k)))) := by
  unfold tauOK at h
  obtain ⟨h1, h⟩ := andB_eq h
  refine ⟨stagesValid_of_ymodel h1, ?_⟩
  cases hl : Nat.beq (ptL (TT a)) 0
  · rw [hl] at h
    dsimp only at h
    obtain ⟨h2, h⟩ := andB_eq h
    obtain ⟨h3, h⟩ := andB_eq h
    obtain ⟨h4, h5⟩ := andB_eq h
    exact Or.inr ⟨Nat.ne_of_beq_eq_false hl, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3,
      Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩
  · rw [hl] at h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hl, Nat.eq_of_beq_eq_true h⟩

theorem tau_rep {k n w Z : Nat} {U TT NT : Nat → Nat}
    (hpt : ∀ y < Z, CodesGood k n U (codesL w (ptP (TT y)) (ptL (TT y))))
    (hnt : ∀ a < Z, ∃ p, tauOK k w U TT NT Z a p = true) :
    ∀ a < Z, StagesValid k (NT a) ∧ ∀ r < 2 ^ k,
      benesPerm k (NT a) r = compN k (wordNets k w U (ptP (TT a)) (ptL (TT a))) r := by
  suffices H : ∀ L, ∀ a < Z, ptL (TT a) = L → StagesValid k (NT a) ∧ ∀ r < 2 ^ k,
      benesPerm k (NT a) r = compN k (wordNets k w U (ptP (TT a)) (ptL (TT a))) r from
    fun a ha => H _ a ha rfl
  intro L
  induction L with
  | zero =>
    intro a ha hL
    obtain ⟨p, hp⟩ := hnt a ha
    obtain ⟨hv, h0 | ⟨hne, -⟩⟩ := tauOK_spec hp
    · refine ⟨hv, fun r hr => ?_⟩
      rw [hL]
      have e := h0.2
      rw [apK_eq] at e
      exact eq_of_idP (acts_netApply hv) (acts_id k k) e r hr
    · exact absurd hL hne
  | succ L ih =>
    intro a ha hL
    obtain ⟨p, hp⟩ := hnt a ha
    obtain ⟨hv, h0 | ⟨-, hpZ, eL, eP, e⟩⟩ := tauOK_spec hp
    · omega
    · have hxw := land_mask_lt (ptP (TT a)) w
      generalize Nat.land (ptP (TT a)) (Nat.sub (Nat.shiftLeft 1 w) 1) = x at eP e hxw
      have hcodes : codesL w (ptP (TT a)) (ptL (TT a)) = x :: codesL w (ptP (TT p)) (ptL (TT p)) := by
        rw [eL, eP, Nat.add_comm, codesL_catW (by rwa [Nat.mul_one]), codesL_one hxw]
        rfl
      have hwn : wordNets k w U (ptP (TT a)) (ptL (TT a)) =
          codeNet k U x :: wordNets k w U (ptP (TT p)) (ptL (TT p)) := by
        rw [wordNets_eq, hcodes, List.map_cons, ← wordNets_eq]
      have hp' := ih p hpZ (by omega)
      have hcx : StagesValid k (codeNet k U x) :=
        (good_codeNet (hpt a ha x (by rw [hcodes]; exact List.mem_cons_self))).2.1
      rw [apK_eq, apK_eq, apK_eq] at e
      have hc := eq_of_idP (acts_netApply hv) ((acts_netApply (P := k) hcx).comp
        (acts_netApply hp'.1)) e
      refine ⟨hv, fun r hr => ?_⟩
      rw [hwn, hc r hr, hp'.2 r hr]
      rfl

theorem tau_good {k n w Z : Nat} {U TT NT : Nat → Nat} (hn : n ≤ 2 ^ k)
    (hpt : ∀ y < Z, CodesGood k n U (codesL w (ptP (TT y)) (ptL (TT y))))
    (hnt : ∀ a < Z, ∃ p, tauOK k w U TT NT Z a p = true) :
    ∀ a < Z, Good k n (NT a) ∧
      netPerm k n (NT a) = cpermL k n U (codesL w (ptP (TT a)) (ptL (TT a))) := by
  intro a ha
  obtain ⟨hv, hc⟩ := tau_rep hpt hnt a ha
  have g1 := good_wordNets (hpt a ha)
  have hG : Good k n (NT a) := ⟨hn, hv, fun i h1 h2 => by rw [hc i h2, compN_fix _ g1 i h1 h2]⟩
  refine ⟨hG, ?_⟩
  rw [← prod_wordNets (hpt a ha)]
  ext i
  rw [netPerm_apply hG, prod_apply _ g1, hc i (by have := i.2; omega)]

theorem recT_spec {k w Z hi top a j rec : Nat} {U TT NT : Nat → Nat}
    (h : recT k w U TT NT Z hi top a j rec = true) :
    ptX rec < Z ∧
      ((ptP (TT (ptX rec)) = catW w (2 * (j + 1)) 1 (ptP (TT a)) ∧
          ptL (TT (ptX rec)) = ptL (TT a) + 1) ∨
        (codesIn w hi top (ptP rec) (ptL rec) = true ∧
          apK k (NT a) (apK k (U j) (idP k)) =
            netsApply k (wid k) (repU (wid k) k) (wordNets k w U (ptP rec) (ptL rec))
              (apK k (NT (ptX rec)) (idP k)))) := by
  unfold recT at h
  obtain ⟨h1, h⟩ := andB_eq h
  refine ⟨Nat.blt_eq.mp h1, ?_⟩
  cases hl : Nat.beq (ptL rec) 65535
  · rw [hl] at h
    dsimp only at h
    obtain ⟨h2, h3⟩ := andB_eq h
    exact Or.inr ⟨h2, Nat.eq_of_beq_eq_true h3⟩
  · rw [hl] at h
    dsimp only at h
    obtain ⟨h2, h3⟩ := andB_eq h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem recT_sem {k n w Z hi top a j rec : Nat} {U TT NT : Nat → Nat} (hn : n ≤ 2 ^ k)
    (hgt : ∀ j' < top, Good k n (U j'))
    (hnt : ∀ y < Z, Good k n (NT y) ∧
      netPerm k n (NT y) = cpermL k n U (codesL w (ptP (TT y)) (ptL (TT y))))
    (ha : a < Z) (hj : j < top) (hj3 : 2 * (j + 1) < 2 ^ w)
    (h : recT k w U TT NT Z hi top a j rec = true) : RecSem k n w U TT Z hi top a j := by
  obtain ⟨hy, hr⟩ := recT_spec h
  rcases hr with ⟨e1, e2⟩ | ⟨hc, e⟩
  · exact recSem_tree hy hj3 e1 e2
  · refine ⟨ptX rec, hy, ptP rec, ptL rec, hc, ?_⟩
    have hcr : CodesGood k n U (codesL w (ptP rec) (ptL rec)) := fun x hx => hgt _ (by
      have := codes_idx hc x hx
      omega)
    have g1 : ∀ N ∈ [U j, NT a], Good k n N := by
      intro N hN
      rcases List.mem_cons.mp hN with rfl | hN
      · exact hgt j hj
      · rw [List.mem_singleton.mp hN]
        exact (hnt a ha).1
    have g2 : ∀ N ∈ NT (ptX rec) :: wordNets k w U (ptP rec) (ptL rec), Good k n N := by
      intro N hN
      rcases List.mem_cons.mp hN with rfl | hN
      · exact (hnt _ hy).1
      · exact good_wordNets hcr N hN
    rw [apK_eq, apK_eq, apK_eq, wid_eq] at e
    have e' : netsApply k (2 ^ k) (repU (2 ^ k) k) [U j, NT a] (idP k) =
        netsApply k (2 ^ k) (repU (2 ^ k) k) (NT (ptX rec) :: wordNets k w U (ptP rec) (ptL rec))
          (idP k) := by
      rw [netsApply_cons, netsApply_cons, netsApply_cons]
      exact e
    have hp := prod_eq_of hn g1 g2 (eq_of_idP (acts_netsApply _ fun N hN => (g1 N hN).2.1)
      (acts_netsApply _ fun N hN => (g2 N hN).2.1) e')
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    rw [prod_wordNets hcr, (hnt a ha).2, (hnt _ hy).2] at hp
    rw [mul_assoc, hp, inv_mul_cancel_left]

end CFSG.KC.YModel.Sch

namespace CFSG.KC.YModel

open CFSG.KC.Loop

theorem tausOK_point {k w Z : Nat} {U TT NT : Nat → Nat} : ∀ (ps : List Nat) (a0 : Nat),
    tausOK k w U TT NT Z a0 ps = true →
      ∀ a, a0 ≤ a → a < a0 + ps.length → ∃ p, tauOK k w U TT NT Z a p = true
  | [], _, _, a, h1, h2 => by simp at h2; omega
  | p :: ps, a0, h, a, h1, h2 => by
    obtain ⟨h3, h4⟩ := Sem.andB_eq h
    rcases Nat.lt_or_ge a0 a with h5 | h5
    · exact tausOK_point ps (a0 + 1) h4 a (by omega) (by simp only [List.length_cons] at h2; omega)
    · exact ⟨p, by rw [show a = a0 by omega]; exact h3⟩

theorem schT_gen {k w Z lo hi top a0 cnt : Nat} {U TT NT : Nat → Nat} :
    ∀ (recs : List Nat) (r0 : Nat),
      List.rec (motive := fun _ => Nat → Bool)
        (fun r => Nat.beq r (Nat.mul cnt (Nat.sub hi lo)))
        (fun rec _ ih r => andB (Nat.blt r (Nat.mul cnt (Nat.sub hi lo)))
          (andB (recT k w U TT NT Z hi top (Nat.add a0 (Nat.div r (Nat.sub hi lo)))
              (Nat.add lo (Nat.mod r (Nat.sub hi lo))) rec)
            (strictB (Nat.succ r) ih)))
        recs r0 = true →
      r0 + recs.length = cnt * (hi - lo) ∧ ∀ r, r0 ≤ r → r < r0 + recs.length →
        ∃ rec, recT k w U TT NT Z hi top (a0 + r / (hi - lo)) (lo + r % (hi - lo)) rec = true := by
  intro recs
  induction recs with
  | nil =>
    intro r0 h
    refine ⟨?_, fun r h1 h2 => by simp at h2; omega⟩
    simpa using Nat.eq_of_beq_eq_true h
  | cons rec rs ih =>
    intro r0 h
    have h1 := Sem.andB_eq h
    have h2 := Sem.andB_eq h1.2
    have h3 : List.rec (motive := fun _ => Nat → Bool)
        (fun r => Nat.beq r (Nat.mul cnt (Nat.sub hi lo)))
        (fun rec _ ih r => andB (Nat.blt r (Nat.mul cnt (Nat.sub hi lo)))
          (andB (recT k w U TT NT Z hi top (Nat.add a0 (Nat.div r (Nat.sub hi lo)))
              (Nat.add lo (Nat.mod r (Nat.sub hi lo))) rec)
            (strictB (Nat.succ r) ih)))
        rs (r0 + 1) = true := h2.2
    obtain ⟨e, hr⟩ := ih (r0 + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun r h4 h5 => ?_⟩
    rcases Nat.lt_or_ge r0 r with h6 | h6
    · exact hr r (by omega) (by simp only [List.length_cons] at h5; omega)
    · have e2 : r = r0 := by omega
      subst e2
      exact ⟨rec, h2.1⟩

theorem schT_rec {k w Z lo hi top a0 cnt : Nat} {U TT NT : Nat → Nat} {recs : List Nat}
    (h : schT k w U TT NT Z lo hi top a0 cnt recs = true) (hlo : lo < hi) :
    ∀ a, a0 ≤ a → a < a0 + cnt → ∀ j, lo ≤ j → j < hi →
      ∃ rec, recT k w U TT NT Z hi top a j rec = true := by
  obtain ⟨e, hr⟩ := schT_gen recs 0 h
  intro a h1 h2 j h3 h4
  have hd : 0 < hi - lo := by omega
  have hlt : (hi - lo) * (a - a0) + (j - lo) < 0 + recs.length := by
    rw [e]
    have : (hi - lo) * (a - a0) + (j - lo) < (hi - lo) * (a - a0 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc _ < (hi - lo) * (a - a0 + 1) := this
      _ ≤ (hi - lo) * cnt := Nat.mul_le_mul_left _ (by omega)
      _ = cnt * (hi - lo) := Nat.mul_comm _ _
  have := hr ((hi - lo) * (a - a0) + (j - lo)) (by omega) hlt
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega), Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (by omega)] at this
  rwa [show a0 + (a - a0) = a by omega, show lo + (j - lo) = j by omega] at this

theorem card_arrClosure_of_schT {k n m w t : Nat} {F Nf U WP WL : Nat → Nat}
    {off bp Z LP LL : Nat → Nat} {TT NT : Nat → Nat → Nat}
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hU : ∀ c < m, U c = Nf c)
    (hoff : off 0 = m) (hmono : ∀ i < t, off i ≤ off (i + 1))
    (hgen0 : ∀ j, off 0 ≤ j → j < off 1 → genOK k w U WP WL 0 m j 0 false = true)
    (hgen : ∀ i, 0 < i → i < t → ∀ j, off i ≤ j → j < off (i + 1) →
      genOK k w U WP WL (off (i - 1)) (off i) j (bp (i - 1)) true = true)
    (hbp : ∀ i < t, bp i < n) (hb0 : ∀ i < t, ptX (TT i 0) = bp i ∧ 0 < Z i)
    (hpts : ∀ i < t, pointsOK k (TT i) (Z i) = true)
    (htr : ∀ i < t, ∀ a < Z i, transOK k w U (TT i) (bp i) (off i) (off (i + 1)) a 1 = true)
    (hnt : ∀ i < t, ∀ a < Z i, ∃ p, tauOK k w U (TT i) (NT i) (Z i) a p = true)
    (hrec : ∀ i < t, ∀ a < Z i, ∀ j, off i ≤ j → j < off (i + 1) →
      ∃ rec, recT k w U (TT i) (NT i) (Z i) (off (i + 1)) (off t) a j rec = true)
    (hlet : ∀ c < m, sweqK k w U (2 * (c + 1)) 1 (LP c) (LL c) = true ∧
      codesIn w m (off t) (LP c) (LL c) = true)
    (hk : k ≤ 32 := by decide) (hw : 2 * m < 2 ^ w := by decide) (hm : 0 < m := by decide) :
    Nat.card (CFSG.YGroups.arrClosure n (linesA (fun _ => n) 32 F m)) =
      ∏ i ∈ Finset.range t, Z i :=
  Sch.card_schR hk hw hm size_linesA' (fun c hc i hi => getElem_linesA' hc hi) h hU hoff hmono
    hgen0 hgen hbp hb0 hpts htr
    (fun i hi a ha j hj1 hj2 hn _ hgt hpt hj3 => by
      obtain ⟨rec, hr⟩ := hrec i hi a ha j hj1 hj2
      exact Sch.recT_sem hn hgt (Sch.tau_good hn hpt (hnt i hi)) ha
        (lt_of_lt_of_le hj2 (Sch.off_le hmono (i + 1) t (by omega) le_rfl)) hj3 hr)
    hlet

end CFSG.KC.YModel

end
