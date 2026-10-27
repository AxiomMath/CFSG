module

public import CFSG.Certificates.Kernel.Enum.ZCH
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimple

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

variable {n w : Nat}

theorem eq22_iff {m p q r s : Nat} :
    eq22 n w m p q r s = true ↔ ∀ i < n, pg w m p (pg w m q i) = pg w m r (pg w m s i) := by
  unfold eq22
  simp only [PK.allN_iff, beq_iff]

theorem ne_comm_of_eq22 {p q : Nat} {gp gq : Equiv.Perm (Fin n)}
    (h : eq22 n w (mask w) p q q p = false) (hp : PRep n w p gp) (hq : PRep n w q gq) :
    gp * gq ≠ gq * gp := by
  intro hc
  have ht : eq22 n w (mask w) p q q p = true := eq22_iff.2 fun i hi => by
    have e1 := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨i, hi⟩ : Fin n) : Nat)) hc
    simp only [Equiv.Perm.mul_apply] at e1
    rw [prep_at hq hi, hp (gq ⟨i, hi⟩), prep_at hp hi, hq (gp ⟨i, hi⟩)]
    exact e1
  rw [h] at ht
  exact Bool.false_ne_true ht

theorem ne_one_of_moves {P q : Nat} {g : Equiv.Perm (Fin n)}
    (h : Nat.beq (pg w (mask w) P q) q = false) (hq : q < n) (hP : PRep n w P g) : g ≠ 1 := by
  intro e
  rw [prep_at hP hq, e] at h
  simp only [Equiv.Perm.one_apply] at h
  rw [Nat.beq_refl] at h
  exact absurd h (by decide)

theorem eq22_prep {p q r s : Nat} {gp gq gr gs : Equiv.Perm (Fin n)}
    (h : eq22 n w (mask w) p q r s = true) (hp : PRep n w p gp) (hq : PRep n w q gq)
    (hr : PRep n w r gr) (hs : PRep n w s gs) : gp * gq = gr * gs :=
  Equiv.ext fun x => Fin.ext (by
    have e := eq22_iff.1 h x x.2
    rw [hq x, hp (gq x), hs x, hr (gs x)] at e
    exact e)

theorem prep_of_beq_idn {e idn : Nat} (h : Nat.beq e idn = true) (hid : PRep n w idn 1) :
    PRep n w e 1 := by
  rw [Nat.eq_of_beq_eq_true h]
  exact hid

theorem vChk_prep {T : Nat → Nat} {sh lm rb rm pm p o i h hi : Nat} {Z Zi VP VC : Nat → Nat}
    {gz g u : Equiv.Perm (Fin n)}
    (hv : vChk T sh lm rb rm n w (mask w) pm Z Zi VP VC h hi p o i = true)
    (hu : PRep n w (rperm T sh lm rb rm pm i) u)
    (hZ : ∀ e < p, PRep n w (Z e) (gz ^ e) ∧ PRep n w (Zi e) (gz ^ e)⁻¹)
    (hh : PRep n w h g) (hhi : PRep n w hi g⁻¹) :
    ∀ e < p, ∃ f < p, g * (gz ^ e * u * (gz ^ e)⁻¹) * g⁻¹ = gz ^ f * u * (gz ^ f)⁻¹ := by
  unfold vChk at hv
  simp only [PK.strictB_eq, PK.allN_iff, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hv
  have hVP : ∀ e < p, PRep n w (VP (Nat.add o e)) (gz ^ e * u * (gz ^ e)⁻¹) := fun e he =>
    eq3_prep (hv e he).1 (hZ e he).1 hu (hZ e he).2
  intro e he
  obtain ⟨-, hf, h2⟩ := hv e he
  exact ⟨_, hf, prep_unique (eq3_prep h2 hh (hVP e he) hhi) (hVP _ hf)⟩

theorem vRange_iff {T : Nat → Nat} {sh lm rb rm m pm h hi p lo cnt : Nat}
    {Z Zi VP VC : Nat → Nat} :
    vRange T sh lm rb rm n w m pm Z Zi VP VC h hi p lo cnt = true ↔
      ∀ t < cnt, vChk T sh lm rb rm n w m pm Z Zi VP VC h hi p (p * t) (lo + t) = true := by
  unfold vRange
  exact PK.allN_iff

theorem hChk_sound {T : Nat → Nat} {sh lm rb rm m nw pm nH idn h1 h2 nR k : Nat}
    {REP : Nat → Nat} (h : hChk T sh lm rb rm n w m nw pm nH idn h1 h2 nR REP k = true) :
    (k = 0 → Nat.beq (rperm T sh lm rb rm pm k) idn = true) ∧
    (k ≠ 0 → fld(rget T sh lm rb rm k, nw, 255) < k ∧
      eq2 n w m (rperm T sh lm rb rm pm k) (rperm T sh lm rb rm pm fld(rget T sh lm rb rm k, nw, 255))
        (nIf(Nat.beq fld(rget T sh lm rb rm k, Nat.add nw 8, 15) 0, h1, h2)) = true) ∧
    fld(rget T sh lm rb rm k, Nat.add nw 12, 255) < nH ∧
    fld(rget T sh lm rb rm k, Nat.add nw 20, 255) < nH ∧
    eq2 n w m (rperm T sh lm rb rm pm fld(rget T sh lm rb rm k, Nat.add nw 12, 255))
      (rperm T sh lm rb rm pm k) h1 = true ∧
    eq2 n w m (rperm T sh lm rb rm pm fld(rget T sh lm rb rm k, Nat.add nw 20, 255))
      (rperm T sh lm rb rm pm k) h2 = true ∧
    (hCi T sh lm rb rm nw k = 15 → Nat.beq (rperm T sh lm rb rm pm k) idn = true) ∧
    (hCi T sh lm rb rm nw k ≠ 15 → fld(rget T sh lm rb rm k, Nat.add nw 28, 255) < nH ∧
      hCi T sh lm rb rm nw k < nR ∧
      eq22 n w m (rperm T sh lm rb rm pm k)
        (rperm T sh lm rb rm pm fld(rget T sh lm rb rm k, Nat.add nw 28, 255))
        (rperm T sh lm rb rm pm fld(rget T sh lm rb rm k, Nat.add nw 28, 255))
        (rperm T sh lm rb rm pm (REP (hCi T sh lm rb rm nw k))) = true) := by
  unfold hChk at h
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hA, h1, h2, h3, h4, hB⟩ := h
  refine ⟨fun hk => ?_, fun hk => ?_, h1, h2, h3, h4, fun hc => ?_, fun hc => ?_⟩
  · exact bIf_true ((beq_iff _ _).2 hk) hA
  · have hc : Nat.beq k (nat_lit 0) = false := by
      cases hb : Nat.beq k (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hk
    have h0 := bIf_false hc hA
    simp only [Bool.and_eq_true, Nat.blt_eq] at h0
    exact h0
  · exact bIf_true ((beq_iff _ _).2 hc) hB
  · have hc' : Nat.beq (hCi T sh lm rb rm nw k) (nat_lit 15) = false := by
      cases hb : Nat.beq (hCi T sh lm rb rm nw k) (nat_lit 15)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hc
    have h0 := bIf_false hc' hB
    simp only [Bool.and_eq_true, Nat.blt_eq, PK.strictB_eq] at h0
    exact h0

theorem hRange_iff {T : Nat → Nat} {sh lm rb rm m nw pm nH idn h1 h2 nR cnt : Nat}
    {REP : Nat → Nat} :
    hRange T sh lm rb rm n w m nw pm nH idn h1 h2 nR REP cnt = true ↔
      ∀ k < cnt, hChk T sh lm rb rm n w m nw pm nH idn h1 h2 nR REP k = true := by
  unfold hRange
  exact PK.allN_iff

theorem listChk_iff {nH i : Nat} {f : Nat → Nat} {L : List Nat} :
    List.rec (motive := fun _ => Bool) true
      (fun l _ ih => bAnd(Nat.blt l nH, bAnd(Nat.beq (f l) i, ih))) L = true ↔
      ∀ l ∈ L, l < nH ∧ f l = i := by
  induction L with
  | nil => simp
  | cons l L ih =>
    change (Nat.blt l nH && (Nat.beq (f l) i && _)) = true ↔ _
    rw [Bool.and_eq_true, Bool.and_eq_true, ih, Nat.blt_eq, beq_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem lpt_prep {T : Nat → Nat} {sh lm rb rm pm : Nat} {s : Nat → Equiv.Perm (Fin n)} :
    ∀ {L : List Nat}, (∀ l ∈ L, PRep n w (rperm T sh lm rb rm pm l) (s l)) →
      ∀ q (hq : q < n), lpt T sh lm rb rm w (mask w) pm L q = ((L.map s).prod ⟨q, hq⟩ : Nat)
  | [], _, q, _ => rfl
  | l :: L, hs, q, hq => by
    have ih := lpt_prep (L := L) (fun l' hl' => hs l' (List.mem_cons_of_mem _ hl')) q hq
    change strictN (lpt T sh lm rb rm w (mask w) pm L q)
      (fun v => pg w (mask w) (rperm T sh lm rb rm pm l) v) = _
    rw [PK.strictN_eq, ih, hs l List.mem_cons_self, List.map_cons, List.prod_cons]
    rfl

theorem ncOK_sound {T : Nat → Nat} {sh lm rb rm nw pm nH hh i : Nat} {L : List Nat}
    {s : Nat → Equiv.Perm (Fin n)} {g : Equiv.Perm (Fin n)}
    (h : ncOK T sh lm rb rm n w (mask w) nw pm nH hh i L = true) (hg : PRep n w hh g)
    (hs : ∀ l ∈ L, PRep n w (rperm T sh lm rb rm pm l) (s l)) :
    (∀ l ∈ L, l < nH ∧ hCi T sh lm rb rm nw l = i) ∧ (L.map s).prod = g := by
  unfold ncOK at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, beq_iff] at h
  refine ⟨listChk_iff.1 h.1, Equiv.ext fun x => Fin.ext ?_⟩
  rw [← lpt_prep hs x x.2, ← h.2 x x.2]
  exact hg x

theorem hList_simple {T : Nat → Nat} {sh lm rb rm nw iw nH idn h1 h2 nR o1 o2 : Nat}
    {REP : Nat → Nat} {NC1 NC2 : Nat → List Nat} {g1 g2 : Equiv.Perm (Fin n)}
    (hH : ∀ k < nH, hChk T sh lm rb rm n w (mask w) nw (mask (n * w)) nH idn h1 h2 nR REP k = true)
    (hn : 0 < nH) (hid : PRep n w idn 1) (hg1 : PRep n w h1 g1) (hg2 : PRep n w h2 g2)
    (ho1 : 0 < o1) (ho2 : 0 < o2) (hp1 : g1 ^ o1 = 1) (hp2 : g2 ^ o2 = 1)
    (hR : nR < 15) (hrep : ∀ i < nR, REP i < nH)
    (hnc1 : ∀ i < nR, ncOK T sh lm rb rm n w (mask w) nw (mask (n * w)) nH h1 i (NC1 i) = true)
    (hnc2 : ∀ i < nR, ncOK T sh lm rb rm n w (mask w) nw (mask (n * w)) nH h2 i (NC2 i) = true)
    (hnab : g1 * g2 ≠ g2 * g1) :
    ∃ s : Nat → Equiv.Perm (Fin n),
      (∀ k < nH, PRep n w (rperm T sh lm rb rm (mask (n * w)) k) (s k)) ∧
      IsSimpleGroup ↥(Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n)))) ∧
      ¬ IsMulCommutative ↥(Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n)))) ∧
      ∀ k < nH, s k ∈ Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n))) := by
  classical
  set pm := mask (n * w)
  set par : Nat → Nat := fun k => fld(rget T sh lm rb rm k, nw, 255)
  set gn : Nat → Nat := fun k => fld(rget T sh lm rb rm k, Nat.add nw 8, 15)
  have hsel : ∀ k, PRep n w (nIf(Nat.beq (gn k) 0, h1, h2))
      (if !Nat.beq (gn k) 0 then g2 else g1) := fun k => by
    cases hb : Nat.beq (gn k) 0
    · exact hg2
    · exact hg1
  have hex : ∀ k, ∃ g : Equiv.Perm (Fin n), k < nH → PRep n w (rperm T sh lm rb rm pm k) g := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < nH
      · by_cases h0 : k = 0
        · exact ⟨1, fun _ => prep_of_beq_idn ((hChk_sound (hH k hk)).1 h0) hid⟩
        · obtain ⟨hp, he⟩ := (hChk_sound (hH k hk)).2.1 h0
          obtain ⟨g, hg⟩ := ih _ hp
          exact ⟨g * _, fun _ => eq2_prep he (hg (by omega)) (hsel k)⟩
      · exact ⟨1, fun h => absurd h hk⟩
  choose s hs using hex
  have hs0 : s 0 = 1 := prep_unique (hs 0 hn) (prep_of_beq_idn ((hChk_sound (hH 0 hn)).1 rfl) hid)
  set cls : Nat → Option (Nat × Nat) := fun k =>
    if hCi T sh lm rb rm nw k = 15 then none
    else some (fld(rget T sh lm rb rm k, Nat.add nw 28, 255), hCi T sh lm rb rm nw k)
  have hsimp := simpleGroup_of_cert g1 g2 nH hn s hs0 par (fun k => !Nat.beq (gn k) 0)
    (fun k hk0 hk => by
      obtain ⟨hp, he⟩ := (hChk_sound (hH k hk)).2.1 (by omega)
      exact ⟨hp, prep_unique (hs k hk) (eq2_prep he (hs _ (by omega)) (hsel k))⟩)
    o1 o2 ho1 ho2 hp1 hp2
    (fun k => fld(rget T sh lm rb rm k, Nat.add nw 12, 255))
    (fun k => fld(rget T sh lm rb rm k, Nat.add nw 20, 255))
    (fun k hk => by
      obtain ⟨-, -, h1, h2, h3, h4, -⟩ := hChk_sound (hH k hk)
      exact ⟨h1, h2, prep_unique (eq2_prep h3 (hs k hk) hg1) (hs _ h1),
        prep_unique (eq2_prep h4 (hs k hk) hg2) (hs _ h2)⟩)
    nR REP hrep cls
    (fun k hk => by
      obtain ⟨-, -, -, -, -, -, hc1, hc2⟩ := hChk_sound (hH k hk)
      by_cases hc : hCi T sh lm rb rm nw k = 15
      · simp only [cls, hc, ↓reduceIte]
        exact prep_unique (hs k hk) (prep_of_beq_idn (hc1 hc) hid)
      · simp only [cls, hc, ↓reduceIte]
        obtain ⟨hu, hi, he⟩ := hc2 hc
        refine ⟨hu, hi, ?_⟩
        have hr := hs _ (hrep _ hi)
        exact (eq22_prep he (hs k hk) (hs _ hu) (hs _ hu) hr))
    (fun i b => if b then NC2 i else NC1 i)
    (fun i hi b => by
      have key : ∀ (hh : Nat) (g : Equiv.Perm (Fin n)) (L : List Nat), PRep n w hh g →
          ncOK T sh lm rb rm n w (mask w) nw pm nH hh i L = true →
          (∀ l ∈ L, l < nH ∧ (cls l).map Prod.snd = some i) ∧ (L.map s).prod = g := by
        intro hh g L hg hL
        have hL1 := (listChk_iff.1 (by
          unfold ncOK at hL
          simp only [PK.bAnd_eq, Bool.and_eq_true] at hL
          exact hL.1))
        have hsL : ∀ l ∈ L, PRep n w (rperm T sh lm rb rm pm l) (s l) := fun l hl =>
          hs l (hL1 l hl).1
        obtain ⟨hc, hp⟩ := ncOK_sound hL hg hsL
        refine ⟨fun l hl => ⟨(hc l hl).1, ?_⟩, hp⟩
        have e : hCi T sh lm rb rm nw l = i := (hc l hl).2
        have hne : hCi T sh lm rb rm nw l ≠ 15 := by omega
        simp only [cls, hne, ↓reduceIte, Option.map_some]
        rw [e]
      cases b
      · exact key h1 g1 _ hg1 (hnc1 i hi)
      · exact key h2 g2 _ hg2 (hnc2 i hi))
    hnab
  exact ⟨s, hs, hsimp⟩

end CFSG.KC.EnumSound

end
