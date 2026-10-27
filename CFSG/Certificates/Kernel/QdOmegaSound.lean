module

public import Certificates.Data.Kernel.QdOmega
public import CFSG.Certificates.Kernel.Sym6SqSound

public section

namespace CFSG.KC.QdOm

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.Sym6Sq
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.EvenSporadicStandard.M24Std

theorem linK_zero : ∀ y : List ℕ, linK y 0 = 0
  | [] => rfl
  | a :: y => by rw [linK_cons, linK_zero y]; simp

theorem linK_nil (d : ℕ) : linK [] d = 0 := rfl

theorem xor_cc (c X Y : ℕ) : X ^^^ Y = c ^^^ X ^^^ (c ^^^ Y) := by
  rw [Nat.xor_assoc c X, ← Nat.xor_assoc X c Y, Nat.xor_comm X c, Nat.xor_assoc c X Y,
    ← Nat.xor_assoc c c, Nat.xor_self, Nat.zero_xor]

theorem linK_xor : ∀ (y : List ℕ) (a b : ℕ), linK y (a ^^^ b) = linK y a ^^^ linK y b
  | [], _, _ => by simp [linK_nil]
  | c :: y, a, b => by
    rw [linK_cons, linK_cons, linK_cons, xor_div_two, linK_xor y, Nat.testBit_xor]
    cases a.testBit 0 <;> cases b.testBit 0 <;> simp <;>
      first | ac_rfl | exact xor_cc _ _ _

theorem linK_comp (y : List ℕ) : ∀ (P : List ℕ) (k : ℕ),
    linK y (linK P k) = linK (P.map (linK y)) k
  | [], _ => linK_zero y
  | p :: P, k => by
    rw [linK_cons, List.map_cons, linK_cons, linK_xor, linK_comp y P]
    by_cases h : k.testBit 0 = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, linK_zero]

theorem linK_append : ∀ (l z : List ℕ) (v c : ℕ), v < 2 ^ l.length →
    linK (l ++ z) (v + 2 ^ l.length * c) = linK l v ^^^ linK z c
  | [], z, v, c, hv => by
    have : v = 0 := by simpa using hv
    subst this
    simp [linK_zero]
  | a :: l, z, v, c, hv => by
    rw [List.cons_append, linK_cons, linK_cons]
    have hlen : (a :: l).length = l.length + 1 := rfl
    rw [hlen] at hv ⊢
    have e2 : 2 ^ (l.length + 1) * c = 2 * (2 ^ l.length * c) := by ring
    have hp : (2 : ℕ) ^ (l.length + 1) = 2 * 2 ^ l.length := by ring
    rw [e2]
    have h1 : (v + 2 * (2 ^ l.length * c)).testBit 0 = v.testBit 0 := by
      rw [Nat.testBit_zero, Nat.testBit_zero]
      congr 1
      apply propext
      constructor <;> intro h <;> omega
    have h2 : (v + 2 * (2 ^ l.length * c)) / 2 = v / 2 + 2 ^ l.length * c := by omega
    have h3 : v / 2 < 2 ^ l.length := by omega
    rw [h1, h2, linK_append l z (v / 2) c h3, Nat.xor_assoc]

theorem foldl_filter_xor (p : ℕ → Bool) (f : ℕ → ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    (l.filter p).foldl (fun a i => a ^^^ f i) acc =
      acc ^^^ l.foldr (fun i r => (if p i = true then f i else 0) ^^^ r) 0
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.filter_cons, List.foldr_cons]
    by_cases h : p i = true
    · rw [if_pos h, if_pos h, List.foldl_cons, foldl_filter_xor p f l, Nat.xor_assoc]
    · rw [if_neg h, if_neg h, foldl_filter_xor p f l, Nat.zero_xor]

theorem qdLin_eq_linK (y0 y1 y2 y3 y4 y5 k : ℕ) :
    qdLin [y0, y1, y2, y3, y4, y5] k = linK [y0, y1, y2, y3, y4, y5] k := by
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  unfold qdLin
  rw [hr, foldl_filter_xor]
  simp only [linK_cons, linK_nil, Nat.testBit_div_two, List.foldr_cons, List.foldr_nil,
    Nat.zero_xor, Nat.xor_zero, List.getD_cons_zero, List.getD_cons_succ]

@[expose] def fxv (c : ℕ) : ℕ := if c = 0 then 24 else if c = 1 then 0 else 8

theorem fx_cls : ∀ k < 64, qdFxTab.getD k 99 = fxv (clsK k) := by decide +kernel

theorem clsK_le (k : ℕ) : clsK k ≤ 2 := by
  unfold clsK
  cases Nat.beq k 0 <;> cases Nat.blt 0 (Nat.land fmK (Nat.shiftLeft 1 k)) <;> decide

theorem fxv_inj : ∀ a ≤ 2, ∀ b ≤ 2, fxv a = fxv b → a = b := by decide

theorem psi_tab : ∀ k < 64, lane psiP (6 * k) = qdPsiTab.getD k 0 ∧
    qdPsiTab.getD k 0 = linK [3, 1, 12, 4, 48, 16] k := by decide +kernel

theorem psiI_tab : ∀ k < 64, lane psiIP (6 * k) = qdPsiInvTab.getD k 0 ∧
    qdPsiInvTab.getD k 0 = linK [2, 3, 8, 12, 32, 48] k := by decide +kernel

theorem plK_lt : ∀ p ∈ plK, p.1 < 64 ∧ p.2 < 64 := by decide

theorem d16_mem {v : ℕ} : v ∈ d16 ↔ v < 16 := by
  have : d16 = List.range 16 := rfl
  rw [this, List.mem_range]

theorem allPr_iff (L : List (ℕ × ℕ)) (f : ℕ → ℕ → Bool) :
    allPr L f = true ↔ ∀ p ∈ L, f p.1 p.2 = true := by
  induction L with
  | nil => simp [allPr]
  | cons p L ih =>
    change CFSG.KC.Ord.andB (f p.1 p.2) (allPr L f) = true ↔ _
    rw [andB_iff, ih, List.forall_mem_cons]

theorem memPr_iff (a b : ℕ) (L : List (ℕ × ℕ)) : memPr a b L = true ↔ (a, b) ∈ L := by
  induction L with
  | nil => simp [memPr]
  | cons p L ih =>
    change CFSG.KC.Ord.orB (CFSG.KC.Ord.andB (Nat.beq p.1 a) (Nat.beq p.2 b)) (memPr a b L) = true ↔ _
    rw [orB_iff, andB_iff, beq_iff, beq_iff, ih, List.mem_cons]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · left
        rw [← h1, ← h2]
      · exact Or.inr h
    · rintro (h | h)
      · left
        subst h
        exact ⟨rfl, rfl⟩
      · exact Or.inr h

theorem cls_of_fx {y : List ℕ} (hy : ∀ a ∈ y, a < 64) {k : ℕ} (hk : k < 64)
    (h : qdFxTab.getD (linK y k) 99 = qdFxTab.getD k 99) : clsK (linK y k) = clsK k := by
  rw [fx_cls _ (linK_lt y hy k), fx_cls k hk] at h
  exact fxv_inj _ (clsK_le _) _ (clsK_le _) h

theorem tabOK_true {T a1 b1 a2 b2 : ℕ} (h : tabOK T a1 b1 a2 b2 = true) :
    ∀ v < 16, lane T (6 * v) = linK [a1, b1, a2, b2] v := by
  unfold tabOK at h
  rw [allL_iff] at h
  intro v hv
  exact beq_iff.1 (h v (d16_mem.2 hv))

theorem conK_true {Q T a1 b1 a2 b2 a3 b3 : ℕ} (h : conK Q T a1 b1 a2 b2 a3 b3 = true) :
    lane T 18 = lane Q (6 * a1) ∧ lane T 6 = lane Q (6 * b1) ∧ lane T 72 = lane Q (6 * a2) ∧
      lane T 24 = lane Q (6 * b2) ∧ a3 ^^^ b3 = lane Q (6 * a3) ∧ a3 = lane Q (6 * b3) := by
  unfold conK at h
  simp only [andB_iff, beq_iff] at h
  exact h

theorem concl_of {tab : List ℕ} {Q : ℕ} {P' : List ℕ}
    (hQ : ∀ k < 64, lane Q (6 * k) = tab.getD k 0 ∧ tab.getD k 0 = linK P' k)
    {T a1 b1 a2 b2 a3 b3 : ℕ} (hlt : ∀ a ∈ [a1, b1, a2, b2, a3, b3], a < 64)
    (hT : ∀ v < 16, lane T (6 * v) = linK [a1, b1, a2, b2] v)
    (hc : conK Q T a1 b1 a2 b2 a3 b3 = true) :
    ∀ k ∈ List.range 64, qdLin [a1, b1, a2, b2, a3, b3] (qdPsiTab.getD k 0) =
      tab.getD (qdLin [a1, b1, a2, b2, a3, b3] k) 0 := by
  intro k hk
  have hk' := List.mem_range.1 hk
  have hpsi : qdPsiTab.getD k 0 = linK [3, 1, 12, 4, 48, 16] k := (psi_tab k hk').2
  have hlk : linK [a1, b1, a2, b2, a3, b3] k < 64 := linK_lt _ hlt k
  rw [hpsi, qdLin_eq_linK, qdLin_eq_linK, (hQ _ hlk).2, linK_comp, linK_comp]
  congr 1
  have hlo : ∀ v < 16, linK [a1, b1, a2, b2, a3, b3] v = lane T (6 * v) := by
    intro v hv
    have e : linK ([a1, b1, a2, b2] ++ [a3, b3]) (v + 2 ^ 4 * 0) =
        linK [a1, b1, a2, b2] v ^^^ linK [a3, b3] 0 := linK_append _ _ v 0 hv
    rw [linK_zero, Nat.xor_zero, Nat.mul_zero, Nat.add_zero] at e
    rw [hT v hv, ← e]
    rfl
  have h48 : linK [a1, b1, a2, b2, a3, b3] 48 = a3 ^^^ b3 := by
    have e : linK ([a1, b1, a2, b2] ++ [a3, b3]) (0 + 2 ^ 4 * 3) =
        linK [a1, b1, a2, b2] 0 ^^^ linK [a3, b3] 3 := linK_append _ _ 0 3 (by norm_num)
    rw [linK_zero, Nat.zero_xor] at e
    rw [show (48 : ℕ) = 0 + 2 ^ 4 * 3 by norm_num]
    rw [show [a1, b1, a2, b2, a3, b3] = [a1, b1, a2, b2] ++ [a3, b3] from rfl, e]
    simp [linK_cons, linK_zero]
  have h16 : linK [a1, b1, a2, b2, a3, b3] 16 = a3 := by
    have e : linK ([a1, b1, a2, b2] ++ [a3, b3]) (0 + 2 ^ 4 * 1) =
        linK [a1, b1, a2, b2] 0 ^^^ linK [a3, b3] 1 := linK_append _ _ 0 1 (by norm_num)
    rw [linK_zero, Nat.zero_xor] at e
    rw [show (16 : ℕ) = 0 + 2 ^ 4 * 1 by norm_num]
    rw [show [a1, b1, a2, b2, a3, b3] = [a1, b1, a2, b2] ++ [a3, b3] from rfl, e]
    simp [linK_cons, linK_zero]
  have hq : ∀ a ∈ [a1, b1, a2, b2, a3, b3], lane Q (6 * a) = linK P' a := fun a ha =>
    ((hQ a (hlt a ha)).1).trans (hQ a (hlt a ha)).2
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := conK_true hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlo 3 (by norm_num), ← hq a1 (by simp)]
    exact c1
  · rw [hlo 1 (by norm_num), ← hq b1 (by simp)]
    exact c2
  · rw [hlo 12 (by norm_num), ← hq a2 (by simp)]
    exact c3
  · rw [hlo 4 (by norm_num), ← hq b2 (by simp)]
    exact c4
  · rw [h48, ← hq a3 (by simp)]
    exact c5
  · rw [h16, ← hq b3 (by simp)]
    exact c6

theorem chkL_of {T x off : ℕ} (h : ∀ v < 16, clsK (lane T (6 * v) ^^^ x) = clsK (v + off)) :
    chkL T x off = true := by
  unfold chkL
  rw [allL_iff]
  intro v hv
  exact beq_iff.2 (h v (d16_mem.1 hv))

theorem body_sound {T a1 b1 a2 b2 a3 b3 : ℕ} (hlt : ∀ a ∈ [a1, b1, a2, b2, a3, b3], a < 64)
    (hT : tabOK T a1 b1 a2 b2 = true)
    (h3 : chkL T 0 0 = true →
      CFSG.KC.Ord.andB (chkL T a3 16) (CFSG.KC.Ord.andB (chkL T b3 32) (chkL T (a3 ^^^ b3) 48)) = true →
      CFSG.KC.Ord.orB (conK psiP T a1 b1 a2 b2 a3 b3) (conK psiIP T a1 b1 a2 b2 a3 b3) = true) :
    QdEnumBody [a1, b1, a2, b2, a3, b3] := by
  intro hyp
  have hT' := tabOK_true hT
  have hcls : ∀ k < 64, clsK (linK [a1, b1, a2, b2, a3, b3] k) = clsK k := fun k hk =>
    cls_of_fx hlt hk (by rw [← qdLin_eq_linK]; exact hyp k (List.mem_range.2 hk))
  have hsplit : ∀ v < 16, ∀ c, linK [a1, b1, a2, b2, a3, b3] (v + 16 * c) =
      lane T (6 * v) ^^^ linK [a3, b3] c := by
    intro v hv c
    rw [hT' v hv]
    exact linK_append [a1, b1, a2, b2] [a3, b3] v c hv
  have hchk : ∀ c ≤ 3, chkL T (linK [a3, b3] c) (16 * c) = true := by
    intro c hc
    refine chkL_of fun v hv => ?_
    rw [← hsplit v hv c]
    exact hcls _ (by omega)
  have e0 : linK [a3, b3] 0 = 0 := linK_zero _
  have e1 : linK [a3, b3] 1 = a3 := by simp [linK_cons, linK_zero]
  have e2 : linK [a3, b3] 2 = b3 := by simp [linK_cons, linK_zero]
  have e3 : linK [a3, b3] 3 = a3 ^^^ b3 := by simp [linK_cons, linK_zero]
  have k0 := hchk 0 (by norm_num)
  have k1 := hchk 1 (by norm_num)
  have k2 := hchk 2 (by norm_num)
  have k3 := hchk 3 (by norm_num)
  rw [e0] at k0
  rw [e1] at k1
  rw [e2] at k2
  rw [e3] at k3
  have h := h3 k0 (andB_iff.2 ⟨k1, andB_iff.2 ⟨k2, k3⟩⟩)
  rcases orB_iff.1 h with h | h
  · exact Or.inl (concl_of psi_tab hlt hT' h)
  · exact Or.inr (concl_of psiI_tab hlt hT' h)

theorem fxv_zero {c : ℕ} (h : fxv c = 0) : c = 1 := by
  unfold fxv at h
  split_ifs at h with h0 h1 <;> omega

theorem mem_plK_of [hc : Fact (covK = true)] {p : ℕ × ℕ} (hp : p ∈ qdPairs) : p ∈ plK := by
  unfold qdPairs at hp
  rw [List.mem_filter] at hp
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨a, ha, hpa⟩ := List.mem_flatMap.1 hp1
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hpa
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hp2
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp2
  have hab : a ^^^ b < 64 := Nat.xor_lt_two_pow (n := 6) ha' hb'
  rw [fx_cls a ha'] at h1
  rw [fx_cls b hb'] at h2
  rw [fx_cls _ hab] at h3
  have hcov := hc.out
  unfold covK at hcov
  rw [allN_iff] at hcov
  have := hcov a ha'
  rw [impB_iff] at this
  have := this (beq_iff.2 (fxv_zero h1))
  rw [allN_iff] at this
  have := this b hb'
  rw [impB_iff, andB_iff, beq_iff, beq_iff, memPr_iff] at this
  exact this ⟨fxv_zero h2, fxv_zero h3⟩

theorem enum_at {O : List (ℕ × ℕ)} (hE : enumK psiP psiIP O plK = true) {p1 p2 p3 : ℕ × ℕ}
    (hp1 : p1 ∈ O) (hO : ∀ p ∈ O, p ∈ plK) (hp2 : p2 ∈ plK) (hp3 : p3 ∈ plK) :
    QdEnumBody [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2] := by
  unfold enumK at hE
  rw [allPr_iff] at hE
  have h := hE p1 hp1
  rw [allPr_iff] at h
  have h' := h p2 hp2
  rw [strictA_eq, andB_iff] at h'
  obtain ⟨hT, himp⟩ := h'
  rw [impB_iff] at himp
  have hlt : ∀ a ∈ [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2], a < 64 := by
    have q1 := plK_lt p1 (hO p1 hp1)
    have q2 := plK_lt p2 hp2
    have q3 := plK_lt p3 hp3
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  refine body_sound hlt hT fun h0 hk => ?_
  have h3 := himp h0
  unfold enum3 at h3
  rw [allPr_iff] at h3
  have h3' := h3 p3 hp3
  rw [strictA_eq, impB_iff] at h3'
  exact h3' hk

theorem qdEnum_of (h1 : enumK psiP psiIP plA plK = true) (h2 : enumK psiP psiIP plB plK = true)
    (hc : covK = true) : QdEnum := by
  have : Fact (covK = true) := ⟨hc⟩
  intro p1 hp1 p2 hp2 p3 hp3
  have q1 := mem_plK_of hp1
  have hsplit : plK = plA ++ plB := rfl
  rw [hsplit, List.mem_append] at q1
  rcases q1 with q1 | q1
  · exact enum_at h1 q1 (fun p hp => by rw [hsplit]; exact List.mem_append_left _ hp)
      (mem_plK_of hp2) (mem_plK_of hp3)
  · exact enum_at h2 q1 (fun p hp => by rw [hsplit]; exact List.mem_append_right _ hp)
      (mem_plK_of hp2) (mem_plK_of hp3)

theorem allI_cons (x : ℕ) (L : List ℕ) (test : ℕ → ℕ → Bool) (k : ℕ) :
    allI (x :: L) test k = CFSG.KC.Ord.andB (test x k) (strictA (Nat.succ k) (allI L test)) := rfl

theorem allI_iff (test : ℕ → ℕ → Bool) : ∀ (L : List ℕ) (k : ℕ),
    allI L test k = true ↔ ∀ i (hi : i < L.length), test L[i] (k + i) = true
  | [], k => by simp [allI]
  | x :: L, k => by
    rw [allI_cons, andB_iff, strictA_eq, allI_iff test L]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := h1 i (by simpa using hi)
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 i] using this
    · intro h
      have h0 := h 0 (by simp)
      rw [List.getElem_cons_zero, Nat.add_zero] at h0
      refine ⟨h0, fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 i] using this

theorem lst_getD (B : List S24) {j : ℕ} (hj : j < 64) : (m24Lst B).getD j 1 = m24Elt B j := by
  simp [m24Lst, List.getD_eq_getElem?_getD, hj]

theorem lst_get (B : List S24) (i : ℕ) (hi : i < (m24Lst B).length) :
    (m24Lst B)[i] = m24Elt B i := by
  simp [m24Lst]

theorem psi_lt : ∀ k < 64, qdPsiTab.getD k 0 < 64 ∧ qdPsiInvTab.getD k 0 < 64 := by
  decide +kernel

theorem qb_codes :
    qbIdx.map (fun j => getK (m24E1l.map fun x : S24 => codeP (x : Perm (Fin 24))) j (one 24)) =
      qdQB.map (fun x : S24 => codeP (x : Perm (Fin 24))) := by
  unfold qbIdx qdQB
  simp only [List.map_cons, List.map_nil]
  simp only [getK_codes]

theorem omK_sound {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (h : omK G m24RGens m24E1Bw wordQdOmega = true) :
    qdOmega * qdOmega * qdOmega = 1 ∧ (∀ s ∈ m24E1l, qdOmega * s * qdOmega⁻¹ = s → s = 1) ∧
      ∀ k ∈ List.range 64, qdPsiTab.getD k 0 < 64 ∧ qdPsiInvTab.getD k 0 < 64 ∧
        qdOmega * qdQ k * qdOmega⁻¹ = qdQ (qdPsiTab.getD k 0) ∧
        qdOmega⁻¹ * qdQ k * qdOmega = qdQ (qdPsiInvTab.getD k 0) := by
  unfold omK at h
  rw [forceA_eq, ← codesE hG, forceA_eq, qb_codes, ← lst_codes qdQB rfl, strictA_eq,
    strictA_eq, ← codeO hG, ciS] at h
  unfold omRun at h
  rw [andB_iff, andB_iff] at h
  obtain ⟨h3, hfp, hps⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [beq_iff, cmS, cmS, c1S] at h3
    exact cinjS h3
  · intro s hs hcs
    rw [allL_iff] at hfp
    have := hfp _ (List.mem_map_of_mem hs)
    rw [impB_iff, beq_iff, beq_iff, cmS, cmS, c1S] at this
    exact cinjS (this (congrArg (fun z : S24 => codeP (z : Perm (Fin 24))) hcs))
  · intro k hk
    have hk' := List.mem_range.1 hk
    obtain ⟨hp1, hp2⟩ := psi_lt k hk'
    refine ⟨hp1, hp2, ?_⟩
    rw [allI_iff] at hps
    have hl : ((m24Lst qdQB).map fun x : S24 => codeP (x : Perm (Fin 24))).length = 64 := by
      simp [m24Lst]
    have := hps k (by rw [hl]; exact hk')
    rw [andB_iff, beq_iff, beq_iff, List.getElem_map, lst_get, Nat.zero_add] at this
    obtain ⟨e1, e2⟩ := this
    have hl1 : lane psiP (Nat.mul 6 k) = qdPsiTab.getD k 0 := (psi_tab k hk').1
    have hl2 : lane psiIP (Nat.mul 6 k) = qdPsiInvTab.getD k 0 := (psiI_tab k hk').1
    rw [hl1, getK_codes, lst_getD _ hp1, cmS, cmS] at e1
    rw [hl2, getK_codes, lst_getD _ hp2, cmS, cmS] at e2
    unfold qdQ
    exact ⟨cinjS e1, cinjS e2⟩

theorem qdOmegaData_of {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (hn : normChk G m24RGens m24E1Bw wordQdOmega = true)
    (ho : omK G m24RGens m24E1Bw wordQdOmega = true) (he : QdEnum) : QdOmegaData :=
  ⟨normChk_sound hG hn, (omK_sound hG ho).1, (omK_sound hG ho).2.1, (omK_sound hG ho).2.2, he⟩

end CFSG.KC.QdOm

end
