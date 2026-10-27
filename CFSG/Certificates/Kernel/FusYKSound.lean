module

public import Certificates.Data.Kernel.FusYK
public import CFSG.Certificates.Kernel.Q47KSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4FusYTests
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Q47KRunSound
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.FusYK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.Q47K
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.FusY
open CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.KLie.CT (notB)

@[expose] def orbitCheckG (form : Array ℕ) (K : List (Array ℕ)) (tab : Array Bool) : Bool :=
  (List.range 64).all fun v => v == 0 || form[v]! != 0 || K.any fun k => tab[k[v]!]!

@[expose] def modelFusCheckG (form : Array ℕ) (n : ℕ) (Qg Eg Fg reps : List (Array ℕ))
    (z : Array ℕ) (k₀ : ℕ) (Eb : List (Array ℕ)) (KE KF : List (List (Array ℕ)))
    (W : List (List ℕ)) : Bool :=
  let L := eltsN n (Eg ++ Fg)
  enumCheckN n (Eg ++ Fg) 256 && !(eqA 64 Eb[k₀]! (idA 64)) &&
    cosetCheck n (eltsN n Qg) Eg[k₀]! L &&
    (List.range 2).all fun i => (List.range 2).all fun j =>
      orbitCheckG form (eltsN 64 (KE[i]! ++ KF[j]!)) (codeTab n reps z L) &&
        invCheck (eltsN 64 (KE[i]! ++ KF[j]!)) Eb[k₀]! W[2 * i + j]!

@[expose] def fusYCheckG (form : Array ℕ) (m16 m32 : MD) (W16 W32 : List (List ℕ)) : Bool :=
  modelFusCheckG form 16 m16.qg m16.eg m16.fg m16.reps m16.z 4 m16.eb m16.ke m16.kf W16 &&
    modelFusCheckG form 32 m32.qg m32.eg m32.fg m32.reps m32.z 1 m32.eb m32.ke m32.kf W32

theorem fusYCheck_eq : fusYCheck = fusYCheckG q47Form q47M16 q47M32 fusYWK16 fusYWK32 := rfl

@[expose] noncomputable def efG (m : MD) (k : ModelK) (i : Nat) : Nat :=
  nIf(Nat.blt i m.eg.length, k.GE i, k.GF (i - m.eg.length))

@[expose] noncomputable def efPts (n w : Nat) (m : MD) (k : ModelK) : List Nat :=
  runK n w (m.eg.length + m.fg.length) (efG m k) 400

@[expose] noncomputable def fusB (form : Array Nat) (n w : Nat) (m : MD) (k : ModelK) (k₀ : Nat)
    (W : List (List Nat)) : Bool :=
  Nat.beq (efPts n w m k).length 256 && CFSG.KLie.CT.notB (Nat.beq (k.GEb k₀) (pidn 64 7)) &&
    cosetK n w ((List.range k.NQ).map k.TQ) (k.GE k₀) (efPts n w m k) &&
    allN 4 fun c => Nat.beq (kefPts m k c).length 168 &&
      orbitK form (kefPts m k c) (tabK n w k.REP k.PZ (efPts n w m k)) &&
      invK (kefPts m k c) (k.GEb k₀) (W.getD c [])

structure FusOK (n w : Nat) (m : MD) (k : ModelK) : Prop where
  rl : m.reps.length = 64
  reps : Bound n w m.reps k.REP
  z : m.z = unpack n w k.PZ ∧ permOK n w (mask w) (n * w) k.PZ (pinvS n w (mask w) k.PZ) = true
  pQ : Pin n w m.qg m.qg.length k.GQ k.NQ k.TQ k.EQ k.SQ
  pE : Pin n w m.eg m.eg.length k.GE k.NE k.TE k.EE k.SE
  pF : Pin n w m.fg m.fg.length k.GF k.NF k.TF k.EF k.SF
  eb : Bound 64 7 m.eb k.GEb
  ks : ∀ i < 4, Bound 64 7 (kListG m i) (k.GK i)

variable {n w : Nat}

theorem getElem!_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) : l[i]! = l.getD i default := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem toArray_get (gs : List (Array ℕ)) (k : Nat) : gs.toArray[k]! = gs[k]! := by
  by_cases h : k < gs.length
  · rw [getElem!_pos gs.toArray k (by simpa using h), getElem!_pos gs k h, List.getElem_toArray]
  · rw [getElem!_neg gs.toArray k (by simpa using h), getElem!_neg gs k h]

theorem getElem!_map' {L : List Nat} {i : Nat} (h : i < L.length) :
    (L.map (unpack n w))[i]! = unpack n w (L.getD i 0) := by
  rw [getElem!_pos _ i (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

theorem bound_of_pin {gs : List (Array ℕ)} {G : Nat → Nat} {N : Nat} {T E S : Nat → Nat}
    (p : Pin n w gs gs.length G N T E S) : Bound n w gs G := fun k hk =>
  ⟨by rw [← toArray_get]; exact p.bind k hk, p.perm k hk⟩

theorem bound_append {A B : List (Array ℕ)} {GA GB : Nat → Nat} (hA : Bound n w A GA)
    (hB : Bound n w B GB) :
    Bound n w (A ++ B) (fun i => nIf(Nat.blt i A.length, GA i, GB (i - A.length))) := by
  intro i hi
  rw [List.length_append] at hi
  beta_reduce
  rw [nIf_ite]
  by_cases h : i < A.length
  · rw [ite_eq_left (Nat.blt_eq.mpr h), getElem!_pos (A ++ B) i (by simp; omega),
      List.getElem_append_left h, ← getElem!_pos A i h]
    exact hA i h
  · have hf : Nat.blt i A.length ≠ true := fun e => h (Nat.blt_eq.mp e)
    rw [ite_eq_right hf, getElem!_pos (A ++ B) i (by simp; omega),
      List.getElem_append_right (by omega), ← getElem!_pos B _ (by omega)]
    exact hB _ (by omega)

theorem memK_any (L : List Nat) (x : Nat) : memK L x = L.any (Nat.beq x) := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    change CFSG.KLie.CT.orB (Nat.beq x y) (memK L x) = _
    rw [ih, orB_eq, List.any_cons]

theorem inLN_memK {L : List Nat} {x : Nat} (hx : PP n w x) (hL : ∀ y ∈ L, PP n w y) :
    inLN n (L.map (unpack n w)) (unpack n w x) = memK L x := by
  unfold inLN
  rw [any_eqA_unpack hx.1 fun q hq => (hL q hq).1, memK_any]

theorem cosetCheck_eq {N : Nat} {TQ : Nat → Nat} {e : Nat} {LP : List Nat}
    (hQ : ∀ i < N, PP n w (TQ i)) (pe : PP n w e) (hL : ∀ y ∈ LP, PP n w y) :
    cosetCheck n ((List.range N).map fun i => unpack n w (TQ i)) (unpack n w e) (LP.map (unpack n w)) =
      cosetK n w ((List.range N).map TQ) e LP := by
  unfold cosetCheck cosetK
  rw [List.all_map, List.all_map]
  refine all_congr_mem fun j hj => ?_
  have pj := hQ j (List.mem_range.1 hj)
  simp only [Function.comp_apply]
  rw [mulN_PP pe pj, mulN_PP (pe.mul pj) (pe.mul pj), eqA_id_PP ((pe.mul pj).mul (pe.mul pj)),
    inLN_memK (pe.mul pj) hL, strictB_eq', orB_eq, notB_eq]
  rfl

theorem invCheck_eq {KP : List Nat} {t : Nat} {W : List Nat} (hK : ∀ y ∈ KP, PP 64 7 y)
    (pt : PP 64 7 t) : invCheck (KP.map (unpack 64 7)) (unpack 64 7 t) W = invK KP t W := by
  unfold invCheck invK
  rw [List.length_map]
  refine all_congr_mem fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have pi := hK _ (Q47K.getD_mem hi')
  have hd : (default : Nat) = 0 := rfl
  rw [getElem!_map' hi', strictB_eq', eqA_id_PP pi, mulN_PP pi pi, eqA_id_PP (pi.mul pi),
    getElem!_getD W i, hd, orB_eq, orB_eq, notB_eq, andB_eq, blt_eq_decide]
  by_cases hw : W.getD i 0 < KP.length
  · have pw := hK _ (Q47K.getD_mem hw)
    rw [getElem!_map' hw, conjA_PP pw pi, eqA_PP (pw.conjK pi) pt, Bool.or_assoc]
    rfl
  · rw [decide_eq_false hw, Bool.false_and, Bool.false_and, Bool.or_assoc]
    rfl

theorem bitK_eq_testBit (F i : Nat) : HeAutK.bitK F i = F.testBit i := by
  unfold HeAutK.bitK
  have e : Nat.land (Nat.shiftRight F i) 1 = F / 2 ^ i % 2 := by
    change (F >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  cases h : Nat.beq (F / 2 ^ i % 2) 1
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

theorem tab_spec (b : Nat → Bool) : ∀ N,
    CFSG.KLie.CT.sumN N (fun v => Nat.mul (bn (b v)) (Nat.shiftLeft 1 v)) < 2 ^ N ∧
      ∀ x < N, (CFSG.KLie.CT.sumN N fun v => Nat.mul (bn (b v)) (Nat.shiftLeft 1 v)).testBit x = b x
  | 0 => ⟨Nat.one_pos, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  | N + 1 => by
    obtain ⟨h1, h2⟩ := tab_spec b N
    have hb : bn (b N) ≤ 1 := by cases b N <;> decide
    have e : CFSG.KLie.CT.sumN (N + 1) (fun v => Nat.mul (bn (b v)) (Nat.shiftLeft 1 v)) =
        2 ^ N * bn (b N) + CFSG.KLie.CT.sumN N (fun v => Nat.mul (bn (b v)) (Nat.shiftLeft 1 v)) := by
      have hs : Nat.shiftLeft 1 N = 2 ^ N := (Nat.shiftLeft_eq 1 N).trans (Nat.one_mul _)
      change bn (b N) * Nat.shiftLeft 1 N +
        CFSG.KLie.CT.sumN N (fun v => Nat.mul (bn (b v)) (Nat.shiftLeft 1 v)) = _
      rw [hs, Nat.mul_comm]
    rw [e]
    refine ⟨?_, fun x hx => ?_⟩
    · have : 2 ^ N * bn (b N) ≤ 2 ^ N := by
        calc 2 ^ N * bn (b N) ≤ 2 ^ N * 1 := Nat.mul_le_mul_left _ hb
          _ = 2 ^ N := Nat.mul_one _
      rw [Nat.pow_succ]
      omega
    · rw [Nat.testBit_two_pow_mul_add _ h1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
      · rw [ite_eq_left hx]
        exact h2 x hx
      · rw [ite_eq_right (Nat.lt_irrefl _), Nat.sub_self, Nat.testBit_zero]
        cases b x <;> decide

theorem codeTab_get {REP : Nat → Nat} {PZ : Nat} {reps : List (Array ℕ)} {z : Array ℕ}
    {LP : List Nat} (hsz : szOK n w = true) (hL : ∀ y ∈ LP, PP n w y) (hr : reps.length = 64)
    (bR : Bound n w reps REP) (hz : z = unpack n w PZ) (pz : PP n w PZ) {x : Nat} (hx : x < 64) :
    (codeTab n reps z (LP.map (unpack n w)))[x]! = HeAutK.bitK (tabK n w REP PZ LP) x := by
  unfold codeTab tabK
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, bitK_eq_testBit,
    (tab_spec _ 64).2 x hx]
  dsimp only
  have pr := PP_of_permOK hsz (bR x (by omega)).2
  rw [(bR x (by omega)).1, hz, inLN_memK pr hL, mulN_PP pr pz, inLN_memK (pr.mul pz) hL, orB_eq]
  rfl

theorem orbitCheck_eq {form : Array ℕ} {REP : Nat → Nat} {PZ : Nat} {reps : List (Array ℕ)}
    {z : Array ℕ} {KP LP : List Nat} (hsz : szOK n w = true) (hK : ∀ y ∈ KP, PP 64 7 y)
    (hL : ∀ y ∈ LP, PP n w y) (hr : reps.length = 64) (bR : Bound n w reps REP)
    (hz : z = unpack n w PZ) (pz : PP n w PZ) :
    orbitCheckG form (KP.map (unpack 64 7)) (codeTab n reps z (LP.map (unpack n w))) =
      orbitK form KP (tabK n w REP PZ LP) := by
  unfold orbitCheckG orbitK
  rw [allN_eq']
  refine all_congr_mem fun v hv => ?_
  have hv' := List.mem_range.1 hv
  rw [any_map_congr (q := fun k => HeAutK.bitK (tabK n w REP PZ LP) (pg 7 (mask 7) k v))
    fun q hq => by
      rw [unpack_get' hv', codeTab_get hsz hL hr bR hz pz ((hK q hq).2.1 v hv')]]
  simp only [orB_eq, notB_eq, bne, beq_nat, Bool.or_assoc]

theorem modelFus_of {form : Array ℕ} {m : MD} {k : ModelK} {k₀ : Nat} {W : List (List ℕ)}
    (h : FusOK n w m k) (he : k₀ < m.eg.length) (hb : k₀ < m.eb.length)
    (hk : fusB form n w m k k₀ W = true) :
    modelFusCheckG form n m.qg m.eg m.fg m.reps m.z k₀ m.eb m.ke m.kf W = true := by
  have bE := bound_of_pin h.pE
  have bF := bound_of_pin h.pF
  have hszn : szOK n w = true := (PP_gen h.pE.ok h.pE.perm 0 (by omega)).sz
  have hsz64 : szOK 64 7 = true := by decide
  have pz : PP n w k.PZ := PP_of_permOK hszn h.z.2
  have pb : PP 64 7 (k.GEb k₀) := PP_of_permOK hsz64 (h.eb k₀ hb).2
  have pe : PP n w (k.GE k₀) := PP_of_permOK hszn (bE k₀ he).2
  unfold fusB at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
  have hl : (runK n w (m.eg.length + m.fg.length) (efG m k) 400).length = 256 :=
    Nat.eq_of_beq_eq_true h1
  obtain ⟨pEF, eEF, cEF⟩ := runK_sound (gs := m.eg ++ m.fg) (G := efG m k) (fuel := 400) hszn
    (List.length_append ..)
    (fun t ht => bound_append bE bF t (by rw [List.length_append]; exact ht))
    (by rw [hl]; decide) (by decide)
  rw [hl] at cEF
  have hL : efPts n w m k = runK n w (m.eg.length + m.fg.length) (efG m k) 400 := rfl
  simp only [modelFusCheckG, Bool.and_eq_true]
  rw [eEF]
  refine ⟨⟨⟨cEF, ?_⟩, ?_⟩, ?_⟩
  · rw [(h.eb k₀ hb).1, eqA_id_PP pb, ← notB_eq]
    exact h2
  · rw [eltsN_eq h.pQ.size h.pQ.bind h.pQ.ok h.pQ.fuel, (bE k₀ he).1,
      cosetCheck_eq (PP_pts h.pQ.ok h.pQ.perm) pe pEF, ← hL]
    exact h3
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    have hi2 := List.mem_range.1 hi
    have hj2 := List.mem_range.1 hj
    have hc := allN_spec h4 (2 * i + j) (by omega)
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨c1, c2⟩, c3⟩ := hc
    have e1 : (2 * i + j) / 2 = i := by omega
    have e2 : (2 * i + j) % 2 = j := by omega
    have bA : Bound 64 7 (m.ke.getD i []) (k.GK i) := by
      have := h.ks i (by omega)
      unfold kListG at this
      rwa [decide_eq_true hi2] at this
    have bB : Bound 64 7 (m.kf.getD j []) (k.GK (2 + j)) := by
      have := h.ks (2 + j) (by omega)
      unfold kListG at this
      rwa [decide_eq_false (by omega : ¬ 2 + j < 2), Nat.add_sub_cancel_left] at this
    have hkef : kefPts m k (2 * i + j) = runK 64 7 ((m.ke.getD i []).length + (m.kf.getD j []).length)
        (fun t => nIf(Nat.blt t (m.ke.getD i []).length, k.GK i t,
          k.GK (2 + j) (t - (m.ke.getD i []).length))) 200 := by
      unfold kefPts kefG
      rw [e1, e2]
    have hl2 : (kefPts m k (2 * i + j)).length = 168 := Nat.eq_of_beq_eq_true c1
    obtain ⟨pK, eK, -⟩ := runK_sound (gs := m.ke.getD i [] ++ m.kf.getD j [])
      (G := fun t => nIf(Nat.blt t (m.ke.getD i []).length, k.GK i t,
        k.GK (2 + j) (t - (m.ke.getD i []).length))) (fuel := 200) hsz64
      (List.length_append ..)
      (fun t ht => bound_append bA bB t (by rw [List.length_append]; exact ht))
      (by rw [← hkef, hl2]; decide) (by decide)
    have hd : (default : List (Array ℕ)) = [] := rfl
    have hdW : (default : List ℕ) = [] := rfl
    rw [getElem!_getD m.ke, getElem!_getD m.kf, getElem!_getD W, hd, hdW, eK, ← hkef,
      (h.eb k₀ hb).1, Bool.and_eq_true]
    rw [← hkef] at pK
    exact ⟨(orbitCheck_eq hszn pK pEF h.rl h.reps h.z.1 pz).trans c2,
      (invCheck_eq pK pb).trans c3⟩

theorem fusYK_sound {form : Array ℕ} {m16 m32 : MD} {k16 k32 : ModelK} {W16 W32 : List (List ℕ)}
    (h16 : FusOK 16 5 m16 k16) (h32 : FusOK 32 6 m32 k32)
    (hk0 : 4 < m16.eg.length ∧ 4 < m16.eb.length ∧ 1 < m32.eg.length ∧ 1 < m32.eb.length)
    (hk16 : fusB form 16 5 m16 k16 4 W16 = true) (hk32 : fusB form 32 6 m32 k32 1 W32 = true) :
    fusYCheckG form m16 m32 W16 W32 = true := by
  unfold fusYCheckG
  rw [Bool.and_eq_true]
  exact ⟨modelFus_of h16 hk0.1 hk0.2.1 hk16, modelFus_of h32 hk0.2.2.1 hk0.2.2.2 hk32⟩

end CFSG.KC.FusYK

end
