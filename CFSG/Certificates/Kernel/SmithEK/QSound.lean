module

public import Certificates.Data.Kernel.SmithEKQ
public import CFSG.LargeExtraspecial.SMod20Basic
public import CFSG.Certificates.Kernel.SmithEK.CdSound
public import CFSG.Certificates.Kernel.SmithEK.RSound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.SmithE.K

open CFSG.SmithE CFSG.LargeExtraspecial.SMod20

structure QPins (W M P : List Nat) (C : List (List Nat)) : Prop where
  w : ∀ i < 891, W.getD i 0 = wt i
  m : ∀ i < 891, M.getD i 0 = wMask i
  p : ∀ i < 891, ∀ a < 693, (P.getD i 0).testBit a = inPlane i a
  c : ∀ k < 693, (C.getD k []).toArray = tvCols k
  wl : W.length = 891
  ml : M.length = 891

theorem nthK_eq {α : Type} (d : α) : ∀ (L : List α) (n : Nat), nthK d L n = L.getD n d
  | [], _ => by simp [nthK]
  | _ :: _, 0 => rfl
  | h :: L, n + 1 => by
    rw [List.getD_cons_succ, ← nthK_eq d L n]
    rfl

theorem allK_iff (f : Nat → Bool) : ∀ L : List Nat, allK f L = true ↔ ∀ g ∈ L, f g = true
  | [] => by simp [allK]
  | g :: L => by
    have e : allK f (g :: L) = (f g && allK f L) := rfl
    rw [e, Bool.and_eq_true, allK_iff f L, List.forall_mem_cons]

theorem apR_eq (A : List Nat) (x : Nat) : apR A x = applyCols A.toArray x := by
  rw [applyCols_arr, List.toList_toArray]
  rfl

theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

theorem parQ_rec (u v : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun k acc => xor acc
      (bitK (Nat.xor (Nat.land u (Nat.shiftRight v 1)) (Nat.land (Nat.shiftRight u 1) v))
        (Nat.mul 2 k))) n =
    Nat.rec (motive := fun _ => Bool) false
      (fun k acc => xor acc (xor (bitK u (Nat.mul 2 k) && bitK v (Nat.add (Nat.mul 2 k) 1))
        (bitK u (Nat.add (Nat.mul 2 k) 1) && bitK v (Nat.mul 2 k)))) n
  | 0 => rfl
  | n + 1 => by
    change xor _ _ = xor _ _
    rw [parQ_rec u v n]
    congr 1
    have e1 : Nat.add (Nat.mul 2 n) 1 = 1 + Nat.mul 2 n := Nat.add_comm _ _
    have e2 : Nat.shiftRight v 1 = v >>> 1 := rfl
    have e3 : Nat.shiftRight u 1 = u >>> 1 := rfl
    rw [e1, bitK_eq, bitK_eq, bitK_eq, bitK_eq, bitK_eq, xor_eq, land_eq, land_eq, e2, e3,
      Nat.testBit_xor, Nat.testBit_land, Nat.testBit_land, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight]

theorem fRK_eq (u v : Nat) : fRK u v = fB u v := by
  rw [← cdFB_eq]
  exact parQ_rec u v 10

theorem al16_eq (n : Nat) : al16 n = atLeast 16 n := atLeastK_eq 16 n

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem decode_mod (c : Nat) : decode (c % 1048576) = decode c := by
  have e : (1048576 : Nat) = 2 ^ 20 := by norm_num
  rw [e]
  funext m
  simp only [decode_apply, Nat.testBit_mod_two_pow, m.2, decide_true, Bool.true_and]

theorem mod_eq_of_decode {a b : Nat} (h : decode a = decode b) : a % 1048576 = b % 1048576 :=
  eq_of_decode_eq (lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) (by norm_num))
    (lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) (by norm_num))
    (by rw [decode_mod, decode_mod, h])

theorem decode_of_mod {a b : Nat} (h : a % 1048576 = b % 1048576) : decode a = decode b := by
  rw [← decode_mod a, h, decode_mod]

theorem decode_bif (b : Bool) (v : Nat) : decode (bif b then v else 0) = bit b • decode v := by
  cases b <;> simp [bit, decode_zero]

theorem decode_apR {C : List (List Nat)} (hC : ∀ k < 693, (C.getD k []).toArray = tvCols k)
    {k : Nat} (hk : k < 693) (x : Nat) : decode (apR (C.getD k []) x) = tvLin k (decode x) := by
  rw [apR_eq, hC k hk, tvLin_decode]

theorem decode_projR (w : Nat) : ∀ (V U : List Nat), decode (projR V U w) =
    ∑ t ∈ Finset.range (min V.length U.length), bit (fB w (U.getD t 0)) • decode (V.getD t 0)
  | [], U => by
    have e : projR [] U w = 0 := rfl
    rw [e, decode_zero]
    simp
  | v :: V, [] => by
    have e : projR (v :: V) [] w = 0 := rfl
    rw [e, decode_zero]
    simp
  | v :: V, u :: U => by
    have e : projR (v :: V) (u :: U) w = (bif fRK w u then v else 0) ^^^ projR V U w := rfl
    rw [e, decode_xor, decode_projR w V U, decode_bif, fRK_eq]
    simp only [List.length_cons, Nat.add_min_add_right, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

theorem dualRowK_sound (v s : Nat) : ∀ (U : List Nat) (t₀ : Nat), dualRowK v s U t₀ = true →
    ∀ t < U.length, fB v (U.getD t 0) = Nat.beq s (t₀ + t)
  | [], _, _ => by simp
  | u :: U, t₀, h => by
    have e : dualRowK v s (u :: U) t₀ = ((fRK v u == Nat.beq s t₀) && dualRowK v s U (t₀ + 1)) :=
      rfl
    rw [e, Bool.and_eq_true, beq_iff_eq, fRK_eq] at h
    intro t ht
    cases t with
    | zero => rw [List.getD_cons_zero, Nat.add_zero, h.1]
    | succ t =>
      rw [List.getD_cons_succ, dualRowK_sound v s U (t₀ + 1) h.2 t
        (by simpa using ht), Nat.add_right_comm, Nat.add_assoc]

theorem dualQK_sound (U : List Nat) : ∀ (G : List Nat) (s₀ : Nat), dualQK U G s₀ = true →
    ∀ s < G.length, ∀ t < U.length, fB (G.getD s 0) (U.getD t 0) = Nat.beq (s₀ + s) t
  | [], _, _ => by simp
  | g :: G, s₀, h => by
    have e : dualQK U (g :: G) s₀ = (dualRowK g s₀ U 0 && dualQK U G (s₀ + 1)) := rfl
    rw [e, Bool.and_eq_true] at h
    intro s hs t ht
    cases s with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero, dualRowK_sound g s₀ U 0 h.1 t ht, Nat.zero_add]
    | succ s =>
      rw [List.getD_cons_succ, dualQK_sound U G (s₀ + 1) h.2 s (by simpa using hs) t ht,
        Nat.add_right_comm, Nat.add_assoc]

theorem adjK_sound (M0 : Nat) (G U : List Nat) : ∀ (W M : List Nat), adjK M0 G U W M = true →
    ∀ j < W.length, j < M.length → al16 (M0 &&& M.getD j 0) =
      Nat.beq (projR G U (W.getD j 0) % 1048576) (W.getD j 0 % 1048576)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | w :: W, m :: M, h => by
    have e : adjK M0 G U (w :: W) (m :: M) = ((al16 (Nat.land M0 m) ==
        Nat.beq (projR G U w % 1048576) (w % 1048576)) && adjK M0 G U W M) := rfl
    rw [e, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj hjm
    cases j with
    | zero => exact h.1
    | succ j =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact adjK_sound M0 G U W M h.2 j (by simpa using hj) (by simpa using hjm)

theorem fixK_sound (w : Nat) : ∀ (C : List (List Nat)) (x : Nat), fixK w C x = true →
    ∀ p < C.length, x.testBit p = true → apR (C.getD p []) w % 1048576 = w % 1048576
  | [], _, _ => by simp
  | A :: C, x, h => by
    have e : fixK w (A :: C) x = ((bif Nat.beq (x % 2) 1 then
        Nat.beq (apR A w % 1048576) (w % 1048576) else true) && fixK w C (x / 2)) := rfl
    rw [e, Bool.and_eq_true] at h
    intro p hp hx
    cases p with
    | zero =>
      rw [Nat.testBit_zero, decide_eq_true_iff] at hx
      have h1 := h.1
      rw [hx] at h1
      simpa using h1
    | succ p =>
      rw [List.getD_cons_succ]
      exact fixK_sound w C (x / 2) h.2 p (by simpa using hp) (by rwa [Nat.testBit_succ] at hx)

theorem resK_sound (U G : List Nat) (w : Nat) : ∀ n, resK U G w n = true → ∀ m < n,
    (2 ^ m ^^^ projR U G (2 ^ m)) % 1048576 = 0 ∨
      (2 ^ m ^^^ projR U G (2 ^ m)) % 1048576 = w % 1048576
  | 0, _ => by simp
  | n + 1, h => by
    have e : resK U G w (n + 1) = (resK U G w n &&
        (Nat.beq (Nat.xor (2 ^ n) (projR U G (2 ^ n)) % 1048576) 0 ||
          Nat.beq (Nat.xor (2 ^ n) (projR U G (2 ^ n)) % 1048576) (w % 1048576))) := rfl
    rw [e, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact resK_sound U G w n h.1 m hm
    · exact h.2

section Qa

variable {W M P : List Nat} {C : List (List Nat)} {G U : List Nat}

set_option exponentiation.threshold 700 in
theorem qaPairK_sound (h0 : QPins W M P C) {g : Nat}
    (h : qaPairK W P C (nthK 0 P 0) g = true) :
    ∃ p : Fin 693, p ∈ planeSet 0 ∧ ∃ k : Fin 891, ¬ Opp 0 k ∧
      decode g = tvLin p.val (wtV k.val) + wtV k.val := by
  simp only [qaPairK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, bitK_eq, nthK_eq, xor_eq,
    land_eq] at h
  obtain ⟨⟨⟨⟨hp, hpi⟩, hk⟩, hopp⟩, hv⟩ := h
  have hpi' : inPlane 0 (gP g) = true := by rw [← h0.p 0 (by norm_num) _ hp]; exact hpi
  refine ⟨⟨gP g, hp⟩, mem_planeSet.2 hpi', ⟨gK g, hk⟩, fun ho => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 hopp)
    rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_iff, Nat.testBit_land,
      Bool.and_eq_true] at ha
    obtain ⟨ha693, ha0, hak⟩ := ha
    rw [h0.p 0 (by norm_num) a ha693] at ha0
    rw [h0.p (gK g) hk a ha693] at hak
    exact Finset.disjoint_left.1 ho ((mem_planeSet (a := ⟨a, ha693⟩)).2 ha0)
      ((mem_planeSet (a := ⟨a, ha693⟩)).2 hak)
  · rw [← decode_mod g]
    change decode (gV g) = _
    rw [hv, decode_mod, decode_xor, decode_apR h0.c hp, h0.w _ hk]
    rfl

theorem qa_sound (h0 : QPins W M P C) (h : qaChkE W M P C G U = true) :
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 693, p ∈ planeSet 0 ∧ ∃ k : Fin 891, ¬ Opp 0 k ∧
        v s = tvLin p.val (wtV k.val) + wtV k.val) ∧
      ∀ j : Fin 891, wtV j.val ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j.val = true := by
  simp only [qaChkE, Bool.and_eq_true, Nat.beq_eq, lenK_eq, allK_iff] at h
  obtain ⟨⟨⟨⟨hG, hU⟩, hpair⟩, hdual⟩, hadj⟩ := h
  have hd := dualQK_sound U G 0 hdual
  have hf : ∀ s t : Fin 10, fModel (decode (G.getD s.val 0)) (decode (U.getD t.val 0)) =
      if s = t then 1 else 0 := by
    intro s t
    rw [fModel_decode, hd s.val (by rw [hG]; exact s.2) t.val (by rw [hU]; exact t.2), Nat.zero_add,
      beq_dec]
    by_cases hst : s = t
    · simp [hst, bit]
    · have : s.val ≠ t.val := fun e => hst (Fin.ext e)
      simp [hst, this, bit]
  have hli : LinearIndependent (ZMod 2) fun s : Fin 10 => decode (G.getD s.val 0) := by
    refine Fintype.linearIndependent_iff.2 fun c hc t => ?_
    have h := congrArg (fun w => fModel w (decode (U.getD t.val 0))) hc
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_zero,
      LinearMap.zero_apply, hf, mul_ite, mul_one, mul_zero] at h
    simpa using h
  refine ⟨fun s => decode (G.getD s.val 0), hli, fun s => ?_, fun j => ?_⟩
  · exact qaPairK_sound h0 (hpair _ (getD_mem (by rw [hG]; exact s.2)))
  · have hW := h0.w j.val j.2
    have hj := adjK_sound _ G U W M hadj j.val (by rw [h0.wl]; exact j.2) (by rw [h0.ml]; exact j.2)
    rw [nthK_eq, h0.m 0 (by norm_num), h0.m j.val j.2, hW, al16_eq] at hj
    have hadjW : adjW 0 j.val = atLeast 16 (wMask 0 &&& wMask j.val) := rfl
    rw [hadjW, hj, beq_dec, decide_eq_true_iff]
    have hsum : decode (projR G U (wt j.val)) = ∑ t : Fin 10,
        fModel (wtV j.val) (decode (U.getD t.val 0)) • decode (G.getD t.val 0) := by
      rw [decode_projR, hG, hU, Nat.min_self, ← Fin.sum_univ_eq_sum_range
        (fun t => bit (fB (wt j.val) (U.getD t 0)) • decode (G.getD t 0)) 10]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [wtV, fModel_decode]
    constructor
    · intro hmem
      apply mod_eq_of_decode
      rw [hsum]
      change _ = wtV j.val
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hmem
      rw [← hc]
      refine Finset.sum_congr rfl fun t _ => congrArg (· • decode (G.getD t.val 0)) ?_
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hf,
        mul_ite, mul_one, mul_zero]
      simp
    · intro he
      rw [wtV, ← decode_of_mod he, hsum]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

end Qa

section Cv

variable {W M P : List Nat} {C : List (List Nat)} {G U : List Nat}

theorem cvPairK_sound (h0 : QPins W M P C) {g : Nat} (h : cvPairK C (nthK 0 P 0) g = true) :
    ∃ p : Fin 693, p ∈ planeSet 0 ∧ ∃ m : Fin 20,
      decode g = tvLin p.val (Pi.single m 1) + Pi.single m 1 := by
  simp only [cvPairK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, bitK_eq, nthK_eq, xor_eq] at h
  obtain ⟨⟨⟨hp, hpi⟩, hm⟩, hv⟩ := h
  have hpi' : inPlane 0 (gP g) = true := by rw [← h0.p 0 (by norm_num) _ hp]; exact hpi
  refine ⟨⟨gP g, hp⟩, mem_planeSet.2 hpi', ⟨gK g, hm⟩, ?_⟩
  rw [← decode_mod g]
  change decode (gV g) = _
  rw [hv, decode_mod, decode_xor, decode_apR h0.c hp]
  rw [decode_two_pow ⟨gK g, hm⟩]

theorem cv_sound (h0 : QPins W M P C)
    (h : cvChkE W P C G U = true) :
    ∀ v : V, (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 := by
  simp only [cvChkE, Bool.and_eq_true, allK_iff] at h
  obtain ⟨⟨hfix, hpair⟩, hres⟩ := h
  have hW0 : nthK 0 W 0 = wt 0 := by rw [nthK_eq, h0.w 0 (by norm_num)]
  rw [hW0] at hfix hres
  have hCl : ∀ k < 693, k < C.length := by
    intro k hk
    by_contra hn
    have e := h0.c k hk
    rw [List.getD_eq_default _ _ (by omega)] at e
    have := size_tvCols k
    rw [← e] at this
    simp at this
  have hself : ∀ p ∈ planeSet 0, tvLin p.val (wtV 0) = wtV 0 := by
    intro p hp
    have hb : (nthK 0 P 0).testBit p.val = true := by
      rw [nthK_eq, h0.p 0 (by norm_num) p.val p.2]
      exact mem_planeSet.1 hp
    have e := fixK_sound _ C _ hfix p.val (hCl p.val p.2) hb
    rw [wtV, ← decode_apR h0.c p.2]
    exact decode_of_mod e
  intro v
  constructor
  · intro hv
    have hw : ∀ g ∈ G, fModel v (decode g) = 0 := by
      intro g hg
      obtain ⟨p, hp, m, he⟩ := cvPairK_sound h0 (hpair g hg)
      have hfx := hv p hp
      have h1 : fModel v (tvLin p.val (Pi.single m 1)) = fModel v (Pi.single m 1) := by
        calc fModel v (tvLin p.val (Pi.single m 1)) =
            fModel (tvLin p.val v) (tvLin p.val (Pi.single m 1)) := by rw [hfx]
          _ = fModel v (Pi.single m 1) := by
            rw [← tvEquiv_apply p.2, ← tvEquiv_apply p.2]
            exact fModel_tvEquiv p.2 _ _
      rw [he, map_add, h1]
      exact CharTwo.add_self_eq_zero _
    set n := min U.length G.length
    have hres' : ∀ m : Fin 20, Pi.single m (1 : ZMod 2) + ∑ t ∈ Finset.range n,
        fModel (Pi.single m 1) (decode (G.getD t 0)) • decode (U.getD t 0) ∈
          Submodule.span (ZMod 2) {wtV 0} := by
      intro m
      have e : decode (2 ^ m.val ^^^ projR U G (2 ^ m.val)) = Pi.single m (1 : ZMod 2) +
          ∑ t ∈ Finset.range n, fModel (Pi.single m 1) (decode (G.getD t 0)) •
            decode (U.getD t 0) := by
        rw [decode_xor, decode_projR, decode_two_pow]
        refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
        rw [← decode_two_pow, fModel_decode]
      rw [← e]
      rcases resK_sound U G (wt 0) 20 hres m.val m.2 with h | h
      · rw [decode_of_mod (b := 0) (by rw [h]), decode_zero]
        exact Submodule.zero_mem _
      · rw [decode_of_mod h]
        exact Submodule.mem_span_singleton_self _
    have hsum : v = ∑ m : Fin 20, v m • Pi.single m (1 : ZMod 2) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    have h0' : ∑ m : Fin 20, v m • ∑ t ∈ Finset.range n,
        fModel (Pi.single m 1) (decode (G.getD t 0)) • decode (U.getD t 0) = 0 := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [← Finset.sum_smul]
      have e : ∑ m : Fin 20, v m * fModel (Pi.single m 1) (decode (G.getD t 0)) =
          fModel v (decode (G.getD t 0)) := by
        conv_rhs => rw [hsum]
        simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      have htG : t < G.length := lt_of_lt_of_le (Finset.mem_range.1 ht) (Nat.min_le_right _ _)
      rw [e, hw _ (getD_mem htG), zero_smul]
    have hv' : v = ∑ m : Fin 20, v m • (Pi.single m (1 : ZMod 2) + ∑ t ∈ Finset.range n,
        fModel (Pi.single m 1) (decode (G.getD t 0)) • decode (U.getD t 0)) := by
      simp only [smul_add, Finset.sum_add_distrib]
      rw [h0', add_zero]
      exact hsum
    have hmem : v ∈ Submodule.span (ZMod 2) {wtV 0} := by
      rw [hv']
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hres' m)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a with rfl | rfl
    · left
      rw [← ha, zero_smul]
    · right
      rw [← ha, one_smul]
  · rintro (rfl | rfl)
    · intro p _
      exact map_zero _
    · exact hself

end Cv

end CFSG.SmithE.K
