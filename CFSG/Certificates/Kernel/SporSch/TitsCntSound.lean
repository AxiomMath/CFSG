module

public import Certificates.Data.Kernel.SporSch.TitsCnt
public import CFSG.Certificates.Kernel.SporSch.TitsInvSound
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.BaseSep
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def IsTr5 (LR TR : Nat → Nat) (t0 t1 t2 t3 t4 : Nat) : Prop :=
  (∃ a < rcnt (LR 0), t0 = trAt 1755 (1755 * 11) LR TR 0 a) ∧
  (∃ a < rcnt (LR 1), t1 = trAt 1755 (1755 * 11) LR TR 1 a) ∧
  (∃ a < rcnt (LR 2), t2 = trAt 1755 (1755 * 11) LR TR 2 a) ∧
  (∃ a < rcnt (LR 3), t3 = trAt 1755 (1755 * 11) LR TR 3 a) ∧
  (∃ a < rcnt (LR 4), t4 = trAt 1755 (1755 * 11) LR TR 4 a)

@[expose] def Agrees (LR TR : Nat → Nat) (P : Nat → Nat → Nat → Nat → Nat → Bool)
    (p : Array Nat → Bool) : Prop :=
  ∀ t0 t1 t2 t3 t4, IsTr5 LR TR t0 t1 t2 t3 t4 →
    P t0 t1 t2 t3 t4 = p (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))

theorem survivors5_filter (L : Array Level) (p q : Array Nat → Bool) :
    (survivors5 1755 L p).filter q = survivors5 1755 L (fun a => p a && q a) := by
  simp only [survivors5, List.filter_flatMap, List.filter_filter, Bool.and_comm]

section Mask

variable {kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}

private theorem isTr5_code {k : Nat} (hk : k < tot5 LR) :
    IsTr5 LR TR
      (trAt 1755 (1755 * 11) LR TR 0 (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1)))
      (trAt 1755 (1755 * 11) LR TR 1 (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1)))
      (trAt 1755 (1755 * 11) LR TR 2 (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)))
      (trAt 1755 (1755 * 11) LR TR 3 (k / rcnt (LR 4) % rcnt (LR 3)))
      (trAt 1755 (1755 * 11) LR TR 4 (k % rcnt (LR 4))) := by
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
  exact ⟨⟨_, d0, rfl⟩, ⟨_, d1, rfl⟩, ⟨_, d2, rfl⟩, ⟨_, d3, rfl⟩, ⟨_, d4, rfl⟩⟩

theorem survivors5_mask (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (h : all5K 1755 (1755 * 11) LR TR (survQ P M) = true) :
    survivors5 1755 (rawLevels 1755 S base) p =
      ((List.range (tot5 LR)).filter (hasBit M)).map
        (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  have hF : ∀ k < tot5 LR, prod5 1755 (rawLevels 1755 S base)
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) (k / rcnt (LR 4) % rcnt (LR 3))
      (k % rcnt (LR 4)) = unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k) ∧
      p (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) = hasBit M k := by
    intro k hk
    obtain ⟨d0, d1, d2, d3, d4, dk⟩ := code_facts hk
    obtain ⟨-, e, -⟩ := prod5_facts hb hp hl d0 d1 d2 d3 d4
    rw [prodCode_eq]
    refine ⟨e, ?_⟩
    have hq := all5K_at h d0 d1 d2 d3 d4
    rw [dk] at hq
    unfold survQ at hq
    rw [hP _ _ _ _ _ (isTr5_code hk)] at hq
    cases hp' : p (unpack 1755 11 (prod5K 1755 11 (mask 11) _ _ _ _ _)) <;>
      cases hd : hasBit M k <;> simp_all
  unfold survivors5
  rw [c0, c1, c2, c3, c4]
  simp only [filter_map_flatMap]
  rw [flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_ite]
  have hT : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) * rcnt (LR 3) * rcnt (LR 4) = tot5 LR := rfl
  rw [hT]
  have hfil : (List.range (tot5 LR)).filter (fun k => p (prod5 1755 (rawLevels 1755 S base)
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) (k / rcnt (LR 4) % rcnt (LR 3))
      (k % rcnt (LR 4)))) = (List.range (tot5 LR)).filter (hasBit M) := by
    apply List.filter_congr
    intro k hk
    have hk := List.mem_range.1 hk
    rw [(hF k hk).1, (hF k hk).2]
  rw [hfil]
  exact List.map_congr_left fun k hk => (hF k (List.mem_range.1 (List.mem_filter.1 hk).1)).1

end Mask

private theorem popc_succ (T M : Nat) :
    popc (T + 1) M = popc T M + (if M.testBit T then 1 else 0) := by
  change Nat.add (popc T M) (Nat.land (Nat.shiftRight M T) 1) = _
  congr 1
  change (M >>> T) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  split_ifs with h
  · simpa using h
  · simp only [decide_eq_true_eq] at h
    omega

private theorem length_filter_hasBit (M : Nat) : ∀ T,
    ((List.range T).filter (hasBit M)).length = popc T M
  | 0 => rfl
  | T + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_hasBit M T,
      popc_succ, List.filter_singleton, Raw.Orb.hasBit_eq]
    cases M.testBit T <;> rfl

theorem surv5K_countT {kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (h : all5K 1755 (1755 * 11) LR TR (survQ P M) = true) :
    (survivors5 1755 (rawLevels 1755 S base) p).length = popc (tot5 LR) M := by
  rw [survivors5_mask hb hp hl hP h, List.length_map, length_filter_hasBit]

theorem surv5K_soundCT {kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    {C : List Nat}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (hM : Nat.beq (maskOf C) M = true) (hA : ascK (tot5 LR) C 0 = true)
    (h : all5K 1755 (1755 * 11) LR TR (survQ P M) = true) :
    survivors5 1755 (rawLevels 1755 S base) p =
      C.map (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) := by
  rw [survivors5_mask hb hp hl hP h]
  congr 1
  obtain ⟨hC1, hC2⟩ := ascK_spec hA
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_lt_range.filter _) hC1
    fun k => ?_
  rw [List.mem_filter, List.mem_range, ← Nat.eq_of_beq_eq_true hM, hasBit_maskOf]
  constructor
  · rintro ⟨-, h⟩
    exact of_decide_eq_true h
  · intro hk
    exact ⟨(hC2 k hk).2, decide_eq_true hk⟩

private theorem survivors5_all {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) :
    survivors5 1755 (rawLevels 1755 S base) (fun _ => true) =
      (List.range (tot5 LR)).map
        (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  unfold survivors5
  rw [c0, c1, c2, c3, c4]
  simp only [filter_map_flatMap]
  rw [flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_range_mul]
  simp only [ite_true]
  rw [← List.map_eq_flatMap]
  have hT : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) * rcnt (LR 3) * rcnt (LR 4) = tot5 LR := rfl
  rw [hT]
  refine List.map_congr_left fun k hk => ?_
  have hk := List.mem_range.1 hk
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
  obtain ⟨-, e, -⟩ := prod5_facts hb hp hl d0 d1 d2 d3 d4
  rw [prodCode_eq]
  exact e

theorem surv5K_propsT {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (p : Array Nat → Bool)
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) :
    (∀ x ∈ survivors5 1755 (rawLevels 1755 S base) p, isInvA 1755 x (invCand 1755 x) = true ∧
      siftA 1755 (rawLevels 1755 S base) base 0 x = true) ∧
    (survivors5 1755 (rawLevels 1755 S base) p).Pairwise (fun a b => eqA 1755 a b = false) := by
  have hd := hd_of_binds hb hp hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  have hf : survivors5 1755 (rawLevels 1755 S base) p =
      (survivors5 1755 (rawLevels 1755 S base) (fun _ => true)).filter p := by
    rw [survivors5_filter]
    rfl
  rw [hf, survivors5_all hb hp hl]
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨hx, -⟩ := List.mem_filter.1 hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    have hct := List.mem_range.1 hc
    obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hct
    have hr := prodCode_rep hb hp hl hct
    exact ⟨isInvA_of_rep hr (rep_invCand hr),
      sift5 hd hbs (c0 ▸ d0) (c1 ▸ d1) (c2 ▸ d2) (c3 ▸ d3) (c4 ▸ d4) hr⟩
  · refine List.Pairwise.filter _ ?_
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb' hab => ?_
    have hat := List.mem_range.1 ha
    have hbt := List.mem_range.1 hb'
    obtain ⟨a0, a1, a2, a3, a4, ae⟩ := code_facts hat
    obtain ⟨b0, b1, b2, b3, b4, be⟩ := code_facts hbt
    apply Bool.eq_false_iff.2
    intro H
    have E := (CFSG.Monster.B.Co2.eqA_iff (prodCode_rep hb hp hl hat)
      (prodCode_rep hb hp hl hbt)).1 H
    obtain ⟨r0, r1, r2, r3, r4⟩ := prod5_inj hd hbs (c0 ▸ a0) (c1 ▸ a1) (c2 ▸ a2) (c3 ▸ a3)
      (c4 ▸ a4) (c0 ▸ b0) (c1 ▸ b1) (c2 ▸ b2) (c3 ▸ b3) (c4 ▸ b4) E
    rw [r0, r1, r2, r3, r4, be] at ae
    omega

theorem surv5K_subT {kS BP M1 M2 : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p1 p2 : Array Nat → Bool} {P1 P2 : Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP)
    (hP1 : Agrees LR TR P1 p1) (h1 : all5K 1755 (1755 * 11) LR TR (survQ P1 M1) = true)
    (hP2 : Agrees LR TR P2 p2) (h2 : all5K 1755 (1755 * 11) LR TR (survQ P2 M2) = true)
    (hsub : Nat.beq (Nat.land M1 M2) M1 = true) :
    ∀ x ∈ survivors5 1755 (rawLevels 1755 S base) p1, p2 x = true := by
  have e1 := survivors5_mask hb hp hl hP1 h1
  have e2 := survivors5_mask hb hp hl hP2 h2
  intro x hx
  rw [e1] at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hkr, hk1⟩ := List.mem_filter.1 hk
  have hk2 : hasBit M2 k = true := by
    rw [Raw.Orb.hasBit_eq] at hk1 ⊢
    have := Nat.eq_of_beq_eq_true hsub
    rw [← this] at hk1
    change (M1 &&& M2).testBit k = true at hk1
    rw [Nat.testBit_and, Bool.and_eq_true] at hk1
    exact hk1.2
  have hmem : unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k) ∈
      survivors5 1755 (rawLevels 1755 S base) p2 := by
    rw [e2]
    exact List.mem_map.2 ⟨k, List.mem_filter.2 ⟨hkr, hk2⟩, rfl⟩
  have hf : survivors5 1755 (rawLevels 1755 S base) p2 =
      (survivors5 1755 (rawLevels 1755 S base) (fun _ => true)).filter p2 := by
    rw [survivors5_filter]
    rfl
  rw [hf] at hmem
  exact (List.mem_filter.1 hmem).2

theorem ktK_eq {kS BP t0 t1 t2 t3 t4 : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP)
    (h0 : canonK 1755 11 (mask 11) (1755 * 11) t0 = true)
    (h1 : canonK 1755 11 (mask 11) (1755 * 11) t1 = true)
    (h2 : canonK 1755 11 (mask 11) (1755 * 11) t2 = true)
    (h3 : canonK 1755 11 (mask 11) (1755 * 11) t3 = true)
    (h4 : canonK 1755 11 (mask 11) (1755 * 11) t4 = true) :
    ktK LR TRI BP t0 t1 t2 t3 t4 =
      siftA 1755 (rawLevels 1755 S base) base 0
        (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) := by
  obtain ⟨-, hg⟩ := gpt_facts h0 h1 h2 h3 h4
  exact (siftPf_eq hb hp hl 5 0 rfl _ _ fun i hi =>
    ⟨by rw [(hg i hi).1, gptR_eq], by rw [gptR_eq]; exact (hg i hi).2⟩).symm

section Group

open CFSG.Certificates CFSG.Monster.B.Co2

variable {kS kO BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}

theorem chain_group (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup) :
    ∃ G : Subgroup (Equiv.Perm (Fin 1755)),
      (∀ (g : Array Nat) (γ : Equiv.Perm (Fin 1755)), Rep 1755 g γ →
        (siftA 1755 (rawLevels 1755 S base) base 0 g = true ↔ γ ∈ G)) ∧
      ∀ γ ∈ G, (∀ t < 5, ∀ h : base[t]! < 1755, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → γ = 1 := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have hc := Raw.Orb.rawChainOK_of_K (chunks := 1) hb hh hl hNS hs
  obtain ⟨hk, -⟩ := Raw.Orb.rawHeadOK_of hb hh
  have hmem : ∀ x ∈ base.toList, x < 1755 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    have ht' : t < 5 := by simpa [hbs] using ht
    have := hbl t ht'
    rwa [getElem!_pos base t (by omega), ← Array.getElem_toList] at this
  let bL : List (Fin 1755) := base.toList.map fun x => ⟨x % 1755, Nat.mod_lt _ (by norm_num)⟩
  have hbnd : bL.Nodup := List.Nodup.map_on (fun x hx y hy e => by
      have e' := congrArg Fin.val e
      simp only at e'
      rwa [Nat.mod_eq_of_lt (hmem x hx), Nat.mod_eq_of_lt (hmem y hy)] at e') hnd
  have hBA : (bL.map Fin.val).toArray = base := by
    apply Array.ext'
    simp only [List.map_map, bL]
    conv_rhs => rw [← List.map_id base.toList]
    apply List.map_congr_left
    intro x hx
    exact Nat.mod_eq_of_lt (hmem x hx)
  have hF := chainCheckFacts hc
  have hA := chainArrays_ofArrays (n := 1755) (hn := by norm_num) (k := kO) (hk := hk) (base := bL)
    (hb := hbnd) (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) hF.strong_inv
  rw [hBA] at hA
  have hv := validSchreier_of_chainOK hA (by norm_num) hc
  refine ⟨_, fun g γ hg => siftA_iff_mem_originalSubgroup hA (by norm_num) hc hg,
    fun γ hγ hfix => RawSchreierDatum.eq_one_of_fixes_base _ hv.1 hγ fun i => ?_⟩
  have hi : (i : Nat) < 5 := by
    have h1 := i.2
    have h2 := hA.base_size
    omega
  have hq : (RawSchreierDatum.ofArrays 1755 (by norm_num) S kO hk bL hbnd
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)).base.get i =
        ⟨base[(i : Nat)]!, hbl i hi⟩ := Fin.ext (hA.base_val i)
  rw [hq]
  exact hfix i hi (hbl i hi)

theorem tr5_rep (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) {a b c d e : Nat} (ha : a < rcnt (LR 0))
    (hb1 : b < rcnt (LR 1)) (hc : c < rcnt (LR 2)) (hd : d < rcnt (LR 3)) (he : e < rcnt (LR 4)) :
    Rep 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) (trAt 1755 (1755 * 11) LR TR 0 a)
      (trAt 1755 (1755 * 11) LR TR 1 b) (trAt 1755 (1755 * 11) LR TR 2 c)
      (trAt 1755 (1755 * 11) LR TR 3 d) (trAt 1755 (1755 * 11) LR TR 4 e)))
      (Raw.Orb.trP 1755 S base 0 a * Raw.Orb.trP 1755 S base 1 b * Raw.Orb.trP 1755 S base 2 c *
        Raw.Orb.trP 1755 S base 3 d * Raw.Orb.trP 1755 S base 4 e) ∧
    siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 (prod5K 1755 11 (mask 11)
      (trAt 1755 (1755 * 11) LR TR 0 a) (trAt 1755 (1755 * 11) LR TR 1 b)
      (trAt 1755 (1755 * 11) LR TR 2 c) (trAt 1755 (1755 * 11) LR TR 3 d)
      (trAt 1755 (1755 * 11) LR TR 4 e))) = true := by
  have hd' := hd_of_binds hb hp hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  obtain ⟨-, e5, -⟩ := prod5_facts hb hp hl ha hb1 hc hd he
  have hr : Rep 1755 (prod5 1755 (rawLevels 1755 S base) a b c d e)
      (Raw.Orb.trP 1755 S base 0 a * Raw.Orb.trP 1755 S base 1 b * Raw.Orb.trP 1755 S base 2 c *
        Raw.Orb.trP 1755 S base 3 d * Raw.Orb.trP 1755 S base 4 e) :=
    rep_compA (rep_compA (rep_compA (rep_compA
      (Raw.Orb.rep_tr hd' (by omega) (c0 ▸ ha)) (Raw.Orb.rep_tr hd' (by omega) (c1 ▸ hb1)))
      (Raw.Orb.rep_tr hd' (by omega) (c2 ▸ hc))) (Raw.Orb.rep_tr hd' (by omega) (c3 ▸ hd)))
      (Raw.Orb.rep_tr hd' (by omega) (c4 ▸ he))
  rw [← e5]
  exact ⟨hr, sift5 hd' hbs (c0 ▸ ha) (c1 ▸ hb1) (c2 ▸ hc) (c3 ▸ hd) (c4 ▸ he) hr⟩

theorem baseComm_of_sep {G : Subgroup (Equiv.Perm (Fin 1755))}
    (hsep : ∀ γ ∈ G, (∀ t < 5, ∀ h : base[t]! < 1755, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → γ = 1)
    (hbl : ∀ t < 5, base[t]! < 1755) (hBP : ∀ t < 5, base[t]! = pg 11 (mask 11) BP t)
    {X Y : Array Nat} {σ τ : Equiv.Perm (Fin 1755)} (hX : Rep 1755 X σ) (hY : Rep 1755 Y τ)
    (hσ : σ ∈ G) (hτ : τ ∈ G) {gx gy : Nat → Nat} (hgx : ∀ i < 1755, gx i = X[i]!)
    (hgy : ∀ i < 1755, gy i = Y[i]!) :
    baseComm BP 5 gx gy = commA X Y := by
  rw [Bool.eq_iff_iff, commA, eqA_iff (rep_compA hX hY) (rep_compA hY hX)]
  have hpt : ∀ t (ht : t < 5), gx (gy base[t]!) = ((σ * τ) ⟨base[t]!, hbl t ht⟩ : Nat) ∧
      gy (gx base[t]!) = ((τ * σ) ⟨base[t]!, hbl t ht⟩ : Nat) := by
    intro t ht
    have hb := hbl t ht
    rw [hgy _ hb, hY.apply hb, hgx _ (τ _).2, hX.apply (τ _).2, hgx _ hb, hX.apply hb,
      hgy _ (σ _).2, hY.apply (σ _).2]
    exact ⟨rfl, rfl⟩
  constructor
  · intro h
    have hfix : ∀ t < 5, ∀ hb : base[t]! < 1755,
        ((τ * σ)⁻¹ * (σ * τ)) ⟨base[t]!, hb⟩ = ⟨base[t]!, hb⟩ := by
      intro t ht hb
      have := allN_spec h t ht
      rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2] at this
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact Fin.ext this
    have h1 := hsep _ (G.mul_mem (G.inv_mem (G.mul_mem hτ hσ)) (G.mul_mem hσ hτ)) hfix
    exact inv_mul_eq_one.1 h1 |>.symm
  · intro h
    unfold baseComm
    refine allN_of_forall fun t ht => ?_
    rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2, h]

theorem gptC_get {k : Nat} (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hk : k < tot5 LR) :
    ∀ i < 1755, gptC LR TR k i =
      (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k))[i]! := by
  intro i hi
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hb hp hl d0 d1 d2 d3 d4
  obtain ⟨-, hg⟩ := gpt_facts k0 k1 k2 k3 k4
  rw [prodCode_eq, (hg i hi).1, ← gptR_eq]
  unfold gptC
  simp only [PackFld.strictN_eqP]
  rfl

theorem rep_of_siftA (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) :
    ∀ d l, l + d = 5 → ∀ g : Array Nat, (∀ i < 1755, g[i]! < 1755) →
      siftA 1755 (rawLevels 1755 S base) base l g = true → ∃ γ, Rep 1755 g γ := by
  have hd' := hd_of_binds hb hp hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro l hl' g _ h
    rw [siftA, dite_eq_right (by rw [ChainArrays.chainLevels_size]; omega)] at h
    refine ⟨1, fun x => ?_⟩
    have := allLt_spec h x.2
    rw [beq_iff_eq, idA_get x.2] at this
    exact this
  | succ d ih =>
    intro l hl' g hg h
    have hls : l < (rawLevels 1755 S base).size := by
      rw [ChainArrays.chainLevels_size]
      omega
    rw [siftA, dite_eq_left hls, ChainArrays.chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    have hlb : l < base.size := by omega
    have rI := Raw.Orb.rep_trInv hd' hlb hk
    have rT := Raw.Orb.rep_tr hd' hlb hk
    obtain ⟨γ', hγ'⟩ := ih (l + 1) (by omega) _ (fun i hi => by
      rw [compA_get hi]
      exact rI.lt (hg i hi)) h
    refine ⟨Raw.Orb.trP 1755 S base l
      ((ChainArrays.lev 1755 S base l).pos[g[base[l]!]!]!) * γ', fun x => ?_⟩
    have e1 := hγ' x
    rw [compA_get x.2] at e1
    have e2 : γ' x = (Raw.Orb.trP 1755 S base l
        ((ChainArrays.lev 1755 S base l).pos[g[base[l]!]!]!))⁻¹ ⟨g[(x : Nat)]!, hg x x.2⟩ :=
      Fin.ext (by rw [← e1, rI.apply (hg x x.2)])
    rw [Equiv.Perm.mul_apply, e2]
    simp

theorem siftPfB_eq {kK BPK BPN : Nat} {PK PKI LRK TRK TRIK : Nat → Nat} {SK : Array (Array Nat)}
    {baseK : Array Nat} (hbK : Binds 1755 11 PK kK 5 BPK SK baseK)
    (hpK : allN kK (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PK j) (PKI j)) = true)
    (hlK : LevelsOK 1755 11 PK PKI LRK TRK TRIK kK 5 BPK) {G : Subgroup (Equiv.Perm (Fin 1755))}
    (hGK : Raw.Orb.Gen 1755 SK SK.size ≤ G)
    (hsep : ∀ γ ∈ G, (∀ t < 5, ∀ h : pg 11 (mask 11) BPN t < 1755,
      γ ⟨pg 11 (mask 11) BPN t, h⟩ = ⟨pg 11 (mask 11) BPN t, h⟩) → γ = 1)
    (hNl : ∀ t < 5, pg 11 (mask 11) BPN t < 1755) :
    ∀ d l, l + d = 5 → ∀ (g : Array Nat) (gf : Nat → Nat) (γ : Equiv.Perm (Fin 1755)),
      Rep 1755 g γ → γ ∈ G → (∀ i < 1755, g[i]! = gf i) →
      siftA 1755 (rawLevels 1755 SK baseK) baseK l g = siftPfB LRK TRIK BPK BPN d l gf := by
  have hd' := hd_of_binds hbK hpK hlK
  have hbl := Raw.Orb.base_lt_of_levels hbK hlK
  have hbs : baseK.size = 5 := hbK.2.2.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro l hl' g gf γ hg hγ hgf
    rw [siftA, dite_eq_right (by rw [ChainArrays.chainLevels_size]; omega)]
    change _ = allN 5 (fun t => strictB (pg 11 (mask 11) BPN t) (fun b => Nat.beq (gf b) b))
    rw [Bool.eq_iff_iff, eqA_iff hg rep_idA]
    constructor
    · rintro rfl
      refine allN_of_forall fun t ht => ?_
      rw [strictB_eq, ← hgf _ (hNl t ht), hg.apply (hNl t ht), Nat.beq_eq]
      rfl
    · intro h
      refine hsep γ hγ fun t ht hb => Fin.ext ?_
      have := allN_spec h t ht
      rw [strictB_eq, ← hgf _ hb, hg.apply hb, Nat.beq_eq] at this
      exact this
  | succ d ih =>
    intro l hl' g gf γ hg hγ hgf
    have hlb : l < 5 := by omega
    have hls : l < (rawLevels 1755 SK baseK).size := by
      rw [ChainArrays.chainLevels_size]
      omega
    obtain ⟨A, hT⟩ := Raw.Orb.agree_levelK hbK hpK hbl (R := LRK) (TRI := TRIK) hlb (hlK l hlb)
    have hbt : baseK[l]! = pg 11 (mask 11) BPK l := hbK.2.2.2.2.2.2 l hlb
    have hbl' := hbl l hlb
    have hz : g[baseK[l]!]! = gf baseK[l]! ∧ gf baseK[l]! < 1755 :=
      ⟨hgf _ hbl', by rw [← hgf _ hbl']; exact hg.lt hbl'⟩
    rw [siftA, dite_eq_left hls, ChainArrays.chainLevels_getElem hls]
    change _ = strictB (LRK l) (fun R => strictB (rpos 11 (mask 11) (1755 * 11) R
      (gf (pg 11 (mask 11) BPK l))) (fun k => bIf(Nat.blt k (rcnt R),
        strictB (TRIK (Nat.add (roff 1755 (1755 * 11) R) k))
          (fun t => siftPfB LRK TRIK BPK BPN d (Nat.succ l) (fun i => pgR t (gf i))), false)))
    rw [strictB_eq, strictB_eq, ← hbt, Raw.Orb.bIf_eq, hz.1]
    by_cases hk : (ChainArrays.lev 1755 SK baseK l).pos[gf baseK[l]!]! <
        (ChainArrays.lev 1755 SK baseK l).pts.size
    · have hK := (A.pos _ hz.2).2 hk
      have hKe := A.posE _ hz.2 hk
      rw [ite_eq_left (Nat.blt_eq.mpr hK), strictB_eq, hKe]
      simp only [hk, decide_true, Bool.true_and]
      have rI := Raw.Orb.rep_trInv hd' (by omega : l < baseK.size) hk
      have hmemT : Raw.Orb.trP 1755 SK baseK l ((ChainArrays.lev 1755 SK baseK l).pos[gf baseK[l]!]!)
          ∈ G := hGK (Raw.Orb.tr_spec hd' (by omega) _ hk).1.1
      refine ih (l + 1) (by omega) _ _ _ (rep_compA rI hg) (G.mul_mem (G.inv_mem hmemT) hγ)
        fun i hi => ?_
      have hR := (A.tr _ hk).2
      have e := (hT _ (hKe ▸ hK)).2 ⟨_, hg.lt hi⟩
      rw [compA_get hi, hgf i hi, pgR_eq]
      rw [← hgf i hi]
      exact (hR.apply (hg.lt hi)).trans e.symm
    · have hK : ¬ rpos 11 (mask 11) (1755 * 11) (LRK l) (gf baseK[l]!) < rcnt (LRK l) :=
        fun h => hk ((A.pos _ hz.2).1 h)
      have hb' : Nat.blt (rpos 11 (mask 11) (1755 * 11) (LRK l) (gf baseK[l]!)) (rcnt (LRK l)) =
          false := by
        cases e : Nat.blt (rpos 11 (mask 11) (1755 * 11) (LRK l) (gf baseK[l]!)) (rcnt (LRK l))
        · rfl
        · exact absurd (Nat.blt_eq.mp e) hK
      rw [hb']
      simp [hk]

end Group

theorem baseComm_eq {kS kO BP NS CH k t0 t1 t2 t3 t4 : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup)
    (htr : IsTr5 LR TR t0 t1 t2 t3 t4) (hk : k < tot5 LR) :
    baseComm BP 5 (gptR t0 t1 t2 t3 t4) (gptC LR TR k) =
      commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
        (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  obtain ⟨rX, sX⟩ := tr5_rep hb hp hl h0 h1 h2 h3 h4
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hb hp hl h0 h1 h2 h3 h4
  obtain ⟨-, hgX⟩ := gpt_facts k0 k1 k2 k3 k4
  have rY := prodCode_rep hb hp hl hk
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
  have sY : siftA 1755 (rawLevels 1755 S base) base 0
      (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) = true := by
    rw [prodCode_eq]
    exact (tr5_rep hb hp hl d0 d1 d2 d3 d4).2
  exact baseComm_of_sep hsep hbl (fun t ht => hb.2.2.2.2.2.2 t ht) rX rY ((hmem _ _ rX).1 sX)
    ((hmem _ _ rY).1 sY) (fun i hi => by rw [gptR_eq]; exact ((hgX i hi).1).symm)
    (gptC_get hb hp hl hk)

theorem baseCommG_eq {kS kO BP NS CH Y t0 t1 t2 t3 t4 : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup)
    (htr : IsTr5 LR TR t0 t1 t2 t3 t4)
    (hYc : canonK 1755 11 (mask 11) (1755 * 11) Y = true)
    (hY : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 Y) = true) :
    baseComm BP 5 (gptR t0 t1 t2 t3 t4) (pgR Y) =
      commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (unpack 1755 11 Y) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  obtain ⟨rX, sX⟩ := tr5_rep hb hp hl h0 h1 h2 h3 h4
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hb hp hl h0 h1 h2 h3 h4
  obtain ⟨-, hgX⟩ := gpt_facts k0 k1 k2 k3 k4
  obtain ⟨-, -, -, rYc⟩ := canonK_facts hYc
  obtain ⟨τ, rY⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rYc i hi) hY
  exact baseComm_of_sep hsep hbl (fun t ht => hb.2.2.2.2.2.2 t ht) rX rY ((hmem _ _ rX).1 sX)
    ((hmem _ _ rY).1 hY) (fun i hi => by rw [gptR_eq]; exact ((hgX i hi).1).symm)
    (fun i hi => by rw [pgR_eq, unpack_getT hi])

theorem ktKB_eq {kK kN kO BPK BPN NS CH t0 t1 t2 t3 t4 : Nat}
    {PK PKI LRK TRK TRIK PN PNI LRN TRN TRIN : Nat → Nat}
    {SK SN : Array (Array Nat)} {baseK baseN : Array Nat} {D : List (List Int)}
    (hbK : Binds 1755 11 PK kK 5 BPK SK baseK)
    (hpK : allN kK (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PK j) (PKI j)) = true)
    (hlK : LevelsOK 1755 11 PK PKI LRK TRK TRIK kK 5 BPK)
    (hbN : Binds 1755 11 PN kN 5 BPN SN baseN)
    (hhN : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PN PNI kN kO D 5 BPN = true)
    (hlN : LevelsOK 1755 11 PN PNI LRN TRN TRIN kN 5 BPN) (hNS : 1755 ≤ NS * CH)
    (hsN : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PN PNI LRN TRN TRIN
      kN BPN 5 i (stepsAt 1755 11 PN kN BPN i) (s * CH) CH = true)
    (hndN : baseN.toList.Nodup)
    (hKN : ∀ j < kK, siftA 1755 (rawLevels 1755 SN baseN) baseN 0 SK[j]! = true)
    (htr : IsTr5 LRN TRN t0 t1 t2 t3 t4) :
    ktKB LRK TRIK BPK BPN t0 t1 t2 t3 t4 =
      siftA 1755 (rawLevels 1755 SK baseK) baseK 0
        (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) := by
  have hpN := (Raw.Orb.head_facts hhN).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hbN hhN hlN hNS hsN hndN
  have hblN := Raw.Orb.base_lt_of_levels hbN hlN
  have hdK := hd_of_binds hbK hpK hlK
  have hSK : SK.size = kK := hbK.2.2.2.1
  have hGK : Raw.Orb.Gen 1755 SK SK.size ≤ G := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    exact (hmem _ _ (Raw.Orb.rep_S hdK j.2)).1 (hKN j (hSK ▸ j.2))
  have hsep' : ∀ γ ∈ G, (∀ t < 5, ∀ h : pg 11 (mask 11) BPN t < 1755,
      γ ⟨pg 11 (mask 11) BPN t, h⟩ = ⟨pg 11 (mask 11) BPN t, h⟩) → γ = 1 := by
    intro γ hγ hfix
    refine hsep γ hγ fun t ht h => ?_
    have e := hbN.2.2.2.2.2.2 t ht
    have := hfix t ht (e ▸ h)
    simp only [← e] at this
    exact this
  have hNl : ∀ t < 5, pg 11 (mask 11) BPN t < 1755 := fun t ht => by
    rw [← hbN.2.2.2.2.2.2 t ht]
    exact hblN t ht
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  obtain ⟨rX, sX⟩ := tr5_rep hbN hpN hlN h0 h1 h2 h3 h4
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hbN hpN hlN h0 h1 h2 h3 h4
  obtain ⟨-, hgX⟩ := gpt_facts k0 k1 k2 k3 k4
  exact (siftPfB_eq hbK hpK hlK hGK hsep' hNl 5 0 rfl _ _ _ rX ((hmem _ _ rX).1 sX)
    fun i hi => by rw [gptR_eq]; exact (hgX i hi).1).symm

open CFSG.Certificates CFSG.Monster.B.Co2 in
theorem qtree_sound {kS kO BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {G Q : List Nat}
    {W : List (Nat × Nat)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup)
    (hA : ascK (tot5 LR) Q 0 = true) (h : qtreeK BP LR TR G Q W = true) (x : Nat)
    (hx : canonK 1755 11 (mask 11) (1755 * 11) x = true) :
    (Q.map fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)).all
        (fun q => commA (unpack 1755 11 x) q) =
      (G.map fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)).all
        (fun q => commA (unpack 1755 11 x) q) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨Gr, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hd' := hd_of_binds hb hp hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  obtain ⟨-, -, -, rx⟩ := canonK_facts hx
  obtain ⟨X, hXd⟩ : ∃ X, X = unpack 1755 11 x := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P : Nat → Array Nat,
      P = fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k) := ⟨_, rfl⟩
  have hPk : ∀ k, unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k) = P k :=
    fun k => by rw [hPd]
  have hXlt : ∀ i < 1755, X[i]! < 1755 := fun i hi => by
    rw [hXd, unpack_getT hi]
    exact rx i hi
  have hPc : ∀ k < tot5 LR, ∃ ρ, Rep 1755 (P k) ρ ∧ ρ ∈ Gr := by
    intro k hk
    obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
    have rY := prodCode_rep hb hp hl hk
    have sY : siftA 1755 (rawLevels 1755 S base) base 0
        (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) = true := by
      rw [prodCode_eq]
      exact (tr5_rep hb hp hl d0 d1 d2 d3 d4).2
    rw [← hPk]
    exact ⟨_, rY, (hmem _ _ rY).1 sY⟩
  have hPlt : ∀ k < tot5 LR, ∀ i < 1755, (P k)[i]! < 1755 := fun k hk i hi => by
    obtain ⟨ρ, hr, -⟩ := hPc k hk
    exact hr.lt hi
  have hcomm : ∀ a : Array Nat, commA X a = true ↔ ∀ i < 1755, X[a[i]!]! = a[X[i]!]! := by
    intro a
    unfold commA eqA
    rw [allLt_iff]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [beq_iff_eq, compA_get hi, compA_get hi]
  have hstep : ∀ c g q, c < tot5 LR → g < tot5 LR → q < tot5 LR →
      treeStep BP LR TR c g q = true → ∀ i < 1755, (P c)[i]! = (P g)[(P q)[i]!]! := by
    intro c g q hc hg hq hT i hi
    obtain ⟨ρc, rc, mc⟩ := hPc c hc
    obtain ⟨ρg, rg, mg⟩ := hPc g hg
    obtain ⟨ρq, rq, mq⟩ := hPc q hq
    have hfix : ∀ t < 5, ∀ h : base[t]! < 1755,
        (ρc⁻¹ * (ρg * ρq)) ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩ := by
      intro t ht hbt
      have := allN_spec hT t ht
      rw [strictB_eq, ← hb.2.2.2.2.2.2 t ht, Nat.beq_eq, gptC_get hb hp hl hc _ hbt,
        gptC_get hb hp hl hq _ hbt, hPk q, gptC_get hb hp hl hg _ (hPlt q hq _ hbt), hPk c, hPk g]
        at this
      rw [rc.apply hbt, rq.apply hbt, rg.apply (ρq _).2] at this
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply]
      exact (Fin.ext this).symm
    have e := hsep _ (Gr.mul_mem (Gr.inv_mem mc) (Gr.mul_mem mg mq)) hfix
    have e' : ρc = ρg * ρq := inv_mul_eq_one.1 e
    rw [rc.apply hi, rq.apply hi, rg.apply (ρq _).2, e']
    rfl
  have htree : ∀ (C : List Nat) (W : List (Nat × Nat)) (S0 : List Nat),
      genTreeK BP LR TR G C W S0 = true → (∀ c ∈ C, c < tot5 LR) →
      (∀ s ∈ S0, s < tot5 LR ∧ commA X (P s) = true) →
      (∀ g ∈ G, g < tot5 LR ∧ commA X (P g) = true) → ∀ c ∈ C, commA X (P c) = true := by
    intro C
    induction C with
    | nil =>
      intro _ _ _ _ _ _ c hc
      exact absurd hc List.not_mem_nil
    | cons c C ih =>
      intro W S0 hT hC hS hG
      cases W with
      | nil => exact absurd hT Bool.false_ne_true
      | cons gp W' =>
        obtain ⟨g, q⟩ := gp
        have hT' : bAnd(memN g G, bAnd(memN q S0, bAnd(treeStep BP LR TR c g q,
            genTreeK BP LR TR G C W' (c :: S0)))) = true := hT
        simp only [bAnd_iff] at hT'
        obtain ⟨h1, h2, h3, h4⟩ := hT'
        have hg := hG g (memN_spec h1)
        have hq := hS q (memN_spec h2)
        have hc : c < tot5 LR := hC c List.mem_cons_self
        have hcc : commA X (P c) = true := by
          have cg := (hcomm _).1 hg.2
          have cq := (hcomm _).1 hq.2
          refine (hcomm _).2 fun i hi => ?_
          rw [hstep c g q hc hg.1 hq.1 h3 i hi, hstep c g q hc hg.1 hq.1 h3 _ (hXlt i hi),
            cg _ (hPlt q hq.1 i hi), cq i hi]
        intro c' hc'
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact hcc
        · refine ih W' (c :: S0) h4 (fun c'' h => hC c'' (List.mem_cons_of_mem _ h)) ?_ hG c' hc'
          intro s hs
          rcases List.mem_cons.1 hs with rfl | hs
          · exact ⟨hc, hcc⟩
          · exact hS s hs
  unfold qtreeK at h
  obtain ⟨hGQ, hQ⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, hQ2⟩ := ascK_spec hA
  have hGQ' : ∀ g ∈ G, g ∈ Q := by
    clear hQ h htree
    induction G with
    | nil => exact fun g hg => absurd hg List.not_mem_nil
    | cons g0 G ih =>
      have h' : bAnd(memN g0 Q, allL (fun g => memN g Q) G) = true := hGQ
      obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h'
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact memN_spec a
      · exact ih b g hg
  cases Q with
  | nil => exact absurd hQ Bool.false_ne_true
  | cons c0 Q' =>
    have hQ' : bAnd(Nat.beq c0 0, genTreeK BP LR TR G Q' W [c0]) = true := hQ
    obtain ⟨h0, hT⟩ := (bAnd_iff _ _).1 hQ'
    have hc0 : c0 = 0 := Nat.eq_of_beq_eq_true h0
    subst hc0
    have h0t : 0 < tot5 LR := (hQ2 0 List.mem_cons_self).2
    have hid : ∀ i < 5, Raw.Orb.trP 1755 S base i 0 = 1 := by
      intro i hi
      have F := Raw.Orb.lev_facts hd' (by omega : i < base.size)
      exact (eqA_iff (Raw.Orb.rep_tr hd' (by omega) F.pos) rep_idA).1 F.tr_zero
    have r0 := prodCode_rep hb hp hl h0t
    simp only [Nat.zero_div, Nat.zero_mod] at r0
    rw [hid 0 (by omega), hid 1 (by omega), hid 2 (by omega), hid 3 (by omega), hid 4 (by omega),
      one_mul, one_mul, one_mul, one_mul] at r0
    rw [hPk] at r0
    have h0c : commA X (P 0) = true :=
      (hcomm _).2 fun i hi => by rw [r0.apply hi, r0.apply (hXlt i hi)]; rfl
    rw [← hXd]
    simp only [hPk]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro H q hq
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hq
      exact H _ (List.mem_map.2 ⟨g, hGQ' g hg, rfl⟩)
    · intro H
      have hG : ∀ g ∈ G, g < tot5 LR ∧ commA X (P g) = true := fun g hg =>
        ⟨(hQ2 g (hGQ' g hg)).2, H _ (List.mem_map.2 ⟨g, hg, rfl⟩)⟩
      intro q hq
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
      rcases List.mem_cons.1 hk with rfl | hk
      · exact h0c
      · refine htree Q' W [0] hT (fun c hc => (hQ2 c (List.mem_cons_of_mem _ hc)).2) ?_ hG k hk
        intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact ⟨h0t, h0c⟩

end CFSG.KS.SporSch

end
