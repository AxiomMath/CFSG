module

public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Certificates.Kernel.SporSch.ChainKClasses
import CFSG.Certificates.Kernel.Spor.PinvSSound
import CFSG.Sporadic.Recognition.LyonsAmalgamInv
import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

variable {n w : Nat}

theorem prep_pinvS {H : Nat} {h : Equiv.Perm (Fin n)} (hw : n < 2 ^ w) (hH : PRep n w H h) :
    PRep n w (pinvS n w (mask w) H) h⁻¹ ∧ pinvS n w (mask w) H >>> (n * w) = 0 := by
  have hI : CFSG.KS.PinvS.InjK n w H :=
    ⟨fun i hi => by rw [hH ⟨i, hi⟩]; exact (h ⟨i, hi⟩).2, fun a ha b hb e => by
      rw [hH ⟨a, ha⟩, hH ⟨b, hb⟩] at e
      exact congrArg Fin.val (h.injective (Fin.ext e))⟩
  refine ⟨fun x => ?_, CFSG.KS.PinvS.pinvS_shr hw hI.1⟩
  have e := CFSG.KS.PinvS.pg_pinvS hw hI (h⁻¹ x).2
  rw [hH (h⁻¹ x)] at e
  simpa using e

theorem prep_cw1 {X H : Nat} {x h : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32) (hw : n < 2 ^ w)
    (hX : PRep n w X x) (hH : PRep n w H h) :
    PRep n w (cw1 n w (mask w) X H) (x * (h * (x * h⁻¹))) :=
  prep_pcomp hn hX (prep_pcomp hn hH (prep_pcomp hn hX (prep_pinvS hw hH).1))

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

@[expose] noncomputable def oddAt (n w : Nat) (LR TR : Nat → Nat) (k mo : Nat) (W : Nat → Nat)
    (j : Nat) : Bool :=
  strictB (elemK n w (mask w) (n * w) (pidn n w) LR TR k j) (fun x =>
    bIf(Nat.beq x (pidn n w), true, bIf(Nat.beq (powK n w (mask w) (pidn n w) x mo) (pidn n w),
      witK n w (mask w) (n * w) (pidn n w) LR TR k (ordK LR k) mo x (W j), true)))

theorem oddK_eq (n w : Nat) (LR TR : Nat → Nat) (k mo : Nat) (W : Nat → Nat) (lo len : Nat) :
    oddK n w (mask w) (n * w) (pidn n w) LR TR k mo W lo len =
      allBlk lo (oddAt n w LR TR k mo W) len := by
  unfold oddK
  rw [Orb.strictB_eq]
  rfl

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem oddWitnessOK_of_oddAt {mo : Nat} {W : Nat → Nat}
    (h : ∀ j < ordK LR k, oddAt n w LR TR k mo W j = true) :
    oddWitnessOK n mo (allTables (certificate hn gens words bv hbs)) = true := by
  set Q := certificate hn gens words bv hbs
  set N := ordK LR k
  have h32 := chainK_h32 hQ
  have hsz := chainK_szOK hQ
  have hf := szOK_facts hsz
  have hw0 := PF.w_pos hf.2
  have hwn : n < 2 ^ w := by omega
  have pid := prep_pidn hf.1 hf.2
  have sid := PF.pidn_shr hf.1 hf.2
  have hA := forall₂_allTables_elem hQ hn hbs
  have hlen := hA.length_eq
  have hmemT : ∀ c < N, ∃ H ∈ allTables Q, Rep n H (elemP n w LR TR k c) := by
    intro c _
    have hyQ : elemP n w LR TR k c ∈ ((List.range N).map (elemP n w LR TR k)).reverse := by
      rw [List.mem_reverse, mem_elemP_iff hQ hn hbs]
      exact elemP_mem hQ hn hbs c
    exact exists_mem_of_forall₂_left hA _ hyQ
  rw [oddWitnessOK, List.all_eq_true]
  intro X hX
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hX
  have hiN : i < N := by
    rw [hlen] at hi
    simpa using hi
  set j := N - 1 - i with hjdef
  have hj : j < N := by omega
  have hRi : Rep n (allTables Q)[i] (elemP n w LR TR k j) := by
    have := hA.get hi (by simpa [← hlen] using hi)
    simp only [List.get_eq_getElem, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range] at this
    convert this using 2
  set x := elemP n w LR TR k j
  set XP := elemK n w (mask w) (n * w) (pidn n w) LR TR k j
  have pX : PRep n w XP x := prep_elemK hQ j
  have sX : XP >>> (n * w) = 0 := elemK_shr hQ j
  have hone := h j hj
  unfold oddAt at hone
  rw [Orb.strictB_eq, Orb.bIf_eq, Orb.bIf_eq, beq_prep hw0 pX pid sX sid,
    beq_prep hw0 (prep_powK hsz pX mo).1 pid (prep_powK hsz pX mo).2 sid] at hone
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hone ⊢
  have hpw1 := powFixW_iff perm_faithful (List.Forall₂.cons hRi List.Forall₂.nil) mo
  simp only [List.prod_cons, List.prod_nil, mul_one] at hpw1
  by_cases e1 : x = 1
  · left; left; left
    exact (CFSG.Sporadic.SmallOddCore.tblEq_idT_iff h32 hRi).2 e1
  by_cases e2 : x ^ mo = 1
  swap
  · left; left; right
    cases e : powFixW n [(allTables Q)[i]] mo
    · rfl
    · exact absurd (hpw1.1 e) e2
  simp only [e1, e2, ↓reduceIte] at hone
  unfold witK at hone
  rw [Orb.bIf_eq, beq_dec] at hone
  by_cases hc0 : W j = 0
  · simp [hc0] at hone
  simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte, Orb.strictB_eq, Orb.bIf_eq,
    Nat.blt_eq] at hone
  by_cases hc1 : Nat.sub (W j) 1 < ordK LR k
  ·
    simp only [hc1, ↓reduceIte] at hone
    left; right
    set c' := Nat.sub (W j) 1
    set y := elemP n w LR TR k c'
    have pY := prep_elemK hQ c'
    have pW := prep_powK hsz (prep_cw1 h32 hwn pX pY) mo
    rw [beq_prep hw0 pW.1 pid pW.2 sid] at hone
    have hne : (x * (y * (x * y⁻¹))) ^ mo ≠ 1 := by
      simp only [decide_eq_true_eq, ite_eq_right_iff, Bool.false_eq_true, imp_false] at hone
      exact hone
    obtain ⟨H, hH, hHR⟩ := hmemT c' hc1
    have hinv := invOK_invT_of_rep h32 hHR
    have hHi := Rep.inv_of_invOK hHR hinv
    rw [List.any_eq_true]
    refine ⟨H, hH, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hinv, ?_⟩
    have hpw := powFixW_iff perm_faithful (List.Forall₂.cons hRi (List.Forall₂.cons hHR
      (List.Forall₂.cons hRi (List.Forall₂.cons hHi List.Forall₂.nil)))) mo
    cases e : powFixW n [(allTables Q)[i], H, (allTables Q)[i], invT n H] mo
    · rfl
    · exact absurd (hpw.1 e) (by simpa [mul_assoc] using hne)
  simp only [hc1, ↓reduceIte] at hone
  by_cases hc2 : Nat.sub (Nat.sub (W j) 1) (ordK LR k) < Nat.mul (ordK LR k) (ordK LR k)
  swap
  · simp only [hc2, ↓reduceIte, Bool.false_eq_true] at hone
  simp only [hc2, ↓reduceIte] at hone
  right
  set c2 := Nat.sub (Nat.sub (W j) 1) (ordK LR k)
  have hNpos : 0 < N := ordK_pos hQ
  have hq : c2 / N < N := (Nat.div_lt_iff_lt_mul hNpos).2 hc2
  have hr : c2 % N < N := Nat.mod_lt _ hNpos
  set y1 := elemP n w LR TR k (c2 / N)
  set y2 := elemP n w LR TR k (c2 % N)
  have p1 := prep_elemK hQ (Nat.div c2 N)
  have p2 := prep_elemK hQ (Nat.mod c2 N)
  have pW := prep_powK hsz (prep_pcomp h32 (prep_cw1 h32 hwn pX p1)
    (prep_pcomp h32 p2 (prep_pcomp h32 pX (prep_pinvS hwn p2).1))) mo
  rw [beq_prep hw0 pW.1 pid pW.2 sid] at hone
  have hne : (x * (y1 * (x * y1⁻¹)) * (y2 * (x * y2⁻¹))) ^ mo ≠ 1 := by
    simp only [decide_eq_true_eq, ite_eq_right_iff, Bool.false_eq_true, imp_false] at hone
    exact hone
  obtain ⟨H1, hH1, hR1⟩ := hmemT _ hq
  obtain ⟨H2, hH2, hR2⟩ := hmemT _ hr
  have hinv1 := invOK_invT_of_rep h32 hR1
  have hinv2 := invOK_invT_of_rep h32 hR2
  have hI1 := Rep.inv_of_invOK hR1 hinv1
  have hI2 := Rep.inv_of_invOK hR2 hinv2
  rw [List.any_eq_true]
  refine ⟨H1, hH1, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨hinv1, ?_⟩
  rw [List.any_eq_true]
  refine ⟨H2, hH2, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨hinv2, ?_⟩
  have hpw := powFixW_iff perm_faithful (List.Forall₂.cons hRi (List.Forall₂.cons hR1
    (List.Forall₂.cons hRi (List.Forall₂.cons hI1 (List.Forall₂.cons hR2
      (List.Forall₂.cons hRi (List.Forall₂.cons hI2 List.Forall₂.nil))))))) mo
  cases e : powFixW n [(allTables Q)[i], H1, (allTables Q)[i], invT n H1, H2,
    (allTables Q)[i], invT n H2] mo
  · rfl
  · exact absurd (hpw.1 e) (by simpa [mul_assoc] using hne)

theorem chainK_odd' {mo : Nat} {W : Nat → Nat}
    (h : oddK n w (mask w) (n * w) (pidn n w) LR TR k mo W 0 (ordK LR k) = true) :
    oddWitnessOK n mo (allTables (certificate hn gens words bv hbs)) = true := by
  refine oddWitnessOK_of_oddAt hQ hn hbs (mo := mo) (W := W) fun j hj => ?_
  rw [oddK_eq, allBlk_eq, List.all_eq_true] at h
  simpa using h j (List.mem_range.2 hj)

theorem chainK_oddB' {mo L NB : Nat} {W : Nat → Nat} (hL : ordK LR k ≤ NB * L)
    (h : ∀ s < NB, oddK n w (mask w) (n * w) (pidn n w) LR TR k mo W (s * L) L = true) :
    oddWitnessOK n mo (allTables (certificate hn gens words bv hbs)) = true :=
  oddWitnessOK_of_oddAt hQ hn hbs
    (of_blocks hQ hL fun s hs => by rw [← oddK_eq]; exact h s hs)

end Chain

end CFSG.KS.SporSch.MOC

end
