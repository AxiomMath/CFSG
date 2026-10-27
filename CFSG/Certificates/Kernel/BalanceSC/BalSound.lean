module

public import CFSG.Certificates.Kernel.BalanceSC.TableSound
public import CFSG.Certificates.Kernel.BalanceSC.Elems
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.BalanceSC.BalSound

open CFSG.KC.BalanceSC CFSG.KC.BalanceSC.SylowEq CFSG.KC.BalanceSC.TableSound
open CFSG.KC.Enum (pg pcomp pidn)
open CFSG.KS (mask pinvS)
open CFSG.KS.Raw (unpack szOK)
open CFSG.KC.BfsPin (PP)
open CFSG.OddStandard.Solomon75.AhatData (Rep rep_mulA eqA_iff)
open Equiv Equiv.Perm Finset

theorem beq_land_one (b i : ℕ) : Nat.beq (Nat.land (Nat.shiftRight b i) 1) 1 = b.testBit i := by
  have e : Nat.land (Nat.shiftRight b i) 1 = b / 2 ^ i % 2 := by
    change (b >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem imgMask_succ (m p b : ℕ) :
    imgMask (m + 1) p b = imgMask m p b ||| (if b.testBit m then 1 <<< pg 4 15 p m else 0) := by
  change Nat.lor (imgMask m p b) (Bool.rec (motive := fun _ => Nat) 0
    (Nat.shiftLeft 1 (pg 4 15 p m)) (Nat.beq (Nat.land (Nat.shiftRight b m) 1) 1)) = _
  rw [beq_land_one]
  cases b.testBit m <;> rfl

theorem testBit_imgMask (p b j : ℕ) : ∀ m, (imgMask m p b).testBit j = true ↔
    ∃ i < m, b.testBit i = true ∧ pg 4 15 p i = j
  | 0 => by
    change (0 : ℕ).testBit j = true ↔ _
    simp
  | m + 1 => by
    rw [imgMask_succ, Nat.testBit_or, Bool.or_eq_true, testBit_imgMask p b j m]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · by_cases hb : b.testBit m = true
        · rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
          exact ⟨m, by omega, hb, of_decide_eq_true h⟩
        · rw [if_neg hb, Nat.zero_testBit] at h
          exact absurd h (by simp)
    · rintro ⟨i, hi, hb, he⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, hb, he⟩
      · refine Or.inr ?_
        rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow]
        exact decide_eq_true he

theorem testBit_unionL (j : ℕ) : ∀ L : List ℕ, (unionL L).testBit j = true ↔
    ∃ m ∈ L, m.testBit j = true
  | [] => by
    change (0 : ℕ).testBit j = true ↔ _
    simp
  | d :: L => by
    change (d ||| unionL L).testBit j = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_unionL j L]
    simp only [List.mem_cons, exists_eq_or_imp]

variable {n : ℕ}

theorem land_fmask (s t : Finset (Fin n)) : Nat.land (fmask s) (fmask t) = fmask (s ∩ t) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change ((fmask s) &&& (fmask t)).testBit j = _
  rw [Nat.testBit_and]
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, testBit_fmask, testBit_fmask, testBit_fmask]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have : y = x := Fin.ext hxy
    subst this
    exact ⟨y, mem_inter.2 ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, (mem_inter.1 hx).1, rfl⟩, ⟨x, (mem_inter.1 hx).2, rfl⟩⟩

theorem nonempty_of_fmask_ne_zero {s : Finset (Fin n)} (h : fmask s ≠ 0) : s.Nonempty := by
  by_contra hs
  rw [not_nonempty_iff_eq_empty] at hs
  subst hs
  exact h (by simp [fmask, nmask])

theorem fmask_singleton (z : Fin n) : fmask {z} = 2 ^ (z : ℕ) := by
  simp [fmask, nmask]

theorem nonOne_two_pow (i : ℕ) : nonOne (2 ^ i) = false := by
  have h1 : Nat.beq (2 ^ i) 0 = false :=
    Bool.eq_false_iff.2 fun h => absurd (Nat.eq_of_beq_eq_true h) (by positivity)
  have h2 : Nat.land (2 ^ i) (Nat.sub (2 ^ i) 1) = 0 := by
    change 2 ^ i &&& (2 ^ i - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  unfold nonOne
  rw [h1, h2]
  rfl

theorem nonOne_fmask {s : Finset (Fin n)} (h : s.card = 1) : nonOne (fmask s) = false := by
  obtain ⟨z, rfl⟩ := card_eq_one.1 h
  rw [fmask_singleton, nonOne_two_pow]

theorem pg_of_rep {p : ℕ} {σ : Perm (Fin n)} (h : Rep n (unpack n 4 p) σ) (i : Fin n) :
    pg 4 15 p i = σ i := by
  have := h i
  rw [CFSG.KS.Raw.Orb.unpack_get i.2] at this
  exact this

theorem imgMask_fmask {p : ℕ} {σ : Perm (Fin n)} (h : Rep n (unpack n 4 p) σ)
    (B : Finset (Fin n)) : imgMask n p (fmask B) = fmask (B.map σ.toEmbedding) := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.2
  rw [testBit_imgMask, testBit_fmask]
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (testBit_fmask B i).1 hb
    exact ⟨σ x, mem_map_of_mem _ hx, (pg_of_rep h x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
    exact ⟨x, x.2, (testBit_fmask B x).2 ⟨x, hx, rfl⟩, pg_of_rep h x⟩

theorem unionL_sortMasks (e : Perm (Fin n)) : unionL (sortMasks e) = fmask e.support := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.2
  rw [testBit_unionL, testBit_fmask]
  constructor
  · rintro ⟨m, hm, hb⟩
    obtain ⟨B, hB, rfl⟩ := mem_sortMasks.1 hm
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
    obtain ⟨z, hz, rfl⟩ := (testBit_fmask _ j).1 hb
    exact ⟨z, (mem_blk.1 hz).mem_support_iff.1 hx, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fmask (blk e z), mem_sortMasks.2 ⟨_, mem_image_of_mem _ hz, rfl⟩,
      (testBit_fmask _ _).2 ⟨z, mem_blk.2 (SameCycle.refl _ _), rfl⟩⟩

theorem rep_pinvS {p : ℕ} (hp : PP n 4 p) {σ : Perm (Fin n)} (hσ : Rep n (unpack n 4 p) σ) :
    Rep n (unpack n 4 (pinvS n 4 15 p)) σ⁻¹ := by
  intro i
  rw [CFSG.KS.Raw.Orb.unpack_get i.2]
  have hw : n < 2 ^ 4 := by
    have := (CFSG.KC.BfsPin.szOK_facts' hp.sz).2
    omega
  have h1 : pg 4 (mask 4) p (σ⁻¹ i : Fin n) = i := by
    have := pg_of_rep hσ (σ⁻¹ i)
    have e1 : σ (σ⁻¹ i) = i := by simp
    rw [e1] at this
    exact this
  have := CFSG.KS.PinvS.pg_pinvS hw hp.2 (σ⁻¹ i).2
  rw [h1] at this
  exact this

theorem isWit_of_witB {pe w : ℕ} {ε σ : Perm (Fin n)} (hpe : PP n 4 pe)
    (he : Rep n (unpack n 4 pe) ε) (hw : PP n 4 w) (hσ : Rep n (unpack n 4 w) σ)
    (h : witB n pe w = true) : IsWit ε σ := by
  have hi : PP n 4 (pinvS n 4 15 w) := hw.inv
  have hir := rep_pinvS hw hσ
  have hpi : PP n 4 (pcomp n 4 15 pe (pinvS n 4 15 w)) := pp_mul hpe hi
  have hf : PP n 4 (pcomp n 4 15 w (pcomp n 4 15 pe (pinvS n 4 15 w))) := pp_mul hw hpi
  have hfr : Rep n (unpack n 4 (pcomp n 4 15 w (pcomp n 4 15 pe (pinvS n 4 15 w))))
      (σ * ε * σ⁻¹) := by
    rw [← mulA_u hw hpi, ← mulA_u hpe hi, mul_assoc]
    exact rep_mulA hσ (rep_mulA he hir)
  have h' : Nat.beq (pcomp n 4 15 (pcomp n 4 15 w (pcomp n 4 15 pe (pinvS n 4 15 w))) pe)
      (pcomp n 4 15 pe (pcomp n 4 15 w (pcomp n 4 15 pe (pinvS n 4 15 w)))) = false := by
    unfold witB at h
    rw [strictB_eq, strictB_eq, notB_eq, Bool.not_eq_true'] at h
    exact h
  intro hc
  have h1 := rep_mulA hfr he
  have h2 := rep_mulA he hfr
  rw [mulA_u hf hpe] at h1
  rw [mulA_u hpe hf] at h2
  have h3 := (eqA_iff h1 h2).2 hc
  rw [eqA_u (pp_mul hf hpe) (pp_mul hpe hf), h'] at h3
  exact absurd h3 (by simp)

variable {e : Perm (Fin n)} {r : ℕ}

theorem isWit_of_critB (hr : r.Prime) (her : e ^ r = 1) (hkr : (cycParts e).card ≤ r) {o : Bool}
    (ho : o = false → (cycParts e).card < r) {p : ℕ} {σ : Perm (Fin n)}
    (hσ : Rep n (unpack n 4 p) σ) (h : critB n o p (sortMasks e) (unionL (sortMasks e)) = true) :
    IsWit e σ := by
  unfold critB at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hsc, hor⟩ := h
  unfold scB at hsc
  rw [anyL_eq, List.any_eq_true] at hsc
  obtain ⟨b, hb, hsc⟩ := hsc
  rw [strictB_eq] at hsc
  unfold scAt at hsc
  rw [bAnd_eq, Bool.and_eq_true, notB_eq, notB_eq, Bool.not_eq_true', Bool.not_eq_true'] at hsc
  obtain ⟨hnm, hmeet⟩ := hsc
  obtain ⟨B, hB, rfl⟩ := mem_sortMasks.1 hb
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
  rw [imgMask_fmask hσ] at hnm hmeet
  have hnot : (blk e x).map σ.toEmbedding ∉ cycParts e := fun hm => by
    have : memL (fmask ((blk e x).map σ.toEmbedding)) (sortMasks e) = true :=
      (memL_iff _ _).2 (mem_sortMasks.2 ⟨_, hm, rfl⟩)
    rw [hnm] at this
    exact absurd this (by simp)
  have hmeet' : ∃ u ∈ blk e x, σ u ∈ e.support := by
    rw [unionL_sortMasks, land_fmask] at hmeet
    have hne : fmask (((blk e x).map σ.toEmbedding) ∩ e.support) ≠ 0 := fun h0 => by
      rw [h0] at hmeet
      exact absurd hmeet (by simp)
    obtain ⟨z, hz⟩ := nonempty_of_fmask_ne_zero hne
    obtain ⟨hz1, hz2⟩ := mem_inter.1 hz
    obtain ⟨u, hu, rfl⟩ := mem_map.1 hz1
    exact ⟨u, hu, hz2⟩
  cases o with
  | false => exact isWit_of_sc hr her (ho rfl) hx hnot hmeet'
  | true =>
    have hor' : orthB n p (sortMasks e) = true := hor
    unfold orthB at hor'
    rw [anyL_eq, List.any_eq_true] at hor'
    obtain ⟨b', hb', hor'⟩ := hor'
    rw [strictB_eq, anyL_eq, List.any_eq_true] at hor'
    obtain ⟨d, hd, hnon⟩ := hor'
    obtain ⟨B', hB', rfl⟩ := mem_sortMasks.1 hb'
    obtain ⟨x', hx', rfl⟩ := mem_image.1 hB'
    obtain ⟨C', hC', rfl⟩ := mem_sortMasks.1 hd
    obtain ⟨y', hy', rfl⟩ := mem_image.1 hC'
    rw [imgMask_fmask hσ, land_fmask] at hnon
    refine isWit_of_sc_orth hr her hkr hx hnot hmeet' ⟨x', hx', y', hy', fun h1 => ?_⟩
    rw [nonOne_fmask h1] at hnon
    exact absurd hnon (by simp)

theorem fld_packI : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ 4) →
    CFSG.KS.PackFld.Fld 4 (packI l) (fun i => l[i]?.getD 0)
  | [], _ => CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_zero 4) (fun i => by simp)
  | x :: xs, h => by
    have hx : x < 2 ^ 4 := h x List.mem_cons_self
    have hf := fld_packI xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hs := CFSG.KS.PackFld.fld_shl 1 hf
    rw [Nat.mul_one] at hs
    refine CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_or (CFSG.KS.PackFld.fld_one hx) hs)
      (fun i => ?_)
    rcases i with _ | i
    · simp
    · simp

theorem packI_facts (hn : n ≤ 15) (hsz : szOK n 4 = true) (e : Perm (Fin n)) :
    PP n 4 (packI (imgList e)) ∧ Rep n (unpack n 4 (packI (imgList e))) e := by
  have hl : ∀ x ∈ imgList e, x < 2 ^ 4 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' : i < n := List.mem_range.1 hi
    simp only [imgE, hi', dite_true]
    have := (e ⟨i, hi'⟩).2
    omega
  have hf := fld_packI (imgList e) hl
  have hpg : ∀ i (hi : i < n), pg 4 (mask 4) (packI (imgList e)) i = e ⟨i, hi⟩ := by
    intro i hi
    rw [CFSG.KS.PackFld.pg_of_fld hf]
    · simp [imgList, imgE, hi]
    · simp only [imgList, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.getD_some, imgE, hi, dite_true]
      have := (e ⟨i, hi⟩).2
      omega
  have hshr : Nat.shiftRight (packI (imgList e)) (n * 4) = 0 := by
    refine CFSG.KS.PackFld.shr_zero_of_fld (by omega) hf fun i hi => ?_
    simp [imgList, hi]
  have hrep : Rep n (unpack n 4 (packI (imgList e))) e := fun i => by
    rw [CFSG.KS.Raw.Orb.unpack_get i.2, hpg i i.2]
  refine ⟨⟨?_, ⟨fun i hi => ?_, fun a ha b hb hab => ?_⟩⟩, hrep⟩
  · unfold CFSG.KS.Prim.canonK
    simp only [CFSG.KS.bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr hshr, CFSG.KS.Raw.Orb.allN_iff.2 fun i hi =>
      Nat.blt_eq.mpr (by rw [hpg i hi]; exact (e _).2)⟩
  · rw [hpg i hi]
    exact (e _).2
  · rw [hpg a ha, hpg b hb] at hab
    have := e.injective (Fin.ext hab)
    exact congrArg Fin.val this

@[expose] def TabIn (n N : ℕ) (PT : ℕ → ℕ) (Q : Subgroup (Perm (Fin n))) : Prop :=
  ∀ i < N, PP n 4 (PT i) ∧ ∃ σ ∈ Q, Rep n (unpack n 4 (PT i)) σ

theorem partRec_cases {N : ℕ} {o : Bool} {PT : ℕ → ℕ} {L : List ℕ} {rec : List (ℕ × ℕ)}
    (h : partRec n N o PT L rec = true) :
    (∃ pr : ℕ × ℕ, pairOK n N o PT L (unionL L) pr.1 pr.2 = true) ∨
      elemsOK n N PT L rec = true := by
  unfold partRec at h
  rw [strictB_eq] at h
  rcases rec with _ | ⟨pr, _ | ⟨pr', t⟩⟩
  · exact Or.inr h
  · have h' : bIf(pairOK n N o PT L (unionL L) pr.1 pr.2, true, elemsOK n N PT L [pr]) = true :=
      h
    cases hp : pairOK n N o PT L (unionL L) pr.1 pr.2
    · rw [hp] at h'
      exact Or.inr h'
    · exact Or.inl ⟨pr, hp⟩
  · exact Or.inr h

variable {N : ℕ} {PT : ℕ → ℕ} {Q : Subgroup (Perm (Fin n))}

theorem wit_of_partsOK (hn : n ≤ 15) (hsz : szOK n 4 = true) (hT : TabIn n N PT Q) {k : ℕ}
    {S : List ℕ} {R : List (List (ℕ × ℕ))} (hS : eqL S (rMasks n r) = true)
    (hP : partsOK n r k N S PT R = true) (hr : r.Prime) (her : e ^ r = 1)
    (hk : (cycParts e).card = k) (hkr : k ≤ r) :
    ∃ w₁ ∈ Q, ∃ w₂ ∈ Q, IsWit e w₁ ∧ IsWit e w₂ ∧ IsWit e (w₁ * w₂) := by
  subst hk
  have hL : sortMasks e ∈ chains S (cycParts e).card 0 := by
    rw [eqL_eq hS]
    exact sortMasks_mem_partsK hr her
  obtain ⟨rec, -, hrec⟩ := zipAll_mem hP _ hL
  have ho : Nat.beq (cycParts e).card r = false → (cycParts e).card < r := fun h => by
    have := Nat.ne_of_beq_eq_false h
    omega
  rcases partRec_cases hrec with ⟨⟨i₁, i₂⟩, hp⟩ | he
  · unfold pairOK at hp
    simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.blt_eq] at hp
    obtain ⟨hi₁, hi₂, hc₁, hc₂, hc₁₂⟩ := hp
    obtain ⟨hp₁, w₁, hw₁, hr₁⟩ := hT i₁ hi₁
    obtain ⟨hp₂, w₂, hw₂, hr₂⟩ := hT i₂ hi₂
    have hr₁₂ := rep_mulA hr₁ hr₂
    rw [mulA_u hp₁ hp₂] at hr₁₂
    exact ⟨w₁, hw₁, w₂, hw₂, isWit_of_critB hr her hkr ho hr₁ hc₁,
      isWit_of_critB hr her hkr ho hr₂ hc₂, isWit_of_critB hr her hkr ho hr₁₂ hc₁₂⟩
  · unfold elemsOK at he
    obtain ⟨⟨i₁, i₂⟩, -, hp⟩ := zipAll_mem he _ (imgList_mem_elemsOf_sort hr her)
    rw [strictB_eq] at hp
    obtain ⟨hpe, hre⟩ := packI_facts hn hsz e
    unfold elemOK at hp
    simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.blt_eq] at hp
    obtain ⟨hi₁, hi₂, hc₁, hc₂, hc₁₂⟩ := hp
    obtain ⟨hp₁, w₁, hw₁, hr₁⟩ := hT i₁ hi₁
    obtain ⟨hp₂, w₂, hw₂, hr₂⟩ := hT i₂ hi₂
    have hr₁₂ := rep_mulA hr₁ hr₂
    rw [mulA_u hp₁ hp₂] at hr₁₂
    exact ⟨w₁, hw₁, w₂, hw₂, isWit_of_witB hpe hre hp₁ hr₁ hc₁, isWit_of_witB hpe hre hp₂ hr₂ hc₂,
      isWit_of_witB hpe hre (pp_mul hp₁ hp₂) hr₁₂ hc₁₂⟩

theorem card_cycParts_mul (hr : r.Prime) (her : e ^ r = 1) :
    (cycParts e).card * r = e.support.card := by
  have hs : e.support = (cycParts e).biUnion id := by
    ext z
    simp only [mem_biUnion, id]
    constructor
    · intro hz
      exact ⟨blk e z, mem_image_of_mem _ hz, mem_blk.2 (SameCycle.refl _ _)⟩
    · rintro ⟨B, hB, hz⟩
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
      exact (mem_blk.1 hz).mem_support_iff.1 hx
  rw [hs, card_biUnion (fun B hB B' hB' hne => by
    obtain ⟨x, -, rfl⟩ := mem_image.1 hB
    obtain ⟨y, -, rfl⟩ := mem_image.1 hB'
    exact disjoint_blk hne)]
  rw [sum_const_nat (m := r) fun B hB => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
    exact card_blk hr her hx]

theorem one_le_card_cycParts (he : e ≠ 1) : 1 ≤ (cycParts e).card := by
  have hs : e.support.Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, support_eq_empty_iff]
    exact he
  exact card_pos.2 (hs.image _)

theorem card_cycParts_mul_le (hr : r.Prime) (her : e ^ r = 1) : (cycParts e).card * r ≤ n := by
  rw [card_cycParts_mul hr her]
  simpa using card_le_univ e.support

theorem tabIn_of_checks [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11) {G : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {PAR LAB : ℕ → ℕ} {PS : List ℕ} (C : Checks n N G PT E PAR LAB PS) :
    TabIn n N PT (CFSG.OddStandard.Solomon75.AhatData.P0 n) :=
  fun _ hi => ⟨(point_facts C hi).1, pt_mem C hn hn' hi⟩

end CFSG.KC.BalanceSC.BalSound

end
