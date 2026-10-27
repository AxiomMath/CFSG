module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowModel

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.Native

@[expose] noncomputable def grpN (n : ℕ) (gs : List (Array ℕ)) : Subgroup (Equiv.Perm (Fin n)) :=
  closure (permsA n gs.toArray)

theorem range_lt (n : ℕ) : ∀ p ∈ List.range n, p < n := fun _ hp => List.mem_range.mp hp

section Enum

variable {n : ℕ} {gs : List (Array ℕ)} {m : ℕ}

theorem enumOK_of_enumCheckN (h : enumCheckN n gs m = true) :
    enumOK n gs.toArray (List.range n) (certN n gs) = true := by
  simp only [enumCheckN, Bool.and_eq_true] at h
  exact h.1

theorem mem_grpN_iff (h : enumCheckN n gs m = true) {x : Equiv.Perm (Fin n)} :
    x ∈ grpN n gs ↔ ∃ t ∈ eltsN n gs, Rep n t x := by
  have hok := enumOK_of_enumCheckN h
  constructor
  · intro hx
    obtain ⟨i, hi, hr⟩ := enumOK_exists_rep (range_lt n) hok hx
    refine ⟨_, ?_, hr⟩
    rw [getElem!_pos (certN n gs).pts i hi]
    exact Array.getElem_mem_toList hi
  · rintro ⟨t, ht, hr⟩
    exact enumOK_mem_of_mem (range_lt n) hok hr ht

theorem card_grpN (h : enumCheckN n gs m = true) : Nat.card (grpN n gs) = m := by
  have hok := enumOK_of_enumCheckN h
  have hm : (certN n gs).pts.size = m := by
    simp only [enumCheckN, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  rw [grpN, (enumOK_spec (range_lt n) hok).2.1, hm]

theorem validA_of_mem (h : enumCheckN n gs m = true) {a : Array ℕ} (ha : a ∈ gs) :
    validA n a = true := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have := enumOK_gens_valid (enumOK_of_enumCheckN h) (k := k) (by simpa using hk)
  simpa [getElem!_pos gs.toArray k (by simpa using hk)] using this

theorem gen_mem_grpN {a : Array ℕ} (ha : a ∈ gs) : permOfArr n a ∈ grpN n gs := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  refine subset_closure ⟨k, by simpa using hk, ?_⟩
  simp [getElem!_pos gs.toArray k (by simpa using hk)]

theorem mem_of_inLN (h : enumCheckN n gs m = true) {t : Array ℕ} {x : Equiv.Perm (Fin n)}
    (hin : inLN n (eltsN n gs) t = true) (ht : Rep n t x) : x ∈ grpN n gs := by
  rw [inLN, List.any_eq_true] at hin
  obtain ⟨u, hu, he⟩ := hin
  exact (mem_grpN_iff h).2 ⟨u, hu, rep_of_eqA ht he⟩

theorem forall_of_all (h : enumCheckN n gs m = true) {f : Array ℕ → Bool}
    (hall : (eltsN n gs).all f = true) {x : Equiv.Perm (Fin n)} (hx : x ∈ grpN n gs) :
    ∃ t, Rep n t x ∧ f t = true := by
  obtain ⟨t, ht, hr⟩ := (mem_grpN_iff h).1 hx
  exact ⟨t, hr, List.all_eq_true.1 hall t ht⟩

theorem validA_of_mem_elts (h : enumCheckN n gs m = true) {t : Array ℕ} (ht : t ∈ eltsN n gs) :
    validA n t = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hi' : i < (certN n gs).pts.size := by simpa [eltsN] using hi
  have := (enumOK_spec (range_lt n) (enumOK_of_enumCheckN h)).2.2 i hi'
  rw [getElem!_pos (certN n gs).pts i hi'] at this
  simpa [eltsN] using this

theorem inLN_of_mem (h : enumCheckN n gs m = true) {t : Array ℕ} {x : Equiv.Perm (Fin n)}
    (hx : x ∈ grpN n gs) (ht : Rep n t x) : inLN n (eltsN n gs) t = true := by
  obtain ⟨u, hu, hr⟩ := (mem_grpN_iff h).1 hx
  rw [inLN, List.any_eq_true]
  exact ⟨u, hu, (eqA_iff ht hr).2 rfl⟩

theorem not_mem_of_inLN (h : enumCheckN n gs m = true) {t : Array ℕ} {x : Equiv.Perm (Fin n)}
    (ht : Rep n t x) (hn : (!(inLN n (eltsN n gs) t)) = true) : x ∉ grpN n gs := by
  intro hx
  rw [inLN_of_mem h hx ht] at hn
  exact absurd hn (by decide)

theorem grpN_le {K : Subgroup (Equiv.Perm (Fin n))} (hK : ∀ a ∈ gs, permOfArr n a ∈ K) :
    grpN n gs ≤ K := by
  rw [grpN, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact hK _ (by simp [getElem!_pos gs.toArray k hk])

end Enum

section Ops

variable {n : ℕ} {a b z t : Array ℕ} {A B Z T : Equiv.Perm (Fin n)}

theorem rep_mulN (ha : Rep n a A) (hb : Rep n b B) : Rep n (mulN n a b) (A * B) :=
  rep_compA ha hb

theorem commN_iff (ha : Rep n a A) (hb : Rep n b B) : commN n a b = true ↔ A * B = B * A :=
  eqA_iff (rep_mulN ha hb) (rep_mulN hb ha)

theorem inZN_iff (hz : Rep n z Z) (ht : Rep n t T) : inZN n z t = true ↔ T = 1 ∨ T = Z := by
  rw [inZN, Bool.or_eq_true, eqA_iff ht rep_idA, eqA_iff ht hz]

theorem commZN_iff (hz : Rep n z Z) (ha : Rep n a A) (hb : Rep n b B) :
    commZN n z a b = true ↔ CommZ Z A B := by
  rw [commZN, Bool.or_eq_true, commN_iff ha hb,
    eqA_iff (rep_mulN ha hb) (rep_mulN (rep_mulN hb ha) hz)]
  rfl

theorem rep_powN (ha : Rep n a A) : ∀ k, Rep n (powN n a k) (A ^ k)
  | 0 => by rw [powN, pow_zero]; exact rep_idA
  | k + 1 => by rw [powN, pow_succ']; exact rep_mulN ha (rep_powN ha k)

end Ops

theorem grpN_le_of_all {n : ℕ} {gs gs' : List (Array ℕ)} {m m' : ℕ}
    (hg : enumCheckN n gs m = true) (hg' : enumCheckN n gs' m' = true)
    (hall : gs'.all (inLN n (eltsN n gs)) = true) : grpN n gs' ≤ grpN n gs :=
  grpN_le fun a ha => mem_of_inLN hg (List.all_eq_true.1 hall a ha)
    (rep_of_validA (validA_of_mem hg' ha))

theorem comm_of_all {n : ℕ} {gs : List (Array ℕ)} {m : ℕ} (hg : enumCheckN n gs m = true)
    (hc : gs.all (fun a => gs.all (commN n a)) = true) :
    ∀ x ∈ grpN n gs, ∀ y ∈ grpN n gs, x * y = y * x := by
  have hmem : ∀ k < gs.toArray.size, gs.toArray[k]! ∈ gs := fun k hk => by
    rw [getElem!_pos gs.toArray k hk]
    simp
  have hle : grpN n gs ≤ centralizer (grpN n gs : Set (Equiv.Perm (Fin n))) := by
    rw [grpN, centralizer_closure]
    refine (closure_le _).mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hcm := List.all_eq_true.1 (List.all_eq_true.1 hc _ (hmem l hl)) _ (hmem k hk)
    exact (commN_iff (rep_of_validA (validA_of_mem hg (hmem l hl)))
      (rep_of_validA (validA_of_mem hg (hmem k hk)))).1 hcm
  intro x hx y hy
  exact mem_centralizer_iff.mp (hle hy) x hx

theorem mem_normalizer_of_map_conj_le' {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))}
    {w : Equiv.Perm (Fin n)} (hw : K.map (MulAut.conj w).toMonoidHom ≤ K) :
    w ∈ normalizer (K : Set (Equiv.Perm (Fin n))) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hw
    (le_of_eq (card_map_of_injective (MulAut.conj w).injective).symm)

theorem le_normalizer_of_all {n : ℕ} {gs hs : List (Array ℕ)} {m : ℕ}
    (hg : enumCheckN n gs m = true) (hv : ∀ g ∈ hs, validA n g = true)
    (hc : hs.all (fun g => gs.all fun q => inLN n (eltsN n gs) (conjA n g q)) = true) :
    grpN n hs ≤ normalizer (grpN n gs : Set (Equiv.Perm (Fin n))) := by
  refine grpN_le fun g hgm => ?_
  have hvg := hv g hgm
  refine mem_normalizer_of_map_conj_le' ?_
  rw [grpN, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hq : gs.toArray[k]! ∈ gs := by
    rw [getElem!_pos gs.toArray k hk]
    simp
  have hin := List.all_eq_true.1 (List.all_eq_true.1 hc g hgm) _ hq
  have hrep := rep_conjA hvg (rep_of_validA (validA_of_mem hg hq))
  have hmem := mem_of_inLN hg hin hrep
  simpa [grpN, MulAut.conj_apply] using hmem

section Count

variable {n : ℕ} {L : List (Array ℕ)} {S : Set (Equiv.Perm (Fin n))}

theorem exists_index (hS : ∀ x ∈ S, ∃ t ∈ L, Rep n t x) :
    ∃ f : S → Fin L.length, ∀ x, Rep n (L.get (f x)) (x : Equiv.Perm (Fin n)) := by
  have hidx : ∀ x : S, ∃ i : Fin L.length, Rep n (L.get i) (x : Equiv.Perm (Fin n)) := by
    intro x
    obtain ⟨t, ht, hr⟩ := hS x x.2
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ⟨⟨i, hi⟩, hr⟩
  choose f hf using hidx
  exact ⟨f, hf⟩

theorem injective_index {f : S → Fin L.length}
    (hf : ∀ x, Rep n (L.get (f x)) (x : Equiv.Perm (Fin n))) : Function.Injective f := by
  intro x y hxy
  have h1 := hf x
  have h2 := hf y
  rw [hxy] at h1
  exact Subtype.ext (h1.unique h2)

theorem card_le_length (hS : ∀ x ∈ S, ∃ t ∈ L, Rep n t x) : Nat.card S ≤ L.length := by
  obtain ⟨f, hf⟩ := exists_index hS
  have := Nat.card_le_card_of_injective f (injective_index hf)
  simpa using this

theorem mem_of_card_eq_length (hS : ∀ x ∈ S, ∃ t ∈ L, Rep n t x)
    (hcard : Nat.card S = L.length) : ∀ t ∈ L, permOfArr n t ∈ S := by
  obtain ⟨f, hf⟩ := exists_index hS
  have hbij : Function.Bijective f :=
    (injective_index hf).bijective_of_nat_card_le (by simp [hcard])
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  obtain ⟨x, hx⟩ := hbij.2 ⟨i, hi⟩
  have h1 := hf x
  rw [hx] at h1
  rw [show L[i] = L.get ⟨i, hi⟩ from rfl, permOfArr_eq_of_rep h1]
  exact x.2

end Count

section Counting

variable {n : ℕ} {gs qs es fs : List (Array ℕ)} {mX mQ mE mF : ℕ} {zt : Array ℕ}
  {Z : Equiv.Perm (Fin n)}

theorem goodQ_of_goodQN (hX : enumCheckN n gs mX = true) (hz : Rep n zt Z) {t : Array ℕ}
    {x : Equiv.Perm (Fin n)} (ht : Rep n t x) (hg : goodQN n (eltsN n gs) zt t = true) :
    GoodQ (grpN n gs) Z x := by
  have hS : ∀ y ∈ setYP (grpN n gs) Z x, ∃ u ∈ setYN n (eltsN n gs) zt t, Rep n u y := by
    rintro y ⟨hyX, hy2, hyc⟩
    obtain ⟨u, hu, hru⟩ := (mem_grpN_iff hX).1 hyX
    refine ⟨u, List.mem_filter.2 ⟨hu, ?_⟩, hru⟩
    rw [Bool.and_eq_true]
    exact ⟨(inZN_iff hz (rep_mulN hru hru)).2 hy2, (commZN_iff hz ht hru).2 hyc⟩
  have hle := card_le_length hS
  simp only [goodQN, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hg
  rcases hg with hlt | ⟨hlen, hany⟩
  · exact Or.inl (lt_of_le_of_lt hle hlt)
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl (hlen ▸ hlt)
    · right
      refine ⟨heq.trans hlen, ?_⟩
      obtain ⟨u, hu, hu'⟩ := List.any_eq_true.1 hany
      obtain ⟨u', hu'', hnc⟩ := List.any_eq_true.1 hu'
      have hmem := mem_of_card_eq_length hS heq
      have hvu := validA_of_mem_elts hX (List.mem_filter.1 hu).1
      have hvu' := validA_of_mem_elts hX (List.mem_filter.1 hu'').1
      refine ⟨_, hmem u hu, _, hmem u' hu'', fun hcz => ?_⟩
      rw [Bool.not_eq_true', ← Bool.not_eq_true] at hnc
      exact hnc ((commZN_iff hz (rep_of_validA hvu) (rep_of_validA hvu')).2 hcz)

theorem card_badQ_of_uniqQN (hX : enumCheckN n gs mX = true) (hQ : enumCheckN n qs mQ = true)
    (hz : Rep n zt Z) (h : uniqQN n (eltsN n gs) (eltsN n qs) zt = true) :
    Nat.card (badQ (grpN n gs) (grpN n qs) Z) < 64 := by
  rw [uniqQN, decide_eq_true_eq] at h
  have hS : ∀ x ∈ badQ (grpN n gs) (grpN n qs) Z, ∃ t ∈ (eltsN n gs).filter (fun x =>
      !(inLN n (eltsN n qs) x) && inZN n zt (mulN n x x) && !(goodQN n (eltsN n gs) zt x)),
      Rep n t x := by
    rintro x ⟨hxX, hxQ, hx2, hng⟩
    obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hX).1 hxX
    refine ⟨t, List.mem_filter.2 ⟨ht, ?_⟩, hrt⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨?_, (inZN_iff hz (rep_mulN hrt hrt)).2 hx2⟩, ?_⟩
    · by_contra hc
      exact hxQ (mem_of_inLN hQ (by simpa using hc) hrt)
    · by_contra hc
      exact hng (goodQ_of_goodQN hX hz hrt (by simpa using hc))
  exact lt_of_le_of_lt (card_le_length hS) h

theorem card_setIP_of_uniqEN (hX : enumCheckN n gs mX = true) (hE : enumCheckN n es mE = true)
    (hF : enumCheckN n fs mF = true) (h : uniqEN n (eltsN n gs) (eltsN n es) (eltsN n fs) = true) :
    ∀ x ∈ grpN n gs, x * x = 1 → x ≠ 1 → x ∉ grpN n es → x ∉ grpN n fs →
      Nat.card (setIP (grpN n gs) x) < 64 := by
  intro x hx hx2 hx1 hxE hxF
  obtain ⟨t, ht, hb⟩ := forall_of_all hX h hx
  simp only [Bool.or_eq_true] at hb
  have h1 : eqA n (mulN n t t) (idA n) = true := (eqA_iff (rep_mulN ht ht) rep_idA).2 hx2
  have h2 : eqA n t (idA n) = false := by
    by_contra hc
    exact hx1 (eq_of_eqA ht rep_idA (by simpa using hc))
  have h3 : inLN n (eltsN n es) t = false := by
    by_contra hc
    exact hxE (mem_of_inLN hE (by simpa using hc) ht)
  have h4 : inLN n (eltsN n fs) t = false := by
    by_contra hc
    exact hxF (mem_of_inLN hF (by simpa using hc) ht)
  rw [h1, h2, h3, h4] at hb
  simp only [Bool.not_true, Bool.false_eq_true, false_or, decide_eq_true_eq] at hb
  have hS : ∀ y ∈ setIP (grpN n gs) x, ∃ u ∈ (eltsN n gs).filter
      (fun y => eqA n (mulN n y y) (idA n) && commN n t y), Rep n u y := by
    rintro y ⟨hyX, hy2, hyc⟩
    obtain ⟨u, hu, hru⟩ := (mem_grpN_iff hX).1 hyX
    refine ⟨u, List.mem_filter.2 ⟨hu, ?_⟩, hru⟩
    rw [Bool.and_eq_true]
    exact ⟨(eqA_iff (rep_mulN hru hru) rep_idA).2 hy2, (commN_iff ht hru).2 hyc⟩
  exact lt_of_le_of_lt (card_le_length hS) hb

end Counting

theorem sylFacts_of {n : ℕ} {gs qs es fs us : List (Array ℕ)} {zt rt st : Array ℕ} {k : ℕ}
    (hX : enumCheckN n gs (2 * k * 128) = true) (hQ : enumCheckN n qs 128 = true)
    (hE : enumCheckN n es 64 = true) (hF : enumCheckN n fs 64 = true)
    (hU : enumCheckN n us 16 = true)
    (hvz : validA n zt = true) (hvr : validA n rt = true) (hvs : validA n st = true)
    (hQX : qs.all (inLN n (eltsN n gs)) = true) (hEX : es.all (inLN n (eltsN n gs)) = true)
    (hFX : fs.all (inLN n (eltsN n gs)) = true) (hUQ : us.all (inLN n (eltsN n qs)) = true)
    (hzQ : inLN n (eltsN n qs) zt = true) (hrX : inLN n (eltsN n gs) rt = true)
    (hsX : inLN n (eltsN n gs) st = true)
    (hnQ : gs.all (fun g => qs.all fun q => inLN n (eltsN n qs) (conjA n g q)) = true)
    (hnE : grpN n qs ≤ normalizer (grpN n es : Set (Equiv.Perm (Fin n))))
    (hnF : grpN n qs ≤ normalizer (grpN n fs : Set (Equiv.Perm (Fin n))))
    (hz2 : eqA n (mulN n zt zt) (idA n) = true) (hz1 : (!(eqA n zt (idA n))) = true)
    (hzc : gs.all (commN n zt) = true)
    (hcen : (eltsN n gs).all (fun x => !(gs.all (commN n x)) || inZN n zt x) = true)
    (hQsq : (eltsN n qs).all (fun x => inZN n zt (mulN n x x)) = true)
    (hQcen : (eltsN n qs).all (fun x => !(qs.all (commN n x)) || inZN n zt x) = true)
    (hQnab : qs.any (fun a => qs.any fun b => !(commN n a b)) = true)
    (hEsq : (eltsN n es).all (fun x => eqA n (mulN n x x) (idA n)) = true)
    (hEc : es.all (fun a => es.all (commN n a)) = true)
    (hFsq : (eltsN n fs).all (fun x => eqA n (mulN n x x) (idA n)) = true)
    (hFc : fs.all (fun a => fs.all (commN n a)) = true)
    (hUsq : (eltsN n us).all (fun x => eqA n (mulN n x x) (idA n)) = true)
    (hUc : us.all (fun a => us.all (commN n a)) = true)
    (hEF : es.any (fun a => !(inLN n (eltsN n fs) a)) = true)
    (hrk : permOfArr n rt ^ k ∈ grpN n qs)
    (hs2 : inLN n (eltsN n qs) (mulN n st st) = true)
    (hsr2 : inLN n (eltsN n qs) (mulN n (mulN n st rt) (mulN n st rt)) = true)
    (hrne : ∀ i, 0 < i → i < k → permOfArr n rt ^ i ∉ grpN n qs)
    (hsne : ∀ i, i < k → permOfArr n st * permOfArr n rt ^ i ∉ grpN n qs)
    (huQ : Nat.card (badQ (grpN n gs) (grpN n qs) (permOfArr n zt)) < 64)
    (huE : uniqEN n (eltsN n gs) (eltsN n es) (eltsN n fs) = true) :
    SylFacts (grpN n gs) (grpN n qs) (grpN n es) (grpN n fs) (grpN n us) (permOfArr n zt)
      (permOfArr n rt) (permOfArr n st) k := by
  have rz := rep_of_validA hvz
  have rr := rep_of_validA hvr
  have rs := rep_of_validA hvs
  have hz2' : permOfArr n zt * permOfArr n zt = 1 := eq_of_eqA (rep_mulN rz rz) rep_idA hz2
  have hzc' : ∀ x ∈ grpN n gs, x * permOfArr n zt = permOfArr n zt * x := by
    have hle : grpN n gs ≤ centralizer ({permOfArr n zt} : Set (Equiv.Perm (Fin n))) := by
      refine grpN_le fun a ha => ?_
      rw [mem_centralizer_singleton_iff]
      exact ((commN_iff rz (rep_of_validA (validA_of_mem hX ha))).1
        (List.all_eq_true.1 hzc a ha)).symm
    exact fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
  refine ⟨card_grpN hX, card_grpN hQ, card_grpN hE, card_grpN hF, card_grpN hU,
    grpN_le_of_all hX hQ hQX, grpN_le_of_all hX hE hEX, grpN_le_of_all hX hF hFX,
    grpN_le_of_all hQ hU hUQ, mem_of_inLN hQ hzQ rz, mem_of_inLN hX hrX rr, mem_of_inLN hX hsX rs,
    le_normalizer_of_all hQ (fun g hg => validA_of_mem hX hg) hnQ, hnE, hnF,
    hz2', ?_, hzc', ?_, ?_, ?_, ?_, ?_, comm_of_all hE hEc, ?_, comm_of_all hF hFc, ?_,
    comm_of_all hU hUc, ?_, hrk, mem_of_inLN hQ hs2 (rep_mulN rs rs),
    mem_of_inLN hQ hsr2 (rep_mulN (rep_mulN rs rr) (rep_mulN rs rr)), hrne, hsne, huQ,
    card_setIP_of_uniqEN hX hE hF huE⟩
  ·
    intro h1
    rw [Bool.not_eq_true', ← Bool.not_eq_true] at hz1
    exact hz1 ((eqA_iff rz rep_idA).2 h1)
  ·
    intro x hx hcomm
    obtain ⟨t, ht, hb⟩ := forall_of_all hX hcen hx
    rw [Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exfalso
      rw [Bool.not_eq_true', ← Bool.not_eq_true] at hb
      refine hb (List.all_eq_true.2 fun a ha => ?_)
      exact (commN_iff ht (rep_of_validA (validA_of_mem hX ha))).2 (hcomm _ (gen_mem_grpN ha))
    · exact (inZN_iff rz ht).1 hb
  · intro x hx
    obtain ⟨t, ht, hb⟩ := forall_of_all hQ hQsq hx
    exact (inZN_iff rz (rep_mulN ht ht)).1 hb
  · intro x hx hcomm
    obtain ⟨t, ht, hb⟩ := forall_of_all hQ hQcen hx
    rw [Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exfalso
      rw [Bool.not_eq_true', ← Bool.not_eq_true] at hb
      refine hb (List.all_eq_true.2 fun a ha => ?_)
      exact (commN_iff ht (rep_of_validA (validA_of_mem hQ ha))).2 (hcomm _ (gen_mem_grpN ha))
    · exact (inZN_iff rz ht).1 hb
  · obtain ⟨a, ha, hb⟩ := List.any_eq_true.1 hQnab
    obtain ⟨b, hb', hab⟩ := List.any_eq_true.1 hb
    refine ⟨_, gen_mem_grpN ha, _, gen_mem_grpN hb', fun he => ?_⟩
    rw [Bool.not_eq_true', ← Bool.not_eq_true] at hab
    exact hab ((commN_iff (rep_of_validA (validA_of_mem hQ ha))
      (rep_of_validA (validA_of_mem hQ hb'))).2 he)
  · intro x hx
    obtain ⟨t, ht, hb⟩ := forall_of_all hE hEsq hx
    exact eq_of_eqA (rep_mulN ht ht) rep_idA hb
  · intro x hx
    obtain ⟨t, ht, hb⟩ := forall_of_all hF hFsq hx
    exact eq_of_eqA (rep_mulN ht ht) rep_idA hb
  · intro x hx
    obtain ⟨t, ht, hb⟩ := forall_of_all hU hUsq hx
    exact eq_of_eqA (rep_mulN ht ht) rep_idA hb
  ·
    intro hEF'
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.1 hEF
    have hra := rep_of_validA (validA_of_mem hE ha)
    have hmem : permOfArr n a ∈ grpN n fs := hEF' ▸ gen_mem_grpN ha
    exact not_mem_of_inLN hF hra hb hmem

noncomputable abbrev X16 : Subgroup (Equiv.Perm (Fin 16)) := grpN 16 heSyl16
noncomputable abbrev Q16 : Subgroup (Equiv.Perm (Fin 16)) := grpN 16 heSylQ16
noncomputable abbrev E16 : Subgroup (Equiv.Perm (Fin 16)) := grpN 16 heSylE16
noncomputable abbrev F16 : Subgroup (Equiv.Perm (Fin 16)) := grpN 16 heSylF16
noncomputable abbrev U16 : Subgroup (Equiv.Perm (Fin 16)) := grpN 16 heSylEz16
noncomputable abbrev z16 : Equiv.Perm (Fin 16) := permOfArr 16 heSylZ16
noncomputable abbrev r16 : Equiv.Perm (Fin 16) := permOfArr 16 heSylR16
noncomputable abbrev s16 : Equiv.Perm (Fin 16) := permOfArr 16 heSylS16

theorem sylCheck16_parts (h : sylCheck16 = true) :
    enumCheck16 heSyl16 1024 = true ∧ enumCheck16 heSylQ16 128 = true ∧
    enumCheck16 heSylE16 64 = true ∧ enumCheck16 heSylF16 64 = true ∧
    enumCheck16 heSylEz16 16 = true ∧ validA 16 heSylZ16 = true ∧ validA 16 heSylR16 = true ∧
    validA 16 heSylS16 = true ∧ heSylQ16.all (inL (elts16 heSyl16)) = true ∧
    heSylE16.all (inL (elts16 heSyl16)) = true ∧ heSylF16.all (inL (elts16 heSyl16)) = true ∧
    heSylEz16.all (inL (elts16 heSylQ16)) = true ∧ inL (elts16 heSylQ16) heSylZ16 = true ∧
    inL (elts16 heSyl16) heSylR16 = true ∧ inL (elts16 heSyl16) heSylS16 = true ∧
    heSyl16.all (fun g => heSylQ16.all fun q => inL (elts16 heSylQ16) (conjA 16 g q)) = true ∧
    heSyl16.all (fun g => heSylE16.all fun q => inL (elts16 heSylE16) (conjA 16 g q)) = true ∧
    heSyl16.all (fun g => heSylF16.all fun q => inL (elts16 heSylF16) (conjA 16 g q)) = true ∧
    eqA 16 (mul16 heSylZ16 heSylZ16) (idA 16) = true ∧ (!(eqA 16 heSylZ16 (idA 16))) = true ∧
    heSyl16.all (comm16 heSylZ16) = true ∧
    (elts16 heSyl16).all (fun x => !(heSyl16.all (comm16 x)) || inZ heSylZ16 x) = true ∧
    (elts16 heSylQ16).all (fun x => inZ heSylZ16 (mul16 x x)) = true ∧
    (elts16 heSylQ16).all (fun x => !(heSylQ16.all (comm16 x)) || inZ heSylZ16 x) = true ∧
    heSylQ16.any (fun a => heSylQ16.any fun b => !(comm16 a b)) = true ∧
    (elts16 heSylE16).all (fun x => eqA 16 (mul16 x x) (idA 16)) = true ∧
    heSylE16.all (fun a => heSylE16.all (comm16 a)) = true ∧
    (elts16 heSylF16).all (fun x => eqA 16 (mul16 x x) (idA 16)) = true ∧
    heSylF16.all (fun a => heSylF16.all (comm16 a)) = true ∧
    (elts16 heSylEz16).all (fun x => eqA 16 (mul16 x x) (idA 16)) = true ∧
    heSylEz16.all (fun a => heSylEz16.all (comm16 a)) = true ∧
    heSylE16.any (fun a => !(inL (elts16 heSylF16) a)) = true ∧
    inL (elts16 heSylQ16) (pow16 heSylR16 4) = true ∧
    inL (elts16 heSylQ16) (mul16 heSylS16 heSylS16) = true ∧
    inL (elts16 heSylQ16) (mul16 (mul16 heSylS16 heSylR16) (mul16 heSylS16 heSylR16)) = true ∧
    (!(inL (elts16 heSylQ16) heSylR16)) = true ∧
    (!(inL (elts16 heSylQ16) (pow16 heSylR16 2))) = true ∧
    (!(inL (elts16 heSylQ16) (pow16 heSylR16 3))) = true ∧
    (!(inL (elts16 heSylQ16) heSylS16)) = true ∧
    (!(inL (elts16 heSylQ16) (mul16 heSylS16 heSylR16))) = true ∧
    (!(inL (elts16 heSylQ16) (mul16 heSylS16 (pow16 heSylR16 2)))) = true ∧
    (!(inL (elts16 heSylQ16) (mul16 heSylS16 (pow16 heSylR16 3)))) = true ∧
    uniqQOK (elts16 heSyl16) (elts16 heSylQ16) heSylZ16 = true ∧
    uniqEOK (elts16 heSyl16) (elts16 heSylE16) (elts16 heSylF16) = true := by
  simp only [sylCheck16, Bool.and_eq_true, and_assoc] at h
  exact h

theorem pow16_eq (a : Array ℕ) : ∀ k, pow16 a k = powN 16 a k
  | 0 => rfl
  | k + 1 => by simp only [pow16, powN, pow16_eq a k]; rfl

theorem card_badQ_of_uniqQOK {gs qs : List (Array ℕ)} {mX mQ : ℕ} {zt : Array ℕ}
    {Z : Equiv.Perm (Fin 16)} (hX : enumCheckN 16 gs mX = true)
    (hQ : enumCheckN 16 qs mQ = true) (hz : Rep 16 zt Z)
    (h : uniqQOK (elts16 gs) (elts16 qs) zt = true) :
    Nat.card (badQ (grpN 16 gs) (grpN 16 qs) Z) < 64 := by
  have h' : (eltsN 16 gs).all (fun x => inLN 16 (eltsN 16 qs) x ||
      !(inZN 16 zt (mulN 16 x x)) || goodQN 16 (eltsN 16 gs) zt x) = true := h
  have hempty : badQ (grpN 16 gs) (grpN 16 qs) Z = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxX, hxQ, hx2, hng⟩
    obtain ⟨t, ht, hb⟩ := forall_of_all hX h' hxX
    simp only [Bool.or_eq_true] at hb
    rcases hb with (hb | hb) | hb
    · exact hxQ (mem_of_inLN hQ hb ht)
    · rw [Bool.not_eq_true', ← Bool.not_eq_true] at hb
      exact hb ((inZN_iff hz (rep_mulN ht ht)).2 hx2)
    · exact hng (goodQ_of_goodQN hX hz ht hb)
  rw [hempty]
  simp

theorem sylFacts16 (h : sylCheck16 = true) : SylFacts X16 Q16 E16 F16 U16 z16 r16 s16 4 := by
  obtain ⟨hX, hQ, hE, hF, hU, hvz, hvr, hvs, hQX, hEX, hFX, hUQ, hzQ, hrX, hsX, hcQ, hcE, hcF,
    hz2, hz1, hzc, hcen, hQsq, hQcen, hQnab, hEsq, hEc, hFsq, hFc, hUsq, hUc, hEF, hr4, hs2,
    hsr2, hr1, hr2, hr3, hs0, hs1, hs2', hs3, huQ, huE⟩ := sylCheck16_parts h
  have rr := rep_of_validA hvr
  have rs := rep_of_validA hvs
  have hQ' : enumCheckN 16 heSylQ16 128 = true := hQ
  have hvX : ∀ g ∈ heSyl16, validA 16 g = true := fun g hg => validA_of_mem hX hg
  have hXQ : grpN 16 heSylQ16 ≤ grpN 16 heSyl16 := grpN_le_of_all hX hQ hQX
  have hpow : ∀ i, Rep 16 (pow16 heSylR16 i) (r16 ^ i) := fun i => by
    rw [pow16_eq]
    exact rep_powN rr i
  refine sylFacts_of (k := 4) hX hQ hE hF hU hvz hvr hvs hQX hEX hFX hUQ hzQ hrX hsX hcQ
    (hXQ.trans (le_normalizer_of_all hE hvX hcE)) (hXQ.trans (le_normalizer_of_all hF hvX hcF))
    hz2 hz1 hzc hcen hQsq hQcen hQnab hEsq hEc hFsq hFc hUsq hUc hEF
    (mem_of_inLN hQ' hr4 (hpow 4)) hs2 hsr2 ?_ ?_
    (card_badQ_of_uniqQOK hX hQ (rep_of_validA hvz) huQ) huE
  · intro i h0 hk
    interval_cases i
    · rw [pow_one]
      exact not_mem_of_inLN hQ' rr hr1
    · exact not_mem_of_inLN hQ' (hpow 2) hr2
    · exact not_mem_of_inLN hQ' (hpow 3) hr3
  · intro i hk
    interval_cases i
    · rw [pow_zero, mul_one]
      exact not_mem_of_inLN hQ' rs hs0
    · rw [pow_one]
      exact not_mem_of_inLN hQ' (rep_mulN rs rr) hs1
    · exact not_mem_of_inLN hQ' (rep_mulN rs (hpow 2)) hs2'
    · exact not_mem_of_inLN hQ' (rep_mulN rs (hpow 3)) hs3

theorem sylCheck16_of (h : heSylowCheckS = true) : sylCheck16 = true := by
  simp only [heSylowCheckS, Bool.and_eq_true] at h
  exact h.2

theorem sylModel16 : SylModel X16 Q16 E16 F16 U16 z16 4 :=
  (sylFacts16 (sylCheck16_of he_sylowCheck)).toModel

noncomputable abbrev Y32 : Subgroup (Equiv.Perm (Fin 32)) :=
  grpN 32 GrSLit.HeldFix.hfT0Tabs32.toList
noncomputable abbrev Q32 : Subgroup (Equiv.Perm (Fin 32)) := grpN 32 heAutQ32
noncomputable abbrev E32 : Subgroup (Equiv.Perm (Fin 32)) := grpN 32 heAutE32
noncomputable abbrev F32 : Subgroup (Equiv.Perm (Fin 32)) := grpN 32 heAutF32
noncomputable abbrev U32 : Subgroup (Equiv.Perm (Fin 32)) := grpN 32 heAutU32
noncomputable abbrev z32 : Equiv.Perm (Fin 32) := permOfArr 32 heAutZ32
noncomputable abbrev r32 : Equiv.Perm (Fin 32) := permOfArr 32 heAutR32
noncomputable abbrev s32 : Equiv.Perm (Fin 32) := permOfArr 32 heAutS32

open GrSLit.HeldFix in
theorem heAutSylowCheck_parts (h : heAutSylowCheck = true) :
    enumCheckN 32 hfT0Tabs32.toList (2 * 8 * 128) = true ∧
    enumCheckN 32 heAutQ32 128 = true ∧ enumCheckN 32 heAutE32 64 = true ∧
    enumCheckN 32 heAutF32 64 = true ∧ enumCheckN 32 heAutU32 16 = true ∧
    validA 32 heAutZ32 = true ∧ validA 32 heAutR32 = true ∧ validA 32 heAutS32 = true ∧
    heAutQ32.all (inLN 32 (eltsN 32 hfT0Tabs32.toList)) = true ∧
    heAutE32.all (inLN 32 (eltsN 32 hfT0Tabs32.toList)) = true ∧
    heAutF32.all (inLN 32 (eltsN 32 hfT0Tabs32.toList)) = true ∧
    heAutU32.all (inLN 32 (eltsN 32 heAutQ32)) = true ∧
    inLN 32 (eltsN 32 heAutQ32) heAutZ32 = true ∧
    inLN 32 (eltsN 32 hfT0Tabs32.toList) heAutR32 = true ∧
    inLN 32 (eltsN 32 hfT0Tabs32.toList) heAutS32 = true ∧
    hfT0Tabs32.toList.all (fun g => heAutQ32.all fun q =>
      inLN 32 (eltsN 32 heAutQ32) (conjA 32 g q)) = true ∧
    heAutQ32.all (fun g => heAutE32.all fun q => inLN 32 (eltsN 32 heAutE32) (conjA 32 g q)) =
      true ∧
    heAutQ32.all (fun g => heAutF32.all fun q => inLN 32 (eltsN 32 heAutF32) (conjA 32 g q)) =
      true ∧
    eqA 32 (mulN 32 heAutZ32 heAutZ32) (idA 32) = true ∧ (!(eqA 32 heAutZ32 (idA 32))) = true ∧
    hfT0Tabs32.toList.all (commN 32 heAutZ32) = true ∧
    (eltsN 32 hfT0Tabs32.toList).all (fun x => !(hfT0Tabs32.toList.all (commN 32 x)) ||
      inZN 32 heAutZ32 x) = true ∧
    (eltsN 32 heAutQ32).all (fun x => inZN 32 heAutZ32 (mulN 32 x x)) = true ∧
    (eltsN 32 heAutQ32).all (fun x => !(heAutQ32.all (commN 32 x)) || inZN 32 heAutZ32 x) =
      true ∧
    heAutQ32.any (fun a => heAutQ32.any fun b => !(commN 32 a b)) = true ∧
    (eltsN 32 heAutE32).all (fun x => eqA 32 (mulN 32 x x) (idA 32)) = true ∧
    heAutE32.all (fun a => heAutE32.all (commN 32 a)) = true ∧
    (eltsN 32 heAutF32).all (fun x => eqA 32 (mulN 32 x x) (idA 32)) = true ∧
    heAutF32.all (fun a => heAutF32.all (commN 32 a)) = true ∧
    (eltsN 32 heAutU32).all (fun x => eqA 32 (mulN 32 x x) (idA 32)) = true ∧
    heAutU32.all (fun a => heAutU32.all (commN 32 a)) = true ∧
    heAutE32.any (fun a => !(inLN 32 (eltsN 32 heAutF32) a)) = true ∧
    inLN 32 (eltsN 32 heAutQ32) (powN 32 heAutR32 8) = true ∧
    inLN 32 (eltsN 32 heAutQ32) (mulN 32 heAutS32 heAutS32) = true ∧
    inLN 32 (eltsN 32 heAutQ32)
      (mulN 32 (mulN 32 heAutS32 heAutR32) (mulN 32 heAutS32 heAutR32)) = true ∧
    (List.range 7).all (fun i => !(inLN 32 (eltsN 32 heAutQ32) (powN 32 heAutR32 (i + 1)))) =
      true ∧
    (List.range 8).all (fun i =>
      !(inLN 32 (eltsN 32 heAutQ32) (mulN 32 heAutS32 (powN 32 heAutR32 i)))) = true ∧
    uniqQN 32 (eltsN 32 hfT0Tabs32.toList) (eltsN 32 heAutQ32) heAutZ32 = true ∧
    uniqEN 32 (eltsN 32 hfT0Tabs32.toList) (eltsN 32 heAutE32) (eltsN 32 heAutF32) = true := by
  simp only [heAutSylowCheck, Bool.and_eq_true, and_assoc] at h
  exact h

theorem sylFacts32 (h : heAutSylowCheck = true) : SylFacts Y32 Q32 E32 F32 U32 z32 r32 s32 8 := by
  obtain ⟨hX, hQ, hE, hF, hU, hvz, hvr, hvs, hQX, hEX, hFX, hUQ, hzQ, hrX, hsX, hcQ, hcE, hcF,
    hz2, hz1, hzc, hcen, hQsq, hQcen, hQnab, hEsq, hEc, hFsq, hFc, hUsq, hUc, hEF, hr8, hs2,
    hsr2, hrne, hsne, huQ, huE⟩ := heAutSylowCheck_parts h
  have rr := rep_of_validA hvr
  have rs := rep_of_validA hvs
  have hvQ : ∀ g ∈ heAutQ32, validA 32 g = true := fun g hg => validA_of_mem hQ hg
  refine sylFacts_of (k := 8) hX hQ hE hF hU hvz hvr hvs hQX hEX hFX hUQ hzQ hrX hsX hcQ
    (le_normalizer_of_all hE hvQ hcE) (le_normalizer_of_all hF hvQ hcF)
    hz2 hz1 hzc hcen hQsq hQcen hQnab hEsq hEc hFsq hFc hUsq hUc hEF
    (mem_of_inLN hQ hr8 (rep_powN rr 8)) hs2 hsr2 ?_ ?_
    (card_badQ_of_uniqQN hX hQ (rep_of_validA hvz) huQ) huE
  · intro i h0 hk
    have hi := List.all_eq_true.1 hrne (i - 1) (List.mem_range.2 (by omega))
    rw [show i - 1 + 1 = i by omega] at hi
    exact not_mem_of_inLN hQ (rep_powN rr i) hi
  · intro i hk
    have hi := List.all_eq_true.1 hsne i (List.mem_range.2 hk)
    exact not_mem_of_inLN hQ (rep_mulN rs (rep_powN rr i)) hi

theorem sylModel32 : SylModel Y32 Q32 E32 F32 U32 z32 8 :=
  (sylFacts32 he_autSylowCheck).toModel

end CFSG.ComponentClassification.AS81.HeSylow
