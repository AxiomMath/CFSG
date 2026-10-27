module

public import Certificates.Data.Kernel.SporLatCodeR
public import CFSG.Certificates.Kernel.SporLatOmegaSound
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer
import Mathlib.Data.List.Sort

public section

namespace CFSG.KC.SLOm

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F CFSG.Quasithin.E6.Spor

theorem decodeSet_lt {n : Nat} (hn : 0 < n) :
    ∀ (fuel c : Nat), ∀ p ∈ decodeSet n fuel c, p < n
  | 0, _, p, hp => by simp [decodeSet] at hp
  | f + 1, c, p, hp => by
    unfold decodeSet at hp
    split at hp
    · simp at hp
    · rcases List.mem_cons.1 hp with rfl | hp
      · have := Nat.mod_lt c (by omega : 0 < n + 1)
        omega
      · exact decodeSet_lt hn f _ p hp

theorem codeSetAct_good {n : Nat} (hn : 0 < n) {t : Array Nat} {f : Nat → Nat} (ht : Good n t f)
    (x : List Nat) : codeSetAct n t x = insN (x.map (codeActF n f)) := by
  unfold codeSetAct
  rw [sortN_eq]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  unfold codeAct codeActF
  rw [sortN_eq]
  congr 2
  exact List.map_congr_left fun p hp => (ht.2 p (decodeSet_lt hn c c p hp)).1

theorem rChkC_sound {n : Nat} {Δ : List Nat} {sTabs : List (Array Nat)} {ta tb zT : Array Nat}
    {uWords : List (List Nat)} {yw nw : List Nat} {r m fuel : Nat} {L AB : Nat → Nat → Nat}
    {Z : Nat → Nat}
    (hS : ∀ l < sTabs.length, Good n (sTabs.toArray.getD l #[]) (L l))
    (ha : Good n ta (AB 0)) (hb : Good n tb (AB 1)) (hz : Good n zT Z)
    (h : rChkC n Δ L sTabs.length AB Z uWords yw nw r m fuel = true) :
    rChk n (codeSetAct n) Δ sTabs ta tb zT uWords yw nw r m = true := by
  unfold rChkC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hn⟩, hu⟩, horb⟩, hcz⟩, hyo⟩, hy1⟩, hyz⟩, hxy⟩ := h
  have hn' : 0 < n := of_decide_eq_true hn
  have hAB : ∀ l < (#[ta, tb] : Array (Array Nat)).size,
      Good n ((#[ta, tb] : Array (Array Nat)).getD l #[]) (AB l)
    | 0, _ => ha
    | 1, _ => hb
    | _ + 2, h => absurd h (by simp)
  have hw : ∀ w ∈ uWords, ∀ l ∈ w, l < (#[ta, tb] : Array (Array Nat)).size := by
    intro w hw l hl
    have := List.all_eq_true.1 h1 w hw
    simpa using List.all_eq_true.1 this l hl
  have hlen : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size =
      sTabs.length + uWords.length := by simp
  have hLet : ∀ l < ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size,
      Good n (((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD l #[]) (L l) := by
    intro l hl
    rw [hlen] at hl
    by_cases hls : l < sTabs.length
    · have e : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD l #[] =
          sTabs.toArray.getD l #[] := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left hls, hls]
      rw [e]
      exact hS l hls
    · obtain ⟨k, rfl⟩ : ∃ k, l = sTabs.length + k := ⟨l - sTabs.length, by omega⟩
      have hk : k < uWords.length := by omega
      have e : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD (sTabs.length + k) #[] =
          wordTabA #[ta, tb] n (uWords.getD k []) := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, hk]
      rw [e]
      have hmem : uWords.getD k [] ∈ uWords := by
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      have g := good_word hAB (hw _ hmem)
      have hk' := all_range (all_range hu k hk)
      refine ⟨g.1, fun p hp => ?_⟩
      rw [(beq_iff_eq.1 (hk' p hp))]
      exact g.2 p hp
  have hcl : ∀ l < ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size, ∀ x : List Nat,
      True → True ∧
        codeSetAct n ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray)[l]! x =
          insN (x.map (codeActF n (L l))) := by
    intro l hl x _
    exact ⟨trivial, by rw [getElem!_eq_getD']; exact codeSetAct_good hn' (hLet l hl) x⟩
  unfold orbOKC at horb
  split at horb
  · next R hR =>
    rw [← hlen] at hR
    obtain ⟨hbo, -⟩ := buildOmega_of_twin (act := codeSetAct n) (cap := m + 1)
      (fun _ : List Nat => True) trivial hcl hR
    simp only [Bool.and_eq_true] at horb
    obtain ⟨⟨hom, hm⟩, hfix⟩ := horb
    unfold omOKC at hom
    simp only [Bool.and_eq_true] at hom
    obtain ⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, o4⟩ := hom
    have hy := good_word hLet (w := yw) (fun l hl => by
      rw [hlen]
      simpa using List.all_eq_true.1 h2 l hl)
    have hS' : ∀ l < sTabs.toArray.size, Good n (sTabs.toArray.getD l #[]) (L l) :=
      fun l hl => hS l (by simpa using hl)
    have hx := good_word hS' (w := nw) (fun l hl => by simpa using List.all_eq_true.1 h3 l hl)
    unfold rChk
    simp only [hbo, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [lettersLt] using h2
    · simpa [lettersLt] using h3
    · refine decide_eq_true ⟨beq_iff_eq.1 o0, of_decide_eq_true o1, fun l hl i hi => ?_,
        fun i hi hi0 => ?_, CFSG.Quasithin.GoldD3.distinctB_of_nodup (of_decide_eq_true o4)⟩
      · have e := List.all_eq_true.1 (List.all_eq_true.1 o2 l (List.mem_range.2 (by
          rw [← hlen]; exact hl))) i (List.mem_range.2 hi)
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at e
        refine ⟨e.1, ?_⟩
        rw [e.2, (hcl l hl _ trivial).2]
      · have e := List.all_eq_true.1 o3 i (List.mem_range.2 hi)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at e
        rcases e with e | ⟨⟨e1, e2⟩, e3⟩
        · omega
        · exact ⟨e1, (by omega), e3⟩
    · simpa using hm
    · rw [List.all_eq_true]
      intro uT huT
      obtain ⟨w, hw', rfl⟩ := List.mem_map.1 huT
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw'
      have hk' : sTabs.length + k < ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).size := by
        rw [hlen]
        omega
      have g := hLet _ hk'
      have e : ((sTabs ++ uWords.map (wordTabA #[ta, tb] n)).toArray).getD (sTabs.length + k) #[] =
          wordTabA #[ta, tb] n uWords[k] := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right, hk]
      rw [e] at g
      have hc := good_comm g hz
      rw [beq_iff_eq]
      refine good_ext hc.1 hc.2 fun p hp => ?_
      have := all_range (all_range hcz k hk) p hp
      exact beq_iff_eq.1 this
    · rw [beq_iff_eq]
      refine good_ext (good_word (L := fun _ => wordF L yw) (fun l hl => by
        have : l = 0 := by simpa using hl
        subst this
        exact hy) (by simp)) (good_idTab n) fun p hp => beq_iff_eq.1 (all_range hyo p hp)
    · obtain ⟨p, hp, e⟩ := not_all_range hy1
      rw [bne_iff_ne]
      exact good_ne hy (good_idTab n) hp (by simpa using e)
    · have hc := good_comm hy hz
      rw [beq_iff_eq]
      exact good_ext hc.1 hc.2 fun p hp => beq_iff_eq.1 (all_range hyz p hp)
    · rw [List.all_eq_true]
      intro i hi
      have hi' := List.mem_range.1 hi
      rw [decide_eq_true_eq, codeSetAct_good hn' hx]
      have := List.all_eq_true.1 hfix _ (getElem!_mem hi')
      exact beq_iff_eq.1 this
    · obtain ⟨p, hp, e⟩ := not_all_range hxy
      have hc := good_comm hy hx
      rw [bne_iff_ne]
      exact good_ne hc.1 hc.2 hp (by simpa using e)
  · simp at horb

end CFSG.KC.SLOm

end
