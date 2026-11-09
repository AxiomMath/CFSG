module

public import Certificates.Data.Kernel.LocalQT.CovT
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCheck

import CFSG.Certificates.Kernel.LocalQTCovTTri
import CFSG.Certificates.Kernel.LocalQTTab2KSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Sporadic.Schreier.PairChain
import CFSG.Sporadic.Schreier.TitsCert

namespace CFSG.KC.LQT.Cov.PfT

open CFSG.KC.LQT.Cov CFSG.KC.LQT.Cov.T CFSG.KC.LQT.Cov.Parse CFSG.KC.LQT.Cov.Eqns
open CFSG.KC.LQT.Cov.Perm CFSG.KC.LQT.Cov.TEqns CFSG.KC.LQT.Syl CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Sporadic.Schreier.Tits

private theorem flags_spec : ∀ Q : List (Bool × Nat),
    (List.rec (motive := fun _ => Bool) true (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q : Bool) =
      true → ∀ q ∈ Q, q.1 = true
  | [], _, q, hq => absurd hq List.not_mem_nil
  | q :: Q, h, q', hq' => by
    change CFSG.KC.Ord.andB q.1 (List.rec (motive := fun _ => Bool) true
      (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q) = true at h
    rw [CFSG.KC.LQT.Cov.Parse.andB_eq', Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact h.1
    · exact flags_spec Q h.2 q' hq'

private theorem words_zero_nil {D : CT}
    (h0 : CFSG.KC.LQT.Syl.lenK (CFSG.KC.LQT.Syl.getK D.words 0 [1]) = 0) :
    D.words.getD 0 [] = [] := by
  have hlen : (D.words.getD 0 [1]).length = 0 := by
    rw [← CFSG.KC.LQT.Cov.Parse.getK_getD]
    exact CFSG.KC.LQT.Cov.Parse.lenK_length .. ▸ h0
  rw [List.getD_eq_getElem?_getD] at hlen ⊢
  cases h : D.words[0]? with
  | none => simp [h] at hlen
  | some w => simpa [h] using hlen

private noncomputable def qT (D : CT) : List (Bool × Nat) :=
  eqnsT D (rowsG D.words) (rowsG D.tgt) (rowsG D.back)

private theorem eqns_checks (D : CT) (H : List (List Nat))
    (hletters : ∀ w ∈ D.words, ∀ l ∈ w, l < 2)
    (hnV : 0 < D.nV)
    (hlenH : CFSG.KC.LQT.Syl.lenK H = 2 * D.nV)
    (htri : triT (rowsG (List.map Prod.snd (qT D))) H = true)
    (hflagsH : (List.rec (motive := fun _ => Bool) true
      (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) (qT D) : Bool) = true)
    (hformsBound : CFSG.KC.LQT.P.allL (List.map Prod.snd (qT D))
      (fun f => Nat.blt f (Nat.pow 2 (Nat.add (Nat.mul 2 D.nV)
        (Nat.mul 32 (CFSG.KC.LQT.Syl.lenK D.blocks))))) = true) :
    (ofCT D).eqns.all (Eqn.valid (ofCT D)) = true ∧ geFinal (ofCT D) = true := by
  have hflags : ∀ q ∈ qT D, q.1 = true := flags_spec _ hflagsH
  have hvalid : (ofCT D).eqns.all (Eqn.valid (ofCT D)) = true := eqnsT_valid hletters hnV hflags
  have hforms : (qT D).map Prod.snd = (ofCT D).forms := eqnsT_forms hletters
  have hfs : ∀ f ∈ (ofCT D).forms, f < 2 ^ (2 * D.nV + 32 * (ofCT D).blocks.length) := by
    intro f hf
    have hf' : f ∈ (qT D).map Prod.snd := by rwa [hforms]
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf'
    have := (CFSG.KC.LQT.P.allL_iff _ _).1 hformsBound q.2 (List.mem_map_of_mem hq)
    simpa [Nat.blt_eq, CFSG.KC.LQT.Cov.Parse.lenK_length, List.length_map, ofCT] using this
  exact ⟨hvalid, tri_geFinal H hletters hlenH htri hfs⟩

section Base

open CFSG.KS.Raw.Orb (PRep)
open CFSG.Monster.B.Co2 (Rep)

private theorem forceLT_go (k : List ℕ → Bool) : ∀ (l acc : List ℕ),
    List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k (List.reverse acc))
      (fun x _ ih acc => strictB x fun x => ih (List.cons x acc)) l acc = k (acc.reverse ++ l)
  | [], acc => by simp
  | x :: l, acc => by
    refine (CFSG.KS.PF.strictB_eqP x _).trans ?_
    beta_reduce
    rw [forceLT_go k l (x :: acc)]
    simp

private theorem forceLT_eq (l : List ℕ) (k : List ℕ → Bool) : forceLT l k = k l :=
  (forceLT_go k l []).trans (by simp)

private theorem getK_map_range (f : ℕ → ℕ) {n j : ℕ} (hj : j < n) :
    getK ((List.range n).map f) j 0 = f j := by
  rw [getK_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

private theorem prep_gen {S : ℕ → ℕ} (hS : ∀ j < 13, titsDerivedArrs[j]! = unpack 1755 11 (S j))
    {j : ℕ} (hj : j < 13) : PRep 1755 11 (S j) (titsT j) :=
  CFSG.KS.Raw.Orb.prep_of_rep (by rw [← hS j hj]; exact titsT_rep hj)

private theorem prep_geninv {P Q : ℕ} {g : Equiv.Perm (Fin 1755)} (hP : PRep 1755 11 P g)
    (h : permOK 1755 11 (mask 11) (1755 * 11) P Q = true) : PRep 1755 11 Q g⁻¹ := by
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  intro x
  have hy := (h3 (g⁻¹ x) (g⁻¹ x).2).2
  have e : pg 11 (mask 11) P (g⁻¹ x) = x := by
    rw [hP (g⁻¹ x)]
    simp
  rw [e] at hy
  exact hy

private theorem wordIn_one_inv (gs : ℕ → Equiv.Perm (Fin 1755)) (z : ℤ) :
    wordIn 13 (fun j => (gs j)⁻¹) [z] = (wordIn 13 gs [z])⁻¹ := by
  unfold wordIn
  cases h : CFSG.Monster.B.Co2.toLetters 13 [z] with
  | nil => simp
  | cons a t =>
    have ht : t = [] := by
      have hl : (CFSG.Monster.B.Co2.toLetters 13 [z]).length ≤ 1 := by
        unfold CFSG.Monster.B.Co2.toLetters
        exact (List.length_filterMap_le _ _).trans (by simp)
      rw [h, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst ht
    obtain ⟨j, b⟩ := a
    cases b <;> simp

private theorem letters_cons_iff {z : ℤ} {w : List ℤ} :
    lettersK 13 (z :: w) = true ↔ lettersK 13 [z] = true ∧ lettersK 13 w = true := by
  rw [CFSG.KS.Raw.Orb.lettersK_cons, CFSG.KS.Raw.Orb.lettersK_cons]
  simp [lettersK]

variable {L IL : List ℕ}

private theorem ptIT_cons (z : ℤ) (wd : List ℤ) (p : ℕ) :
    ptIT 11 (mask 11) L IL (z :: wd) p = ptIT 11 (mask 11) L IL wd
      (pg 11 (mask 11) (Bool.rec (motive := fun _ => ℕ)
        (getK L (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) 1) 0)
        (getK IL (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) 1) 0)
        (Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) 1) 0)) p) := by
  change strictN (CFSG.KS.Mathieu.icode z) (fun c => strictN (pg 11 (mask 11)
    (Bool.rec (motive := fun _ => ℕ) (getK L (Nat.sub (Nat.shiftRight c 1) 1) 0)
      (getK IL (Nat.sub (Nat.shiftRight c 1) 1) 0) (Nat.beq (Nat.land c 1) 0)) p)
    (ptIT 11 (mask 11) L IL wd)) = _
  simp only [CFSG.KS.PF.strictN_eqP]

private theorem sel_pt (hL : ∀ j < 13, PRep 1755 11 (getK L j 0) (titsT j))
    (hIL : ∀ j < 13, PRep 1755 11 (getK IL j 0) (titsT j)⁻¹) {z : ℤ}
    (hz : lettersK 13 [z] = true) (x : Fin 1755) :
    pg 11 (mask 11) (Bool.rec (motive := fun _ => ℕ)
        (getK L (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) 1) 0)
        (getK IL (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1) 1) 0)
        (Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) 1) 0)) x =
      ((wordIn 13 titsT [z])⁻¹ x : ℕ) := by
  have h := (CFSG.KS.Raw.Orb.prep_wordK (n := 1755) (w := 11) (by norm_num) (by norm_num)
    (PS := fun j => getK IL j 0) (PSI := fun j => getK L j 0)
    (gs := fun j => (titsT j)⁻¹) (j := 13) hIL (fun j hj => by simpa using hL j hj) [z] hz).1 x
  rw [CFSG.KS.Raw.Orb.wordK_cons, CFSG.KS.Raw.Orb.wordK_nil,
    CFSG.KS.PF.pg_pcomp (by norm_num) x.2,
    CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) x.2] at h
  rw [← wordIn_one_inv]
  exact h

private theorem ptIT_eq (hL : ∀ j < 13, PRep 1755 11 (getK L j 0) (titsT j))
    (hIL : ∀ j < 13, PRep 1755 11 (getK IL j 0) (titsT j)⁻¹) :
    ∀ (wd : List ℤ), lettersK 13 wd = true → ∀ x : Fin 1755,
      ptIT 11 (mask 11) L IL wd x = ((wordIn 13 titsT wd)⁻¹ x : ℕ)
  | [], _, x => by
    change (x : ℕ) = _
    simp [wordIn, CFSG.Monster.B.Co2.toLetters]
  | z :: wd, hl, x => by
    obtain ⟨h1, h2⟩ := letters_cons_iff.1 hl
    rw [ptIT_cons, sel_pt hL hIL h1 x, ptIT_eq hL hIL wd h2]
    have hw : wordIn 13 titsT (z :: wd) = wordIn 13 titsT [z] * wordIn 13 titsT wd := by
      rw [← wordIn_append]
      rfl
    rw [hw, mul_inv_rev, Equiv.Perm.mul_apply]

private theorem ptIT_lt2 : ∀ (wd : List ℤ) (p : ℕ), p < 2 ^ 11 →
    ptIT 11 (mask 11) L IL wd p < 2 ^ 11
  | [], _, hp => hp
  | z :: wd, _, _ => by
    rw [ptIT_cons]
    exact ptIT_lt2 wd _ (CFSG.KS.PF.pg_lt 11 _ _)

private theorem ptVT_cons (XW : List (List ℤ)) (i : ℕ) (u : List ℕ) (p : ℕ) :
    ptVT 11 (mask 11) L IL XW (i :: u) p =
      ptVT 11 (mask 11) L IL XW u (ptIT 11 (mask 11) L IL (getK XW i []) p) :=
  CFSG.KS.PF.strictN_eqP _ _

private theorem ptVT_append (XW : List (List ℤ)) : ∀ (u : List ℕ) (i p : ℕ),
    ptVT 11 (mask 11) L IL XW (u ++ [i]) p =
      ptIT 11 (mask 11) L IL (getK XW i []) (ptVT 11 (mask 11) L IL XW u p)
  | [], i, p => by
    rw [List.nil_append, ptVT_cons]
    rfl
  | j :: u, i, p => by
    rw [List.cons_append, ptVT_cons, ptVT_cons, ptVT_append XW u]

private theorem ptVT_lt2 (XW : List (List ℤ)) : ∀ (u : List ℕ) (p : ℕ), p < 2 ^ 11 →
    ptVT 11 (mask 11) L IL XW u p < 2 ^ 11
  | [], _, hp => hp
  | i :: u, p, hp => by
    rw [ptVT_cons]
    exact ptVT_lt2 XW u _ (ptIT_lt2 _ _ hp)

private theorem mapFT_ofFnW (nb : ℕ) (f : ℕ → ℕ) (c : ℕ) :
    mapFT 11 (mask 11) nb f c =
      CFSG.KC.LQT.PW.ofFnW nb 11 (fun j => f (pg 11 (mask 11) c j)) := by
  induction nb with
  | zero => rfl
  | succ j ih =>
    change Nat.lor (mapFT 11 (mask 11) j f c)
        (Nat.shiftLeft (f (pg 11 (mask 11) c j)) (Nat.mul 11 j)) =
      Nat.lor (CFSG.KC.LQT.PW.ofFnW j 11 (fun j => f (pg 11 (mask 11) c j)))
        (Nat.shiftLeft (f (pg 11 (mask 11) c j)) (Nat.mul 11 j))
    rw [ih]

private theorem fld_mapFT {f : ℕ → ℕ} (hf : ∀ p < 2 ^ 11, f p < 2 ^ 11) (c : ℕ) :
    CFSG.KS.PF.Fld 11 (mapFT 11 (mask 11) 6 f c)
      (fun j => if j < 6 then f (pg 11 (mask 11) c j) else 0) := by
  rw [mapFT_ofFnW]
  exact CFSG.KS.PF.fld_ofFnW 11 _ (fun j => hf _ (CFSG.KS.PF.pg_lt 11 c j)) 6

private theorem pg_mapFT {f : ℕ → ℕ} (hf : ∀ p < 2 ^ 11, f p < 2 ^ 11) (c : ℕ) {j : ℕ}
    (hj : j < 6) : pg 11 (mask 11) (mapFT 11 (mask 11) 6 f c) j = f (pg 11 (mask 11) c j) := by
  have h := CFSG.KS.PF.pg_of_fld (fld_mapFT hf c) (i := j) (by
    rw [if_pos hj]
    exact hf _ (CFSG.KS.PF.pg_lt 11 c j))
  rw [h, if_pos hj]

private theorem mapFT_congr {f g : ℕ → ℕ} (hf : ∀ p < 2 ^ 11, f p < 2 ^ 11)
    (hg : ∀ p < 2 ^ 11, g p < 2 ^ 11) {c c' : ℕ}
    (h : ∀ j < 6, f (pg 11 (mask 11) c j) = g (pg 11 (mask 11) c' j)) :
    mapFT 11 (mask 11) 6 f c = mapFT 11 (mask 11) 6 g c' :=
  CFSG.KS.PF.eq_of_fld (by norm_num) (fld_mapFT hf c)
    (CFSG.KS.PF.fld_congr (fld_mapFT hg c') fun j => by
      by_cases hj : j < 6
      · rw [if_pos hj, if_pos hj]
        exact (h j hj).symm
      · rw [if_neg hj, if_neg hj])

private theorem baseTits_fix :
    mapFT 11 (mask 11) 6 (fun q => q) (baseTits 11) = baseTits 11 := by
  decide

private theorem base_lt : ∀ j < 6, pg 11 (mask 11) (baseTits 11) j < 1755 := by
  intro j hj
  interval_cases j <;> decide

private theorem base_cover (p : Fin 1755) (hp : (p : ℕ) ∈ [0, 1, 5, 6, 24, 12]) :
    ∃ j < 6, pg 11 (mask 11) (baseTits 11) j = p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h <;> rw [h]
  exacts [⟨0, by norm_num, by decide⟩, ⟨1, by norm_num, by decide⟩, ⟨2, by norm_num, by decide⟩,
    ⟨3, by norm_num, by decide⟩, ⟨4, by norm_num, by decide⟩, ⟨5, by norm_num, by decide⟩]

private theorem tits_faithful :
    CFSG.Sporadic.Schreier.BaseFaithful titsD [0, 1, 5, 6, 24, 12] := by
  have h := CFSG.Sporadic.Schreier.baseFaithful_of_valid titsQD_valid
  rwa [titsQD_original, CERT_Tits_Schreier_validity.2.2.2.2.2.2.2.2.2.2.1] at h

private theorem eq_of_fields {g h : Equiv.Perm (Fin 1755)} (hg : g ∈ titsD) (hh : h ∈ titsD)
    (e : ∀ j < 6, ∀ x : Fin 1755, (x : ℕ) = pg 11 (mask 11) (baseTits 11) j →
      (g⁻¹ x : ℕ) = (h⁻¹ x : ℕ)) : g = h := by
  have h1 := tits_faithful (h * g⁻¹) (Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hg))
    fun p hp => by
      obtain ⟨j, hj, hpj⟩ := base_cover p hp
      rw [Equiv.Perm.mul_apply, Fin.ext (e j hj p hpj.symm)]
      simp
  exact (mul_inv_eq_one.mp h1).symm

private theorem parTGgo_spec (nV : ℕ) (TG : List (List ℕ)) (WR : List (List (List ℕ))) :
    ∀ (P : List ℕ) (c : ℕ), (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun p _ ih c => strictB c fun c =>
        CFSG.KC.Ord.andB (Nat.beq (getRG TG (Nat.add (Nat.mul 2 p)
          (Nat.mod (lastK (getRG WR c [])) 2)) nV) c) (ih (Nat.succ c))) P c : Bool) = true →
      ∀ k < P.length, getRG TG (2 * getK P k 0 + lastK (getRG WR (c + k) []) % 2) nV = c + k
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | p :: P, c, h, k, hk => by
    change strictB c (fun c => CFSG.KC.Ord.andB (Nat.beq (getRG TG (Nat.add (Nat.mul 2 p)
        (Nat.mod (lastK (getRG WR c [])) 2)) nV) c)
      (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun p _ ih c => strictB c fun c =>
          CFSG.KC.Ord.andB (Nat.beq (getRG TG (Nat.add (Nat.mul 2 p)
            (Nat.mod (lastK (getRG WR c [])) 2)) nV) c) (ih (Nat.succ c))) P (Nat.succ c))) = true
      at h
    rw [CFSG.KS.PF.strictB_eqP, andB_eq', Bool.and_eq_true, Nat.beq_eq] at h
    rcases k with _ | k
    · exact h.1
    · have := parTGgo_spec nV TG WR P (c + 1) h.2 k (by simpa using hk)
      simpa [getK_getD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private theorem parTG_spec {nV : ℕ} {TG : List (List ℕ)} {WR : List (List (List ℕ))}
    {P : List ℕ} (h : parTG nV TG WR P = true) : ∀ c, 0 < c → c < P.length + 1 →
      getRG TG (2 * getK P (c - 1) 0 + lastK (getRG WR c []) % 2) nV = c := by
  intro c hc hcn
  have := parTGgo_spec nV TG WR P 1 h (c - 1) (by omega)
  rwa [show 1 + (c - 1) = c by omega] at this

private noncomputable def treeV (st : ℕ → ℕ → ℕ) (b : ℕ) (P : List ℕ) : ℕ → ℕ
  | 0 => b
  | v + 1 => if h : getK P v 0 < v + 1 then st (v + 1) (treeV st b P (getK P v 0)) else 0
termination_by v => v
decreasing_by exact h

private theorem treeV_zero (st : ℕ → ℕ → ℕ) (b : ℕ) (P : List ℕ) : treeV st b P 0 = b := by
  rw [treeV]

private theorem treeV_succ (st : ℕ → ℕ → ℕ) (b : ℕ) (P : List ℕ) {v : ℕ}
    (h : getK P v 0 < v + 1) : treeV st b P (v + 1) = st (v + 1) (treeV st b P (getK P v 0)) := by
  rw [treeV, dif_pos h]

end Base

section Cov

open CFSG.KS.Raw.Orb (PRep)
open CFSG.Monster.B.Co2 (Rep)

variable {L IL : List ℕ}

private theorem xw_get (D : CT) {l : ℕ} (hl : l < 2) :
    (ofCT D).x (fo l) = wordIn 13 titsT (getK D.xw l []) := by
  rw [getK_getD]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem xw_letters {D : CT} (hxw : D.xw.length = 2)
    (hlx : CFSG.KC.LQT.T2.allT D.xw (lettersK 13) = true) {l : ℕ} (hl : l < 2) :
    lettersK 13 (getK D.xw l []) = true := by
  rw [getK_getD]
  refine (CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hlx _ ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.getElem_mem _

private theorem ptVT_eq {D : CT} (hxw : D.xw.length = 2)
    (hlx : CFSG.KC.LQT.T2.allT D.xw (lettersK 13) = true)
    (hL : ∀ j < 13, PRep 1755 11 (getK L j 0) (titsT j))
    (hIL : ∀ j < 13, PRep 1755 11 (getK IL j 0) (titsT j)⁻¹) :
    ∀ (u : List ℕ), (∀ l ∈ u, l < 2) → ∀ x : Fin 1755,
      ptVT 11 (mask 11) L IL D.xw u x =
        ((((u.map fun l => (ofCT D).x (fo l)).prod)⁻¹ x : Fin 1755) : ℕ)
  | [], _, x => by
    change (x : ℕ) = _
    simp
  | l :: u, hu, x => by
    have hl : l < 2 := hu l (by simp)
    rw [ptVT_cons, ptIT_eq hL hIL _ (xw_letters hxw hlx hl) x,
      ptVT_eq hxw hlx hL hIL u (fun l' hl' => hu l' (by simp [hl'])), List.map_cons,
      List.prod_cons, xw_get D hl]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]

private theorem el_eq (D : CT) (v : ℕ) :
    (ofCT D).tab.el (ofCT D).x v = ((D.words.getD v []).map fun l => (ofCT D).x (fo l)).prod := by
  unfold CayTab.el
  change ((((ofCT D).words[v]!).map fo).map (ofCT D).x).prod = _
  have hw : (ofCT D).words = D.words.toArray := rfl
  rw [hw, toArray_getElem!_list, List.map_map]
  rfl

private theorem el_mem (D : CT) (v : ℕ) : (ofCT D).tab.el (ofCT D).x v ∈ titsD := by
  rw [el_eq]
  exact Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
    exact wordIn_titsT_mem_titsD _

private theorem word_mem {D : CT} (hwords : D.words.length = D.nV)
    {v : ℕ} (hv : v < D.nV) : D.words.getD v [] ∈ D.words := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hwords]; exact hv),
    Option.getD_some]
  exact List.getElem_mem _

private theorem FR_get {nV : ℕ} {f : ℕ → ℕ} {v : ℕ} (hv : v < nV) :
    getRG (rowsG (List.map f (List.range nV))) v 0 = f v := by
  rw [getRG_rowsG, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact hv),
    Option.map_some, Option.getD_some, List.getElem_range]

private theorem list_idx {l : List ℕ} {j m : ℕ} (h : Nat.blt (getK l j m) m = true) :
    l[j]! = getK l j 0 ∧ getK l j 0 < m := by
  have h' : l.getD j m < m := by simpa [getK_getD] using h
  obtain ⟨-, hd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt h'
  refine ⟨by rw [CFSG.KC.LQT.Cov.Perm.list_get, getK_getD], ?_⟩
  rw [getK_getD, hd]
  exact h'

end Cov

end CFSG.KC.LQT.Cov.PfT

public section

namespace CFSG.KC.LQT.Cov

open CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Sporadic.Schreier.Tits CFSG.KC.LQT.Syl CFSG.KC.LQT.Cov.Parse
open CFSG.KC.LQT.Cov.T CFSG.KC.LQT.Cov.Eqns CFSG.KC.LQT.Cov.PfT CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem covT_sound (cs : List Char) (D : CT) (hp : parseT cs = some D) (P FL : List ℕ)
    (H : List (List ℕ)) (nV0 : ℕ) (S SI : ℕ → ℕ)
    (hS : ∀ j < 13, titsDerivedArrs[j]! = CFSG.KS.Raw.unpack 1755 11 (S j))
    (hA : covTA 1755 11 13 S SI D P FL nV0 = true) (hB : covTB D H = true) :
    covCheck (parseData (String.ofList cs)) = true ∧ (parseData (String.ofList cs)).nV = nV0 := by
  rw [covTA] at hA
  · rw [covTB] at hB
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hA
    obtain ⟨-, hxwlen, hnv0, hlx, hpar, htree, hlenFL, hFL0, hforce⟩ := hA
    rw [forceLT_eq] at hforce
    beta_reduce at hforce
    rw [forceLT_eq] at hforce
    beta_reduce at hforce
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hforce
    obtain ⟨hpermAll, hgood, hdist, hblk⟩ := hforce
    obtain ⟨hxw2, hwords, hletters, hpd⟩ := parseT_sound hp
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hB
    obtain ⟨hlenH, htri, hflagsH, hformsBound⟩ := hB
    set L := List.map S (List.range 13) with hLdef
    set IL := List.map SI (List.range 13) with hILdef
    set WR := rowsG D.words with hWR
    have hperm : ∀ j < 13,
        permOK 1755 11 (mask 11) (1755 * 11) (getK L j 0) (getK IL j 0) = true :=
      fun j hj => (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 hpermAll j hj
    have hL : ∀ j < 13, CFSG.KS.Raw.Orb.PRep 1755 11 (getK L j 0) (titsT j) := fun j hj => by
      rw [hLdef, getK_map_range S hj]
      exact prep_gen hS hj
    have hIL : ∀ j < 13, CFSG.KS.Raw.Orb.PRep 1755 11 (getK IL j 0) (titsT j)⁻¹ :=
      fun j hj => prep_geninv (hL j hj) (hperm j hj)
    obtain ⟨hnP, hparS⟩ := parOK_spec hpar
    let st : ℕ → ℕ → ℕ := fun c prev => mapFT 11 (mask 11) 6
      (ptIT 11 (mask 11) L IL (getK D.xw (Nat.mod (lastK (getRG WR c [])) 2) [])) prev
    let T : ℕ → ℕ := treeV st (baseTits 11) P
    have hT0 : T 0 = baseTits 11 := treeV_zero st _ P
    have hTs : ∀ c, 0 < c → c < D.nV → T c = st c (T (getK P (c - 1) 0)) := by
      intro c hc hcn
      obtain ⟨v, rfl⟩ : ∃ v, c = v + 1 := ⟨c - 1, by omega⟩
      have hp := (hparS (v + 1) hc hcn).1
      rw [Nat.add_sub_cancel] at hp ⊢
      exact treeV_succ st _ P hp
    rw [goodTB] at hgood
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hgood
    obtain ⟨h0, hw0, hmain⟩ := hgood
    have hFT : ∀ c, c < D.nV → getRG (rowsG FL) c 0 = T c := by
      intro c
      induction c using Nat.strong_induction_on with
      | _ c ih =>
        intro hc
        rcases Nat.eq_zero_or_pos c with rfl | hc0
        · rw [getRG_rowsG, ← getK_getD, Nat.beq_eq.mp hFL0, hT0]
        · have hpc := (hparS c hc0 hc).1
          have hi : lastK (getRG WR c []) % 2 < 2 := Nat.mod_lt _ (by decide)
          have hm := (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1
            ((CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 hmain (getK P (c - 1) 0) (by omega)) _ hi
          rw [CFSG.KS.PF.strictB_eqP] at hm
          simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.add_eq,
            Nat.mul_eq] at hm
          obtain ⟨-, -, he, -⟩ := hm
          rw [parTG_spec htree c hc0 (by omega), ih _ hpc (by omega)] at he
          rw [Nat.beq_eq.mp he, hTs c hc0 hc]
          rfl
    have hFLeq : FL = (List.range D.nV).map T := by
      have hl : FL.length = D.nV := by
        have := Nat.beq_eq.mp hlenFL
        rwa [CFSG.KC.LQT.Cov.Parse.lenK_length] at this
      apply List.ext_getElem (by simp [hl])
      intro n h1 h2
      have := hFT n (by omega)
      rw [getRG_rowsG, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
        Option.getD_some] at this
      simpa using this
    rw [hFLeq] at hmain hdist hblk
    have hnV : 0 < D.nV := Nat.blt_eq.mp h0
    have hz : D.words.getD 0 [] = [] := words_zero_nil (Nat.beq_eq.mp hw0)
    have hTv : ∀ v, v < D.nV → T v = mapFT 11 (mask 11) 6
        (ptVT 11 (mask 11) L IL D.xw (getRG WR v [])) (baseTits 11) := by
      intro v
      induction v using Nat.strong_induction_on with
      | _ v ih =>
        intro hv
        rcases Nat.eq_zero_or_pos v with rfl | hv0
        · rw [hT0, hWR, getRG_rowsG, hz]
          exact baseTits_fix.symm
        · obtain ⟨hplt, hne, hwd⟩ := hparS v hv0 hv
          have hl2 : lastK (getRG WR v []) < 2 := lastK_lt (fun l hl => hletters _
            (word_mem hwords hv) l (by rwa [hWR, getRG_rowsG] at hl)) hne
          rw [hTs v hv0 hv, ih _ hplt (by omega)]
          change mapFT 11 (mask 11) 6
              (ptIT 11 (mask 11) L IL (getK D.xw (Nat.mod (lastK (getRG WR v [])) 2) []))
              (mapFT 11 (mask 11) 6 (ptVT 11 (mask 11) L IL D.xw
                (getRG WR (getK P (v - 1) 0) [])) (baseTits 11)) = _
          have hm2 : Nat.mod (lastK (getRG WR v [])) 2 = lastK (getRG WR v []) :=
            Nat.mod_eq_of_lt hl2
          rw [hm2]
          conv_rhs => rw [← hwd]
          apply mapFT_congr (fun p hp => ptIT_lt2 _ _ hp) (fun p hp => ptVT_lt2 _ _ _ hp)
          intro j hj
          rw [pg_mapFT (fun p hp => ptVT_lt2 _ _ _ hp) _ hj, ptVT_append]
    have pg_T : ∀ v, v < D.nV → ∀ j < 6, pg 11 (mask 11) (T v) j =
        ptVT 11 (mask 11) L IL D.xw (getRG WR v []) (pg 11 (mask 11) (baseTits 11) j) := by
      intro v hv j hj
      rw [hTv v hv, pg_mapFT (fun p hp => ptVT_lt2 _ _ _ hp) _ hj]
    have hptV : ∀ v, v < D.nV → ∀ x : Fin 1755, ptVT 11 (mask 11) L IL D.xw (getRG WR v []) x =
        (((ofCT D).tab.el (ofCT D).x v)⁻¹ x : ℕ) := by
      intro v hv x
      rw [hWR, getRG_rowsG, ptVT_eq hxw2 hlx hL hIL _ (hletters _ (word_mem hwords hv)), el_eq]
    have hlo : ∀ l < 2, CFSG.Monster.B.Co2.Native.lettersOK 13 (D.xw.getD l []) = true :=
      fun l hl => by
      have := CFSG.KS.Prim.lettersK_sound (xw_letters hxw2 hlx hl)
      rwa [getK_getD] at this
    have hx : ∀ i, CFSG.Monster.B.Co2.Rep 1755 ((ofCT D).xa i) ((ofCT D).x i) := by
      intro i
      refine (ofCT D).xa_rep i ?_
      fin_cases i
      · exact hlo 0 (by norm_num)
      · exact hlo 1 (by norm_num)
    have hrep : ∀ {v : ℕ}, v < D.nV →
        CFSG.Monster.B.Co2.Rep 1755 ((ofCT D).elaTab[v]!) ((ofCT D).tab.el (ofCT D).x v) :=
      fun hv => (ofCT D).rep_el hx hv
    have hFg : ∀ {v : ℕ}, v < D.nV → getRG (rowsG ((List.range D.nV).map T)) v 0 = T v :=
      fun hv => FR_get hv
    have hgoodC : goodCheck (ofCT D) (ofCT D).elaTab = true := by
      rw [CFSG.KC.LQT.Cov.Perm.allLtK_iff] at hmain
      rw [goodCheck]
      simp only [Bool.and_eq_true, decide_eq_true_eq, CFSG.Monster.B.Co2.allLt_iff, and_assoc]
      refine ⟨hlo 0 (by norm_num), hlo 1 (by norm_num), hnV, ?_, ?_, ?_⟩
      · have hw : (ofCT D).words = D.words.toArray := rfl
        rw [hw, toArray_getElem!_list, hz]
        rfl
      · intro v hv i hi
        have hm := (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 (hmain v hv) i hi
        rw [CFSG.KS.PF.strictB_eqP] at hm
        simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hm
        obtain ⟨ht, hb, he, hback⟩ := hm
        simp only [getRG_rowsG, Nat.add_eq, Nat.mul_eq] at ht hb hback
        rw [getRG_rowsG D.tgt] at he
        simp only [Nat.add_eq, Nat.mul_eq] at he
        have htlt : D.tgt.getD (2 * v + i) D.nV < D.nV := Nat.blt_eq.mp ht
        have hblt : D.back.getD (2 * v + i) D.nV < D.nV := Nat.blt_eq.mp hb
        obtain ⟨-, htd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt htlt
        obtain ⟨-, hbd⟩ := CFSG.KC.LQT.Cov.Perm.getD_dflt hblt
        have htg : (ofCT D).tgtA = D.tgt.toArray := rfl
        have hbk : (ofCT D).backA = D.back.toArray := rfl
        have htA : (ofCT D).tgtA[2 * v + i]! = D.tgt.getD (2 * v + i) D.nV := by
          rw [htg, CFSG.KC.LQT.Cov.Perm.arr_get, ← htd]
        have hbA : (ofCT D).backA[2 * v + i]! = D.back.getD (2 * v + i) D.nV := by
          rw [hbk, CFSG.KC.LQT.Cov.Perm.arr_get, ← hbd]
        rw [hFg htlt, hFg hv] at he
        have he' := Nat.beq_eq.mp he
        have hel : (ofCT D).tab.el (ofCT D).x (D.tgt.getD (2 * v + i) D.nV) =
            (ofCT D).tab.el (ofCT D).x v * (ofCT D).x (fo i) := by
          apply eq_of_fields (el_mem D _) (Subgroup.mul_mem _ (el_mem D v)
            (wordIn_titsT_mem_titsD _))
          intro j hj x hxj
          have h1 := congrArg (fun c => pg 11 (mask 11) c j) he'
          rw [pg_T _ htlt j hj, pg_mapFT (fun p hp => ptIT_lt2 _ _ hp) _ hj, pg_T v hv j hj,
            ← hxj, hptV _ htlt x, hptV v hv x,
            ptIT_eq hL hIL _ (xw_letters hxw2 hlx hi)] at h1
          rw [← xw_get D hi] at h1
          rw [mul_inv_rev, Equiv.Perm.mul_apply]
          exact h1
        refine ⟨by rw [htA]; exact htlt, by rw [hbA]; exact hblt, ?_, ?_⟩
        · rw [htA]
          exact (CFSG.Monster.B.Co2.eqA_iff (hrep htlt)
            (CFSG.Monster.B.Co2.rep_compA (hrep hv) (hx _))).2 hel
        · rw [hbA, ← hbd, htg, CFSG.KC.LQT.Cov.Perm.arr_get, beq_iff_eq]
          exact Nat.eq_of_beq_eq_true hback
      · intro u hu v hv
        by_cases huv : u < v
        · rw [decide_eq_true huv]
          simp only [Bool.not_true, Bool.false_or]
          rw [Bool.not_eq_true', Bool.eq_false_iff]
          intro heq
          have hel := (CFSG.Monster.B.Co2.eqA_iff (hrep hu) (hrep hv)).1 heq
          have hTT : T u = T v := by
            rw [hTv u hu, hTv v hv]
            apply mapFT_congr (fun p hp => ptVT_lt2 _ _ _ hp) (fun p hp => ptVT_lt2 _ _ _ hp)
            intro j hj
            have hb := base_lt j hj
            have e1 := hptV u hu ⟨_, hb⟩
            have e2 := hptV v hv ⟨_, hb⟩
            rw [hel] at e1
            exact e1.trans e2.symm
          have hnd := CFSG.KC.LQT.T2.nodup_of_distinctS hdist
          have hlu : u < ((List.range D.nV).map T).length := by
            rw [List.length_map, List.length_range]
            exact hu
          have hlv : v < ((List.range D.nV).map T).length := by
            rw [List.length_map, List.length_range]
            exact hv
          have helem : ((List.range D.nV).map T)[u]'hlu = ((List.range D.nV).map T)[v]'hlv := by
            simp only [List.getElem_map, List.getElem_range]
            exact hTT
          have := (List.Nodup.getElem_inj_iff hnd).1 helem
          omega
        · simp [huv]
    have hblocks : (ofCT D).blocks.all (blkCheck (ofCT D) (ofCT D).elaTab) = true := by
      have hbl : (ofCT D).blocks = D.blocks.map (fun b =>
          ({ gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 } : Blk)) := rfl
      rw [hbl, List.all_map]
      apply List.all_eq_true.2
      intro bl hbl
      have h := (CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hblk bl hbl
      rw [blkTB] at h
      simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
      obtain ⟨hl, hlen, h32, hall⟩ := h
      rw [CFSG.KC.LQT.Cov.Perm.allLtK_iff] at hall
      have hlo' := CFSG.KS.Prim.lettersK_sound hl
      have hGa := rep_wordArr_titsT hlo'
      have hinv := isInvA_of_rep hGa (rep_invCand hGa)
      have hGi := CFSG.Monster.B.Co2.rep_inv_of_isInvA hGa hinv
      simp only [Function.comp_apply, blkCheck, Bool.and_eq_true, decide_eq_true_eq,
        CFSG.Monster.B.Co2.allLt_iff, beq_iff_eq]
      refine ⟨⟨⟨⟨hlo', hinv⟩, ?_⟩, ?_⟩, ?_⟩
      · simpa [CFSG.KC.LQT.Cov.Parse.lenK_length] using Nat.beq_eq.mp hlen
      · simpa [CFSG.KC.LQT.Cov.Parse.lenK_length] using Nat.ble_eq.mp h32
      · intro j hj
        have hm := hall j (by simpa [CFSG.KC.LQT.Cov.Parse.lenK_length] using hj)
        simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hm
        obtain ⟨ha, hb, he⟩ := hm
        obtain ⟨hia, ha'⟩ := list_idx ha
        obtain ⟨hib, hb'⟩ := list_idx hb
        refine ⟨⟨by rw [hia]; exact ha', by rw [hib]; exact hb'⟩, ?_⟩
        rw [hia, hib]
        rw [hFg hb'] at he
        have he' := Nat.beq_eq.mp he
        have e2 : (ofCT D).tab.el (ofCT D).x (getK bl.2.2.1 j 0) * wordIn 13 titsT bl.1 =
            wordIn 13 titsT bl.1 * (ofCT D).tab.el (ofCT D).x (getK bl.2.1 j 0) := by
          apply eq_of_fields (Subgroup.mul_mem _ (el_mem D _) (wordIn_titsT_mem_titsD _))
            (Subgroup.mul_mem _ (wordIn_titsT_mem_titsD _) (el_mem D _))
          intro j' hj' x hxj
          have h1 := congrArg (fun c => pg 11 (mask 11) c j') he'
          rw [pg_mapFT (fun p hp => ptIT_lt2 _ _ hp) _ hj', pg_T _ hb' j' hj',
            pg_mapFT (fun p hp => ptVT_lt2 _ _ _ (ptIT_lt2 _ _ hp)) _ hj', ← hxj,
            hptV _ hb' x, ptIT_eq hL hIL _ hl x,
            ptIT_eq hL hIL _ hl (((ofCT D).tab.el (ofCT D).x (getK bl.2.2.1 j 0))⁻¹ x),
            hptV _ ha' _] at h1
          rw [mul_inv_rev, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
          exact h1
        have hrel : wordIn 13 titsT bl.1 * (ofCT D).tab.el (ofCT D).x (getK bl.2.1 j 0) *
            (wordIn 13 titsT bl.1)⁻¹ = (ofCT D).tab.el (ofCT D).x (getK bl.2.2.1 j 0) := by
          rw [← e2, mul_assoc, mul_inv_cancel, mul_one]
        exact (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA
          (CFSG.Monster.B.Co2.rep_compA hGa (hrep ha')) hGi) (hrep hb')).2 hrel
    obtain ⟨hvalid, hge⟩ :=
      eqns_checks D H hletters hnV (Nat.beq_eq.mp hlenH) htri hflagsH hformsBound
    rw [hpd, covCheck]
    refine ⟨?_, Nat.beq_eq.mp hnv0⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨hgoodC, hblocks⟩, hvalid⟩, hge⟩

end CFSG.KC.LQT.Cov

end
