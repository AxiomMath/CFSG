module

public import Certificates.Data.Kernel.Spor.MSylowCent
public import CFSG.Certificates.Kernel.Spor.MSylowSound
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Certificates.Kernel.Spor.PCountWSound

public section

namespace CFSG.KS.MSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Monster.B.Mathieu
open CFSG.KS.PK CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC

variable {n : Nat}

theorem letP_pkw {w : Nat} (vs ws : List (Equiv.Perm (Fin n))) (l : Int) :
    letP (pkw w (1 : Equiv.Perm (Fin n))) (vs.map (pkw w)) (ws.map (pkw w)) l =
      pkw w (if 0 < l then vs.getD (l.natAbs - 1) 1 else ws.getD (l.natAbs - 1) 1) := by
  have hg : ∀ (L : List (Equiv.Perm (Fin n))) (k : Nat),
      (L.map (pkw w)).getD k (pkw w 1) = pkw w (L.getD k 1) := fun L k => getD_map (pkw w) L k 1
  rcases l with (_ | j) | k
  · change getDN _ 0 _ = _
    rw [getDN_eq, hg]
    simp
  · change getDN _ j _ = _
    have e : (Int.ofNat (j + 1)).natAbs - 1 = j := rfl
    have e' : (0 : Int) < Int.ofNat (j + 1) := Int.ofNat_succ_pos j
    rw [getDN_eq, hg, if_pos e', e]
  · change getDN _ k _ = _
    rw [getDN_eq, hg]
    simp

theorem wordV_pkw {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (vs : List (Equiv.Perm (Fin n))) :
    ∀ ws : List Int, wordV n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (vs.map (pkw w))
      ((vs.map (·⁻¹)).map (pkw w)) ws = pkw w (wordValue vs ws)
  | [] => by rw [wordValue_nil']; rfl
  | l :: ws => by
    rw [wordV_cons, PK.strictN_eq, wordV_pkw hn32 hw vs ws, letP_pkw, pkw_mul hw hn32,
      wordValue_cons', letterValue_eq, getD_map_inv]

theorem wordI_pkw {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (vs : List (Equiv.Perm (Fin n))) :
    ∀ ws : List Int, wordI n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (vs.map (pkw w))
      ((vs.map (·⁻¹)).map (pkw w)) ws = pkw w (wordValue vs ws)⁻¹
  | [] => by rw [wordValue_nil', inv_one]; rfl
  | l :: ws => by
    rw [wordI_cons, PK.strictN_eq, wordI_pkw hn32 hw vs ws]
    change pcomp n w (mask w) _ (letP _ ((vs.map (·⁻¹)).map (pkw w)) (vs.map (pkw w)) l) = _
    rw [letP_pkw, pkw_mul hw hn32, wordValue_cons', letterValue_eq, mul_inv_rev, getD_map_inv]
    split_ifs <;> simp

theorem slpRun_pkw {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) :
    ∀ (ds : List (List Int)) (vs : List (Equiv.Perm (Fin n))),
      slpRun n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) ds (vs.map (pkw w))
          ((vs.map (·⁻¹)).map (pkw w)) =
        ((ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map (pkw w),
          ((ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map (·⁻¹)).map (pkw w))
  | [], _ => rfl
  | d :: ds, vs => by
    have e := slpRun_pkw hn32 hw ds (vs ++ [wordValue vs d])
    simp only [List.map_append, List.map_cons, List.map_nil] at e
    rw [slpRun_cons, strictP_eq, strictP_eq, wordV_pkw hn32 hw, wordI_pkw hn32 hw, e]
    rfl

theorem slpP_pkw {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (x y : Equiv.Perm (Fin n))
    (ds : List (List Int)) :
    slpP n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w x) (pkw w x⁻¹) (pkw w y)
        (pkw w y⁻¹) ds =
      ((slpVals x y ds).map (pkw w), ((slpVals x y ds).map (·⁻¹)).map (pkw w)) :=
  slpRun_pkw hn32 hw ds [x, y]

theorem exprsV_pkw {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (L : List (Equiv.Perm (Fin n))) :
    ∀ es : List (List Int),
      exprsV n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (L.map (pkw w), (L.map (·⁻¹)).map (pkw w))
        es = es.map fun e => pkw w (wordValue L e)
  | [] => rfl
  | e :: es => by
    change wordV n w (mask w) _ (L.map (pkw w)) ((L.map (·⁻¹)).map (pkw w)) e ::
      exprsV n w (mask w) _ _ es = _
    rw [wordV_pkw hn32 hw, exprsV_pkw hn32 hw L es]
    rfl

theorem exprsV_slpP_pkw {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (x y : Equiv.Perm (Fin n))
    (ds es : List (List Int)) :
    exprsV n w (mask w) (pkw w (1 : Equiv.Perm (Fin n)))
        (slpP n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w x) (pkw w x⁻¹) (pkw w y)
          (pkw w y⁻¹) ds) es =
      es.map fun e => pkw w (slpExpr x y ds e) := by
  rw [slpP_pkw hn32 hw, exprsV_pkw hn32 hw]
  rfl

theorem prep_pkw {w : Nat} (hw : n ≤ 2 ^ w) (g : Equiv.Perm (Fin n)) : PRep n w (pkw w g) g :=
  fun x => by
    rw [PK.pg_eq]
    change fd w (pkw w g) x = _
    rw [fd_pkw hw g x.2]
    simp [pv, x.2]

theorem pkw_shr {w : Nat} (hw : n ≤ 2 ^ w) (g : Equiv.Perm (Fin n)) : pkw w g >>> (n * w) = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  exact Nat.div_eq_of_lt (pkw_lt hw g)

theorem beq_canon {w P Q : Nat} {x y : Equiv.Perm (Fin n)} (hw : 0 < w) (hP : PRep n w P x)
    (hQ : PRep n w Q y) (sP : P >>> (n * w) = 0) (sQ : Q >>> (n * w) = 0) :
    Nat.beq P Q = decide (x = y) := by
  by_cases e : x = y
  · rw [decide_eq_true e]
    have : P = Q := PF.eq_of_fields hw sP sQ fun i hi => by rw [hP ⟨i, hi⟩, hQ ⟨i, hi⟩, e]
    rw [this]
    exact Nat.beq_refl _
  · rw [decide_eq_false e]
    cases hb : Nat.beq P Q
    · rfl
    · rw [Nat.eq_of_beq_eq_true hb] at hP
      exact absurd (Raw.Orb.prep_unique hP hQ) e

theorem allL_comm_pkw {w P : Nat} {x : Equiv.Perm (Fin n)} (hn32 : n < 2 ^ 32) (hw0 : 0 < w)
    (hw : n ≤ 2 ^ w) (hP : PRep n w P x) : ∀ ps : List (Equiv.Perm (Fin n)),
      allL (fun g => Nat.beq (pcomp n w (mask w) P g) (pcomp n w (mask w) g P))
        (ps.map (pkw w)) = decide (∀ p ∈ ps, x * p = p * x)
  | [] => by simp [allL]
  | p :: ps => by
    change bAnd(Nat.beq (pcomp n w (mask w) P (pkw w p)) (pcomp n w (mask w) (pkw w p) P),
      allL _ (ps.map (pkw w))) = _
    rw [beq_pcomp_iff hn32 hw0 hP (prep_pkw hw p) (prep_pkw hw p) hP,
      allL_comm_pkw hn32 hw0 hw hP ps, PK.bAnd_eq]
    simp [List.forall_mem_cons]

theorem centBadP_eq {w P : Nat} {x : Equiv.Perm (Fin n)} (hn24 : n < 16777216)
    (hw1 : n + 1 < 2 ^ w) (hP : PRep n w P x) (sP : P >>> (n * w) = 0)
    (z : Equiv.Perm (Fin n)) (ps : List (Equiv.Perm (Fin n))) :
    centBadP n w (mask w) (pidn n w) (pkw w z) (ps.map (pkw w)) P =
      decide ((∀ p ∈ ps, x * p = p * x) ∧ x ≠ 1 ∧ x ≠ z) := by
  have hn32 : n < 2 ^ 32 := by omega
  have hw : n ≤ 2 ^ w := by omega
  have hw0 : 0 < w := PF.w_pos hw1
  have e1 : ∀ c : Bool, bIf(c, false, true) = !c := fun c => by cases c <;> rfl
  unfold centBadP commAllP
  rw [allL_comm_pkw hn32 hw0 hw hP, beq_canon hw0 hP (prep_pidn hn24 hw1) sP (PF.pidn_shr hn24 hw1),
    beq_canon hw0 hP (prep_pkw hw z) sP (pkw_shr hw z)]
  simp only [e1, PK.bAnd_eq]
  simp [Bool.decide_and]

variable {w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem cent_of_scan (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (z : Equiv.Perm (Fin n))
    (ps : List (Equiv.Perm (Fin n)))
    (h : enumFrom n w (mask w) (n * w) LR TR (centBadP n w (mask w) (pidn n w) (pkw w z)
      (ps.map (pkw w))) k 0 (pidn n w) 0 = 0) :
    ∀ g ∈ enumeration (certificate hn gens words bv hbs), (∀ p ∈ ps, g * p = p * g) →
      g = 1 ∨ g = z := by
  have hn24 : n < 16777216 := by have := hQ.2.2.1; omega
  have hw1 : n + 1 < 2 ^ w := hQ.2.1
  have e := enumFrom_spec hQ
    (q := fun x => decide ((∀ p ∈ ps, x * p = p * x) ∧ x ≠ 1 ∧ x ≠ z))
    (fun P x hP sP => centBadP_eq hn24 hw1 hP sP z ps) k 0 (by omega) (pidn n w) 1 0
    (prep_pidn hn24 hw1) (PF.pidn_shr hn24 hw1)
  rw [h] at e
  simp only [Nat.zero_add, one_mul, List.map_id'] at e
  have e2 : (List.range k).map (fun t => trL n w LR TR t) = (List.range k).map (trL n w LR TR) :=
    rfl
  rw [e2, ← enumeration_trL hQ hn hbs] at e
  have hz := List.countP_eq_zero.1 e.symm
  intro g hg hc
  have := hz g hg
  simp only [decide_eq_true_eq, not_and, not_not] at this
  by_cases h1 : g = 1
  · exact Or.inl h1
  · exact Or.inr (this hc h1)

theorem sylCentOK_of_scan (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {a b z : Equiv.Perm (Fin n)}
    {ds es : List (List Int)} {cap N kk : Nat}
    (hP : sylowAutOK n (toTable a) (toTable b) ds es (toTable z) cap N kk = true)
    (hzb : z * b ≠ b * z)
    (h : enumFrom n w (mask w) (n * w) LR TR (centBadP n w (mask w) (pidn n w) (pkw w z)
      (es.map fun e => pkw w (slpExpr a b ds e))) k 0 (pidn n w) 0 = 0) :
    sylCentOK n (sylowGens n (toTable a) (toTable b) ds es) (toTable z) (toTable b)
      (allTables (certificate hn gens words bv hbs)) = true := by
  have hn32 : n < 2 ^ 32 := chainK_h32 hQ
  have hra : Rep n (toTable a) a := rep_toTable hn32 a
  have hrb : Rep n (toTable b) b := rep_toTable hn32 b
  have hrz : Rep n (toTable z) z := rep_toTable hn32 z
  simp only [sylowAutOK, Bool.and_eq_true] at hP
  have h1 := hP.1.1.1.1.1.1.1.1.1.1.1.1
  have h2 := hP.1.1.1.1.1.1.1.1.1.1.1.2
  have hV := rep_tblSlp hn32 hra hrb ds h1
  have hmap : (es.map fun e => pkw w (slpExpr a b ds e)) = (es.map (slpExpr a b ds)).map (pkw w) := by
    rw [List.map_map]
    rfl
  rw [hmap] at h
  have hcent := cent_of_scan hn hbs hQ z _ h
  simp only [sylCentOK, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · cases hc : commT n (toTable z) (toTable b)
    · rfl
    · exact absurd ((commT_iff hrz hrb).1 hc) hzb
  · rw [List.all_eq_true]
    intro D hD
    obtain ⟨g, hg, hDg⟩ := CFSG.Sporadic.Schreier.exists_mem_of_forall₂_right
      (forall₂_allTables hn32 _) D hD
    rw [List.mem_reverse] at hg
    cases hall : (sylowGens n (toTable a) (toTable b) ds es).all fun p => commT n D p
    · rfl
    · have hc : ∀ p ∈ es.map (slpExpr a b ds), g * p = p * g := by
        intro p hp
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        have hok := List.all_eq_true.1 h2 e he
        have hr := rep_tblWord hn32 hV e hok
        have hmem : (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 e).1 ∈
            sylowGens n (toTable a) (toTable b) ds es := by
          simp only [sylowGens, List.mem_toArray, List.mem_map]
          exact ⟨e, he, rfl⟩
        have := (Array.all_eq_true_iff_forall_mem.1 hall) _ hmem
        exact (commT_iff hDg hr).1 this
      rcases hcent g hg hc with rfl | rfl
      · simp [tblEq_of_rep hDg (Rep.idT hn32)]
      · simp [tblEq_of_rep hDg hrz]

end CFSG.KS.MSyl

end
