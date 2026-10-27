module

public import Certificates.Data.Kernel.Spor.MSylow
public import CFSG.Sporadic.Schreier.MathieuSylowAutSpec
import CFSG.Certificates.Kernel.Spor.MSylowSound
public import CFSG.Certificates.Kernel.Spor.PCountWSound

public section

namespace CFSG.KS.MSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Monster.B.Mathieu CFSG.KS.PK

variable {n : Nat}

private theorem beq_pkw_iff {w : Nat} (hw : n ≤ 2 ^ w) {σ τ : Equiv.Perm (Fin n)} :
    Nat.beq (pkw w σ) (pkw w τ) = true ↔ σ = τ := by
  rw [Nat.beq_eq]
  exact ⟨pkw_inj hw, fun h => h ▸ rfl⟩

private theorem letP_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (vs ws : List (Equiv.Perm (Fin n))) (l : Int) :
    letP (pkw wd (1 : Equiv.Perm (Fin n))) (vs.map (pkw wd)) (ws.map (pkw wd)) l =
      pkw wd (if 0 < l then vs.getD (l.natAbs - 1) 1 else ws.getD (l.natAbs - 1) 1) := by
  have hg : ∀ (L : List (Equiv.Perm (Fin n))) (k : Nat),
      (L.map (pkw wd)).getD k (pkw wd 1) = pkw wd (L.getD k 1) := fun L k => getD_map (pkw wd) L k 1
  rcases l with (_ | j) | k
  · show getDN _ 0 _ = _
    rw [getDN_eq, hg]
    simp
  · show getDN _ j _ = _
    have e : (Int.ofNat (j + 1)).natAbs - 1 = j := rfl
    have e' : (0 : Int) < Int.ofNat (j + 1) := Int.ofNat_succ_pos j
    rw [getDN_eq, hg, if_pos e', e]
  · show getDN _ k _ = _
    rw [getDN_eq, hg]
    simp

private theorem wordV_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (vs : List (Equiv.Perm (Fin n))) : ∀ w : List Int,
    wordV n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (vs.map (pkw wd)) ((vs.map (·⁻¹)).map (pkw wd)) w =
      pkw wd (wordValue vs w)
  | [] => by rw [wordValue_nil']; rfl
  | l :: w => by
    rw [wordV_cons, strictN_eq, wordV_pkw hn32 hw vs w, letP_pkw hn32 hw, pkw_mul hw hn32, wordValue_cons',
      letterValue_eq, getD_map_inv]

private theorem wordI_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (vs : List (Equiv.Perm (Fin n))) : ∀ w : List Int,
    wordI n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (vs.map (pkw wd)) ((vs.map (·⁻¹)).map (pkw wd)) w =
      pkw wd (wordValue vs w)⁻¹
  | [] => by rw [wordValue_nil', inv_one]; rfl
  | l :: w => by
    rw [wordI_cons, strictN_eq, wordI_pkw hn32 hw vs w]
    show pcomp n wd (mask wd) _ (letP _ ((vs.map (·⁻¹)).map (pkw wd)) (vs.map (pkw wd)) l) = _
    rw [letP_pkw hn32 hw, pkw_mul hw hn32, wordValue_cons', letterValue_eq, mul_inv_rev, getD_map_inv]
    split_ifs <;> simp

private theorem slpRun_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) : ∀ (ds : List (List Int)) (vs : List (Equiv.Perm (Fin n))),
    slpRun n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) ds (vs.map (pkw wd)) ((vs.map (·⁻¹)).map (pkw wd)) =
      ((ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map (pkw wd),
        ((ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map (·⁻¹)).map (pkw wd))
  | [], _ => rfl
  | d :: ds, vs => by
    have e := slpRun_pkw hn32 hw ds (vs ++ [wordValue vs d])
    simp only [List.map_append, List.map_cons, List.map_nil] at e
    rw [slpRun_cons, strictP_eq, strictP_eq, wordV_pkw hn32 hw, wordI_pkw hn32 hw, e]
    rfl

private theorem slpP_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (x y : Equiv.Perm (Fin n)) (ds : List (List Int)) :
    slpP n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) (pkw wd x⁻¹) (pkw wd y) (pkw wd y⁻¹) ds =
      ((slpVals x y ds).map (pkw wd), ((slpVals x y ds).map (·⁻¹)).map (pkw wd)) :=
  slpRun_pkw hn32 hw ds [x, y]

private theorem exprsV_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (L : List (Equiv.Perm (Fin n))) : ∀ es : List (List Int),
    exprsV n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (L.map (pkw wd), (L.map (·⁻¹)).map (pkw wd)) es =
      es.map fun e => pkw wd (wordValue L e)
  | [] => rfl
  | e :: es => by
    show wordV n wd (mask wd) _ (L.map (pkw wd)) ((L.map (·⁻¹)).map (pkw wd)) e :: exprsV n wd (mask wd) _ _ es = _
    rw [wordV_pkw hn32 hw, exprsV_pkw hn32 hw L es]
    rfl

private theorem exprsI_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (L : List (Equiv.Perm (Fin n))) : ∀ es : List (List Int),
    exprsI n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (L.map (pkw wd), (L.map (·⁻¹)).map (pkw wd)) es =
      es.map fun e => pkw wd (wordValue L e)⁻¹
  | [] => rfl
  | e :: es => by
    show wordI n wd (mask wd) _ (L.map (pkw wd)) ((L.map (·⁻¹)).map (pkw wd)) e :: exprsI n wd (mask wd) _ _ es = _
    rw [wordI_pkw hn32 hw, exprsI_pkw hn32 hw L es]
    rfl

private theorem powP_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (x : Equiv.Perm (Fin n)) : ∀ e : Nat,
    powP n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) e = pkw wd (x ^ e)
  | 0 => by rw [pow_zero]; rfl
  | e + 1 => by
    show strictN (powP n wd (mask wd) _ (pkw wd x) e) _ = _
    rw [strictN_eq, powP_pkw hn32 hw x e, pkw_mul hw hn32, ← pow_succ']

private theorem ordLoop_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (x : Equiv.Perm (Fin n)) (o : Nat) :
    ∀ (k f d : Nat), d + k = o → k < f →
      (ordLoop n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) o f (pkw wd (x ^ d)) d = true ↔
        x ^ o = 1 ∧ ∀ e, d ≤ e → e < o → e ∣ o → x ^ e ≠ 1)
  | _, 0, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | 0, f + 1, d, hd, _ => by
    have h : ordLoop n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) o (f + 1) (pkw wd (x ^ d)) d =
        bIf(Nat.beq d o, Nat.beq (pkw wd (x ^ d)) (pkw wd 1),
          bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq (pkw wd (x ^ d)) (pkw wd 1), false, true),
            true), strictB (pcomp n wd (mask wd) (pkw wd (x ^ d)) (pkw wd x)) (fun q =>
              ordLoop n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) o f q (Nat.succ d)))) := rfl
    have hdo : d = o := by omega
    subst hdo
    rw [h, bIf_eq]
    simp only [Nat.beq_refl, ↓reduceIte, beq_pkw_iff hw]
    exact ⟨fun h => ⟨h, fun e h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩
  | k + 1, f + 1, d, hd, hf => by
    have h : ordLoop n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) o (f + 1) (pkw wd (x ^ d)) d =
        bIf(Nat.beq d o, Nat.beq (pkw wd (x ^ d)) (pkw wd 1),
          bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq (pkw wd (x ^ d)) (pkw wd 1), false, true),
            true), strictB (pcomp n wd (mask wd) (pkw wd (x ^ d)) (pkw wd x)) (fun q =>
              ordLoop n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) o f q (Nat.succ d)))) := rfl
    have hdo : (Nat.beq d o = true) = False := by rw [Nat.beq_eq]; exact eq_false (by omega)
    rw [h, bIf_eq]
    simp only [hdo, ↓reduceIte]
    rw [bAnd_eq, strictB_eq, pkw_mul hw hn32, ← pow_succ, Bool.and_eq_true,
      ordLoop_pkw hn32 hw x o k f (d + 1) (by omega) (by omega), bIf_eq, bIf_eq]
    simp only [Nat.beq_eq, beq_pkw_iff hw]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, fun e he1 he2 he3 => ?_⟩
      rcases Nat.eq_or_lt_of_le he1 with hde | he1
      · subst hde
        have hm : Nat.mod o d = 0 := Nat.mod_eq_zero_of_dvd he3
        simp only [hm, ↓reduceIte] at h1
        intro hx
        simp [hx] at h1
      · exact h3 e he1 he2 he3
    · rintro ⟨h2, h3⟩
      refine ⟨?_, h2, fun e he1 he2 he3 => h3 e (by omega) he2 he3⟩
      split_ifs with hm hx
      · exact absurd hx (h3 d le_rfl (by omega) (Nat.dvd_of_mod_eq_zero (n := o) hm))
      · rfl
      · rfl

private theorem ordExP_pkw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (x : Equiv.Perm (Fin n)) {o : Nat} (ho : 0 < o) :
    ordExP n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) (pkw wd x) o = true ↔ orderOf x = o := by
  have h := ordLoop_pkw hn32 hw x o (o - 1) o 1 (by omega) (by omega)
  rw [pow_one] at h
  rw [ordExP, h]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < orderOf x := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨o, ho, h1⟩)
    have hd := orderOf_dvd_of_pow_eq_one h1
    rcases Nat.lt_or_ge (orderOf x) o with hl | hl
    · exact absurd (pow_orderOf_eq_one x) (h2 _ hpos hl hd)
    · exact le_antisymm (Nat.le_of_dvd ho hd) hl
  · rintro rfl
    refine ⟨pow_orderOf_eq_one x, fun e he1 he2 _ hx => ?_⟩
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hx)
    omega

private def SimAw (wd n : Nat) (A : Array Table) (E : List Nat) : Prop :=
  E.length = A.size ∧ ∀ i < A.size, ∀ σ : Equiv.Perm (Fin n), Rep n A[i]! σ → E.getD i 0 = pkw wd σ

section

open CFSG.KS.KeyBfs

variable {G : Array Table} {gg : Nat → Equiv.Perm (Fin n)} {Gp : List Nat}


private theorem sim_inner_stepw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (hG : ∀ l < G.size, Rep n G[l]! (gg l)) {h j : Nat} {s : St}
    {E : List Nat} {τ : Equiv.Perm (Fin n)} (hj : j < G.size)
    (hI : CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h j s)
    (hh : h < s.2.1.size) (hτ : Rep n s.2.1[h]! τ) (hS : SimAw wd n s.2.1 E) :
    ∃ s', innerBody n (fun l y => compT n y G[l]!) s.2.1[h]! h j s = pure (ForInStep.yield s') ∧
      CInv n G.size (fun l y => compT n y G[l]!) (idT n)
        (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h (j + 1) s' ∧
      s.2.1.size ≤ s'.2.1.size ∧ s'.2.1[h]! = s.2.1[h]! ∧
      SimAw wd n s'.2.1 (if memB (pkw wd (τ * gg j)) E = true then E else E ++ [pkw wd (τ * gg j)]) := by
  obtain ⟨s', e, hI', hle, hh'⟩ := cinv_inner_step (good_step hG) hj hI hh
  refine ⟨s', e, hI', hle, hh', ?_⟩
  obtain ⟨-, -, -, -, hg, -, hK, -, -⟩ := hI
  have hTr : Rep n (compT n s.2.1[h]! G[j]!) (τ * gg j) := Rep.compT hτ (hG j hj)
  have hmem : memB (pkw wd (τ * gg j)) E = s.1.contains (key n (compT n s.2.1[h]! G[j]!)) := by
    rw [Bool.eq_iff_iff, memB_iff, hK]
    constructor
    · intro hm
      obtain ⟨i, hi, hiE⟩ := List.getElem_of_mem hm
      have hi' : i < s.2.1.size := hS.1 ▸ hi
      obtain ⟨σ, hσ⟩ := hg i hi'
      have := hS.2 i hi' σ hσ
      rw [getD_eq_getElem' hi, hiE] at this
      refine ⟨i, hi', ?_⟩
      rw [← pkw_inj hw this] at hσ
      exact CFSG.KS.ClassOne.key_eq_of_rep hσ hTr
    · rintro ⟨i, hi, hk⟩
      obtain ⟨σ, hσ⟩ := hg i hi
      have hσe : σ = τ * gg j := CFSG.KS.Tbl.key_inj hσ hTr hk
      have := hS.2 i hi σ hσ
      rw [← hS.1] at hi
      rw [getD_eq_getElem' hi] at this
      rw [← hσe, ← this]
      exact List.getElem_mem hi
  simp only [innerBody] at e
  by_cases hc : s.1.contains (key n (compT n s.2.1[h]! G[j]!)) = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at e
    have e' : s' = (s.1, s.2.1, s.2.2.1, s.2.2.2) := (ForInStep.yield.inj e).symm
    rw [e', if_pos (hmem.trans hc)]
    exact hS
  · have hc' : s.1.contains (key n (compT n s.2.1[h]! G[j]!)) = false := Bool.eq_false_iff.2 hc
    simp only [hc', Bool.not_false, ↓reduceIte] at e
    have e' := (ForInStep.yield.inj e).symm
    rw [e', if_neg (by rw [hmem]; exact hc)]
    refine ⟨by simp [hS.1], fun i hi σ hσ => ?_⟩
    change i < (s.2.1.push (compT n s.2.1[h]! G[j]!)).size at hi
    change Rep n (s.2.1.push (compT n s.2.1[h]! G[j]!))[i]! σ at hσ
    rw [Array.size_push] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | rfl
    · rw [push_lt a] at hσ
      have hi' : i < E.length := hS.1 ▸ a
      rw [getD_eq_getElem' (by simp; omega), List.getElem_append_left hi', ← getD_eq_getElem' hi']
      exact hS.2 i a σ hσ
    · rw [push_eq] at hσ
      have hσe : σ = τ * gg j := CFSG.KS.Tbl.key_inj hσ hTr rfl
      rw [← hS.1, hσe]
      simp

private theorem sim_innerw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (hG : ∀ l < G.size, Rep n G[l]! (gg l)) (hGp : Gp.length = G.size)
    (hGv : ∀ l < G.size, Gp.getD l 0 = pkw wd (gg l)) {h : Nat} {s : St} {E : List Nat}
    (hI : CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h 0 s)
    (hh : h < s.2.1.size) (hS : SimAw wd n s.2.1 E) :
    let s' := Id.run (forIn (List.range' 0 G.size) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerBody n (fun l y => compT n y G[l]!) s.2.1[h]! h))
    SimAw wd n s'.2.1 (clAdd n wd (mask wd) (getN E h) Gp E) ∧ s.2.1.size ≤ s'.2.1.size := by
  obtain ⟨τ, hτ⟩ := hI.2.2.2.2.1 h hh
  have hy : getN E h = pkw wd τ := by rw [getN_eq]; exact hS.2 h hh τ hτ
  have := forIn_range'_yield G.size 0 (s.1, s.2.1, s.2.2.1, s.2.2.2)
    (innerBody n (fun l y => compT n y G[l]!) s.2.1[h]! h)
    (fun j s' => CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h j s' ∧ s.2.1.size ≤ s'.2.1.size ∧
      s'.2.1[h]! = s.2.1[h]! ∧ SimAw wd n s'.2.1 (clAdd n wd (mask wd) (pkw wd τ) (Gp.take j) E))
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨hI', hle, he, hS'⟩ := hP
      have hτ' : Rep n s'.2.1[h]! τ := he ▸ hτ
      obtain ⟨s'', e, hI'', hle', he', hS''⟩ := sim_inner_stepw hn32 hw hG hj hI' (by omega) hτ' hS'
      rw [he] at e
      refine ⟨s'', e, hI'', by omega, he'.trans he, ?_⟩
      have ht : Gp.take (j + 1) = Gp.take j ++ [Gp.getD j 0] := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega),
          getD_eq_getElem' (show j < Gp.length by omega)]
        rfl
      rw [ht, clAdd_append, clAdd_cons', hGv j hj, pkw_mul hw hn32]
      exact hS'')
    ⟨hI, le_rfl, rfl, hS⟩
  obtain ⟨-, hle, -, hS'⟩ := this
  rw [List.take_of_length_le (by omega), ← hy] at hS'
  exact ⟨hS', hle⟩

private theorem sim_outerw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (hG : ∀ l < G.size, Rep n G[l]! (gg l)) (hGp : Gp.length = G.size)
    (hGv : ∀ l < G.size, Gp.getD l 0 = pkw wd (gg l)) (cap : Nat) :
    let s := Id.run (forIn (List.range' 0 cap) (initSt n (idT n))
      (outerBody n (fun l y => compT n y G[l]!) G.size))
    (∃ h', CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h' 0 s) ∧
      SimAw wd n s.2.1 (clRun n wd (mask wd) Gp cap 0 [pkw wd (1 : Equiv.Perm (Fin n))]) := by
  have hn32 : n < 2 ^ 32 := by omega
  have hroot : ∃ σ : Equiv.Perm (Fin n), Rep n (idT n) σ := ⟨1, Rep.idT hn32⟩
  have hinit : SimAw wd n (initSt n (idT n)).2.1 [pkw wd (1 : Equiv.Perm (Fin n))] := by
    refine ⟨by simp [initSt], fun i hi σ hσ => ?_⟩
    have hi0 : i = 0 := by simp [initSt] at hi; omega
    subst hi0
    have h1 : σ = 1 := CFSG.KS.ClassOne.rep_unique hσ (by simpa [initSt] using Rep.idT (G := Equiv.Perm (Fin n)) hn32)
    rw [h1]
    rfl
  refine forIn_range'_done cap 0 (initSt n (idT n)) (outerBody n (fun l y => compT n y G[l]!) G.size)
    (fun j s => j ≤ s.2.1.size ∧ CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) j 0 s ∧ ∃ E, SimAw wd n s.2.1 E ∧
        clRun n wd (mask wd) Gp (cap - j) j E =
          clRun n wd (mask wd) Gp cap 0 [pkw wd (1 : Equiv.Perm (Fin n))])
    (fun s => (∃ h', CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h' 0 s) ∧
      SimAw wd n s.2.1 (clRun n wd (mask wd) Gp cap 0 [pkw wd (1 : Equiv.Perm (Fin n))]))
    (fun j hj s hP => ?_) (fun s hP => ?_)
    ⟨Nat.zero_le _, cinv_init hroot, _, hinit, rfl⟩
  · obtain ⟨hjs, hI, E, hS, hE⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge j s.2.1.size with a | a
    · have hin := cinv_inner (good_step hG) hI a
      have hsim := sim_innerw hn32 hw hG hGp hGv hI a hS
      refine Or.inl ⟨_, by simp [outerBody, a], by omega, hin.1, _, hsim.1, ?_⟩
      rw [← hE, show cap - j = cap - (j + 1) + 1 by omega, clRun_succ, if_pos (hS.1 ▸ a)]
    · refine Or.inr ⟨s, by simp [outerBody, show ¬ j < s.2.1.size by omega], ⟨j, hI⟩, ?_⟩
      rw [← hE, clRun_ge _ _ _ _ _ _ (by rw [hS.1]; exact a)]
      exact hS
  · obtain ⟨-, hI, E, hS, hE⟩ := hP
    refine ⟨⟨cap, hI⟩, ?_⟩
    rw [← hE, Nat.sub_self]
    exact hS

private theorem mulClosure_simw {wd : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ wd) (hG : ∀ l < G.size, Rep n G[l]! (gg l))
    (hGp : Gp.length = G.size) (hGv : ∀ l < G.size, Gp.getD l 0 = pkw wd (gg l)) (cap : Nat) :
    mulTreeOK n G (mulClosure n G cap).1 (mulClosure n G cap).2.1 (mulClosure n G cap).2.2 = true ∧
      keysDistinct n (mulClosure n G cap).1.toList = true ∧
      SimAw wd n (mulClosure n G cap).1 (closP n wd (mask wd) (pkw wd (1 : Equiv.Perm (Fin n))) Gp cap) ∧
      ∀ i < (mulClosure n G cap).1.size, ∃ σ : Equiv.Perm (Fin n), Rep n (mulClosure n G cap).1[i]! σ := by
  have hO := sim_outerw hn32 hw hG hGp hGv cap
  rw [mulClosure_eq]
  unfold keyBfs
  generalize Id.run (forIn (List.range' 0 cap) (initSt n (idT n))
    (outerBody n (fun l y => compT n y G[l]!) G.size)) = s at hO
  obtain ⟨⟨h', a1, a2, a3, a4, a5, a6, -, a8, -⟩, hS⟩ := hO
  refine ⟨?_, ?_, hS, a5⟩
  · unfold mulTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨a1, by rw [a4]; exact CFSG.KS.ClassOne.tblEq_refl _⟩, allIn_eq_true.2 fun k hk1 hk2 => ?_⟩
    obtain ⟨t1, t2, t3⟩ := a8 k (by omega) hk2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨t1, t2⟩, ?_⟩
    have t3' : s.2.1[k]! = compT n s.2.1[s.2.2.1[k]!]! G[s.2.2.2[k]!]! := t3
    rw [← t3']
    exact CFSG.KS.ClassOne.tblEq_refl _
  · apply CFSG.KS.Tbl.keysDistinct_of_nodup
    rw [List.nodup_iff_injective_get]
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at hij
    have hi : (i : Nat) < s.2.1.size := by simpa using i.2
    have hj : (j : Nat) < s.2.1.size := by simpa using j.2
    exact Fin.ext (a6 i hi j hj (by simpa [getElem!_pos, hi, hj] using hij))

end

theorem sylowAutP_sound_w {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (a b z : Equiv.Perm (Fin n)) (ds es : List (List Int)) (cap N k : Nat)
    (h : sylowAutP n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w a) (pkw w a⁻¹) (pkw w b)
      (pkw w b⁻¹) ds es (pkw w z) (pkw w z⁻¹) cap N k = true) :
    sylowAutOK n (toTable a) (toTable b) ds es (toTable z) cap N k = true := by
  have ha := rep_toTable hn32 a
  have hb := rep_toTable hn32 b
  have hz := rep_toTable hn32 z
  have hVr := rep_tblSlp' hn32 ha hb ds
  obtain ⟨gg, hgg⟩ : ∃ gg : Nat → Equiv.Perm (Fin n),
      ∀ l, gg l = wordValue (slpVals a b ds) (es.getD l []) := ⟨_, fun _ => rfl⟩
  have hGsize : (sylowGens n (toTable a) (toTable b) ds es).size = es.length := by
    simp [sylowGens]
  have hG : ∀ l < (sylowGens n (toTable a) (toTable b) ds es).size,
      Rep n (sylowGens n (toTable a) (toTable b) ds es)[l]! (gg l) := by
    intro l hl
    rw [hGsize] at hl
    have e : (sylowGens n (toTable a) (toTable b) ds es)[l]! =
        (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 es[l]).1 := by
      simp [sylowGens, hl]
    rw [e, hgg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    exact rep_tblWord' hn32 hVr _
  have hGp : (es.map fun e => pkw w (wordValue (slpVals a b ds) e)).length =
      (sylowGens n (toTable a) (toTable b) ds es).size := by simp [hGsize]
  have hGv : ∀ l < (sylowGens n (toTable a) (toTable b) ds es).size,
      (es.map fun e => pkw w (wordValue (slpVals a b ds) e)).getD l 0 = pkw w (gg l) := by
    intro l hl
    rw [hGsize] at hl
    rw [getD_eq_getElem' (by simpa using hl), List.getElem_map, hgg, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
  have hGi : ∀ l < (sylowGens n (toTable a) (toTable b) ds es).size,
      (es.map fun e => pkw w (wordValue (slpVals a b ds) e)⁻¹).getD l 0 = pkw w (gg l)⁻¹ := by
    intro l hl
    rw [hGsize] at hl
    rw [getD_eq_getElem' (by simpa using hl), List.getElem_map, hgg, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
  obtain ⟨htree, hkeys, hsim, hgood⟩ := mulClosure_simw hn32 hw hG hGp hGv cap
  unfold sylowAutP at h
  simp only [strictB_eq, slpP_pkw hn32 hw, exprsV_pkw hn32 hw, exprsI_pkw hn32 hw, bAnd_eq, Bool.and_eq_true,
    Nat.beq_eq] at h
  obtain ⟨-, -, -, hcl1, hcl2, -, hlen, hN1, hN2, hma, hmz, hcomm⟩ := h
  simp only [sylowAutOK, Bool.and_eq_true, beq_iff_eq, and_assoc]
  set G := sylowGens n (toTable a) (toTable b) ds es with hGdef
  set C := mulClosure n G cap with hCdef
  set Gp := es.map fun e => pkw w (wordValue (slpVals a b ds) e) with hGpdef
  set E := closP n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) Gp cap with hEdef
  have hK : Nat.shiftLeft 1 k = 2 ^ k := (Nat.shiftLeft_eq 1 k).trans (one_mul _)
  have memE : ∀ σ : Equiv.Perm (Fin n), pkw w σ ∈ E → ∃ j, ∃ hj : j < C.1.size, Rep n C.1[j] σ := by
    intro σ hm
    obtain ⟨j, hj, hjE⟩ := List.getElem_of_mem hm
    have hj' : j < C.1.size := hsim.1 ▸ hj
    obtain ⟨τ, hτ⟩ := hgood j hj'
    have := hsim.2 j hj' τ hτ
    rw [getD_eq_getElem' hj, hjE] at this
    rw [getElem!_pos C.1 j hj', ← pkw_inj hw this] at hτ
    exact ⟨j, hj', hτ⟩
  have inE : ∀ i < C.1.size, ∀ σ : Equiv.Perm (Fin n), Rep n C.1[i]! σ → pkw w σ ∈ E := by
    intro i hi σ hσ
    have := hsim.2 i hi σ hσ
    rw [getD_eq_getElem' (hsim.1 ▸ hi)] at this
    rw [← this]
    exact List.getElem_mem _
  have hGpm : ∀ l < G.size, pkw w (gg l) ∈ Gp := by
    intro l hl
    rw [← hGv l hl, getD_eq_getElem' (hGp ▸ hl)]
    exact List.getElem_mem _
  have hGim : ∀ l < G.size, pkw w (gg l)⁻¹ ∈ es.map fun e => pkw w (wordValue (slpVals a b ds) e)⁻¹ := by
    intro l hl
    rw [← hGi l hl, getD_eq_getElem' (by simpa [hGsize] using hl)]
    exact List.getElem_mem _
  have hInvG : ∀ l < G.size, (G.map (invT n))[l]! = invT n G[l]! := by
    intro l hl
    rw [getElem!_pos (G.map (invT n)) l (by simpa using hl), getElem!_pos G l hl, Array.getElem_map]
  refine ⟨tblSlp_ok hn32 ha hb ds, List.all_eq_true.2 fun e _ => tblWord_flag hn32 hVr e,
    List.all_eq_true.2 fun i hi => ?_, htree, ?_, hkeys, ?_, ?_, ?_, ?_, ?_, ?_,
    CFSG.KS.Tbl.invOK_invT hn32 hz⟩
  · rw [List.mem_range] at hi
    rw [hInvG i hi]
    exact CFSG.KS.Tbl.invOK_invT hn32 (hG i hi)
  · unfold mulClosedOK
    rw [Array.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro l hl
    rw [List.mem_range] at hl
    obtain ⟨σ, hσ⟩ := hgood i hi
    have hσE := inE i hi σ hσ
    rw [getElem!_pos C.1 i hi] at hσ
    rw [Bool.and_eq_true, Array.any_eq_true, Array.any_eq_true]
    constructor
    · have := (allL_iff _ _).1 ((allL_iff _ _).1 hcl1 _ hσE) _ (hGpm l hl)
      rw [memB_iff, pkw_mul hw hn32] at this
      obtain ⟨j, hj, hjr⟩ := memE _ this
      exact ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hjr (Rep.compT hσ (hG l hl))).2 rfl⟩
    · have := (allL_iff _ _).1 ((allL_iff _ _).1 hcl2 _ hσE) _ (hGim l hl)
      rw [memB_iff, pkw_mul hw hn32] at this
      obtain ⟨j, hj, hjr⟩ := memE _ this
      refine ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hjr (Rep.compT hσ ?_)).2 rfl⟩
      rw [hInvG l hl]
      exact CFSG.KS.Tbl.invT_rep hn32 (hG l hl)
  · rw [← hsim.1, hlen, hK]
  · rw [← hK]
    exact hN1
  · rw [← hK]
    exact hN2
  · obtain ⟨j, hj, hjr⟩ := memE a ((memB_iff _ _).1 hma)
    exact Array.any_eq_true.2 ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hjr ha).2 rfl⟩
  · obtain ⟨j, hj, hjr⟩ := memE z ((memB_iff _ _).1 hmz)
    exact Array.any_eq_true.2 ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hz hjr).2 rfl⟩
  · refine Array.all_eq_true.2 fun i hi => ?_
    have hGi' : Rep n G[i] (gg i) := by
      have := hG i hi
      rwa [getElem!_pos G i hi] at this
    have := (allL_iff _ _).1 hcomm _ (hGpm i hi)
    rw [Nat.beq_eq, pkw_mul hw hn32, pkw_mul hw hn32] at this
    rw [commT, CFSG.KS.Tbl.tblEq_iff_eq (Rep.compT hz hGi') (Rep.compT hGi' hz)]
    exact pkw_inj hw this

theorem survF_sound_w {w : Nat} (hn32 : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (Q : RawSchreierDatum n)
    (a b z : Equiv.Perm (Fin n)) (ds es : List (List Int)) {r s mb : Nat} (hr : 0 < r)
    (hs : 0 < s) (hmb : 0 < mb)
    (h : ∀ g ∈ enumeration Q, survF n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w a)
      (pkw w a⁻¹) (pkw w b) (pkw w (z * b * z⁻¹)) ds es
      (exprsV n w (mask w) (pkw w (1 : Equiv.Perm (Fin n)))
        (slpP n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w a) (pkw w a⁻¹) (pkw w b)
          (pkw w b⁻¹) ds) es)
      r s mb (pkw w g) = 0) :
    survivorsOK n (toTable a) (toTable b) (toTable z) ds es r s mb (orderTables Q mb) = true := by
  have ha := rep_toTable hn32 a
  have hb := rep_toTable hn32 b
  have hz := rep_toTable hn32 z
  simp only [survivorsOK, List.all_eq_true]
  intro y hy
  obtain ⟨g, hg, hyg⟩ := exists_of_forall₂ (forall₂_orderTables hn32 Q hmb) y hy
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hg
  obtain ⟨hgQ, hgo⟩ := hg
  have hV := rep_tblSlp' hn32 ha hyg ds
  have hVb := rep_tblSlp' hn32 ha hb ds
  have hgi := pow_pred_eq_inv hgo hmb
  by_cases hp : pairTest n r s 2 mb (toTable a) y = true
  swap
  · simp [hp]
  have hcw : List.Forall₂ (Rep n) (commWord (toTable a) y 2 mb)
      (a :: g :: (List.replicate (2 - 1) a ++ List.replicate (mb - 1) g)) :=
    .cons ha (.cons hyg (forall₂_append (forall₂_replicate ha _) (forall₂_replicate hyg _)))
  have hpo := hp
  rw [pairTest, Bool.and_eq_true, ordW_iff perm_faithful (.cons ha (.cons hyg .nil)) hr,
    ordW_iff perm_faithful hcw hs] at hpo
  simp only [List.prod_cons, List.prod_nil, mul_one, Nat.reduceSub, List.replicate_one,
    List.singleton_append, List.prod_replicate, hgi] at hpo
  have hF := h g hgQ
  unfold survF at hF
  have hgi' : g ^ (Nat.sub mb 1) = g⁻¹ := hgi
  rw [powP_pkw hn32 hw, hgi'] at hF
  simp only [pkw_mul hw hn32, slpP_pkw hn32 hw, exprsV_pkw hn32 hw, nIf_eq, bAnd_eq, bIf_eq, Bool.and_eq_true,
    ordExP_pkw hn32 hw _ hmb, ordExP_pkw hn32 hw _ hr, ordExP_pkw hn32 hw _ hs, beq_pkw_iff hw] at hF
  have hall : ∀ q : Bool, q = true ∨ q = false := fun q => by cases q <;> simp
  simp only [hp, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨tblSlp_ok hn32 ha hyg ds, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hq
    exact tblWord_flag hn32 hV e
  by_cases hall2 : (((es.map (tblWord n (tblSlp n (toTable a) y ds).1)).zip
      (sylowGens n (toTable a) (toTable b) ds es).toList).all fun q => tblEq n q.1.1 q.2) = true
  swap
  · exact Or.inl (Or.inl (Bool.eq_false_iff.2 hall2))
  rw [show (sylowGens n (toTable a) (toTable b) ds es).toList =
      es.map (fun e => (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 e).1) by
    simp [sylowGens]] at hall2
  have heq : ∀ e ∈ es, wordValue (slpVals a g ds) e = wordValue (slpVals a b ds) e := by
    have := all_zip_map (tblWord n (tblSlp n (toTable a) y ds).1)
      (fun e => (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 e).1)
      (fun q p => tblEq n q.1 p) es hall2
    intro e he
    exact (CFSG.KS.Tbl.tblEq_iff_eq (rep_tblWord' hn32 hV e) (rep_tblWord' hn32 hVb e)).1
      (this e he)
  have hA := allEqP_map (fun e => pkw w (wordValue (slpVals a g ds) e))
    (fun e => pkw w (wordValue (slpVals a b ds) e)) es fun e he => by rw [heq e he]
  have hgb : g = b ∨ g = z * b * z⁻¹ := by
    by_contra hc
    push Not at hc
    simp [hgo, hpo.1, hpo.2, hA, hc.1, hc.2] at hF
  rcases hgb with rfl | rfl
  · exact Or.inl (Or.inr ((CFSG.KS.Tbl.tblEq_iff_eq hyg hb).2 rfl))
  · exact Or.inr ((CFSG.KS.Tbl.tblEq_iff_eq hyg
      (rep_conjT hz (CFSG.KS.Tbl.invT_rep hn32 hz) hb)).2 rfl)

end CFSG.KS.MSyl

end
