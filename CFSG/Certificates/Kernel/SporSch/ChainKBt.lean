module

public import Certificates.Data.Kernel.SporSch.MathieuBT
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu
open CFSG.Certificates.ChainArrays

variable {n w : Nat}

theorem walkK_succ (w m Z t fuel q c : Nat) :
    walkK w m Z t (fuel + 1) q c =
      if pg w m Z q = t then c + 1 else walkK w m Z t fuel (pg w m Z q) (c + 1) := by
  change strictN (pg w m Z q) (fun q' => nIf(Nat.beq q' t, Nat.succ c,
    walkK w m Z t fuel q' (Nat.succ c))) = _
  rw [Orb.strictN_eq, Orb.nIf_eq, beq_dec]
  simp

theorem walkK_sound {Z : Nat} {z : Equiv.Perm (Fin n)} (hZ : PRep n w Z z) (t : Fin n) :
    ∀ fuel (q : Fin n) c, walkK w (mask w) Z t fuel q c ≠ 0 →
      ∃ e, walkK w (mask w) Z t fuel q c = c + e ∧ 0 < e ∧ (z ^ e) q = t
  | 0, _, _, h => absurd rfl h
  | fuel + 1, q, c, h => by
    rw [walkK_succ, hZ q] at h ⊢
    by_cases hq : ((z q : Fin n) : Nat) = t
    · simp only [hq, ↓reduceIte]
      exact ⟨1, rfl, Nat.one_pos, by rw [pow_one]; exact Fin.ext hq⟩
    · simp only [hq, ↓reduceIte] at h ⊢
      obtain ⟨e, he, he0, hze⟩ := walkK_sound hZ t fuel (z q) (c + 1) h
      refine ⟨e + 1, by rw [he]; omega, by omega, ?_⟩
      rw [pow_succ, Equiv.Perm.mul_apply, hze]

theorem walkK_period {Z : Nat} {z : Equiv.Perm (Fin n)} (hZ : PRep n w Z z) (q : Fin n) :
    walkK w (mask w) Z q n q 0 = Function.minimalPeriod z q := by
  have hper : q ∈ Function.periodicPts z := by
    refine ⟨orderOf z, orderOf_pos z, ?_⟩
    change z^[orderOf z] q = q
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hmp := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hfix : (z ^ Function.minimalPeriod z q) q = q := by
    have := Function.isPeriodicPt_minimalPeriod z q
    rwa [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow] at this
  have hne : ∀ b, 0 < b → b < Function.minimalPeriod z q → (z ^ b) q ≠ q := by
    intro b hb hbm e
    refine Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hbm ?_
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow]
    exact e
  have key : ∀ t c, (∀ b, 0 < b → b ≤ c → (z ^ b) q ≠ q) →
      Function.minimalPeriod z q ≤ c + t →
      walkK w (mask w) Z q t ((z ^ c) q) c = Function.minimalPeriod z q := by
    intro t
    induction t with
    | zero =>
      intro c hb hle
      exact absurd hfix (hb _ hmp (by omega))
    | succ t ih =>
      intro c hb hle
      rw [walkK_succ, hZ, ← Equiv.Perm.mul_apply, ← pow_succ']
      by_cases hc : (((z ^ (c + 1)) q : Fin n) : Nat) = q
      · simp only [hc, ↓reduceIte]
        have hx : (z ^ (c + 1)) q = q := Fin.ext hc
        rcases Nat.lt_trichotomy (c + 1) (Function.minimalPeriod z q) with h | h | h
        · exact absurd hx (hne _ (by omega) h)
        · exact h
        · exact absurd hfix (hb _ hmp (by omega))
      · simp only [hc, ↓reduceIte]
        exact ih (c + 1) (fun b hb0 hbc => by
          rcases Nat.lt_or_ge b (c + 1) with h | h
          · exact hb b hb0 (by omega)
          · have : b = c + 1 := by omega
            subst this
            exact fun e => hc (congrArg Fin.val e)) (by omega)
  have := key n 0 (fun b hb hb0 => absurd hb0 (by omega))
    (by simpa using Function.minimalPeriod_le_card (f := z) (x := q))
  simpa using this

theorem minimalPeriod_conj (g x : Equiv.Perm (Fin n)) (b : Fin n) :
    Function.minimalPeriod (g * x * g⁻¹) (g b) = Function.minimalPeriod x b := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.2
  intro m
  rw [Function.IsPeriodicPt, Function.IsFixedPt, Function.IsPeriodicPt, Function.IsFixedPt,
    ← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow, conj_pow, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]
  simp [g.injective.eq_iff]

theorem fwdK_sound {X : Nat} {x : Equiv.Perm (Fin n)} (hX : PRep n w X x) {BP i : Nat}
    (hb : ∀ j ≤ i, pg w (mask w) BP j < n) (h : fwdK n w (mask w) BP X i ≠ 0) :
    ∃ j, ∃ hj : j < i, ∃ e, 0 < e ∧ fwdK n w (mask w) BP X i = 1 + j + 64 * e ∧
      (x ^ e) ⟨pg w (mask w) BP j, hb j (Nat.le_of_lt hj)⟩ = ⟨pg w (mask w) BP i, hb i le_rfl⟩ := by
  set P : Nat → Nat → Prop := fun t acc => acc = 0 ∨ ∃ j, ∃ hj : j < i, j < t ∧ ∃ e, 0 < e ∧
    acc = 1 + j + 64 * e ∧
    (x ^ e) ⟨pg w (mask w) BP j, hb j (Nat.le_of_lt hj)⟩ = ⟨pg w (mask w) BP i, hb i le_rfl⟩
  have step : ∀ t < i, ∀ acc, P t acc → P (t + 1) (nIf(Nat.beq acc (nat_lit 0),
      strictN (walkK w (mask w) X (pg w (mask w) BP i) n (pg w (mask w) BP t) (nat_lit 0)) (fun e =>
        nIf(Nat.beq e (nat_lit 0), nat_lit 0, Nat.succ (Nat.add t (Nat.mul (nat_lit 64) e)))),
        acc)) := by
    intro t ht acc hP
    rw [Orb.nIf_eq, beq_dec, Orb.strictN_eq, Orb.nIf_eq, beq_dec]
    by_cases h0 : acc = 0
    · simp only [h0, decide_true, ↓reduceIte]
      by_cases hw0 : walkK w (mask w) X (pg w (mask w) BP i) n (pg w (mask w) BP t) 0 = 0
      · simp [hw0, P]
      · simp only [hw0, decide_false, Bool.false_eq_true, ↓reduceIte]
        right
        obtain ⟨e, he, he0, hze⟩ := walkK_sound hX ⟨pg w (mask w) BP i, hb i le_rfl⟩ n
          ⟨pg w (mask w) BP t, hb t (Nat.le_of_lt ht)⟩ 0 hw0
        refine ⟨t, ht, by omega, e, he0, ?_, hze⟩
        simp only at he
        rw [he]
        simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]
        omega
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      rcases hP with h' | ⟨j, hj, hjt, e, he0, he, hze⟩
      · exact absurd h' h0
      · exact Or.inr ⟨j, hj, by omega, e, he0, he, hze⟩
  have hfold : ∀ t ≤ i, P t ((List.range t).foldl (fun acc j => nIf(Nat.beq acc (nat_lit 0),
      strictN (walkK w (mask w) X (pg w (mask w) BP i) n (pg w (mask w) BP j) (nat_lit 0)) (fun e =>
        nIf(Nat.beq e (nat_lit 0), nat_lit 0, Nat.succ (Nat.add j (Nat.mul (nat_lit 64) e)))),
        acc)) 0) := by
    intro t
    induction t with
    | zero => intro _; exact Or.inl rfl
    | succ t ih =>
      intro ht
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact step t ht _ (ih (by omega))
  have e : fwdK n w (mask w) BP X i = (List.range i).foldl (fun acc j =>
      nIf(Nat.beq acc (nat_lit 0),
      strictN (walkK w (mask w) X (pg w (mask w) BP i) n (pg w (mask w) BP j) (nat_lit 0)) (fun e =>
        nIf(Nat.beq e (nat_lit 0), nat_lit 0, Nat.succ (Nat.add j (Nat.mul (nat_lit 64) e)))),
        acc)) 0 := by
    unfold fwdK
    rw [foldUp_eq]
  rcases hfold i le_rfl with h' | h'
  · rw [← e] at h'
    exact absurd h' h
  · rw [← e] at h'
    obtain ⟨j, hj, -, e', he0, he, hze⟩ := h'
    exact ⟨j, hj, e', he0, he, hze⟩

theorem sum_single (f : Nat → Nat) (t0 : Nat) : ∀ c, (∀ t < c, t ≠ t0 → f t = 0) →
    ((List.range c).map f).sum = if t0 < c then f t0 else 0
  | 0, _ => by simp
  | c + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_single f t0 c
      (fun t ht => h t (by omega))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hc : t0 = c
    · subst hc
      simp
    · rw [h c (by omega) (Ne.symm hc)]
      by_cases h1 : t0 < c
      · simp [h1, show t0 < c + 1 by omega]
      · simp [h1, show ¬ t0 < c + 1 by omega]

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

omit hn hbs in
theorem bv_val {i : Nat} (hi : i < k) : ((bv.get ⟨i, hi⟩ : Fin n) : Nat) = pg w (mask w) BP i := by
  have e := List.getElem_of_eq hQ.2.2.2.2.1 (i := i) (by simp [hi])
  simpa [Vector.get] using e

theorem tr_mem {i t : Nat} (hi : i < k) (ht : t < rcnt (LR i)) :
    trP n w LR TR i t ∈ (certificate hn gens words bv hbs).levelSubgroup i := by
  have hmem : trP n w LR TR i t ∈ levelTransversals (certificate hn gens words bv hbs) ⟨i, hi⟩ := by
    rw [levelTransversals_eq hQ hn hbs hi]
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩
  exact mem_levelSubgroup_of_mem_levelTransversals _ ⟨i, hi⟩ hmem

theorem tr_base {i t : Nat} (hi : i < k) (ht : t < rcnt (LR i)) :
    ((trP n w LR TR i t (bv.get ⟨i, hi⟩) : Fin n) : Nat) = rpt w (mask w) (LR i) t := by
  obtain ⟨hA, hraw⟩ := chainK_arrays hn hbs hQ
  have hF := chainCheckFacts hraw
  have hAg := (chainK_agree hQ hi).1
  have hk : t < (lev n (strongArr n w kS PS) (baseArr w k BP) i).pts.size := hAg.cnt ▸ ht
  have ht' := hA.transversal_of_lt hF hi hk
  have hx : levPts (certificate hn gens words bv hbs) (strongArr n w kS PS) (baseArr w k BP) i t ∈
      (certificate hn gens words bv hbs).orbitPoints ⟨i, hi⟩ := by
    change ((CFSG.Certificates.RawSchreierDatum.orbitSearch _ ⟨i, hi⟩).transversal? _).isSome = true
    rw [ht']
    rfl
  have hs := ((certificate hn gens words bv hbs).transversal_getD_spec ⟨i, hi⟩ _ hx).2.2
  change ((CFSG.Certificates.RawSchreierDatum.orbitSearch _ ⟨i, hi⟩).transversal? _).getD 1 _ = _
    at hs
  rw [ht', Option.getD_some] at hs
  have heq := (hA.rep_levT hF hi hk).unique (hAg.tr t hk).1
  rw [heq] at hs
  have hb : (certificate hn gens words bv hbs).base.get ⟨i, hi⟩ = bv.get ⟨i, hi⟩ := rfl
  rw [hb] at hs
  rw [hs, hA.levPts_val hF hi hk, hAg.pt t hk]

theorem rpos_rpt {i t : Nat} (hi : i < k) (ht : t < rcnt (LR i)) :
    rpos w (mask w) (n * w) (LR i) (rpt w (mask w) (LR i) t) = t := by
  obtain ⟨hA, hraw⟩ := chainK_arrays hn hbs hQ
  have hF := chainCheckFacts hraw
  have hAg := (chainK_agree hQ hi).1
  have hk : t < (lev n (strongArr n w kS PS) (baseArr w k BP) i).pts.size := hAg.cnt ▸ ht
  have hLF := hA.levelFacts hF hi
  rw [hAg.pt t hk]
  have hz := hLF.pts_lt t hk
  rw [hAg.posE _ hz (by rw [hLF.pos_pts t hk]; exact hk), hLF.pos_pts t hk]

theorem products_mem {i d : Nat} (hid : i + d ≤ k) :
    ∀ g ∈ products ((List.range d).map fun t => trL n w LR TR (i + t)),
      g ∈ (certificate hn gens words bv hbs).levelSubgroup i := by
  refine mem_of_mem_products ((certificate hn gens words bv hbs).levelSubgroup i).toSubmonoid _ ?_
  intro T hT t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hT
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  have hs' := List.mem_range.1 hs
  exact (certificate hn gens words bv hbs).levelSubgroup_antitone i (i + s) (by omega)
    (tr_mem hQ hn hbs (by omega) (List.mem_range.1 ht'))

omit hQ in
theorem fixes_base {i j : Nat} {g : Equiv.Perm (Fin n)}
    (hg : g ∈ (certificate hn gens words bv hbs).levelSubgroup i) (hj : j < i) (hjk : j < k) :
    g (bv.get ⟨j, hjk⟩) = bv.get ⟨j, hjk⟩ :=
  (certificate hn gens words bv hbs).levelSubgroup_fixes_base_index i g hg ⟨j, hjk⟩ hj

end Chain

theorem itF_pow {Y : Nat} {y : Equiv.Perm (Fin n)} (pY : PRep n w Y y) :
    ∀ (e : Nat) (q : Fin n), itF (fun p => pg w (mask w) Y p) e q = ((y ^ e) q : Nat)
  | 0, _ => rfl
  | e + 1, q => by
    change strictN (itF (fun p => pg w (mask w) Y p) e q) (fun p => pg w (mask w) Y p) = _
    rw [Orb.strictN_eq, itF_pow pY e q, pow_succ', Equiv.Perm.mul_apply, ← pY]

section Bt

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem btGo_spec (hk64 : k ≤ 64) {X Y : Nat} {x y : Equiv.Perm (Fin n)} (pX : PRep n w X x)
    (pY : PRep n w Y y) :
    ∀ d i, i + d = k → ∀ (Hp Hip : Nat) (H : Equiv.Perm (Fin n)) (s : Nat), PRep n w Hp H →
      PRep n w Hip H⁻¹ →
      btGo n w (mask w) (n * w) BP LR TR TRI X Y d i Hp Hip s =
        s + ((products ((List.range d).map fun t => trL n w LR TR (i + t))).map (H * ·)).countP
          (fun g => decide (g * x = y * g))
  | 0, i, _, Hp, Hip, H, s, pH, _ => by
    have h32 := chainK_h32 hQ
    have hw := PF.w_pos hQ.2.1
    change nIf(Nat.beq (pcomp n w (mask w) Hp X) (pcomp n w (mask w) Y Hp), Nat.succ s, s) = _
    rw [Orb.nIf_eq, beq_pcomp_iff h32 hw pH pX pY pH]
    simp only [List.range_zero, List.map_nil, products, List.map_cons, mul_one,
      List.countP_singleton]
    split <;> simp_all
  | d + 1, i, hid, Hp, Hip, H, s, pH, pHi => by
    have h32 := chainK_h32 hQ
    have hi : i < k := by omega
    have hAg := chainK_agree hQ hi
    set R := LR i
    set c := rcnt R
    set o := roff n (n * w) R
    set Q := certificate hn gens words bv hbs
    set bI := bv.get ⟨i, hi⟩
    set rest := products ((List.range d).map fun t => trL n w LR TR (i + 1 + t))
    set cnt : Nat → Nat := fun t => (rest.map ((H * trP n w LR TR i t) * ·)).countP
      (fun g => decide (g * x = y * g))
    have ih : ∀ t < c, ∀ s', btGo n w (mask w) (n * w) BP LR TR TRI X Y d (i + 1)
        (pcomp n w (mask w) Hp (TR (o + t))) (pcomp n w (mask w) (TRI (o + t)) Hip) s' =
          s' + cnt t := by
      intro t ht s'
      have p1 := prep_pcomp h32 pH (hAg.2 t ht).1
      have p2 := prep_pcomp h32 (hAg.2 t ht).2 pHi
      rw [← mul_inv_rev] at p2
      exact btGo_spec hk64 pX pY d (i + 1) (by omega) _ _ _ s' p1 p2
    have hsol : ∀ t < c, cnt t ≠ 0 → ∃ x' ∈ rest,
        (H * trP n w LR TR i t * x') * x = y * (H * trP n w LR TR i t * x') := by
      intro t _ h
      obtain ⟨g, hg, hgP⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero h)
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hg
      exact ⟨x', hx', by simpa using hgP⟩
    have hrest : ∀ x' ∈ rest, x' ∈ Q.levelSubgroup (i + 1) :=
      products_mem hQ hn hbs (i := i + 1) (d := d) (by omega)
    have hbv : ((bI : Fin n) : Nat) = pg w (mask w) BP i := bv_val hQ hi
    have e : btGo n w (mask w) (n * w) BP LR TR TRI X Y (d + 1) i Hp Hip s =
        strictN (LR i) (fun R => strictN (pg w (mask w) BP i) (fun b =>
        strictN (roff n (n * w) R) (fun o => strictN (fwdK n w (mask w) BP X i) (fun fc =>
        nIf(Nat.beq fc (nat_lit 0),
          strictN (walkK w (mask w) X b n b (nat_lit 0)) (fun lb =>
            foldUp (rcnt R) (fun t s => strictN (pg w (mask w) Hp (rpt w (mask w) R t)) (fun q =>
              nIf(Nat.beq (walkK w (mask w) Y q n q (nat_lit 0)) lb,
                btGo n w (mask w) (n * w) BP LR TR TRI X Y d (Nat.succ i)
                  (pcomp n w (mask w) Hp (TR (Nat.add o t)))
                  (pcomp n w (mask w) (TRI (Nat.add o t)) Hip) s, s))) s),
          strictN (Nat.pred fc) (fun c =>
            strictN (rpos w (mask w) (n * w) R (pg w (mask w) Hip (itF (fun p => pg w (mask w) Y p)
              (Nat.div c (nat_lit 64)) (pg w (mask w) Hp (pg w (mask w) BP
                (Nat.mod c (nat_lit 64))))))) (fun t =>
            nIf(Nat.blt t (rcnt R),
              btGo n w (mask w) (n * w) BP LR TR TRI X Y d (Nat.succ i)
                (pcomp n w (mask w) Hp (TR (Nat.add o t)))
                (pcomp n w (mask w) (TRI (Nat.add o t)) Hip) s, s)))))))) := rfl
    rw [e]
    simp only [Orb.strictN_eq]
    rw [range_map_succ, countP_products_cons, trL, List.map_map]
    change _ = s + ((List.range c).map cnt).sum
    rw [Orb.nIf_eq, beq_dec]
    by_cases hfc : fwdK n w (mask w) BP X i = 0
    ·
      simp only [hfc, decide_true, ↓reduceIte]
      rw [foldUp_eq]
      refine (foldl_eq_add (X := fun t => if walkK w (mask w) Y (pg w (mask w) Hp
        (rpt w (mask w) (LR i) t)) n (pg w (mask w) Hp (rpt w (mask w) (LR i) t)) 0 =
          walkK w (mask w) X (pg w (mask w) BP i) n (pg w (mask w) BP i) 0 then cnt t else 0)
        _ (fun t ht s' => ?_) s).trans ?_
      · rw [Orb.nIf_eq, beq_dec]
        by_cases h : walkK w (mask w) Y (pg w (mask w) Hp (rpt w (mask w) (LR i) t)) n
            (pg w (mask w) Hp (rpt w (mask w) (LR i) t)) 0 =
          walkK w (mask w) X (pg w (mask w) BP i) n (pg w (mask w) BP i) 0
        · simp only [h, decide_true, ↓reduceIte]
          exact ih t (List.mem_range.1 ht) s'
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      · congr 2
        apply List.map_congr_left
        intro t ht
        have ht' := List.mem_range.1 ht
        split
        · rfl
        · rename_i hc
          by_contra hne
          apply hc
          obtain ⟨x', hx', hgx⟩ := hsol t ht' (Ne.symm hne)
          set T := trP n w LR TR i t
          set g := H * T * x'
          have hy : y = g * x * g⁻¹ := by rw [hgx]; group
          have hx'b : x' bI = bI := fixes_base hn hbs (hrest x' hx') (Nat.lt_succ_self i) hi
          have hgb : g bI = H (T bI) := by
            simp only [g, Equiv.Perm.mul_apply, hx'b]
          have hq : pg w (mask w) Hp (rpt w (mask w) R t) = ((H (T bI) : Fin n) : Nat) := by
            rw [← tr_base hQ hn hbs hi ht', pH]
          rw [hq, ← hbv, walkK_period pY, walkK_period pX, ← hgb, hy, minimalPeriod_conj]
    ·
      simp only [hfc, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hb : ∀ j ≤ i, pg w (mask w) BP j < n := fun j hj => by
        rw [← bv_val hQ (by omega : j < k)]
        exact (bv.get ⟨j, _⟩).2
      obtain ⟨j, hj, e', he0, hcode, hze⟩ := fwdK_sound pX hb hfc
      have hjk : j < k := by omega
      have hd : Nat.div (Nat.pred (fwdK n w (mask w) BP X i)) 64 = e' := by
        rw [hcode]
        change (1 + j + 64 * e' - 1) / 64 = e'
        omega
      have hm : Nat.mod (Nat.pred (fwdK n w (mask w) BP X i)) 64 = j := by
        rw [hcode]
        change (1 + j + 64 * e' - 1) % 64 = j
        omega
      rw [hd, hm]
      set bJ := bv.get ⟨j, hjk⟩
      have hbJ : ((bJ : Fin n) : Nat) = pg w (mask w) BP j := bv_val hQ hjk
      have hz : pg w (mask w) Hip (itF (fun p => pg w (mask w) Y p) e'
          (pg w (mask w) Hp (pg w (mask w) BP j))) = ((H⁻¹ ((y ^ e') (H bJ)) : Fin n) : Nat) := by
        rw [← hbJ, pH bJ, itF_pow pY e' (H bJ), pHi]
      rw [hz]
      set t0 := rpos w (mask w) (n * w) R ((H⁻¹ ((y ^ e') (H bJ)) : Fin n) : Nat)
      have huniq : ∀ t < c, t ≠ t0 → cnt t = 0 := by
        intro t ht hne
        by_contra hc
        obtain ⟨x', hx', hgx⟩ := hsol t ht hc
        apply hne
        set T := trP n w LR TR i t
        set g := H * T * x'
        have hx'I : x' bI = bI := fixes_base hn hbs (hrest x' hx') (Nat.lt_succ_self i) hi
        have hx'J : x' bJ = bJ := fixes_base hn hbs (hrest x' hx') (by omega) hjk
        have hTJ : T bJ = bJ := fixes_base hn hbs (tr_mem hQ hn hbs hi ht) hj hjk
        have hxe : (x ^ e') bJ = bI := by
          have eJ : bJ = ⟨pg w (mask w) BP j, hb j (Nat.le_of_lt hj)⟩ := Fin.ext hbJ
          have eI : bI = ⟨pg w (mask w) BP i, hb i le_rfl⟩ := Fin.ext hbv
          rw [eJ, eI]
          exact hze
        have hsemi : g * x ^ e' = y ^ e' * g := (SemiconjBy.pow_right hgx e').eq
        have h1 : g bI = H (T bI) := by simp only [g, Equiv.Perm.mul_apply, hx'I]
        have h2 : g bI = (y ^ e') (H bJ) := by
          rw [← hxe, ← Equiv.Perm.mul_apply, hsemi, Equiv.Perm.mul_apply]
          simp only [g, Equiv.Perm.mul_apply, hx'J, hTJ]
        have hTb : T bI = H⁻¹ ((y ^ e') (H bJ)) := by
          rw [← h2, h1]
          simp
        rw [← rpos_rpt hQ hn hbs hi ht, ← tr_base hQ hn hbs hi ht]
        change _ = rpos w (mask w) (n * w) R ((H⁻¹ ((y ^ e') (H bJ)) : Fin n) : Nat)
        rw [← hTb]
      rw [sum_single cnt t0 c huniq, Orb.nIf_eq]
      by_cases ht0 : t0 < c
      · have hb0 : Nat.blt t0 (rcnt (LR i)) = true := Nat.blt_eq.mpr ht0
        simp only [hb0, ht0, ↓reduceIte]
        exact ih t0 ht0 s
      · have hb0 : Nat.blt t0 (rcnt (LR i)) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact ht0 (Nat.blt_eq.mp h)
        simp only [hb0, ht0, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem btK_eq (hk64 : k ≤ 64) {X Y : Nat} {x y : Equiv.Perm (Fin n)} (pX : PRep n w X x)
    (pY : PRep n w Y y) :
    btK n w (mask w) (n * w) BP k LR TR TRI X Y =
      (enumeration (certificate hn gens words bv hbs)).countP
        (fun g => decide (g * x = y * g)) := by
  have pid := prep_pidn (chainK_n24 hQ) hQ.2.1
  have pidi : PRep n w (pidn n w) (1 : Equiv.Perm (Fin n))⁻¹ := by rw [inv_one]; exact pid
  unfold btK
  rw [btGo_spec hQ hn hbs hk64 pX pY k 0 (Nat.zero_add k) _ _ 1 0 pid pidi, Nat.zero_add,
    enumeration_trL hQ hn hbs]
  simp only [Nat.zero_add, one_mul, List.map_id']

end Bt

end CFSG.KS.SporSch.MOC

end
