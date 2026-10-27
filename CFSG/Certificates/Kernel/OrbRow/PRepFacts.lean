module

public import CFSG.Certificates.Kernel.OrbRow.CentSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw.Orb CFSG.KS.PF

variable {n w : ℕ}

theorem prep_unique {P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g) (hh : PRep n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_inv {P Q : ℕ} {g : Equiv.Perm (Fin n)}
    (h : permOK n w (mask w) (n * w) P Q = true) (hP : PRep n w P g) : PRep n w Q g⁻¹ := by
  obtain ⟨-, -, h3⟩ := permOK_facts h
  intro x
  have := (h3 (g⁻¹ x) (g⁻¹ x).2).2
  have e : pg w (mask w) P (g⁻¹ x) = x := by
    rw [hP (g⁻¹ x)]
    exact congrArg Fin.val (g.apply_symm_apply x)
  rw [e] at this
  exact this

theorem eq_of_prep {P Q : ℕ} {g : Equiv.Perm (Fin n)} (hw : 0 < w) (hP : PRep n w P g)
    (hQ : PRep n w Q g) (hp : P >>> (n * w) = 0) (hq : Q >>> (n * w) = 0) : P = Q :=
  eq_of_fields hw hp hq fun i hi => by
    have e1 : pg w (mask w) P i = g ⟨i, hi⟩ := hP ⟨i, hi⟩
    have e2 : pg w (mask w) Q i = g ⟨i, hi⟩ := hQ ⟨i, hi⟩
    rw [e1, e2]

theorem testBit_iff_fld {lv j : ℕ} :
    Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true ↔ lv.testBit j = true := by
  have e : Nat.land (Nat.shiftRight lv j) (nat_lit 1) = lv / 2 ^ j % 2 := by
    change (lv >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; rfl⟩

theorem lvOk_of_letter {k lv j : ℕ} (h : j < k ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true) :
    lvOk k lv j :=
  lvOk_iff.2 ⟨h.1, testBit_iff_fld.1 h.2⟩

theorem commOK_iff {zp yp : ℕ} {z y : Equiv.Perm (Fin n)} (hz : PRep n w zp z)
    (hy : PRep n w yp y) : commOK n w (mask w) zp yp = true ↔ z * y = y * z := by
  unfold commOK eq22
  rw [allN_iff]
  constructor
  · intro h
    ext x
    have h1 := Nat.eq_of_beq_eq_true (h x x.2)
    rw [hy x, hz (y x), hz x, hy (z x)] at h1
    simpa [Equiv.Perm.mul_apply] using h1
  · intro h i hi
    have h1 := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨i, hi⟩ : Fin n) : ℕ)) h
    simp only [Equiv.Perm.mul_apply] at h1
    have ey : pg w (mask w) yp i = y ⟨i, hi⟩ := hy ⟨i, hi⟩
    have ez : pg w (mask w) zp i = z ⟨i, hi⟩ := hz ⟨i, hi⟩
    rw [ey, ez, hz (y ⟨i, hi⟩), hy (z ⟨i, hi⟩), h1]
    exact Nat.beq_refl _

theorem iterate_prep {P : ℕ} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) :
    ∀ (e : ℕ) (x : Fin n), (pg w (mask w) P)^[e] x = ((g ^ e) x : ℕ)
  | 0, x => by simp
  | e + 1, x => by
    rw [Function.iterate_succ_apply', iterate_prep hP e x, hP, pow_succ', Equiv.Perm.mul_apply]

theorem pow_eq_one_of_powIdK {P e : ℕ} {g : Equiv.Perm (Fin n)}
    (h : powIdK n w (mask w) P e = true) (hP : PRep n w P g) : g ^ e = 1 := by
  ext x
  have h1 := powIdK_sound h x.2
  rw [iterate_prep hP] at h1
  exact h1

theorem ne_one_of_movesK {P : ℕ} {g : Equiv.Perm (Fin n)} (h : movesK n w (mask w) P = true)
    (hP : PRep n w P g) : g ≠ 1 := by
  obtain ⟨i, hi, hne⟩ := movesK_sound h
  intro h1
  apply hne
  have e : pg w (mask w) P i = g ⟨i, hi⟩ := hP ⟨i, hi⟩
  rw [e, h1]
  rfl

@[expose] noncomputable def keyR (w : ℕ) (f : ℕ → ℕ) (nf : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun t ih => Nat.lor ih (Nat.shiftLeft (f t) (Nat.mul w t))) nf

theorem keyR_congr {f f' : ℕ → ℕ} : ∀ {nf : ℕ}, (∀ t < nf, f t = f' t) →
    keyR w f nf = keyR w f' nf
  | 0, _ => rfl
  | nf + 1, h => by
    change Nat.lor (keyR w f nf) (Nat.shiftLeft (f nf) (Nat.mul w nf)) =
      Nat.lor (keyR w f' nf) (Nat.shiftLeft (f' nf) (Nat.mul w nf))
    rw [keyR_congr (fun t ht => h t (by omega)), h nf (by omega)]

theorem fld_keyR {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ w) :
    ∀ nf, Fld w (keyR w f nf) (fun i => if i < nf then f i else 0)
  | 0 => fld_congr (fld_zero w) (fun i => by simp)
  | nf + 1 => by
    change Fld w (keyR w f nf ||| f nf <<< (w * nf)) _
    refine fld_congr (fld_or (fld_keyR hf nf) (fld_shl nf (fld_one (hf nf)))) fun i => ?_
    rcases Nat.lt_trichotomy i nf with h | h | h
    · have h1 : ¬ nf ≤ i := by omega
      have h2 : i < nf + 1 := by omega
      simp only [h, h1, h2, ↓reduceIte, Nat.or_zero]
    · subst h
      simp
    · have h1 : ¬ i < nf := by omega
      have h2 : ¬ i < nf + 1 := by omega
      have h3 : i - nf ≠ 0 := by omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.zero_or, le_of_lt h]

theorem pg_keyR {f : ℕ → ℕ} (hf : ∀ t, f t < 2 ^ w) {nf t : ℕ} (ht : t < nf) :
    pg w (mask w) (keyR w f nf) t = f t := by
  have h := pg_of_fld (i := t) (fld_keyR hf nf) (by simp only [ht, ↓reduceIte]; exact hf t)
  simp only [ht, ↓reduceIte] at h
  exact h

@[expose] def tf {k : ℕ} (u : Fin k → Fin n) (t : ℕ) : ℕ := if h : t < k then u ⟨t, h⟩ else 0

@[expose] noncomputable def tkey (w : ℕ) {k : ℕ} (u : Fin k → Fin n) : ℕ := keyR w (tf u) k

theorem tf_lt (hw : n + 1 < 2 ^ w) {k : ℕ} (u : Fin k → Fin n) (t : ℕ) : tf u t < 2 ^ w := by
  unfold tf
  split
  · rename_i h
    have := (u ⟨t, h⟩).2
    omega
  · omega

theorem pg_tkey (hw : n + 1 < 2 ^ w) {k : ℕ} (u : Fin k → Fin n) (i : Fin k) :
    pg w (mask w) (tkey w u) i = u i := by
  rw [tkey, pg_keyR (tf_lt hw u) i.2, tf, dif_pos i.2]

theorem tkey_inj (hw : n + 1 < 2 ^ w) {k : ℕ} {u u' : Fin k → Fin n}
    (h : tkey w u = tkey w u') : u = u' := by
  funext i
  apply Fin.ext
  rw [← pg_tkey hw u i, ← pg_tkey hw u' i, h]

theorem subKey_tkey {k : ℕ} {B : List ℕ} {off : ℕ} {v : Fin k → Fin n}
    (hv : ∀ i : Fin k, getS B (off + i) = v i) : subKey w B off k = tkey w v := by
  change keyR w (fun t => getS B (Nat.add off t)) k = keyR w (tf v) k
  refine keyR_congr fun t ht => ?_
  rw [tf, dif_pos ht]
  exact hv ⟨t, ht⟩

theorem mapKey_tkey (hw : n + 1 < 2 ^ w) {k gp : ℕ} {g : Equiv.Perm (Fin n)}
    (hg : PRep n w gp g) (u : Fin k → Fin n) :
    mapKey w (mask w) gp k (tkey w u) = tkey w (fun i => g (u i)) := by
  change keyR w (fun t => pg w (mask w) gp (pg w (mask w) (tkey w u) t)) k = keyR w (tf _) k
  refine keyR_congr fun t ht => ?_
  rw [pg_tkey hw u ⟨t, ht⟩, tf, dif_pos ht]
  exact hg (u ⟨t, ht⟩)

theorem conjKey_tkey {k yp yip gp : ℕ} {y g : Equiv.Perm (Fin n)} (hy : PRep n w yp y)
    (hyi : PRep n w yip y⁻¹) (hg : PRep n w gp g) {B : List ℕ} {off : ℕ} {v : Fin k → Fin n}
    (hv : ∀ i : Fin k, getS B (off + i) = v i) :
    conjKey w (mask w) yp yip gp B off k = tkey w (fun i => (y * g * y⁻¹) (v i)) := by
  change keyR w (fun t => pg w (mask w) yp (pg w (mask w) gp (pg w (mask w) yip
    (getS B (Nat.add off t))))) k = keyR w (tf _) k
  refine keyR_congr fun t ht => ?_
  have e : getS B (Nat.add off t) = v ⟨t, ht⟩ := hv ⟨t, ht⟩
  rw [e, hyi, hg, hy, tf, dif_pos ht]
  rfl

@[expose] noncomputable def decP (n w p : ℕ) (i : Fin n) : Fin n :=
  if h : pg w (mask w) p i < n then ⟨_, h⟩ else i

theorem decP_of_prep {p : ℕ} {g : Equiv.Perm (Fin n)} (hp : PRep n w p g) : decP n w p = ⇑g := by
  funext i
  unfold decP
  rw [dif_pos (by rw [hp i]; exact (g i).2)]
  exact Fin.ext (hp i)

end CFSG.KC.OrbRow

end
