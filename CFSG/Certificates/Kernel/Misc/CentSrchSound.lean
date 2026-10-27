module

public import Certificates.Data.Kernel.Misc.CentSrch
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.NativeSchreierEnum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.KC.CentSrch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates

theorem cs_recAnd (f : ℕ → Bool) : ∀ N, Nat.rec (motive := fun _ => Bool) true
    (fun r ih => f r && ih) N = true ↔ ∀ r < N, f r = true
  | 0 => ⟨fun _ r hr => absurd hr (Nat.not_lt_zero r), fun _ => rfl⟩
  | N + 1 => by
    change (f N && Nat.rec (motive := fun _ => Bool) true (fun r ih => f r && ih) N) = true ↔ _
    rw [Bool.and_eq_true, cs_recAnd f N]
    constructor
    · rintro ⟨h1, h2⟩ r hr
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | rfl
      · exact h2 r h
      · exact h1
    · intro h
      exact ⟨h N (Nat.lt_succ_self N), fun r hr => h r (Nat.lt_succ_of_lt hr)⟩

theorem cs_foldr_sum (F : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (hF : ∀ k s, F k s = s + g k) :
    ∀ c a, (List.range c).foldr F a = a + ∑ k ∈ Finset.range c, g k
  | 0, a => by simp
  | c + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, cs_foldr_sum F g hF c,
      Finset.sum_range_succ, hF]
    omega

theorem cs_mod_ext {u v t : ℕ} (h : ∀ q < t, u.testBit q = v.testBit q) : u % 2 ^ t = v % 2 ^ t :=
  Nat.eq_of_testBit_eq fun q => by
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hq : q < t
    · rw [h q hq]
    · simp [hq]

theorem cs_lane {t s x v : ℕ} (hx : x < 2 ^ (t * s)) (hv : v < 2 ^ t) :
    Nat.lor x (Nat.shiftLeft v (t * s)) < 2 ^ (t * (s + 1)) ∧
    (∀ l < s, Nat.lor x (Nat.shiftLeft v (t * s)) / 2 ^ (t * l) % 2 ^ t =
      x / 2 ^ (t * l) % 2 ^ t) ∧
    Nat.lor x (Nat.shiftLeft v (t * s)) / 2 ^ (t * s) % 2 ^ t = v := by
  have e : Nat.lor x (Nat.shiftLeft v (t * s)) = v * 2 ^ (t * s) + x := by
    change x ||| v <<< (t * s) = _
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  rw [e]
  refine ⟨?_, fun l hl => ?_, ?_⟩
  · calc v * 2 ^ (t * s) + x < v * 2 ^ (t * s) + 2 ^ (t * s) := by omega
      _ = (v + 1) * 2 ^ (t * s) := by ring
      _ ≤ 2 ^ t * 2 ^ (t * s) := Nat.mul_le_mul_right _ hv
      _ = 2 ^ (t * (s + 1)) := by rw [← pow_add]; ring_nf
  · apply cs_mod_ext
    intro q hq
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, ← Nat.shiftLeft_eq,
      Nat.shiftLeft_add_eq_or_of_lt hx v, Nat.testBit_or, Nat.testBit_shiftLeft]
    have : ¬ (q + t * l ≥ t * s) := by
      have : t * (l + 1) ≤ t * s := Nat.mul_le_mul_left _ hl
      rw [Nat.mul_succ] at this
      omega
    simp [this]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx,
      Nat.zero_add, Nat.mod_eq_of_lt hv]

theorem cs_wAt (Wd l : ℕ) : wAt Wd l = Wd / 2 ^ (16 * l) % 2 ^ 16 :=
  Orb.fld_eq Wd (16 * l) 16

theorem cs_dAt {n w DP j p : ℕ} (hp : p < n) :
    dAt n w (mask w) DP j p = pg w (mask w)
      (Nat.land (Nat.shiftRight DP (Nat.mul (Nat.mul n w) j)) (mask (Nat.mul n w))) p := by
  unfold dAt
  rw [Orb.pg_eq, Orb.pg_eq, Orb.fld_eq]
  apply cs_mod_ext
  intro q hq
  simp only [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.add_eq, Nat.mul_eq]
  have h1 : q + w * p < n * w := by
    have : w * (p + 1) ≤ w * n := Nat.mul_le_mul_left _ hp
    rw [Nat.mul_succ] at this
    rw [Nat.mul_comm n w]
    omega
  simp only [h1, decide_true, Bool.true_and]
  congr 1
  ring

theorem cs_prep_ppow {n w P : ℕ} {g : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hP : Orb.PRep n w P g) :
    ∀ e, Orb.PRep n w (ppow n w (mask w) (pidn n w) P e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact Orb.prep_pidn hn hw
  | e + 1 => by
    have h : ppow n w (mask w) (pidn n w) P (e + 1) =
        pcomp n w (mask w) P (ppow n w (mask w) (pidn n w) P e) := Orb.strictN_eq _ _
    rw [h, pow_succ']
    exact Orb.prep_pcomp (by omega) hP (cs_prep_ppow hn hw hP e)

theorem cs_fwdW_succ (w m : ℕ) (TR : ℕ → ℕ) (Wd i p : ℕ) :
    fwdW w m TR Wd (i + 1) p = fwdW w m TR Wd i (pg w m (TR (wAt Wd i)) p) :=
  Orb.strictN_eq _ _

theorem cs_invW_succ (w m : ℕ) (TRI : ℕ → ℕ) (Wd i a : ℕ) :
    invW w m TRI Wd (i + 1) a = pg w m (TRI (wAt Wd i)) (invW w m TRI Wd i a) :=
  Orb.strictN_eq _ _

theorem cs_fwdW_congr (w m : ℕ) (TR : ℕ → ℕ) {Wd Wd' : ℕ} :
    ∀ i, (∀ l < i, wAt Wd l = wAt Wd' l) → ∀ p, fwdW w m TR Wd i p = fwdW w m TR Wd' i p
  | 0, _, _ => rfl
  | i + 1, h, p => by
    rw [cs_fwdW_succ, cs_fwdW_succ, h i (Nat.lt_succ_self i),
      cs_fwdW_congr w m TR i (fun l hl => h l (Nat.lt_succ_of_lt hl))]

theorem cs_invW_congr (w m : ℕ) (TRI : ℕ → ℕ) {Wd Wd' : ℕ} :
    ∀ i, (∀ l < i, wAt Wd l = wAt Wd' l) → ∀ a, invW w m TRI Wd i a = invW w m TRI Wd' i a
  | 0, _, _ => rfl
  | i + 1, h, a => by
    rw [cs_invW_succ, cs_invW_succ, h i (Nat.lt_succ_self i),
      cs_invW_congr w m TRI i (fun l hl => h l (Nat.lt_succ_of_lt hl))]

theorem cs_land7 (z : ℕ) : Nat.land z 7 < 8 := by
  have e : Nat.land z 7 = z % 2 ^ 3 := Nat.and_two_pow_sub_one_eq_mod z 3
  rw [e]
  exact Nat.mod_lt _ (by norm_num)

theorem cs_cases (m : ℕ) : m = 0 ∨ m = 0 + 1 ∨ ∃ e, m = e + 1 + 1 := by
  rcases m with _ | _ | e
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨e, rfl⟩)

open CFSG.Certificates.ChainArrays in
theorem srch_sound {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb)
    (hro : ∀ i < nb, roff n (n * w) (LR i) + rcnt (LR i) ≤ 65536)
    {X Y DP : ℕ} {x y : Equiv.Perm (Fin n)} (hx : Orb.PRep n w X x) (hy : Orb.PRep n w Y y)
    (hxQ : x ∈ Q.originalSubgroup) (hyQ : y ∈ Q.originalSubgroup)
    {pl : List ℕ} (hpl : planOK n w nb BP DP pl 0 = true) (hd : dOK n w X Y DP = true) :
    Nat.card ↥(Q.originalSubgroup ⊓ Subgroup.centralizer ({x, y} : Set (Equiv.Perm (Fin n)))) =
      srch n w nb LR TR TRI BP DP [X, Y] pl 0 0 0 := by
  classical
  subst hnb
  have hn65 : n < 65536 := hb.2.2.1
  have hn : n < 2 ^ 32 := by omega
  have hn24 : n < 16777216 := by omega
  have hw2 : n + 1 < 2 ^ w := hb.2.1
  have hbl := Orb.base_lt_of_levels hb hl
  have hbv : ∀ t (ht : t < Q.baseCount),
      ((Q.base.get ⟨t, ht⟩ : Fin n) : ℕ) = pg w (mask w) BP t :=
    fun t ht => (hA.base_val ⟨t, ht⟩).trans (hb.2.2.2.2.2.2 t ht)
  have hlev : ∀ i (hi : i < Q.baseCount),
      rcnt (LR i) = (lev n S base i).pts.size ∧
      (∀ k < rcnt (LR i), rpt w (mask w) (LR i) k = (lev n S base i).pts[k]!) ∧
      (∀ z < n, rpos w (mask w) (Nat.mul n w) (LR i) z < rcnt (LR i) →
        (lev n S base i).pts[rpos w (mask w) (Nat.mul n w) (LR i) z]! = z) ∧
      (∀ k < rcnt (LR i), rpos w (mask w) (Nat.mul n w) (LR i) (lev n S base i).pts[k]! = k) ∧
      (∀ k < rcnt (LR i), Orb.PRep n w (TR (roff n (Nat.mul n w) (LR i) + k)) (levT n S base i k) ∧
        Orb.PRep n w (TRI (roff n (Nat.mul n w) (LR i) + k)) (levT n S base i k)⁻¹) := by
    intro i hi
    obtain ⟨Ag, P⟩ := Orb.agree_levelK hb hp hbl (TRI := TRI) (R := LR) hi (hl i hi)
    have F := hA.levelFacts hF hi
    refine ⟨Ag.cnt, fun k hk => Ag.pt k (Ag.cnt ▸ hk), fun z hz hzr => ?_, fun k hk => ?_,
      fun k hk => ?_⟩
    · have hq := (Ag.pos z hz).1 hzr
      have e : rpos w (mask w) (Nat.mul n w) (LR i) z = (lev n S base i).pos[z]! :=
        Ag.posE z hz hq
      rw [e]
      exact F.pts_pos z hz hq
    · have hk' : k < (lev n S base i).pts.size := Ag.cnt ▸ hk
      have hpk := F.pos_pts k hk'
      have e : rpos w (mask w) (Nat.mul n w) (LR i) (lev n S base i).pts[k]! =
          (lev n S base i).pos[(lev n S base i).pts[k]!]! :=
        Ag.posE _ (F.pts_lt k hk') (by rw [hpk]; exact hk')
      rw [e, hpk]
    · have hk' : k < (lev n S base i).pts.size := Ag.cnt ▸ hk
      obtain ⟨h1, h2⟩ := P k hk
      exact ⟨fun z => (h1 z).trans (((Ag.tr k hk').1 z).symm.trans (hA.rep_levT hF hi hk' z)),
        fun z => (h2 z).trans (((Ag.tr k hk').2 z).symm.trans (hA.rep_levTInv hF hi hk' z))⟩
  have hG1 : ∀ i (hi : i < Q.baseCount) k (hk : k < (lev n S base i).pts.size),
      ((levT n S base i k (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ) = (lev n S base i).pts[k]! := by
    intro i hi k hk
    have ht := hA.transversal_of_lt hF hi hk
    have hx : levPts Q S base i k ∈ Q.orbitPoints ⟨i, hi⟩ := by
      change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).isSome = true
      rw [ht]
      rfl
    have h := (Q.transversal_getD_spec ⟨i, hi⟩ _ hx).2.2
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).getD 1 _ = _ at h
    rw [ht, Option.getD_some] at h
    rw [h, hA.levPts_val hF hi hk]
  have hG2 : ∀ i (hi : i < Q.baseCount) (h : Equiv.Perm (Fin n)), h ∈ Q.levelSubgroup i →
      (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]! < (lev n S base i).pts.size ∧
      (levT n S base i (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]!)⁻¹ * h ∈
        Q.levelSubgroup (i + 1) := by
    intro i hi h hh
    have hx : h (Q.base.get ⟨i, hi⟩) ∈ Q.orbitPoints ⟨i, hi⟩ := by
      rw [Q.orbitPoints_eq_orbit]
      exact ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨hk, -, ht⟩ := hA.orbitPoints_spec hF hi hx
    obtain ⟨-, hmem, hval⟩ := Q.transversal_getD_spec ⟨i, hi⟩ _ hx
    rw [ht] at hmem hval
    refine ⟨hk, ?_⟩
    set t := levT n S base i (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]!
      with htdef
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩]
    refine Subgroup.mem_inf.2
      ⟨(Q.levelSubgroup i).mul_mem ((Q.levelSubgroup i).inv_mem hmem) hh, ?_⟩
    have htb : t (Q.base.get ⟨i, hi⟩) = h (Q.base.get ⟨i, hi⟩) := hval
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]
    change t⁻¹ (h (Q.base.get ⟨i, hi⟩)) = Q.base.get ⟨i, hi⟩
    rw [← htb]
    simp
  set Dg : ℕ → Equiv.Perm (Fin n) := fun j =>
    x ^ (Nat.mod (Nat.succ j) 3) * y ^ (Nat.div (Nat.succ j) 3) with hDg
  have hD : ∀ j < 8, ∀ p : Fin n, dAt n w (mask w) DP j p = (Dg j p : ℕ) := by
    intro j hj p
    have hd' := hd
    unfold dOK at hd'
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at hd'
    have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hd'.2.2 j hj)
    rw [cs_dAt p.2, e]
    exact Orb.prep_pcomp hn (cs_prep_ppow hn24 hw2 hx _) (cs_prep_ppow hn24 hw2 hy _) p
  have hDc : ∀ c : Equiv.Perm (Fin n), c * x = x * c → c * y = y * c →
      ∀ j p, Dg j (c p) = c (Dg j p) := by
    intro c hcx hcy j p
    have hc : Commute c (Dg j) :=
      (Commute.pow_right (a := c) hcx _).mul_right (Commute.pow_right (a := c) hcy _)
    have := congrArg (fun g : Equiv.Perm (Fin n) => g p) hc.eq
    simp only [Equiv.Perm.mul_apply] at this
    exact this.symm
  have hfold : ∀ (F : ℕ → ℕ → ℕ) (g : ℕ → ℕ), (∀ k s, F k s = s + g k) →
      ∀ c, foldN c F 0 = ∑ k ∈ Finset.range c, g k := fun F g hF c => by
    rw [Orb.foldN_eq, cs_foldr_sum F g hF c 0, Nat.zero_add]
  have hlen : ∀ (pl : List ℕ) (i : ℕ), planOK n w Q.baseCount BP DP pl i = true →
      i + pl.length = Q.baseCount := by
    intro pl
    induction pl with
    | nil =>
      intro i h
      have := Nat.eq_of_beq_eq_true h
      simp [this]
    | cons E pl ih =>
      intro i h
      have e : planOK n w Q.baseCount BP DP (E :: pl) i =
          (entryOK n w (mask w) BP DP E i && planOK n w Q.baseCount BP DP pl (i + 1)) :=
        Orb.bAnd_eq _ _
      rw [e, Bool.and_eq_true] at h
      have := ih (i + 1) h.2
      simp only [List.length_cons]
      omega
  have key : ∀ (pl : List ℕ) (i : ℕ), planOK n w Q.baseCount BP DP pl i = true →
      ∀ (Wd B : ℕ) (σ : Equiv.Perm (Fin n)), σ ∈ Q.levelSubgroup 0 →
      (∀ p : Fin n, fwdW w (mask w) TR Wd i p = σ p) →
      (∀ a : Fin n, invW w (mask w) TRI Wd i a = σ⁻¹ a) →
      (∀ l (hl : l < i) (hl' : l < Q.baseCount),
        pg w (mask w) B l = σ (Q.base.get ⟨l, hl'⟩)) →
      Wd < 2 ^ (16 * i) → B < 2 ^ (w * i) →
      srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl i Wd B =
        (Finset.univ.filter fun c =>
          σ⁻¹ * c ∈ Q.levelSubgroup i ∧ c * x = x * c ∧ c * y = y * c).card := by
    intro pl
    induction pl with
    | nil =>
      intro i hpl Wd B σ hσ hfw _ hBl _ _
      have hiN : i = Q.baseCount := Nat.eq_of_beq_eq_true hpl
      subst hiN
      have hσ' : σ ∈ Q.originalSubgroup := by rwa [← Q.levelSubgroup_zero_eq_original hQ]
      have hone : ∀ (Z : ℕ) (z : Equiv.Perm (Fin n)), Orb.PRep n w Z z →
          (allN Q.baseCount (fun t => Nat.beq (fwdW w (mask w) TR Wd Q.baseCount
            (pg w (mask w) Z (pg w (mask w) BP t))) (pg w (mask w) Z (pg w (mask w) B t))) = true ↔
            ∀ t (ht : t < Q.baseCount),
              σ (z (Q.base.get ⟨t, ht⟩)) = z (σ (Q.base.get ⟨t, ht⟩))) := by
        intro Z z hZ
        rw [Orb.allN_iff]
        refine forall_congr' fun t => forall_congr' fun ht => ?_
        rw [← hbv t ht, hZ, hfw, hBl t ht ht, hZ, Orb.beq_dec, decide_eq_true_iff, Fin.val_inj]
      have hleaf : leafOK w (mask w) Q.baseCount TR BP Wd B [X, Y] = true ↔
          (σ * x = x * σ ∧ σ * y = y * σ) := by
        change Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false true
            (allN Q.baseCount (fun t => Nat.beq (fwdW w (mask w) TR Wd Q.baseCount
              (pg w (mask w) Y (pg w (mask w) BP t))) (pg w (mask w) Y (pg w (mask w) B t)))))
          (allN Q.baseCount (fun t => Nat.beq (fwdW w (mask w) TR Wd Q.baseCount
            (pg w (mask w) X (pg w (mask w) BP t))) (pg w (mask w) X (pg w (mask w) B t)))) =
            true ↔ _
        rw [Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_true, Bool.and_eq_true, hone X x hx, hone Y y hy]
        have hc : ∀ z : Equiv.Perm (Fin n), z ∈ Q.originalSubgroup →
            ((∀ t (ht : t < Q.baseCount),
              σ (z (Q.base.get ⟨t, ht⟩)) = z (σ (Q.base.get ⟨t, ht⟩))) ↔ σ * z = z * σ) := by
          intro z hz
          constructor
          · intro h
            have h1 : (z * σ)⁻¹ * (σ * z) = 1 := by
              refine Q.eq_one_of_fixes_base hQ (Q.originalSubgroup.mul_mem
                (Q.originalSubgroup.inv_mem (Q.originalSubgroup.mul_mem hz hσ'))
                (Q.originalSubgroup.mul_mem hσ' hz)) fun t => ?_
              rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h t t.2, mul_inv_rev,
                Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq]
            exact (inv_mul_eq_one.1 h1).symm
          · intro h t ht
            have := congrArg (fun g : Equiv.Perm (Fin n) => g (Q.base.get ⟨t, ht⟩)) h
            simpa only [Equiv.Perm.mul_apply] using this
        rw [hc x hxQ, hc y hyQ]
      have hf : ∀ c : Equiv.Perm (Fin n), (σ⁻¹ * c ∈ Q.levelSubgroup Q.baseCount ∧
          c * x = x * c ∧ c * y = y * c) ↔ (c = σ ∧ σ * x = x * σ ∧ σ * y = y * σ) := by
        intro c
        rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot, inv_mul_eq_one]
        constructor
        · rintro ⟨rfl, h⟩
          exact ⟨rfl, h⟩
        · rintro ⟨rfl, h⟩
          exact ⟨rfl, h⟩
      change Bool.rec (motive := fun _ => ℕ) 0 1
        (leafOK w (mask w) Q.baseCount TR BP Wd B [X, Y]) = _
      rw [Orb.nIf_eq]
      split_ifs with hL
      · symm
        refine Finset.card_eq_one.2 ⟨σ, ?_⟩
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [hf c]
        exact ⟨fun h => h.1, fun h => ⟨h, hleaf.1 hL⟩⟩
      · symm
        refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun c _ h => hL ?_)
        exact hleaf.2 ((hf c).1 h).2
    | cons E pl ih =>
      intro i hpl Wd B σ hσ hfw hiv hBl hW hB
      have e0 : planOK n w Q.baseCount BP DP (E :: pl) i =
          (entryOK n w (mask w) BP DP E i && planOK n w Q.baseCount BP DP pl (i + 1)) :=
        Orb.bAnd_eq _ _
      rw [e0, Bool.and_eq_true] at hpl
      obtain ⟨hE, hpl⟩ := hpl
      have hi : i < Q.baseCount := by
        have := hlen pl (i + 1) hpl
        omega
      obtain ⟨hc, hpt, hpos, hrpos, htr⟩ := hlev i hi
      have F := hA.levelFacts hF hi
      have hτm : ∀ k < rcnt (LR i), levT n S base i k ∈ Q.levelSubgroup i := fun k hk =>
        hA.levT_mem hF hi (hc ▸ hk)
      have hτb : ∀ k < rcnt (LR i), ((levT n S base i k (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ) =
          (lev n S base i).pts[k]! := fun k hk => hG1 i hi k (hc ▸ hk)
      unfold entryOK at hE
      rw [Orb.bAnd_eq, Bool.and_eq_true] at hE
      obtain ⟨hrs, hEm⟩ := hE
      simp only [relsOK, Orb.bAnd_eq] at hrs
      have hrs' := (cs_recAnd _ _).1 hrs
      set f : ℕ → ℕ := fun k => (Finset.univ.filter fun c =>
        (σ * levT n S base i k)⁻¹ * c ∈ Q.levelSubgroup (i + 1) ∧
          c * x = x * c ∧ c * y = y * c).card with hfdef
      set a : ℕ → ℕ := fun k => fwdW w (mask w) TR Wd i (rpt w (mask w) (LR i) k) with hadef
      have hak : ∀ k < rcnt (LR i), a k = (σ (levT n S base i k (Q.base.get ⟨i, hi⟩)) : ℕ) := by
        intro k hk
        simp only [hadef]
        rw [hpt k hk, ← hτb k hk, hfw]
      have hakn : ∀ k < rcnt (LR i), a k < n := fun k hk => by
        rw [hak k hk]
        exact (σ _).2
      have hrel : ∀ k < rcnt (LR i), ∀ c : Equiv.Perm (Fin n),
          (σ * levT n S base i k)⁻¹ * c ∈ Q.levelSubgroup (i + 1) →
          (∀ l (hl : l < i), c (Q.base.get ⟨l, by omega⟩) = σ (Q.base.get ⟨l, by omega⟩)) ∧
          ((c (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ) = a k := by
        intro k hk c hc'
        have e : c = σ * levT n S base i k * ((σ * levT n S base i k)⁻¹ * c) := by group
        refine ⟨fun l hl => ?_, ?_⟩
        · rw [e, Equiv.Perm.mul_apply, Q.levelSubgroup_fixes_base_index (i + 1) _ hc'
            ⟨l, by omega⟩ (Nat.lt_succ_of_lt hl), Equiv.Perm.mul_apply,
            Q.levelSubgroup_fixes_base_index i _ (hτm k hk) ⟨l, by omega⟩ hl]
        · rw [hak k hk, e, Equiv.Perm.mul_apply, Q.levelSubgroup_fixes_base_index (i + 1) _ hc'
            ⟨i, hi⟩ (Nat.lt_succ_self i), Equiv.Perm.mul_apply]
      have hrelOK : ∀ k < rcnt (LR i), ∀ c : Equiv.Perm (Fin n),
          (σ * levT n S base i k)⁻¹ * c ∈ Q.levelSubgroup (i + 1) → c * x = x * c →
          c * y = y * c → relOK n w (mask w) DP E i B (a k) = true := by
        intro k hk c hc' hcx hcy
        obtain ⟨hlt, hbi⟩ := hrel k hk c hc'
        unfold relOK
        simp only [Orb.bAnd_eq]
        rw [cs_recAnd]
        intro r hr
        have h := hrs' r hr
        simp only [Bool.and_eq_true, Nat.ble_eq] at h
        obtain ⟨hle, heq⟩ := h
        have hj8 := cs_land7 (Nat.shiftRight (eRel E r) 3)
        generalize Nat.land (eRel E r) 7 = l at hle heq ⊢
        generalize Nat.land (Nat.shiftRight (eRel E r) 3) 7 = j at hj8 heq ⊢
        have himg : imgAt w (mask w) B i (a k) l =
            ((c (Q.base.get ⟨l, by omega⟩) : Fin n) : ℕ) := by
          unfold imgAt
          rw [Orb.nIf_eq, Orb.blt_dec]
          by_cases h : l < i
          · rw [if_pos (decide_eq_true h), hBl l h (by omega), hlt l h]
          · have hli : l = i := by omega
            subst hli
            rw [if_neg (by simpa using h), ← hbi]
        have e2 : Dg j (Q.base.get ⟨l, by omega⟩) = Q.base.get ⟨i, hi⟩ :=
          Fin.ext (by rw [← hD j hj8, hbv, hbv]; exact Nat.eq_of_beq_eq_true heq)
        rw [himg, hD j hj8, hDc c hcx hcy, Orb.beq_dec, decide_eq_true_iff, ← hbi, e2]
      have hchild : ∀ k < rcnt (LR i), child n w (mask w) (Nat.mul n w) DP E i (LR i) Wd B (a k) k
          (srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl) = f k := by
        intro k hk
        obtain ⟨hTR, hTRI⟩ := htr k hk
        have hro' : roff n (Nat.mul n w) (LR i) + rcnt (LR i) ≤ 65536 := hro i hi
        have hok : roff n (Nat.mul n w) (LR i) + k < 2 ^ 16 := by
          have : (2 : ℕ) ^ 16 = 65536 := by norm_num
          omega
        have hal : a k < 2 ^ w := by
          have := hakn k hk
          omega
        obtain ⟨hW1, hW2, hW3⟩ := cs_lane (t := 16) (s := i) hW hok
        obtain ⟨hB1, hB2, hB3⟩ := cs_lane (t := w) (s := i) hB hal
        have hwl : ∀ l < i, wAt (Nat.lor Wd (Nat.shiftLeft (roff n (Nat.mul n w) (LR i) + k)
            (16 * i))) l = wAt Wd l := by
          intro l hl
          rw [cs_wAt, cs_wAt, hW2 l hl]
        have hwi : wAt (Nat.lor Wd (Nat.shiftLeft (roff n (Nat.mul n w) (LR i) + k) (16 * i))) i =
            roff n (Nat.mul n w) (LR i) + k := by
          rw [cs_wAt, hW3]
        unfold child
        rw [Orb.nIf_eq, Orb.bAnd_eq, Nat.blt_eq.mpr hk, Bool.true_and]
        split_ifs with hr
        · refine (ih (i + 1) hpl (Nat.lor Wd (Nat.shiftLeft (roff n (Nat.mul n w) (LR i) + k)
            (16 * i))) (Nat.lor B (Nat.shiftLeft (a k) (w * i))) (σ * levT n S base i k) ?_ ?_ ?_
            ?_ hW1 hB1).trans rfl
          · exact (Q.levelSubgroup 0).mul_mem hσ
              (Q.levelSubgroup_antitone 0 i (Nat.zero_le i) (hτm k hk))
          · intro p
            rw [cs_fwdW_succ, hwi, hTR p, cs_fwdW_congr w (mask w) TR i hwl, hfw,
              Equiv.Perm.mul_apply]
          · intro q
            rw [cs_invW_succ, hwi, cs_invW_congr w (mask w) TRI i hwl, hiv, hTRI, mul_inv_rev,
              Equiv.Perm.mul_apply]
          · intro l hl hl'
            rw [Orb.pg_eq]
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · rw [hB2 l hl, ← Orb.pg_eq, hBl l hl hl', Equiv.Perm.mul_apply,
                Q.levelSubgroup_fixes_base_index i _ (hτm k hk) ⟨l, hl'⟩ hl]
            · rw [hB3, hak k hk, Equiv.Perm.mul_apply]
        · symm
          simp only [hfdef]
          refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_)
          rintro c - ⟨hc', hcx, hcy⟩
          exact hr (hrelOK k hk c hc' hcx hcy)
      have htgt : ∀ p : Fin n, tgt n w (mask w) (Nat.mul n w) TRI DP E i (LR i) Wd B p
          (srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl) =
          ∑ k ∈ Finset.range (rcnt (LR i)), if a k = p then f k else 0 := by
        intro p
        unfold tgt
        rw [Orb.strictN_eq, hiv p]
        have hakp : ∀ k < rcnt (LR i), a k = p ↔
            (lev n S base i).pts[k]! = ((σ⁻¹ p : Fin n) : ℕ) := by
          intro k hk
          rw [hak k hk, ← hτb k hk, Fin.val_inj, Fin.val_inj, Equiv.Perm.eq_inv_iff_eq]
        by_cases hk0 : rpos w (mask w) (Nat.mul n w) (LR i) ((σ⁻¹ p : Fin n) : ℕ) < rcnt (LR i)
        · have hp0 := hpos _ (σ⁻¹ p).2 hk0
          have ha0 : a (rpos w (mask w) (Nat.mul n w) (LR i) ((σ⁻¹ p : Fin n) : ℕ)) = p :=
            (hakp _ hk0).2 hp0
          rw [Finset.sum_eq_single_of_mem _ (Finset.mem_range.2 hk0), if_pos ha0,
            ← hchild _ hk0, ha0]
          intro k hk hne
          rw [if_neg]
          intro hkp
          apply hne
          rw [Finset.mem_range] at hk
          rw [← (hakp k hk).1 hkp, hrpos k hk]
        · have hblt : Nat.blt (rpos w (mask w) (Nat.mul n w) (LR i) ((σ⁻¹ p : Fin n) : ℕ))
              (rcnt (LR i)) = false := Bool.eq_false_iff.2 fun h => hk0 (Nat.blt_eq.mp h)
          unfold child
          rw [Orb.nIf_eq, Orb.bAnd_eq, hblt, Bool.false_and, if_neg Bool.false_ne_true]
          symm
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_range] at hk
          rw [if_neg]
          intro hkp
          apply hk0
          rw [← (hakp k hk).1 hkp, hrpos k hk]
          exact hk
      have hfib : (Finset.univ.filter fun c =>
          σ⁻¹ * c ∈ Q.levelSubgroup i ∧ c * x = x * c ∧ c * y = y * c).card =
          ∑ k ∈ Finset.range (rcnt (LR i)), f k := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun c =>
          (lev n S base i).pos[(((σ⁻¹ * c) (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]!)
          (t := Finset.range (rcnt (LR i))) ?_]
        · refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          simp only [hfdef]
          congr 1
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨hci, hcm⟩, hkc⟩
            refine ⟨?_, hcm⟩
            have := (hG2 i hi _ hci).2
            rw [hkc] at this
            rwa [mul_inv_rev, mul_assoc]
          · rintro ⟨hc', hcm⟩
            have e : σ⁻¹ * c = levT n S base i k * ((σ * levT n S base i k)⁻¹ * c) := by group
            refine ⟨⟨?_, hcm⟩, ?_⟩
            · rw [e]
              exact (Q.levelSubgroup i).mul_mem (hτm k hk)
                (Q.levelSubgroup_antitone i (i + 1) (Nat.le_succ i) hc')
            · rw [e, Equiv.Perm.mul_apply, Q.levelSubgroup_fixes_base_index (i + 1) _ hc'
                ⟨i, hi⟩ (Nat.lt_succ_self i), hτb k hk, F.pos_pts k (hc ▸ hk)]
        · intro c hcK
          rw [Finset.mem_coe, Finset.mem_filter] at hcK
          rw [Finset.mem_coe, Finset.mem_range, hc]
          exact (hG2 i hi _ hcK.2.1).1
      change strictN (LR i) (fun R => level n w (mask w) (Nat.mul n w) TR TRI DP E i R Wd B
        (srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl)) = _
      rw [Orb.strictN_eq, hfib]
      unfold level
      obtain hm | hm | ⟨e, hm⟩ := cs_cases (emode E)
      ·
        simp only [hm, Nat.rec_zero, Orb.bAnd_eq, Bool.and_eq_true] at hEm ⊢
        obtain ⟨hl0, hd0⟩ := hEm
        have hl0' : eL E < i := Nat.blt_eq.mp hl0
        have hj0 : eJ E < 8 := cs_land7 _
        rw [Orb.strictN_eq, hBl (eL E) hl0' (by omega), hD (eJ E) hj0, htgt]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        split_ifs with hak0
        · rfl
        · symm
          simp only [hfdef]
          refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_)
          rintro c - ⟨hc', hcx, hcy⟩
          apply hak0
          obtain ⟨hlt, hbi⟩ := hrel k hk c hc'
          have e2 : Dg (eJ E) (Q.base.get ⟨eL E, by omega⟩) = Q.base.get ⟨i, hi⟩ :=
            Fin.ext (by rw [← hD (eJ E) hj0, hbv, hbv]; exact Nat.eq_of_beq_eq_true hd0)
          rw [← hbi, ← e2, ← hDc c hcx hcy, hlt (eL E) hl0']
      ·
        simp only [hm, Nat.rec_add_one, Nat.rec_zero] at hEm ⊢
        have hZ : ∀ k < rcnt (LR i), f k ≠ 0 →
            Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 (a k))) = true := by
          intro k hk hf0
          obtain ⟨c, hcm⟩ := Finset.card_ne_zero.1 hf0
          rw [Finset.mem_filter] at hcm
          obtain ⟨-, hc', hcx, hcy⟩ := hcm
          obtain ⟨-, hbi⟩ := hrel k hk c hc'
          have hfx : fixAll n w (mask w) DP E i (a k) = true := by
            unfold fixAll
            simp only [Orb.bAnd_eq]
            rw [cs_recAnd]
            intro r hr
            have h := hrs' r hr
            simp only [Bool.and_eq_true, Nat.ble_eq] at h
            obtain ⟨-, heq⟩ := h
            have hj8 := cs_land7 (Nat.shiftRight (eRel E r) 3)
            generalize Nat.land (eRel E r) 7 = l at heq ⊢
            generalize Nat.land (Nat.shiftRight (eRel E r) 3) 7 = j at hj8 heq ⊢
            cases hb : Nat.beq l i
            · rfl
            · have hli : l = i := Nat.eq_of_beq_eq_true hb
              subst hli
              have e2 : Dg j (Q.base.get ⟨l, hi⟩) = Q.base.get ⟨l, hi⟩ :=
                Fin.ext (by rw [← hD j hj8, hbv]; exact Nat.eq_of_beq_eq_true heq)
              change Nat.beq (dAt n w (mask w) DP j (a k)) (a k) = true
              rw [← hbi, hD j hj8, hDc c hcx hcy, e2, Orb.beq_dec, decide_eq_true_iff]
          have := Orb.allN_iff.1 hEm (a k) (hakn k hk)
          rw [hfx] at this
          simpa using this
        refine (hfold _ (fun p => if Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 p)) = true then
          tgt n w (mask w) (Nat.mul n w) TRI DP E i (LR i) Wd B p
            (srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl) else 0) (fun p s => ?_) n).trans ?_
        · beta_reduce
          rw [Orb.nIf_eq]
          split_ifs <;> simp
        · calc ∑ p ∈ Finset.range n, (if Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 p)) = true
                then tgt n w (mask w) (Nat.mul n w) TRI DP E i (LR i) Wd B p
                  (srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl) else 0)
              = ∑ p ∈ Finset.range n, ∑ k ∈ Finset.range (rcnt (LR i)),
                  (if a k = p then f k else 0) := by
                refine Finset.sum_congr rfl fun p hp => ?_
                rw [Finset.mem_range] at hp
                split_ifs with hmk
                · exact htgt ⟨p, hp⟩
                · symm
                  refine Finset.sum_eq_zero fun k hk => ?_
                  rw [Finset.mem_range] at hk
                  split_ifs with hkp
                  · by_contra hf0
                    exact hmk (hkp ▸ hZ k hk hf0)
                  · rfl
            _ = ∑ k ∈ Finset.range (rcnt (LR i)), ∑ p ∈ Finset.range n,
                  (if a k = p then f k else 0) := Finset.sum_comm
            _ = ∑ k ∈ Finset.range (rcnt (LR i)), f k := by
                refine Finset.sum_congr rfl fun k hk => ?_
                rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (hakn k (Finset.mem_range.1 hk)))]
      ·
        simp only [hm, Nat.rec_add_one] at ⊢
        refine (hfold _ (fun k => child n w (mask w) (Nat.mul n w) DP E i (LR i) Wd B (a k) k
          (srch n w Q.baseCount LR TR TRI BP DP [X, Y] pl)) (fun k s => ?_) (rcnt (LR i))).trans ?_
        · beta_reduce
          rw [Orb.strictN_eq]
          rfl
        · exact Finset.sum_congr rfl fun k hk => hchild k (Finset.mem_range.1 hk)
  have hfin : Nat.card ↥(Q.originalSubgroup ⊓
      Subgroup.centralizer ({x, y} : Set (Equiv.Perm (Fin n)))) =
      (Finset.univ.filter fun c => (1 : Equiv.Perm (Fin n))⁻¹ * c ∈ Q.levelSubgroup 0 ∧
        c * x = x * c ∧ c * y = y * c).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Finset.mem_filter, inv_one, one_mul,
      Q.levelSubgroup_zero_eq_original hQ]
    simp only [Finset.mem_univ, true_and, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2.symm, h3.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2.symm, h3.symm⟩⟩
  rw [hfin]
  exact (key pl 0 hpl 0 0 1 (Subgroup.one_mem _) (fun p => rfl) (fun a => rfl)
    (fun l hl => absurd hl (Nat.not_lt_zero l)) (by norm_num) (by norm_num)).symm

end CFSG.KC.CentSrch

end
