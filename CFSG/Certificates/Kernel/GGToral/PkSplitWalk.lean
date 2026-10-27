module

public import CFSG.Certificates.Kernel.GGToral.PkWalkCommon
public import CFSG.Certificates.Kernel.GGToral.PkCase

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.StepTwoToralCert

theorem memB_lor_shift (m c y : ℕ) :
    memB (Nat.lor m (Nat.shiftLeft 1 c)) y = true ↔ memB m y = true ∨ y = c := by
  rw [memB_iff, memB_iff]
  change (m ||| 1 <<< c).testBit y = true ↔ _
  rw [Nat.testBit_lor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_iff]
  exact or_congr Iff.rfl eq_comm

theorem memB_land (a b r : ℕ) :
    memB (Nat.land a b) r = true ↔ memB a r = true ∧ memB b r = true := by
  rw [memB_iff, memB_iff, memB_iff]
  change (a &&& b).testBit r = true ↔ _
  rw [Nat.testBit_land, Bool.and_eq_true]

theorem memB_maskOf_of_mem {r : ℕ} : ∀ {mem : List ℕ}, r ∈ mem → memB (maskOf mem) r = true
  | [], h => absurd h (by simp)
  | a :: mem, h => by
    change memB (Nat.lor (maskOf mem) (Nat.shiftLeft 1 a)) r = true
    rw [memB_lor_shift]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (memB_maskOf_of_mem h)

theorem digits_inj {p : ℕ} {f g : ℕ → ℕ} : ∀ k, (∀ j < k, f j < p) → (∀ j < k, g j < p) →
    Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add (Nat.mul ih p) (f j)) k =
      Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add (Nat.mul ih p) (g j)) k →
    ∀ j < k, f j = g j := by
  intro k
  induction k with
  | zero => exact fun _ _ _ j hj => absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro hf hg h j hj
    change Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add (Nat.mul ih p) (f j)) k * p +
        f k = Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add (Nat.mul ih p) (g j)) k * p +
        g k at h
    have hfk := hf k (by omega)
    have hgk := hg k (by omega)
    have hk : f k = g k := by
      have h1 := congrArg (· % p) h
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfk, add_comm,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hgk] at h1
      exact h1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hk] at h
      have hp : 0 < p := by omega
      exact ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
        (Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)) j hj
    · exact hk

theorem codeP_inj {H : Hd} (hp : 0 < H.p) {x y : ℕ} (hx : red H x = true) (hy : red H y = true)
    (h : codeP H x = codeP H y) : x = y := by
  obtain ⟨hxl, hxv⟩ := red_spec hp hx
  obtain ⟨hyl, hyv⟩ := red_spec hp hy
  have hd := digits_inj (f := fun j => lane x (H.n - 1 - j)) (g := fun j => lane y (H.n - 1 - j))
    H.n (fun j hj => hxv _ (by omega)) (fun j hj => hyv _ (by omega)) h
  rw [eq_packN_lane hxl, eq_packN_lane hyl]
  refine packN_congr fun j hj => ?_
  have := hd (H.n - 1 - j) (by omega)
  rwa [show H.n - 1 - (H.n - 1 - j) = j by omega] at this

theorem inM_addM (H : Hd) (m v x : ℕ) :
    inM H (addM H m v) x = true ↔ inM H m x = true ∨ codeP H x = codeP H v :=
  memB_lor_shift _ _ _

theorem inM_maskL_iff (H : Hd) (T : List ℕ) (x : ℕ) :
    inM H (maskL H T) x = true ↔ ∃ t ∈ T, codeP H x = codeP H t := by
  induction T with
  | nil => simp [maskL, inM, memB_zero]
  | cons t T ih =>
    change inM H (addM H (maskL H T) t) x = true ↔ _
    rw [inM_addM, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

theorem allVec_iff (H : Hd) (T : List ℕ) : allVec H T = true ↔ ∀ v ∈ T, vecOK H v = true := by
  induction T with
  | nil => simp [allVec]
  | cons t T ih =>
    change andB (vecOK H t) (allVec H T) = true ↔ _
    rw [andB_eq_true, ih, List.forall_mem_cons]

theorem vecOK_iff (H : Hd) (v : ℕ) :
    vecOK H v = true ↔ red H v = true ∧ v ≠ 0 ∧ inV H v = true := by
  unfold vecOK
  rw [andB_eq_true, andB_eq_true, notB_eq_true]
  exact and_congr Iff.rfl (and_congr ⟨Nat.ne_of_beq_eq_false,
    fun h => Bool.eq_false_iff.mpr fun h1 => h (Nat.eq_of_beq_eq_true h1)⟩ Iff.rfl)

theorem mem_of_inM_maskL {H : Hd} (hp : 0 < H.p) {T : List ℕ} (hT : ∀ t ∈ T, red H t = true)
    {x : ℕ} (hx : red H x = true) (h : inM H (maskL H T) x = true) : x ∈ T := by
  obtain ⟨t, ht, hc⟩ := (inM_maskL_iff H T x).mp h
  rw [codeP_inj hp hx (hT t ht) hc]
  exact ht

theorem inM_maskL_of_mem (H : Hd) {T : List ℕ} {x : ℕ} (hx : x ∈ T) :
    inM H (maskL H T) x = true :=
  (inM_maskL_iff H T x).mpr ⟨x, hx, rfl⟩

theorem letter_eq_modL (H : Hd) (l f : ℕ) : ∃ x, letter H l f = modL H.p H.n x := by
  unfold letter twLetter
  cases tw H <;> cases Nat.blt l H.n <;> cases Nat.beq l 0 <;> cases Nat.beq l 1 <;>
    cases Nat.beq l 2 <;> exact ⟨_, rfl⟩

theorem red_letter {H : Hd} (hp : 0 < H.p) (hp16 : H.p ≤ 65536) (l f : ℕ) :
    red H (letter H l f) = true := by
  obtain ⟨x, hx⟩ := letter_eq_modL H l f
  rw [hx]
  exact red_modL hp hp16 x

theorem chainOK_word {H : Hd} (hp : 0 < H.p) (hp16 : H.p ≤ 65536) {reps : List ℕ} :
    ∀ {ents : List ℕ}, ChainOK H reps ents → (∀ e ∈ ents, red H e = true) →
      ∀ e ∈ ents, ∃ w, word H w e ∈ reps
  | [], _, _, e, he => absurd he (by simp)
  | v :: ents, ⟨h1, h2⟩, hr, e, he => by
    have hr' : ∀ e ∈ ents, red H e = true := fun e he => hr e (List.mem_cons_of_mem _ he)
    rcases List.mem_cons.mp he with rfl | he
    · rcases h1 with h1 | ⟨g, hg⟩
      · exact ⟨[], h1⟩
      · obtain ⟨w, hw⟩ := chainOK_word hp hp16 h2 hr' _
          (mem_of_inM_maskL hp hr' (red_letter hp hp16 g e) hg)
        exact ⟨g :: w, hw⟩
    · exact chainOK_word hp hp16 h2 hr' e he

theorem zeroAt_iff (H : Hd) (P : List ℕ) (v : ℕ) :
    zeroAt H P v = true ↔ ∀ q ∈ P, zL H v q = true := by
  induction P with
  | nil => simp [zeroAt]
  | cons q P ih =>
    change andB (zL H v q) (zeroAt H P v) = true ↔ _
    rw [andB_eq_true, ih, List.forall_mem_cons]

theorem rowsOK_tri {H : Hd} {mu : ℕ} {mem : List ℕ} :
    ∀ {P : List ℕ} {R : List (ℕ × ℕ × List ℕ)}, RowsOK H mu mem P R →
      (∀ x ∈ R, x.1 = combo H mu x.2.2 ∧ pairsOK H mem x.2.2 = true ∧ x.2.1 < H.n ∧
        zL H x.1 x.2.1 = false) ∧ (∀ x ∈ R, ∀ q ∈ P, zL H x.1 q = true) ∧
      ∀ i j, i < j → j < R.length →
        zL H (R.getD j (0, 0, [])).1 (R.getD i (0, 0, [])).2.1 = true
  | _, [], _ => ⟨by simp, by simp, fun _ _ _ hj => absurd hj (by simp)⟩
  | P, (vec, piv, ps) :: R, ⟨h1, h2, h3, h4, h5, h6⟩ => by
    obtain ⟨hR1, hR2, hR3⟩ := rowsOK_tri h6
    refine ⟨List.forall_mem_cons.mpr ⟨⟨h1, h2, h3, h4⟩, hR1⟩,
      List.forall_mem_cons.mpr ⟨(zeroAt_iff H P vec).mp h5,
        fun x hx q hq => hR2 x hx q (List.mem_cons_of_mem _ hq)⟩, ?_⟩
    intro i j hij hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hjR : j < R.length := by simpa using hj
    rcases i with _ | i
    · have hmem : R.getD j (0, 0, []) ∈ R := by
        rw [List.getD_eq_getElem _ _ hjR]
        exact List.getElem_mem hjR
      exact hR2 _ hmem piv List.mem_cons_self
    · exact hR3 i j (by omega) hjR

theorem nthM_mem : ∀ (ms : List ℕ) (k : ℕ), nthM ms k = 0 ∨ nthM ms k ∈ ms := by
  intro ms
  induction ms with
  | nil => exact fun _ => Or.inl rfl
  | cons m ms ih =>
    intro k
    have e : nthM (m :: ms) k =
        Bool.rec (motive := fun _ => ℕ) (nthM ms (k - 1)) m (Nat.beq k 0) := rfl
    rw [e]
    cases Nat.beq k 0
    · rcases ih (k - 1) with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · exact Or.inr List.mem_cons_self

theorem lmFacts_zero (H : Hd) : LMFacts H 0 :=
  ⟨[], [], ⟨rfl, by simp, by simp, trivial⟩, rfl, by simp⟩

theorem red_of_lanes {H : Hd} {v : ℕ} (hv : v < 2 ^ (16 * H.n)) (hl : ∀ j < H.n, lane v j < H.p) :
    red H v = true := by
  refine Nat.beq_eq_true_eq _ _ ▸ ?_
  rw [modL_eq_packN]
  conv_rhs => rw [eq_packN_lane hv]
  exact packN_congr fun j hj => Nat.mod_eq_of_lt (hl j hj)

theorem red_zero (H : Hd) (hp : 0 < H.p) : red H 0 = true :=
  red_of_lanes (Nat.pow_pos (by norm_num)) fun j _ => by simp [lane_eq, hp]

theorem closedOK_spec {H : Hd} {phi cm : ℕ} :
    ∀ {mem : List ℕ}, closedOK H phi cm mem = true →
      ∀ r ∈ mem, ∀ s, memB (row H.adj r) s = true → memB phi s = true → memB cm s = true
  | [], _, r, hr, _, _, _ => absurd hr (by simp)
  | a :: mem, h, r, hr, s, hs1, hs2 => by
    change andB (Nat.beq (Nat.lor (Nat.land (row H.adj a) phi) cm) cm) (closedOK H phi cm mem) =
      true at h
    rw [andB_eq_true] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [← Nat.eq_of_beq_eq_true h.1, memB_lor, memB_land]
      exact Or.inl ⟨hs1, hs2⟩
    · exact closedOK_spec h.2 r hr s hs1 hs2

theorem allKilled_spec {H : Hd} {v : ℕ} :
    ∀ {mem : List ℕ}, allKilled H mem v = true → ∀ r ∈ mem, killed H r v = true
  | [], _, r, hr => absurd hr (by simp)
  | a :: mem, h, r, hr => by
    change andB (killed H a v) (andB (orB (notB (tw H)) (killed H (lane H.gam a) v))
      (allKilled H mem v)) = true at h
    simp only [andB_eq_true] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1
    · exact allKilled_spec h.2.2 r hr

theorem genValid_spec {mem : List ℕ} {g : ℕ} (h : genValid mem g = true) :
    g = 0 ∨ g - 1 ∈ mem := by
  unfold genValid at h
  rw [orB_eq_true] at h
  rcases h with h | h
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · refine Or.inr ?_
    induction mem with
    | nil => exact absurd h (by simp)
    | cons r mem ih =>
      change orB (Nat.beq r (Nat.sub g 1)) (List.rec (motive := fun _ => Bool) false
        (fun r _ ih => orB (Nat.beq r (Nat.sub g 1)) ih) mem) = true at h
      rw [orB_eq_true] at h
      rcases h with h | h
      · have e : r = g - 1 := Nat.eq_of_beq_eq_true h
        rw [e]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

section Vec

variable {τ : Tag} {p mode : ℕ} {H : Hd}

theorem vecZ_zero (p n : ℕ) : vecZ p n 0 = 0 := by
  funext j
  simp [vecZ, lane_eq]

theorem vecZ_inj (h : tagHdOK τ p mode H = true) {x y : ℕ} (hx : red H x = true)
    (hy : red H y = true) (hxy : vecZ p τ.rank x = vecZ p τ.rank y) : x = y := by
  obtain ⟨-, -, hn, hpp, hp3, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hxl, hxv⟩ := red_spec hpos hx
  obtain ⟨hyl, hyv⟩ := red_spec hpos hy
  rw [eq_packN_lane hxl, eq_packN_lane hyl]
  refine packN_congr fun j hj => ?_
  have := congrFun hxy ⟨j, by omega⟩
  simp only [vecZ] at this
  exact (lane_cast_inj (by have := hxv j hj; omega) (by have := hyv j hj; omega)).mp this

theorem vecZ_ne_zero (h : tagHdOK τ p mode H = true) {x : ℕ} (hx : red H x = true)
    (h0 : x ≠ 0) : vecZ p τ.rank x ≠ 0 := by
  obtain ⟨-, -, -, hpp, hp3, -⟩ := tagHdOK_basic h
  intro h1
  exact h0 (vecZ_inj h hx (red_zero H (by omega)) (h1.trans (vecZ_zero p τ.rank).symm))

theorem vecZ_apply_eq_zero (h : tagHdOK τ p mode H = true) (v : ℕ) (q : Fin τ.rank) :
    vecZ p τ.rank v q = 0 ↔ zL H v q = true := by
  obtain ⟨-, -, -, hpp, -⟩ := tagHdOK_basic h
  unfold zL vecZ
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, ← hpp]
  exact ⟨fun h0 => Nat.beq_eq_true_eq _ _ ▸ h0, Nat.eq_of_beq_eq_true⟩

theorem vecZ_modL_lin (h : tagHdOK τ p mode H = true) {x y a c : ℕ} (hx : red H x = true)
    (hy : red H y = true) (ha : a < 16) (hc : c < 16) :
    vecZ p τ.rank (modL H.p H.n (a * x + c * y)) =
      (a : ZMod p) • vecZ p τ.rank x + (c : ZMod p) • vecZ p τ.rank y := by
  obtain ⟨-, -, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hxl, hxv⟩ := red_spec hpos hx
  obtain ⟨hyl, hyv⟩ := red_spec hpos hy
  have hpk : a * x + c * y = packN H.n (fun j => a * lane x j + c * lane y j) := by
    conv_lhs => rw [eq_packN_lane hxl, eq_packN_lane hyl]
    rw [packN_eq_sum, packN_eq_sum, packN_eq_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hb : ∀ j < τ.rank, a * lane x j + c * lane y j < 65536 := fun j hj => by
    have h1 := hxv j (by omega)
    have h2 := hyv j (by omega)
    have h3 : a * lane x j ≤ 16 * 16 := Nat.mul_le_mul (by omega) (by omega)
    have h4 : c * lane y j ≤ 16 * 16 := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [hpk, hpp, hn]
  funext j
  rw [vecZ_modL_packN hb j]
  simp only [vecZ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem red_cor (h : tagHdOK τ p mode H = true) {r : ℕ} (hr : r < H.np) :
    red H (row H.cor r) = true := by
  obtain ⟨-, -, -, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have hlt : ∀ j, corC τ H r j < H.p := fun j => by
    unfold corC
    dsimp only
    generalize Nat.ble (negC τ H r j) (Nat.mul 2 (rtC H r j)) = b
    cases b
    · exact Nat.mod_lt _ hpos
    · exact Nat.mod_lt _ hpos
  have hb : ∀ j < H.n, corC τ H r j < 65536 := fun j _ => by have := hlt j; omega
  rw [(tagHdOK_cor h hr).1]
  exact red_of_lanes (packN_lt hb) fun j hj => by rw [lane_packN hb hj]; exact hlt j

theorem latChar_neg (f : Fin τ.rank → ZMod p) (α : Fin τ.rank → ℤ) :
    latChar p f (-α) = -latChar p f α := by
  simp [latChar, Finset.sum_neg_distrib]

theorem latGram_neg_left (S : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (α β : Fin τ.rank → ℤ) :
    latGram S (-α) β = -latGram S α β := by
  simp [latGram, Finset.sum_neg_distrib]

theorem latGram_neg_right (S : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (α β : Fin τ.rank → ℤ) :
    latGram S α (-β) = -latGram S α β := by
  simp [latGram, Finset.sum_neg_distrib]

theorem latGram_rowZ_ne (h : tagHdOK τ p mode H = true) {r : ℕ} (hr : r < H.np) :
    latGram τ.symmetrizedCartan (rowZ τ H r) (rowZ τ H r) ≠ 0 := by
  have hex := (tagHdOK_cor h hr).2
  unfold corExact at hex
  rw [andB_eq_true, Nat.blt_eq] at hex
  have hg := hex.1
  unfold gramC at hg
  have h2 : sumN H.n (fun j => rtC H r j * lane (tgDiag τ) j * negC τ H r j) <
      sumN H.n (fun j => rtC H r j * lane (tgDiag τ) j * (2 * rtC H r j)) := Nat.lt_of_sub_pos hg
  rw [latGram_rowZ h r]
  omega

theorem cor_mem_eigen (h : tagHdOK τ p mode H = true) {r : ℕ} (hr : r < H.np)
    {O : Set (Fin τ.rank → ℤ)} (hO : rowZ τ H r ∈ O) :
    vecZ p τ.rank (row H.cor r) ∈ latEigenCoroot p τ.symmetrizedCartan 1 O := by
  rw [vecZ_cor h hr]
  refine ⟨latCorootZ τ.symmetrizedCartan (rowZ τ H r),
    Submodule.subset_span ⟨rowZ τ H r, hO, rfl⟩, fun i => rfl, 0, Submodule.zero_mem _, ?_⟩
  funext k
  have hk : (Equiv.symm (1 : Equiv.Perm (Fin τ.rank))) k = k := rfl
  simp [hk]

theorem combo_spec (h : tagHdOK τ p 0 H = true) {a : ℕ} (ha : red H a = true) {mem : List ℕ}
    (hmem : ∀ r ∈ mem, r < H.np) {T : Submodule (ZMod p) (Fin τ.rank → ZMod p)}
    (hTa : vecZ p τ.rank a ∈ T) (hTc : ∀ r ∈ mem, vecZ p τ.rank (row H.cor r) ∈ T) :
    ∀ ps, pairsOK H mem ps = true →
      red H (combo H a ps) = true ∧ vecZ p τ.rank (combo H a ps) ∈ T := by
  obtain ⟨-, hm, -, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have htw : tw H = false := by
    rw [tw, hm]
    rfl
  intro ps
  induction ps with
  | nil =>
    refine fun _ => ⟨red_zero H hpos, ?_⟩
    change vecZ p τ.rank 0 ∈ T
    rw [vecZ_zero]
    exact T.zero_mem
  | cons gc ps ih =>
    intro hps
    have hps' : andB (genValid mem (gc / 256)) (andB (Nat.blt (gc % 256) H.p)
      (pairsOK H mem ps)) = true := hps
    simp only [andB_eq_true, Nat.blt_eq] at hps'
    obtain ⟨hg, hc, hps⟩ := hps'
    obtain ⟨hr, hm⟩ := ih hps
    have hy : red H (genOf H a (gc / 256)) = true ∧ vecZ p τ.rank (genOf H a (gc / 256)) ∈ T := by
      unfold genOf
      rw [htw]
      cases hg0 : Nat.beq (gc / 256) 0
      · have hm' := (genValid_spec hg).resolve_left (Nat.ne_of_beq_eq_false hg0)
        exact ⟨red_cor h (hmem _ hm'), hTc _ hm'⟩
      · exact ⟨ha, hTa⟩
    have e : combo H a (gc :: ps) =
        modL H.p H.n (1 * combo H a ps + (gc % 256) * genOf H a (gc / 256)) := by
      rw [one_mul]
      rfl
    rw [e, vecZ_modL_lin h hr hy.1 (by norm_num) (by omega)]
    exact ⟨red_modL hpos (by omega) _, T.add_mem (T.smul_mem _ hm) (T.smul_mem _ hy.2)⟩

end Vec

section Comp

variable {τ : Tag} {p mode : ℕ}
  {H : Hd}

@[expose] def rootsOf (τ : Tag) (H : Hd) (mem : List ℕ) : Set (Fin τ.rank → ℤ) :=
  {β | ∃ r ∈ mem, β = rowZ τ H r ∨ β = -rowZ τ H r}

theorem linkedOK_aux (h : tagHdOK τ p mode H = true) {Φ : Set (Fin τ.rank → ℤ)} {Q : ℕ → Prop}
    (hQ : ∀ r, Q r → r < H.np ∧ rowZ τ H r ∈ Φ) :
    ∀ (mem : List ℕ) (pre : ℕ),
      List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun r _ ih => fun pre => andB (orB (Nat.beq pre 0)
          (notB (Nat.beq (Nat.land (row H.adj r) pre) 0))) (ih (Nat.lor pre (Nat.shiftLeft 1 r))))
        mem pre = true →
      (∀ r ∈ mem, Q r) → (∀ s, memB pre s = true → Q s) →
      (∀ s t, memB pre s = true → memB pre t = true →
        latLinked τ.symmetrizedCartan Φ (rowZ τ H s) (rowZ τ H t)) →
      ∀ s t, (memB pre s = true ∨ s ∈ mem) → (memB pre t = true ∨ t ∈ mem) →
        latLinked τ.symmetrizedCartan Φ (rowZ τ H s) (rowZ τ H t) := by
  intro mem
  induction mem with
  | nil =>
    intro pre _ _ _ hL s t hs ht
    exact hL s t (hs.resolve_right (by simp)) (ht.resolve_right (by simp))
  | cons r mem ih =>
    intro pre h1 hm hpre hL
    obtain ⟨h2, h3⟩ := (andB_eq_true _ _).mp h1
    have hr := hm r List.mem_cons_self
    obtain ⟨hr1, hr2⟩ := hQ r hr
    have hrl : ∀ s, memB pre s = true →
        latLinked τ.symmetrizedCartan Φ (rowZ τ H r) (rowZ τ H s) := by
      intro s hs
      rcases (orB_eq_true _ _).mp h2 with h0 | h0
      · rw [Nat.eq_of_beq_eq_true h0, memB_zero] at hs
        exact absurd hs (by simp)
      · rw [notB_eq_true] at h0
        obtain ⟨s0, hs0⟩ := Nat.exists_testBit_of_ne_zero (Nat.ne_of_beq_eq_false h0)
        have hb := (memB_land _ _ s0).mp ((memB_iff _ _).mpr hs0)
        obtain ⟨hs01, hs02⟩ := hQ s0 (hpre s0 hb.2)
        have hg := (adj_iff h hr1 hs01).mp hb.1
        refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hr2, hs02, ?_⟩)
          (hL s0 s hb.2 hs)
        rwa [latGram_symmetrizedCartan_comm]
    have hL' : ∀ s t, memB (Nat.lor pre (Nat.shiftLeft 1 r)) s = true →
        memB (Nat.lor pre (Nat.shiftLeft 1 r)) t = true →
        latLinked τ.symmetrizedCartan Φ (rowZ τ H s) (rowZ τ H t) := by
      intro s t hs ht
      rcases (memB_lor_shift _ _ _).mp hs with hs | hs <;>
        rcases (memB_lor_shift _ _ _).mp ht with ht | ht
      · exact hL s t hs ht
      · rw [ht]
        exact Relation.EqvGen.symm _ _ (hrl s hs)
      · rw [hs]
        exact hrl t ht
      · rw [hs, ht]
        exact Relation.EqvGen.refl _
    intro s t hs ht
    have hconv : ∀ x, (memB pre x = true ∨ x ∈ r :: mem) →
        (memB (Nat.lor pre (Nat.shiftLeft 1 r)) x = true ∨ x ∈ mem) := by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl ((memB_lor_shift _ _ _).mpr (Or.inl hx))
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl ((memB_lor_shift _ _ _).mpr (Or.inr rfl))
        · exact Or.inr hx
    exact ih _ h3 (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      (fun x hx => ((memB_lor_shift _ _ _).mp hx).elim (hpre x) fun e => e ▸ hr) hL' s t
      (hconv s hs) (hconv t ht)

theorem comp_eq_rootsOf (h : tagHdOK τ p mode H = true)
    (hroot : ∀ r < H.np, IsRoot τ (rowZ τ H r))
    (hall : ∀ α, IsRoot τ α → ∃ r < H.np, α = rowZ τ H r ∨ α = -rowZ τ H r)
    {f : Fin τ.rank → ZMod p} {phi : ℕ}
    (hphi : ∀ r < H.np, memB phi r = true ↔ latChar p f (rowZ τ H r) = 0)
    {mem : List ℕ} (hsub : ∀ r ∈ mem, memB phi r = true ∧ r < H.np)
    (hcl : closedOK H phi (maskOf mem) mem = true) (hlk : linkedOK H mem = true)
    {r0 : ℕ} (hr0 : r0 ∈ mem) {α : Fin τ.rank → ℤ} (hα : α = rowZ τ H r0 ∨ α = -rowZ τ H r0) :
    {β | latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f) α β} = rootsOf τ H mem := by
  have hin : ∀ r ∈ mem, rowZ τ H r ∈ latPhi {α | IsRoot τ α} p f ∧
      -rowZ τ H r ∈ latPhi {α | IsRoot τ α} p f := fun r hr => by
    obtain ⟨h1, h2⟩ := hsub r hr
    have hz := (hphi r h2).mp h1
    exact ⟨⟨hroot r h2, hz⟩, ⟨CFSG.LieType.Chevalley.IsRoot.neg (hroot r h2), by rw [latChar_neg, hz, neg_zero]⟩⟩
  have hstep : ∀ x y, latGram τ.symmetrizedCartan x y ≠ 0 →
      y ∈ latPhi {α | IsRoot τ α} p f → x ∈ rootsOf τ H mem → y ∈ rootsOf τ H mem := by
    rintro x y hxy ⟨hy, hyf⟩ ⟨r, hr, hx⟩
    obtain ⟨s, hs, hys⟩ := hall y hy
    have hsz : latChar p f (rowZ τ H s) = 0 := by
      rcases hys with rfl | rfl
      · exact hyf
      · rw [latChar_neg] at hyf
        exact neg_eq_zero.mp hyf
    have hg : latGram τ.symmetrizedCartan (rowZ τ H r) (rowZ τ H s) ≠ 0 := by
      rcases hx with rfl | rfl <;> rcases hys with rfl | rfl <;>
        simpa [latGram_neg_left, latGram_neg_right] using hxy
    have hadj := (adj_iff h (hsub r hr).2 hs).mpr (by rwa [latGram_symmetrizedCartan_comm])
    exact ⟨s, memB_maskOf (closedOK_spec hcl r hr s hadj ((hphi s hs).mpr hsz)), hys⟩
  have hiff : ∀ x y, latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f) x y →
      (x ∈ rootsOf τ H mem ↔ y ∈ rootsOf τ H mem) := by
    intro x y hl
    induction hl with
    | rel x y h =>
      exact ⟨hstep x y h.2.2 h.2.1,
        hstep y x (by rw [latGram_symmetrizedCartan_comm]; exact h.2.2) h.1⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have hLk := linkedOK_aux h (Q := fun r => r ∈ mem) (fun r hr => ⟨(hsub r hr).2, (hin r hr).1⟩)
    mem 0 hlk (fun r hr => hr) (fun s hs => by rw [memB_zero] at hs; exact absurd hs (by simp))
    (fun s t hs => by rw [memB_zero] at hs; exact absurd hs (by simp))
  have hpm : ∀ r ∈ mem, latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f)
      (rowZ τ H r) (-rowZ τ H r) := fun r hr =>
    Relation.EqvGen.rel _ _ ⟨(hin r hr).1, (hin r hr).2, by
      rw [latGram_neg_right]
      exact neg_ne_zero.mpr (latGram_rowZ_ne h (hsub r hr).2)⟩
  have hα0 : latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f) α (rowZ τ H r0) := by
    rcases hα with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.symm _ _ (hpm r0 hr0)
  ext β
  refine ⟨fun hβ => (hiff _ _ hβ).mp ⟨r0, hr0, hα⟩, ?_⟩
  rintro ⟨s, hs, hβs⟩
  have h1 := Relation.EqvGen.trans _ _ _ hα0 (hLk r0 s (Or.inr hr0) (Or.inr hs))
  rcases hβs with rfl | rfl
  · exact h1
  · exact Relation.EqvGen.trans _ _ _ h1 (hpm s hs)

end Comp

section Kinds

variable {τ : Tag} {p : ℕ} {H : Hd}

theorem three_le_finrank_of_tri {n : ℕ} {F : Type*} [Field F] {W : Submodule F (Fin n → F)}
    {a b c : Fin n → F} {i1 i2 i3 : Fin n} (ha : a i1 ≠ 0) (hb : b i2 ≠ 0) (hc : c i3 ≠ 0)
    (hb1 : b i1 = 0) (hc1 : c i1 = 0) (hc2 : c i2 = 0) (haW : a ∈ W) (hbW : b ∈ W) (hcW : c ∈ W) :
    3 ≤ Module.finrank F W := by
  refine card_le_finrank_of_tri ![a, b, c] ![i1, i2, i3] (fun j => ?_) (fun i j hij => ?_) W
    (fun j => ?_)
  · fin_cases j <;> assumption
  · fin_cases i <;> fin_cases j <;> simp_all <;> contradiction
  · fin_cases j <;> assumption

theorem kind0_finrank (hp : p.Prime) {mode : ℕ} (h : tagHdOK τ p mode H = true) {mem : List ℕ}
    (hmem : ∀ r ∈ mem, r < H.np) (h7 : ∀ r < H.np, ∀ j < H.n, rtC H r j ≤ 7)
    {v1 q1 v2 q2 v3 q3 : ℕ} (hk : kerOK H mem v1 q1 v2 q2 v3 q3 = true) :
    3 ≤ Module.finrank (ZMod p)
      ↥((⊤ : Submodule (ZMod p) (Fin τ.rank → ZMod p)) ⊓ annSub p (rootsOf τ H mem)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hn, -⟩ := tagHdOK_basic h
  unfold kerOK kerVec at hk
  simp only [andB_eq_true, notB_eq_true, Nat.blt_eq] at hk
  obtain ⟨⟨hr1, -, hk1, hq1, hz1⟩, ⟨hr2, -, hk2, hq2, hz2⟩, ⟨hr3, -, hk3, hq3, hz3⟩, h21, h31,
    h32⟩ := hk
  have hann : ∀ v, red H v = true → allKilled H mem v = true →
      vecZ p τ.rank v ∈ (⊤ ⊓ annSub p (rootsOf τ H mem) :
        Submodule (ZMod p) (Fin τ.rank → ZMod p)) := by
    intro v hv hkv
    refine ⟨Submodule.mem_top, fun β hβ => ?_⟩
    obtain ⟨r, hr, hβ⟩ := hβ
    have hz := (killed_iff h (hmem r hr) (h7 r (hmem r hr)) hv).mp (allKilled_spec hkv r hr)
    rcases hβ with rfl | rfl
    · exact hz
    · rw [latChar_neg, hz]
      exact neg_zero
  have hne : ∀ {v q : ℕ} (hq : q < H.n), zL H v q = false → vecZ p τ.rank v ⟨q, by omega⟩ ≠ 0 :=
    fun hq hz h0 => Bool.eq_false_iff.mp hz ((vecZ_apply_eq_zero h _ _).mp h0)
  exact three_le_finrank_of_tri (hne hq1 hz1) (hne hq2 hz2) (hne hq3 hz3)
    ((vecZ_apply_eq_zero h _ ⟨q1, by omega⟩).mpr h21)
    ((vecZ_apply_eq_zero h _ ⟨q1, by omega⟩).mpr h31)
    ((vecZ_apply_eq_zero h _ ⟨q2, by omega⟩).mpr h32) (hann _ hr1 hk1) (hann _ hr2 hk2)
    (hann _ hr3 hk3)

theorem kind1_facts (hp : p.Prime) (h : tagHdOK τ p 0 H = true) {a : ℕ} (ha : red H a = true)
    {mem : List ℕ} (hmem : ∀ r ∈ mem, r < H.np) {R : List (ℕ × ℕ × List ℕ)}
    (hR : RowsOK H a mem [] R) (hlen : dimV H ≤ R.length + 1) :
    ∃ S : Submodule (ZMod p) (Fin τ.rank → ZMod p), S ≤ ⊤ ∧
      S ≤ Submodule.span (ZMod p) (insert (vecZ p τ.rank a)
        (((⊤ : Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Set (Fin τ.rank → ZMod p)) ∩
          latEigenCoroot p τ.symmetrizedCartan 1 (rootsOf τ H mem))) ∧
      Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) (Fin τ.rank → ZMod p)) ≤
        Module.finrank (ZMod p) S + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hm, hn, -⟩ := tagHdOK_basic h
  have htw : tw H = false := by
    rw [tw, hm]
    rfl
  obtain ⟨hR1, -, hR3⟩ := rowsOK_tri hR
  have hcomb := combo_spec h ha hmem (T := Submodule.span (ZMod p) (insert (vecZ p τ.rank a)
      (((⊤ : Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Set (Fin τ.rank → ZMod p)) ∩
        latEigenCoroot p τ.symmetrizedCartan 1 (rootsOf τ H mem))))
    (Submodule.subset_span (Set.mem_insert _ _)) (fun r hr => Submodule.subset_span
      (Set.mem_insert_of_mem _ ⟨Submodule.mem_top, cor_mem_eigen h (hmem r hr)
        ⟨r, hr, Or.inl rfl⟩⟩))
  have hmemR : ∀ i : Fin R.length, R.getD i (0, 0, []) ∈ R := fun i => by
    rw [List.getD_eq_getElem _ _ i.2]
    exact List.getElem_mem i.2
  let v : Fin R.length → Fin τ.rank → ZMod p := fun i => vecZ p τ.rank (R.getD i (0, 0, [])).1
  let c : Fin R.length → Fin τ.rank := fun i =>
    ⟨(R.getD i (0, 0, [])).2.1, by have := (hR1 _ (hmemR i)).2.2.1; omega⟩
  refine ⟨Submodule.span (ZMod p) (Set.range v), le_top, Submodule.span_le.mpr ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    obtain ⟨h1, h2, -, -⟩ := hR1 _ (hmemR i)
    change vecZ p τ.rank (R.getD i (0, 0, [])).1 ∈ _
    rw [h1]
    exact (hcomb _ h2).2
  · have hli := card_le_finrank_of_tri v c
      (fun j h0 => Bool.eq_false_iff.mp (hR1 _ (hmemR j)).2.2.2
        ((vecZ_apply_eq_zero h _ _).mp h0))
      (fun i j hij => (vecZ_apply_eq_zero h _ _).mpr (hR3 i j hij j.2))
      (Submodule.span (ZMod p) (Set.range v)) (fun i => Submodule.subset_span ⟨i, rfl⟩)
    rw [finrank_top, Module.finrank_fin_fun]
    have hd : dimV H = H.n := by
      unfold dimV
      rw [htw]
    omega

theorem closed_W {M : Set (Fin τ.rank → ZMod p)}
    (hM : ∀ i, ∀ x ∈ M, cowAct (CFSG.LieType.Chevalley.simple τ i) x ∈ M) :
    ∀ u : WeylGroup τ, ∀ x ∈ M, cowAct u x ∈ M := by
  intro u
  have hu : u ∈ Subgroup.closure (Set.range (CFSG.LieType.Chevalley.simple τ)) := by
    rw [(coxeterSystem τ).subgroup_closure_range_simple]
    exact Subgroup.mem_top u
  induction hu using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hM i
  | inv_mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [simple_inv]
    exact hM i
  | one =>
    intro x hx
    rw [cowAct_one]
    exact hx
  | mul x y _ _ hx hy =>
    intro z hz
    rw [cowAct_mul]
    exact hx _ (hy z hz)

@[expose] def vset (τ : Tag) (p : ℕ) (l : List ℕ) : Set (Fin τ.rank → ZMod p) :=
  {x | ∃ e ∈ l, vecZ p τ.rank e = x}

theorem lm_planeFree (h : tagHdOK τ p 0 H = true) {mask : ℕ} (hlm : LMFacts H mask) :
    ∃ ents : List ℕ, (∀ x, red H x = true → (inM H mask x = true ↔ x ∈ ents)) ∧
      (∀ u : WeylGroup τ, ∀ x ∈ vset τ p ents, cowAct u x ∈ vset τ p ents) ∧
      ∃ R, PlaneFree 1 (vset τ p ents) R := by
  obtain ⟨-, hm, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have hp16' : H.p ≤ 65536 := by omega
  have htw : tw H = false := by
    rw [tw, hm]
    rfl
  obtain ⟨reps, ents, ⟨hmask, hok, hreps, hch⟩, hcl, hnp⟩ := hlm
  have hred : ∀ e ∈ ents, red H e = true := fun e he => ((vecOK_iff _ _).mp (hok e he)).1
  have hin : ∀ x, red H x = true → (inM H mask x = true ↔ x ∈ ents) := fun x hx => by
    rw [hmask]
    exact ⟨mem_of_inM_maskL hpos hred hx, inM_maskL_of_mem H⟩
  have hclose : ∀ e ∈ ents, ∀ g < ngens H, inM H mask (letter H g e) = true := by
    clear hreps hch hnp hok hred hin hmask
    induction ents with
    | nil => exact fun e he => absurd he (by simp)
    | cons v ents ih =>
      intro e he
      obtain ⟨h1, h2⟩ := (andB_eq_true _ _).mp hcl
      rcases List.mem_cons.mp he with rfl | he
      · exact allN_eq_true.mp h1
      · exact ih h2 e he
  have hng : ngens H = τ.rank := by
    unfold ngens
    rw [htw]
    exact hn
  have hsimp : ∀ i, ∀ x ∈ vset τ p ents,
      cowAct (CFSG.LieType.Chevalley.simple τ i) x ∈ vset τ p ents := by
    rintro i _ ⟨e, he, rfl⟩
    have hl := hclose e he i (by rw [hng]; exact i.2)
    obtain ⟨hv, -⟩ := vecZ_letter_split h (hred e he) i
    refine ⟨letter H i e, (hin _ (red_letter hpos hp16' _ _)).mp hl, ?_⟩
    rw [hv, tcLetterElt, dif_pos i.2]
  have hW := closed_W hsimp
  refine ⟨ents, hin, hW, vset τ p reps, ⊤, fun u _ => commutesPi_perm_one u, ?_,
    fun u _ e he => hW u e he, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hreps r hr, rfl⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨w, hw⟩ := chainOK_word hpos hp16' hch hred e he
    exact ⟨tcWordElt τ w, Submonoid.mem_top _, word H w e, hw,
      (vecZ_word_split h w (hred e he)).1⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨e, he, rfl⟩
    have hr' := hred r (hreps r hr)
    have he' := hred e he
    obtain ⟨t, ht⟩ := hnp r hr e he
    unfold npItem at ht
    cases htp : Nat.blt t H.p
    · rw [htp] at ht
      dsimp only at ht
      simp only [andB_eq_true, notB_eq_true, Nat.blt_eq] at ht
      obtain ⟨hlt, hx0, hxm⟩ := ht
      have hlt' : t < H.p + H.p * H.p := hlt
      change inM H mask (modL H.p H.n ((t - H.p) / H.p * r + (t - H.p) % H.p * e)) = false at hxm
      have hA : (t - H.p) / H.p < 16 := by
        have : (t - H.p) / H.p < H.p := by
          rw [Nat.div_lt_iff_lt_mul hpos]
          rcases Nat.lt_or_ge t H.p with h4 | h4
          · rw [Nat.sub_eq_zero_of_le h4.le]
            exact Nat.mul_pos hpos hpos
          · exact Nat.sub_lt_left_of_lt_add h4 hlt'
        omega
      have hC : (t - H.p) % H.p < 16 := by
        have := Nat.mod_lt (t - H.p) hpos
        omega
      have hv := vecZ_modL_lin h hr' he' hA hC
      refine Or.inr ⟨(((t - H.p) / H.p : ℕ) : ZMod p), (((t - H.p) % H.p : ℕ) : ZMod p), ?_, ?_⟩
      · rw [← hv]
        exact vecZ_ne_zero h (red_modL hpos hp16' _) (Nat.ne_of_beq_eq_false hx0)
      · rw [← hv]
        rintro ⟨e', he'', hee⟩
        have := vecZ_inj h (hred e' he'') (red_modL hpos hp16' _) hee
        have h1 := (hin e' (hred e' he'')).mpr he''
        rw [this] at h1
        rw [h1] at hxm
        exact absurd hxm (by simp)
    · rw [htp] at ht
      have htp' : t < 16 := by
        have := Nat.blt_eq.mp htp
        omega
      have he2 : e = modL H.p H.n (t * r + 0 * r) := by
        rw [zero_mul, add_zero]
        exact Nat.eq_of_beq_eq_true ht
      refine Or.inl ⟨(t : ZMod p), ?_⟩
      rw [he2, vecZ_modL_lin h hr' hr' htp' (by norm_num)]
      simp

theorem normal_lt (hτ : tgOK τ = true) {μ : Fin τ.rank → ℤ}
    (hμ : (kacOf τ).IsNormal p μ) (hp16 : p < 16) : ∀ i, μ i < 65536 := by
  intro i
  have hθ : 1 ≤ (kacOf τ).θ i := by
    have hpos : ∀ t ∈ pkTheta τ, 0 < t := by
      cases τ <;> simp [tgOK] at hτ <;> decide
    have := hpos ((kacOf τ).θ i).toNat (by rw [pkTheta_eq hτ]; simp)
    omega
  have hle : (kacOf τ).θ i * μ i ≤ (kacOf τ).θ ⬝ᵥ μ := by
    unfold dotProduct
    exact Finset.single_le_sum (f := fun j => (kacOf τ).θ j * μ j)
      (fun j _ => mul_nonneg ((kacOf τ).θ_nonneg j) (hμ.1 j)) (Finset.mem_univ i)
  have h1 : μ i ≤ (kacOf τ).θ i * μ i := le_mul_of_one_le_left (hμ.1 i) hθ
  have h2 := hμ.2
  omega

end Kinds

theorem pkSplit_caseFacts {τ : Tag} {p : ℕ} (hp : p.Prime) {D : List ℕ}
    (hc : pkCheck (pkTheta τ) D = true) (hh : pkHead τ.rootCertificate.roots D = true)
    (ht : pkTag τ p 0 D = true) :
    ∀ μ : Fin τ.rank → ℤ, (kacOf τ).IsNormal p μ → modP p μ ≠ 0 →
      ∀ O : Set (Fin τ.rank → ℤ),
        IsCompOrbit τ.symmetrizedCartan 1 (latPhi {α | IsRoot τ α} p (modP p μ)) O →
        CaseFacts p 1 ⊤ (modP p μ) O := by
  intro μ hμ hμ0 O hO
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, s, hH, hD⟩ := hdK_spec ht
  have h : tagHdOK τ p 0 H = true := hH
  obtain ⟨hτ, hm, hn, hpp, hp3, hp16, hnp, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have hp16' : H.p ≤ 65536 := by omega
  have hnp0 : 0 < H.np := by
    rw [hnp]
    cases τ <;> decide
  obtain ⟨hroot, hall⟩ := rows_roots hD hnp0 hn hh
  have h7 := rtC_le hD hnp0 hh
  have htw : tw H = false := by
    rw [tw, hm]
    rfl
  obtain ⟨ms, hms, tg, htab, hcase⟩ := pkCheck_walk hD hc
  have hpts : pkPts H (pkTheta τ) = alcNZ p τ.rank (pkTheta τ) := by
    unfold pkPts
    rw [htw, hpp, hn]
  have hnorm : ∀ ν : Fin τ.rank → ℤ, (kacOf τ).IsNormal p ν → modP p ν ≠ 0 →
      ∃ b, red H b = true ∧ b ∈ pkPts H (pkTheta τ) ∧ vecZ p τ.rank b = modP p ν := by
    intro ν hν hν0
    have hvz := vecZ_modL_packPt (p := p) hν.1 (normal_lt hτ hν (by omega))
    have hb0 : modL p τ.rank (packPt ν) ≠ 0 := fun h0 => hν0 (by
      rw [← hvz, h0, vecZ_zero])
    refine ⟨modL p τ.rank (packPt ν), ?_, hpts ▸ alcNZ_complete hτ hν hb0, hvz⟩
    have e : ∀ x, modL p τ.rank x = modL H.p H.n x := fun x => by rw [hpp, hn]
    rw [e]
    exact red_modL hpos hp16' _
  obtain ⟨a, hared, ha, hvz⟩ := hnorm μ hμ hμ0
  obtain ⟨phi, hphiOK, cls, hcls, hcov⟩ := hcase a ha
  have hphi1 : phi < 2 ^ H.np ∧ allN H.np (fun r => beqB (memB phi r) (killed H r a)) = true := by
    have := (andB_eq_true _ _).mp hphiOK
    refine ⟨?_, this.2⟩
    have h1 := Nat.blt_eq.mp this.1
    change phi < 1 <<< H.np at h1
    rwa [Nat.shiftLeft_eq, one_mul] at h1
  have hphi : ∀ r < H.np, memB phi r = true ↔
      latChar p (vecZ p τ.rank a) (rowZ τ H r) = 0 := by
    intro r hr
    have hb := allN_eq_true.mp hphi1.2 r hr
    rw [← killed_iff h hr (h7 r hr) hared]
    cases h1 : memB phi r <;> cases h2 : killed H r a <;> rw [h1, h2] at hb <;>
      simp_all [beqB, notB]
  have hphinp : ∀ r, memB phi r = true → r < H.np := by
    intro r hr
    by_contra hge
    have h1 : phi < 2 ^ r := lt_of_lt_of_le hphi1.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [memB_iff, Nat.testBit_eq_false_of_lt h1] at hr
    exact absurd hr (by simp)
  obtain ⟨α, hαΦ, rfl⟩ := hO
  rw [← hvz] at hαΦ ⊢
  obtain ⟨r0, hr0, hα⟩ := hall α hαΦ.1
  have hr0z : latChar p (vecZ p τ.rank a) (rowZ τ H r0) = 0 := by
    have := hαΦ.2
    rcases hα with rfl | rfl
    · exact this
    · rw [latChar_neg] at this
      exact neg_eq_zero.mp this
  obtain ⟨c, hc, hr0c⟩ := hcov r0 ((hphi r0 hr0).mpr hr0z)
  obtain ⟨hland, hcl, hlk, hkind⟩ := hcls c hc
  have hsub : ∀ r ∈ c.1, memB phi r = true ∧ r < H.np := fun r hr => by
    have h1 := memB_maskOf_of_mem hr
    rw [← hland, memB_land] at h1
    exact ⟨h1.2, hphinp r h1.2⟩
  have hO : {β | ∃ k : ℕ, latLinked τ.symmetrizedCartan
      (latPhi {α | IsRoot τ α} p (vecZ p τ.rank a)) ((latPerm 1)^[k] α) β} = rootsOf τ H c.1 := by
    rw [← comp_eq_rootsOf h hroot hall hphi hsub hcl hlk hr0c hα]
    ext β
    simp only [Set.mem_setOf_eq, latPerm_one_iterate]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  rw [hO]
  have hmem : ∀ r ∈ c.1, r < H.np := fun r hr => (hsub r hr).2
  rcases hkind with ⟨-, v1, q1, v2, q2, v3, q3, hk⟩ | ⟨-, R, hlen, hR⟩ | ⟨mask, hmk, hwit⟩
  · exact Or.inl (kind0_finrank hp h hmem h7 hk)
  · exact Or.inr (Or.inl (kind1_facts hp h hared hmem hR hlen))
  · refine Or.inr (Or.inr ?_)
    have hlm : LMFacts H mask := by
      rcases hmk with ⟨-, rfl⟩ | ⟨-, k, rfl⟩
      · exact lmFacts_zero H
      · rcases nthM_mem ms k with h0 | h0
        · rw [h0]
          exact lmFacts_zero H
        · exact hms _ h0
    obtain ⟨ents, hin, hW, R, hPF⟩ := lm_planeFree h hlm
    refine ⟨vset τ p ents, R, hPF, fun t _ ht0 htM => ?_⟩
    obtain ⟨w0, ν, hw0, hν⟩ :=
      (kacOf τ).exists_normal p hp.pos (fun i => (((t i).val : ℕ) : ℤ))
    have h1 : cowAct w0⁻¹ (modP p ν) = t := by
      funext i
      have h2 := hw0 (Pi.single i 1)
      simp only [cowAct, inv_inv]
      have hc' : latChar p (modP p ν) (w0 • Pi.single i 1) =
          (((w0 • (Pi.single i 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν : ℤ) : ZMod p) := by
        simp [latChar, modP, dotProduct]
      rw [hc']
      have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
      rw [Int.cast_sub, sub_eq_zero] at h3
      rw [h3]
      simp [single_dotProduct]
    have hν0 : modP p ν ≠ 0 := by
      intro h0
      apply ht0
      rw [← h1, h0]
      exact cowAct_zero _
    obtain ⟨b, hbred, hb, hvb⟩ := hnorm ν hν hν0
    have htg : ∃ t' ∈ tg, red H t' = true ∧ ∃ g : WeylGroup τ,
        vecZ p τ.rank t' = cowAct g (vecZ p τ.rank b) := by
      rcases htab with rfl | ⟨hall', hw⟩
      · exact ⟨b, hb, hbred, 1, (cowAct_one _).symm⟩
      · obtain ⟨w, hw'⟩ := hw b hb
        have hT : ∀ v ∈ tg, red H v = true := fun v hv =>
          ((vecOK_iff _ _).mp ((allVec_iff H tg).mp hall' v hv)).1
        obtain ⟨h5, h6⟩ := vecZ_word_split h w hbred
        exact ⟨word H w b, mem_of_inM_maskL hpos hT h6 hw', h6, tcWordElt τ w, h5⟩
    obtain ⟨t', ht'tg, ht'red, g, hg⟩ := htg
    have ht : t = cowAct (w0⁻¹ * g⁻¹) (vecZ p τ.rank t') := by
      rw [hg, cowAct_mul, cowAct_inv_cowAct, hvb, h1]
    have hm' : inM H mask t' = false := by
      cases hmt : inM H mask t'
      · rfl
      · exfalso
        apply htM
        rw [ht]
        exact hW _ _ ⟨t', (hin t' ht'red).mp hmt, rfl⟩
    obtain ⟨ps, w2, hps, hc0, hw2⟩ := hwit t' ht'tg hm'
    have hcomb := combo_spec h hared hmem (T := Submodule.span (ZMod p) (insert (vecZ p τ.rank a)
        (((⊤ : Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Set (Fin τ.rank → ZMod p)) ∩
          latEigenCoroot p τ.symmetrizedCartan 1 (rootsOf τ H c.1))))
      (Submodule.subset_span (Set.mem_insert _ _)) (fun r hr => Submodule.subset_span
        (Set.mem_insert_of_mem _ ⟨Submodule.mem_top, cor_mem_eigen h (hmem r hr)
          ⟨r, hr, Or.inl rfl⟩⟩)) ps hps
    obtain ⟨h8, h9⟩ := vecZ_word_split h w2 hcomb.1
    refine ⟨vecZ p τ.rank (combo H a ps), hcomb.2, vecZ_ne_zero h hcomb.1 hc0,
      w0⁻¹ * g⁻¹ * tcWordElt τ w2, commutesPi_perm_one _, ?_⟩
    rw [cowAct_mul, ← h8, hw2, ← ht]

end CFSG.KC.GGToral
