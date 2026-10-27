module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Enum
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Fix

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem bsearchAux_complete {A : Array ℕ} (hs : sortedK A = true) {k : ℕ} :
    ∀ (fuel lo hi : ℕ), hi ≤ A.size → hi - lo < 2 ^ fuel → ∀ i, lo ≤ i → i < hi →
      A.getD i 0 = k → ∃ j, bsearchAux A k fuel lo hi = some j ∧ j < A.size ∧ A.getD j 0 = k
  | 0, lo, hi, _, hlt, i, hli, hih, _ => by
    simp at hlt
    omega
  | fuel + 1, lo, hi, hhi, hlt, i, hli, hih, hk => by
    have hlh : lo < hi := lt_of_le_of_lt hli hih
    have hmono : ∀ a b, a ≤ b → b < A.size → A.getD a 0 ≤ A.getD b 0 := fun a b hab hb => by
      rcases Nat.eq_or_lt_of_le hab with rfl | h
      · exact le_rfl
      · exact (Enum.lt_of_sortedK hs h hb).le
    have h2 : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
    rw [bsearchAux, ite_eq_left hlh]
    simp only
    by_cases h1 : A.getD ((lo + hi) / 2) 0 < k
    · rw [ite_eq_left h1]
      refine bsearchAux_complete hs fuel _ hi hhi (by omega) i ?_ hih hk
      by_contra hc
      have := hmono i ((lo + hi) / 2) (by omega) (by omega)
      omega
    · rw [ite_eq_right h1]
      by_cases h3 : A.getD ((lo + hi) / 2) 0 = k
      · rw [ite_eq_left h3]
        exact ⟨_, rfl, by omega, h3⟩
      · rw [ite_eq_right h3]
        refine bsearchAux_complete hs fuel lo _ (by omega) (by omega) i hli ?_ hk
        by_contra hc
        have := hmono ((lo + hi) / 2) i (by omega) (by omega)
        omega

theorem memK_of_mem {A : Array ℕ} (hs : sortedK A = true) (hsize : A.size < 2 ^ 64) {k : ℕ}
    {i : ℕ} (hi : i < A.size) (hk : A.getD i 0 = k) : memK A k = true := by
  obtain ⟨j, hj, hjs, hjk⟩ := bsearchAux_complete hs 64 0 A.size le_rfl (by omega) i
    (Nat.zero_le _) hi hk
  unfold memK
  rw [hj]
  simp [hjs, hjk]

@[expose] def fpowAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, b, n, acc =>
    if n = 0 then acc else fpowAux f (mulK b b) (n / 2) (if n % 2 = 1 then mulK acc b else acc)

@[expose] def fpowK (a n : ℕ) : ℕ := fpowAux 64 a n idK

theorem toMatK_fpowAux : ∀ (f b n acc : ℕ), n < 2 ^ f →
    toMatK (fpowAux f b n acc) = toMatK acc * toMatK b ^ n
  | 0, b, n, acc, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [fpowAux]
  | f + 1, b, n, acc, h => by
    rw [fpowAux]
    by_cases h0 : n = 0
    · subst h0
      simp
    rw [ite_eq_right h0, toMatK_fpowAux f _ _ _ (by rw [pow_succ] at h; omega), toMatK_mulK, ← sq,
      ← pow_mul]
    by_cases h1 : n % 2 = 1
    · rw [ite_eq_left h1, toMatK_mulK, mul_assoc, ← pow_succ']
      congr 2
      omega
    · rw [ite_eq_right h1]
      congr 2
      omega

theorem toMatK_fpowK (a : ℕ) {n : ℕ} (hn : n < 2 ^ 64) : toMatK (fpowK a n) = toMatK a ^ n := by
  rw [fpowK, toMatK_fpowAux 64 a n idK hn, toMatK_idK, one_mul]

theorem Rep.fpow {a : ℕ} {x : GL12} (ha : Rep a x) {n : ℕ} (hn : n < 2 ^ 64) :
    Rep (fpowK a n) (x ^ n) := by
  rw [Rep, toMatK_fpowK a hn, ha, Units.val_pow_eq_pow_val]

theorem fpowK_lt (a n : ℕ) : fpowK a n < 2 ^ 144 := by
  unfold fpowK
  suffices h : ∀ f b n acc, acc < 2 ^ 144 → fpowAux f b n acc < 2 ^ 144 from h _ _ _ _ idK_lt
  intro f
  induction f with
  | zero => intro b n acc h; simpa [fpowAux] using h
  | succ f ih =>
    intro b n acc h
    rw [fpowAux]
    split_ifs
    · exact h
    · exact ih _ _ _ (mulK_lt _ _)
    · exact ih _ _ _ h

@[expose] noncomputable def keyOfMat (M : Mat12) : ℕ := keyOf (matBits 12 12 M)

theorem toMatK_keyOfMat (M : Mat12) : toMatK (keyOfMat M) = M := by
  rw [keyOfMat, toMatK_keyOf, toMat_matBits]

theorem keyOfMat_lt (M : Mat12) : keyOfMat M < 2 ^ 144 := keyOf_lt _

theorem rep_keyOfMat (x : GL12) : Rep (keyOfMat x) x := toMatK_keyOfMat _

@[expose] def fixCount (k : ℕ) : ℕ := ((Finset.range 4096).filter fun v => mulVecK k v = v).card

theorem card_fixM_eq (k : ℕ) : Nat.card (fixM (toMatK k)) = fixCount k := by
  rw [fixCount, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun v => ⟨vecBits v.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (vecBits_lt _), ?_⟩⟩
      invFun := fun n => ⟨toVec 12 n.1, ?_⟩
      left_inv := fun v => Subtype.ext (toVec_vecBits _)
      right_inv := fun n => Subtype.ext (vecBits_toVec
        (Finset.mem_range.1 (Finset.mem_filter.1 n.2).1)) }
  · apply toVec_injOn (mulVecK_lt _ _) (vecBits_lt _)
    rw [toVec_mulVecK, toVec_vecBits]
    exact v.2
  · have h := (Finset.mem_filter.1 n.2).2
    show toMatK k *ᵥ toVec 12 n.1 = toVec 12 n.1
    rw [← toVec_mulVecK, h]

namespace Enum

variable {gs : Array (ℕ × ℕ)} {E : Enum}

theorem rep_of_memK (h : enumOK gs E = true) {k : ℕ} (hk : memK E.keys k = true) :
    ∃ x ∈ grpOf gs, Rep k x := by
  obtain ⟨i, hi, rfl⟩ := exists_of_memK hk
  exact exists_mem h i hi

theorem mem_of_memK (h : enumOK gs E = true) {k : ℕ} (hk : memK E.keys k = true) {x : GL12}
    (hx : Rep k x) : x ∈ grpOf gs := by
  obtain ⟨y, hy, hry⟩ := rep_of_memK h hk
  rwa [hry.unique hx] at hy

theorem memK_of_mem' (h : enumOK gs E = true) (hsz : E.keys.size < 2 ^ 64) {x : GL12}
    (hx : x ∈ grpOf gs) {k : ℕ} (hk : Rep k x) (hk' : k < 2 ^ 144) : memK E.keys k = true := by
  obtain ⟨i, hi, hri⟩ := exists_key h hx
  exact memK_of_mem (of_enumOK h).2.1 hsz hi (hri.key_unique hk (key_lt h hi) hk')

end Enum

@[expose] def gensIn (gs : Array (ℕ × ℕ)) (E : Enum) : Bool := gs.all fun g => memK E.keys g.1

theorem grpOf_le_of_gensIn {gs hs : Array (ℕ × ℕ)} {E : Enum} (hg : gensOK gs = true)
    (hE : enumOK hs E = true) (h : gensIn gs E = true) : grpOf gs ≤ grpOf hs := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  simp only [gensIn, Array.all_eq_true] at h
  have hk : memK E.keys (genK gs j).1 = true := by
    rw [genK, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
    exact h j hj
  exact Enum.mem_of_memK hE hk (rep_genG hg j)

@[expose] def commGens (gs : Array (ℕ × ℕ)) (k : ℕ) : Bool :=
  gs.all fun g => mulK k g.1 == mulK g.1 k

theorem commute_of_commGens {gs : Array (ℕ × ℕ)} (hg : gensOK gs = true) {k : ℕ} {y : GL12}
    (hy : Rep k y) (h : commGens gs k = true) : ∀ x ∈ grpOf gs, y * x = x * y := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    simp only [commGens, Array.all_eq_true, beq_iff_eq] at h
    have hkj : mulK k (genK gs j).1 = mulK (genK gs j).1 k := by
      rw [genK, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
      exact h j hj
    have h1 := hy.mul (rep_genG hg j)
    have h2 := (rep_genG hg j).mul hy
    rw [hkj] at h1
    exact h1.unique h2
  | one => rw [mul_one, one_mul]
  | mul a b _ _ ha hb =>
    rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | inv a _ ha =>
    calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
      _ = a⁻¹ * (y * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * y := by group

theorem key_eq_of_mul {a b : ℕ} {x y : GL12} (ha : Rep a x) (hb : Rep b y) (h : x * y = y * x) :
    mulK a b = mulK b a :=
  (ha.mul hb).key_unique (h ▸ hb.mul ha) (mulK_lt _ _) (mulK_lt _ _)

theorem genK_eq {gs : Array (ℕ × ℕ)} {j : ℕ} (hj : j < gs.size) : genK gs j = gs[j] := by
  rw [genK, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]

theorem genG_mem_grpOf {gs : Array (ℕ × ℕ)} {j : ℕ} (hj : j < gs.size) : genG gs j ∈ grpOf gs :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem grpOf_le_of_reps {gs : Array (ℕ × ℕ)} (hg : gensOK gs = true) {S : Subgroup GL12}
    (h : ∀ j < gs.size, ∃ x ∈ S, Rep (genK gs j).1 x) : grpOf gs ≤ S := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨x, hx, hr⟩ := h j hj
  rwa [(rep_genG hg j).unique hr]

@[expose] def centerCheck (gs : Array (ℕ × ℕ)) (E : Enum) (zs : List ℕ) : Bool :=
  E.keys.all fun k => !(commGens gs k) || zs.contains k

theorem exists_of_centerCheck {gs : Array (ℕ × ℕ)} {E : Enum} {zs : List ℕ}
    (hE : enumOK gs E = true) (h : centerCheck gs E zs = true) {z : GL12} (hz : z ∈ grpOf gs)
    (hc : ∀ x ∈ grpOf gs, z * x = x * z) : ∃ k ∈ zs, Rep k z := by
  have hg := (Enum.of_enumOK hE).1
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hz
  refine ⟨_, ?_, hr⟩
  simp only [centerCheck, Array.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h
  rcases h i hi with h1 | h1
  · exfalso
    have : commGens gs (E.keys.getD i 0) = true := by
      simp only [commGens, Array.all_eq_true, beq_iff_eq]
      intro j hj
      have := key_eq_of_mul hr (rep_genG hg j) (hc _ (genG_mem_grpOf hj))
      rwa [genK_eq hj] at this
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [this] at h1
    exact absurd h1 (by decide)
  · rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

theorem getD_mem {A : Array ℕ} {i : ℕ} (hi : i < A.size) : A.getD i 0 = A[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

@[expose] def centInCheck (E : Enum) (b : ℕ) (E₂ : Enum) : Bool :=
  E.keys.all fun k => mulK k b != mulK b k || memK E₂.keys k

theorem mem_of_centInCheck {gs gs₂ : Array (ℕ × ℕ)} {E E₂ : Enum} {b : ℕ}
    (hE : enumOK gs E = true) (hE₂ : enumOK gs₂ E₂ = true) (h : centInCheck E b E₂ = true)
    {x : GL12} (hx : x ∈ grpOf gs) {y : GL12} (hy : Rep b y) (hc : x * y = y * x) :
    x ∈ grpOf gs₂ := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hx
  simp only [centInCheck, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rcases h i hi with h1 | h1
  · rw [← getD_mem hi] at h1
    exact absurd (key_eq_of_mul hr hy hc) h1
  · rw [← getD_mem hi] at h1
    exact Enum.mem_of_memK hE₂ h1 hr

@[expose] def invFixCheck (E : Enum) (n : ℕ) : Bool :=
  E.keys.all fun k => mulK k k != idK || (decide (n ≤ (kerBasis k).length) && fixLB k (kerBasis k))

theorem fix_of_invFixCheck {gs : Array (ℕ × ℕ)} {E : Enum} {n : ℕ} (hE : enumOK gs E = true)
    (h : invFixCheck E n = true) {y : GL12} (hy : y ∈ grpOf gs) (hy2 : y * y = 1) :
    2 ^ n ≤ Nat.card (fixM (y : Mat12)) := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hy
  simp only [invFixCheck, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  have hsq : mulK (E.keys.getD i 0) (E.keys.getD i 0) = idK :=
    (hr.mul hr).key_unique (by rw [hy2]; exact rep_one) (mulK_lt _ _) idK_lt
  rcases h i hi with h1 | ⟨h1, h2⟩
  · rw [← getD_mem hi] at h1
    exact absurd hsq h1
  · rw [← getD_mem hi] at h1 h2
    rw [← fixM_of_rep hr]
    exact (Nat.pow_le_pow_right (by norm_num) h1).trans (fixLB_sound h2)

@[expose] def no8Check (E : Enum) : Bool :=
  E.keys.all fun k => fpowK k 8 != idK || fpowK k 4 == idK

theorem pow_four_of_no8Check {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true)
    (h : no8Check E = true) {y : GL12} (hy : y ∈ grpOf gs) (h8 : y ^ 8 = 1) : y ^ 4 = 1 := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hy
  simp only [no8Check, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h i hi with h1 | h1
  · rw [← getD_mem hi] at h1
    exact absurd ((hr.fpow (by norm_num)).key_unique (by rw [h8]; exact rep_one) (fpowK_lt _ _)
      idK_lt) h1
  · rw [← getD_mem hi] at h1
    exact (hr.fpow (n := 4) (by norm_num)).unique (by rw [h1]; exact rep_one)

theorem card_fixM_one : Nat.card (fixM ((1 : GL12) : Mat12)) = 2 ^ 12 := by
  have : fixM ((1 : GL12) : Mat12) = Set.univ := by
    ext v
    simp [fixM]
  rw [this, Nat.card_univ]
  simp [Nat.card_eq_fintype_card]

@[expose] def oneClassCheck (E : Enum) (tK : ℕ) : Bool :=
  E.keys.all fun s => mulK s s != idK || s == idK ||
    (decide (8 ≤ (kerBasis s).length) && fixLB s (kerBasis s)) ||
    E.keys.any fun y => mulK y tK == mulK s y

theorem conj_of_oneClassCheck {gs : Array (ℕ × ℕ)} {E : Enum} {tK : ℕ}
    (hE : enumOK gs E = true) (h : oneClassCheck E tK = true) {tb : GL12} (ht : Rep tK tb)
    {s : GL12} (hs : s ∈ grpOf gs) (hs2 : s * s = 1)
    (hfix : Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7) : ∃ y ∈ grpOf gs, s = y * tb * y⁻¹ := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hs
  simp only [oneClassCheck, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq, Array.any_eq_true] at h
  rcases h i hi with ((h1 | h1) | ⟨h1, h2⟩) | ⟨j, hj, h1⟩
  · rw [← getD_mem hi] at h1
    exact absurd ((hr.mul hr).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h1
  · rw [← getD_mem hi] at h1
    rw [h1] at hr
    have : s = 1 := hr.unique rep_one
    rw [this, card_fixM_one] at hfix
    norm_num at hfix
  · rw [← getD_mem hi] at h1 h2
    rw [← fixM_of_rep hr] at hfix
    have := (Nat.pow_le_pow_right (by norm_num) h1).trans (fixLB_sound h2)
    omega
  · rw [← getD_mem hi, ← getD_mem hj] at h1
    obtain ⟨y, hy, hry⟩ := Enum.exists_mem hE j hj
    refine ⟨y, hy, ?_⟩
    have e : y * tb = s * y := by
      have h3 := hry.mul ht
      rw [h1] at h3
      exact h3.unique (hr.mul hry)
    calc s = s * y * y⁻¹ := by group
      _ = y * tb * y⁻¹ := by rw [← e]

@[expose] def imgCheck (tK : ℕ) : Bool :=
  (List.range 4096).all fun v => mulVecK tK v != v ||
    (List.range 4096).any fun x => (mulVecK tK x ^^^ x) == v

theorem exists_of_imgCheck {tK : ℕ} (h : imgCheck tK = true) {v : Vec12}
    (hv : toMatK tK *ᵥ v = v) : ∃ x : Vec12, toMatK tK *ᵥ x + x = v := by
  simp only [imgCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.any_eq_true, beq_iff_eq] at h
  have hfix : mulVecK tK (vecBits v) = vecBits v := by
    apply toVec_injOn (mulVecK_lt _ _) (vecBits_lt _)
    rw [toVec_mulVecK, toVec_vecBits, hv]
  rcases h _ (vecBits_lt v) with h1 | ⟨x, -, hx⟩
  · exact absurd hfix h1
  · refine ⟨toVec 12 x, ?_⟩
    rw [← toVec_mulVecK, ← toVec_xor, hx, toVec_vecBits]

@[expose] def baseK (gs : Array (ℕ × ℕ)) : Array ℕ := gs.map (·.1)

@[expose] def baseG (gs : Array (ℕ × ℕ)) : Array GL12 := gs.map fun g => glOf g.1 g.2

theorem baseK_size (gs : Array (ℕ × ℕ)) : (baseK gs).size = (baseG gs).size := by
  simp [baseK, baseG]

theorem rep_base {gs : Array (ℕ × ℕ)} (hg : gensOK gs = true) (i : ℕ) :
    Rep ((baseK gs).getD i idK) ((baseG gs).getD i 1) := by
  by_cases hi : i < gs.size
  · have h1 : (baseK gs).getD i idK = (genK gs i).1 := by
      simp [baseK, genK, Array.getD_eq_getD_getElem?, hi]
    have h2 : (baseG gs).getD i 1 = genG gs i := by
      simp [baseG, genG, genK, Array.getD_eq_getD_getElem?, hi]
    rw [h1, h2]
    exact rep_genG hg i
  · have h1 : (baseK gs).getD i idK = idK := by
      simp [baseK, Array.getD_eq_getD_getElem?, hi]
    have h2 : (baseG gs).getD i 1 = 1 := by
      simp [baseG, Array.getD_eq_getD_getElem?, hi]
    rw [h1, h2]
    exact rep_one

theorem base_mem {gs : Array (ℕ × ℕ)} {S : Subgroup GL12}
    (h : ∀ j < gs.size, genG gs j ∈ S) (i : ℕ) : (baseG gs).getD i 1 ∈ S := by
  by_cases hi : i < gs.size
  · have h2 : (baseG gs).getD i 1 = genG gs i := by
      simp [baseG, genG, genK, Array.getD_eq_getD_getElem?, hi]
    rw [h2]
    exact h i hi
  · have h2 : (baseG gs).getD i 1 = 1 := by
      simp [baseG, Array.getD_eq_getD_getElem?, hi]
    rw [h2]
    exact one_mem S

theorem baseK_lt (gs : Array (ℕ × ℕ)) (h : (baseK gs).all (· < 2 ^ 144) = true) (i : ℕ) :
    (baseK gs).getD i idK < 2 ^ 144 := by
  by_cases hi : i < (baseK gs).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
    simp only [Array.all_eq_true, decide_eq_true_eq] at h
    exact h i hi
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact idK_lt

@[expose] def brayCheck (gs : Array (ℕ × ℕ)) (prog : List (ℕ × ℕ × ℕ)) (out tK : ℕ)
    (EC : Enum) : Bool :=
  let z := (runK (baseK gs) prog).getD out idK
  gensOK gs && (baseK gs).all (· < 2 ^ 144) && mulK z tK == mulK tK z && !(EC.keys.contains z)

theorem exists_of_brayCheck {gs cs : Array (ℕ × ℕ)} {prog : List (ℕ × ℕ × ℕ)} {out tK : ℕ}
    {EC : Enum} (hEC : enumOK cs EC = true) (h : brayCheck gs prog out tK EC = true)
    {S : Subgroup GL12} (hS : ∀ j < gs.size, genG gs j ∈ S) {tb : GL12} (ht : Rep tK tb) :
    ∃ z ∈ S, z * tb = tb * z ∧ z ∉ grpOf cs := by
  simp only [brayCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hg, hlt⟩, hc⟩, hn⟩ := h
  have hrep := runK_rep prog (baseK gs) (baseG gs) (baseK_size gs) (rep_base hg) out
  have hmem := runG_mem S prog (baseG gs) (base_mem hS) out
  have hzlt := runK_lt prog (baseK gs) (baseK_lt gs hlt) out
  refine ⟨_, hmem, ?_, Enum.not_mem hEC hzlt hrep hn⟩
  have h1 := hrep.mul ht
  rw [hc] at h1
  exact h1.unique (ht.mul hrep)

@[expose] def slpGens (gs : Array (ℕ × ℕ)) (prog : List (ℕ × ℕ × ℕ)) (outs : List ℕ) :
    Array (ℕ × ℕ) :=
  (outs.map fun o => ((runK (baseK gs) prog).getD o idK,
    fpowK ((runK (baseK gs) prog).getD o idK) 8191)).toArray

theorem grpOf_slpGens_le {gs : Array (ℕ × ℕ)} {prog : List (ℕ × ℕ × ℕ)} {outs : List ℕ}
    {S : Subgroup GL12} (hg : gensOK gs = true) (hS : ∀ j < gs.size, genG gs j ∈ S)
    (hg' : gensOK (slpGens gs prog outs) = true) : grpOf (slpGens gs prog outs) ≤ S := by
  refine grpOf_le_of_reps hg' fun j hj => ?_
  have hj' : j < outs.length := by simpa [slpGens] using hj
  refine ⟨(runG (baseG gs) prog).getD outs[j] 1, runG_mem S prog (baseG gs) (base_mem hS) _, ?_⟩
  have e : (genK (slpGens gs prog outs) j).1 = (runK (baseK gs) prog).getD outs[j] idK := by
    rw [genK_eq hj]
    simp [slpGens]
  rw [e]
  exact runK_rep prog (baseK gs) (baseG gs) (baseK_size gs) (rep_base hg) _

@[expose] def commCount (E : Enum) (s : ℕ) : ℕ :=
  ((Finset.range E.keys.size).filter fun i =>
    mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0)).card

theorem card_inf_centralizer_le_commCount {gs : Array (ℕ × ℕ)} {E : Enum}
    (hE : enumOK gs E = true) {s : GL12} {sK : ℕ} (hs : Rep sK s) :
    Nat.card ↥(grpOf gs ⊓ Subgroup.centralizer ({s} : Set GL12)) ≤ commCount E sK := by
  classical
  have hkey : ∀ x : ↥(grpOf gs ⊓ Subgroup.centralizer ({s} : Set GL12)),
      ∃ i < E.keys.size, Rep (E.keys.getD i 0) x := fun x => Enum.exists_key hE x.2.1
  choose f hf hfr using hkey
  rw [commCount, ← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun x => ⟨f x, Finset.mem_filter.2
    ⟨Finset.mem_range.2 (hf x), ?_⟩⟩) ?_
  · have hc : (x : GL12) * s = s * x := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    exact key_eq_of_mul (hfr x) hs hc
  · intro x y e
    have e' : f x = f y := congrArg Subtype.val e
    have := hfr y
    rw [← e'] at this
    exact Subtype.ext ((hfr x).unique this)

@[expose] def secondCheck (E : Enum) (tK uK n : ℕ) : Bool :=
  E.keys.all fun s => mulK s s != idK || s == idK ||
    (decide (8 ≤ (kerBasis s).length) && fixLB s (kerBasis s)) || decide (commCount E s < n) ||
    (E.keys.any fun y => mulK y tK == mulK s y) || (E.keys.any fun y => mulK y uK == mulK s y)

theorem conj_of_secondCheck {gs : Array (ℕ × ℕ)} {E : Enum} {tK uK n : ℕ}
    (hE : enumOK gs E = true) (h : secondCheck E tK uK n = true) {tb u : GL12} (ht : Rep tK tb)
    (hu : Rep uK u) {s : GL12} (hs : s ∈ grpOf gs) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hfix : Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7)
    (hn : n ≤ Nat.card ↥(grpOf gs ⊓ Subgroup.centralizer ({s} : Set GL12))) :
    ∃ y ∈ grpOf gs, s = y * tb * y⁻¹ ∨ s = y * u * y⁻¹ := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hs
  simp only [secondCheck, Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq, Array.any_eq_true] at h
  have hconj : ∀ {vK : ℕ} {v : GL12}, Rep vK v → ∀ j, j < E.keys.size →
      mulK (E.keys.getD j 0) vK = mulK (E.keys.getD i 0) (E.keys.getD j 0) →
        ∃ y ∈ grpOf gs, s = y * v * y⁻¹ := by
    intro vK v hv j hj h1
    obtain ⟨y, hy, hry⟩ := Enum.exists_mem hE j hj
    refine ⟨y, hy, ?_⟩
    have e : y * v = s * y := by
      have h3 := hry.mul hv
      rw [h1] at h3
      exact h3.unique (hr.mul hry)
    calc s = s * y * y⁻¹ := by group
      _ = y * v * y⁻¹ := by rw [← e]
  rcases h i hi with ((((h1 | h1) | ⟨h1, h2⟩) | h1) | ⟨j, hj, h1⟩) | ⟨j, hj, h1⟩
  · rw [← getD_mem hi] at h1
    exact absurd ((hr.mul hr).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h1
  · rw [← getD_mem hi] at h1
    rw [h1] at hr
    exact absurd (hr.unique rep_one) hs1
  · rw [← getD_mem hi] at h1 h2
    rw [← fixM_of_rep hr] at hfix
    have := (Nat.pow_le_pow_right (by norm_num) h1).trans (fixLB_sound h2)
    omega
  · rw [← getD_mem hi] at h1
    have := card_inf_centralizer_le_commCount hE hr
    omega
  · rw [← getD_mem hi, ← getD_mem hj] at h1
    obtain ⟨y, hy, e⟩ := hconj ht j hj h1
    exact ⟨y, hy, Or.inl e⟩
  · rw [← getD_mem hi, ← getD_mem hj] at h1
    obtain ⟨y, hy, e⟩ := hconj hu j hj h1
    exact ⟨y, hy, Or.inr e⟩

end CFSG.EvenSmallLie.OmegaEight.Stage2
