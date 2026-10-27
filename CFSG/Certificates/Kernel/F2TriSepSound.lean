module

public import Certificates.Data.Kernel.F2TriSep
public import CFSG.Certificates.Kernel.F2AlgRankSound

public section

namespace CFSG.KC.F2TriSep

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.F2W CFSG.KC.F2AlgRank CFSG.Sporadic.SmallF2
open scoped Matrix

@[expose] noncomputable def genAlg (d : Nat) (G : List Nat) :
    Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)) :=
  Algebra.adjoin (ZMod 2) {X | ∃ g ∈ G, X = rowsMatrix d (unpackR d g)}

theorem tsStrictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem tsAndB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

theorem tsOrB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

theorem getL_mem_or : ∀ (L : List Nat) (o : Nat), getL 0 L o = 0 ∨ getL 0 L o ∈ L
  | [], _ => Or.inl rfl
  | a :: L, 0 => Or.inr List.mem_cons_self
  | a :: L, o + 1 => by
    rcases getL_mem_or L o with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem a h)

theorem unpackR_getElem? {d M i : Nat} (hi : i < d) : (unpackR d M)[i]? = some (rowF d M i) := by
  simp [unpackR, rowF_eq, hi]

theorem rowsMatrix_row (d M : Nat) (i : Fin d) :
    rowsMatrix d (unpackR d M) i = toVecD d (rowF d M i) := by
  funext j
  rw [rowsMatrix_apply, unpackR_getElem? i.isLt, Option.getD_some]

theorem rowsMatrix_unpackR_zero (d : Nat) : rowsMatrix d (unpackR d 0) = 0 := by
  ext i j
  rw [rowsMatrix_row, rowF_eq, Nat.zero_div, Nat.zero_mod, toVecD_zero]
  rfl

theorem tsUnpackR_idF (d : Nat) : unpackR d (idF d) = CFSG.Sporadic.SmallF2.Native.idRows d := by
  unfold unpackR CFSG.Sporadic.SmallF2.Native.idRows
  congr 1
  funext i
  rw [← rowF_eq]
  have hf : ∀ j < d, CFSG.KLie.CT.pw2 j < 2 ^ d := fun j hj => by
    rw [show CFSG.KLie.CT.pw2 j = 2 ^ j from Nat.one_shiftLeft j]
    exact Nat.pow_lt_pow_right (by omega) hj
  rw [Nat.one_shiftLeft]
  have := rowF_orN d (f := CFSG.KLie.CT.pw2) hf i.isLt
  rw [show CFSG.KLie.CT.pw2 i.val = 2 ^ i.val from Nat.one_shiftLeft _] at this
  exact this

theorem rowsMatrix_mulW (d A B : Nat) :
    rowsMatrix d (unpackR d (mulW d A B)) = rowsMatrix d (unpackR d A) * rowsMatrix d (unpackR d B) := by
  rw [← mulRows_unpackW, rowsMatrix_mulRows]

theorem algK_spec (d : Nat) (G : List Nat) {k : List Nat → Bool} :
    ∀ (tree : List (Nat × Nat)) (acc : List Nat), algK d G tree acc k = true →
      ∃ L, k L = true ∧ ∀ P : Nat → Prop, (∀ x ∈ acc, P x) → P 0 →
        (∀ g x, P x → P (mulW d (getL 0 G g) x)) → ∀ x ∈ L, P x
  | [], acc, h => ⟨acc, h, fun _ hacc _ _ => hacc⟩
  | (o, g) :: tree, acc, h => by
    change strictB (mulW d (getL (nat_lit 0) G g) (getL (nat_lit 0) acc o))
      (fun M => algK d G tree (M :: acc) k) = true at h
    rw [tsStrictB_eq] at h
    obtain ⟨L, hk, hL⟩ := algK_spec d G tree _ h
    refine ⟨L, hk, fun P hacc h0 hstep => hL P ?_ h0 hstep⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine hstep _ _ ?_
      rcases getL_mem_or acc o with he | he
      · rw [he]
        exact h0
      · exact hacc _ he
    · exact hacc x hx

theorem allN_spec' {n : Nat} {f : Nat → Bool} (h : CFSG.KLie.CT.allN n f = true) :
    ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    change CFSG.KLie.CT.andB (f n) (CFSG.KLie.CT.allN n f) = true at h
    rw [tsAndB_eq, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.2 i hi
    · exact h.1

theorem rowF_xor (d a b i : Nat) : rowF d (a ^^^ b) i = rowF d a i ^^^ rowF d b i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rowF_eq, rowF_eq, rowF_eq, Nat.testBit_xor, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (j < d) <;> simp

theorem rowsMatrix_xor (d a b : Nat) :
    rowsMatrix d (unpackR d (a ^^^ b)) = rowsMatrix d (unpackR d a) + rowsMatrix d (unpackR d b) := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_row, rowsMatrix_row, rowsMatrix_row, rowF_xor, toVecD_xor]
  rfl

theorem selK_mem {d : Nat} {A : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2))} :
    ∀ {L : List Nat}, (∀ x ∈ L, rowsMatrix d (unpackR d x) ∈ A) →
      ∀ m, rowsMatrix d (unpackR d (selK L m)) ∈ A
  | [], _, _ => by
    change rowsMatrix d (unpackR d 0) ∈ A
    rw [rowsMatrix_unpackR_zero]
    exact Subalgebra.zero_mem _
  | M :: L, hL, m => by
    change rowsMatrix d (unpackR d (Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) M
      (CFSG.KLie.CT.bit m (nat_lit 0))) (selK L (Nat.shiftRight m (nat_lit 1))))) ∈ A
    rw [show ∀ a b : Nat, Nat.xor a b = a ^^^ b from fun _ _ => rfl, rowsMatrix_xor]
    refine Subalgebra.add_mem _ ?_ (selK_mem (fun x hx => hL x (List.mem_cons_of_mem M hx)) _)
    cases CFSG.KLie.CT.bit m (nat_lit 0)
    · change rowsMatrix d (unpackR d 0) ∈ A
      rw [rowsMatrix_unpackR_zero]
      exact Subalgebra.zero_mem _
    · exact hL M List.mem_cons_self

theorem rowF_outerK {d t f : Nat} (hf : f < 2 ^ d) {i : Nat} (hi : i < d) :
    rowF d (outerK d t f) i = if t.testBit i then f else 0 := by
  have h := rowF_orN d (f := fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) f
    (CFSG.KLie.CT.bit t i))
    (fun j _ => by cases CFSG.KLie.CT.bit t j <;> first | exact Nat.two_pow_pos d | exact hf) hi
  refine h.trans ?_
  dsimp only
  rw [bit_eq]
  cases t.testBit i <;> rfl

theorem colsK_spec {d NT w k : Nat} (h : colsK d NT w k = true) :
    ∀ c < d, k ≤ c → rowF d NT c = 0 ∨ rowF d NT c = w := by
  intro c hc hkc
  have := allN_spec' h c hc
  simp only [tsOrB_eq, tsStrictB_eq, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  rcases this with h1 | h1
  · omega
  · exact h1

theorem single_eq_toVecD {d : Nat} (c : Fin d) :
    (Pi.single c 1 : Fin d → ZMod 2) = toVecD d (2 ^ c.val) := by
  funext j
  rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = c
  · subst h
    simp
  · have h' : c.val ≠ j.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem mulVec_toVecD_pow {d : Nat} (M : Nat) (c : Fin d) :
    rowsMatrix d (unpackR d M) *ᵥ toVecD d (2 ^ c.val) = toVecD d (rowF d (trK d M) c) := by
  rw [← single_eq_toVecD, ← rowsMatrix_row, ← transposeRows_unpackR, rowsMatrix_transposeRows]
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem triK_facts {d : Nat} {G : List Nat} {tree : List (Nat × Nat)} {masks ts : List Nat}
    {F Dm w : Nat} (h : triK d G tree masks ts F Dm w = true) :
    ∃ Y N : Nat → Matrix (Fin d) (Fin d) (ZMod 2),
      (∀ k < d - 2, Y k ∈ genAlg d G) ∧
      (∀ k < d - 2, ∀ v, N k *ᵥ v =
        Y k *ᵥ v + (toVecD d (rowF d F (k + 1)) ⬝ᵥ v) • toVecD d (getL 0 ts k)) ∧
      (∀ k < d - 2, ∀ c : Fin d, k + 1 ≤ c.val →
        N k *ᵥ (rowsMatrix d (unpackR d Dm) *ᵥ Pi.single c 1) ∈
          Submodule.span (ZMod 2) {toVecD d w}) ∧
      rowsMatrix d (unpackR d Dm) * rowsMatrix d (unpackR d F) = 1 ∧
      rowsMatrix d (unpackR d Dm) *ᵥ toVecD d (2 ^ (d - 1)) = toVecD d w := by
  unfold triK at h
  obtain ⟨L, hk, hL⟩ := algK_spec d G tree [idF d] h
  simp only [tsAndB_eq, Bool.and_eq_true, Nat.beq_eq] at hk
  obtain ⟨hall, hinv, hcol⟩ := hk
  have hLalg : ∀ x ∈ L, rowsMatrix d (unpackR d x) ∈ genAlg d G := by
    refine hL (fun x => rowsMatrix d (unpackR d x) ∈ genAlg d G) ?_ ?_ ?_
    · intro x hx
      rw [List.mem_singleton.1 hx, tsUnpackR_idF, rowsMatrix_idRows]
      exact Subalgebra.one_mem _
    · rw [rowsMatrix_unpackR_zero]
      exact Subalgebra.zero_mem _
    · intro g x hx
      rw [rowsMatrix_mulW]
      refine Subalgebra.mul_mem _ ?_ hx
      rcases getL_mem_or G g with h0 | h1
      · rw [h0, rowsMatrix_unpackR_zero]
        exact Subalgebra.zero_mem _
      · exact Algebra.subset_adjoin ⟨_, h1, rfl⟩
  have hallk := allN_spec' hall
  refine ⟨fun k => rowsMatrix d (unpackR d (selK L (getL 0 masks k))),
    fun k => rowsMatrix d (unpackR d (Nat.xor (selK L (getL 0 masks k))
      (outerK d (getL 0 ts k) (rowF d F (k + 1))))),
    fun k _ => selK_mem hLalg _, fun k _ v => ?_, fun k hk c hc => ?_, ?_, ?_⟩
  · funext i
    rw [Pi.add_apply, mulVec_row, mulVec_row, Pi.smul_apply, smul_eq_mul,
      show ∀ a b : Nat, Nat.xor a b = a ^^^ b from fun _ _ => rfl, rowF_xor,
      toVecD_xor, add_dotProduct, rowF_outerK (rowF_lt d F (k + 1)) i.isLt, toVecD_apply]
    cases (getL 0 ts k).testBit i.val
    · simp [toVecD_zero]
    · simp
  · have hc' := hallk k (by omega)
    simp only [tsStrictB_eq] at hc'
    have hcc := colsK_spec hc' c.val c.isLt hc
    rw [Matrix.mulVec_mulVec, ← rowsMatrix_mulW, single_eq_toVecD, mulVec_toVecD_pow]
    rcases hcc with h0 | h1
    · rw [h0, toVecD_zero]
      exact Submodule.zero_mem _
    · rw [h1]
      exact Submodule.mem_span_singleton_self _
  · rw [← rowsMatrix_mulW, hinv, tsUnpackR_idF, rowsMatrix_idRows]
  · rw [rowsMatrix_mulVec, transposeRows_unpackR, vecMulN_unpackR, ← hcol]
    congr 2
    change 2 ^ (d - 1) = 1 <<< Nat.pred d
    rw [Nat.one_shiftLeft, Nat.pred_eq_sub_one]

theorem add_self_vec {d : Nat} (u : Fin d → ZMod 2) : u + u = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize u i = a
  revert a
  decide

theorem eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  revert a
  decide

theorem triK_sound {d : Nat} {G : List Nat} {tree : List (Nat × Nat)} {masks ts : List Nat}
    {F Dm w : Nat} (h : triK d G tree masks ts F Dm w = true)
    (U : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hG : ∀ g ∈ G, ∀ u ∈ U, rowsMatrix d (unpackR d g) *ᵥ u ∈ U) (hw : toVecD d w ∈ U)
    {y : Fin d → ZMod 2} (hy : y ∈ U) (h0 : toVecD d (rowF d F 0) ⬝ᵥ y = 0)
    (hyw : y ∉ Submodule.span (ZMod 2) {toVecD d w}) :
    ∃ k < d - 2, toVecD d (getL 0 ts k) ∈ U := by
  classical
  obtain ⟨Y, N, hYalg, hN, hcol, hinv, hlast⟩ := triK_facts h
  have hpres : ∀ k < d - 2, ∀ u ∈ U, Y k *ᵥ u ∈ U := by
    intro k hk
    have hle : genAlg d G ≤ stabAlg U := by
      refine Algebra.adjoin_le ?_
      rintro X ⟨g, hg, rfl⟩
      exact hG g hg
    exact hle (hYalg k hk)
  have hyD : y = rowsMatrix d (unpackR d Dm) *ᵥ (rowsMatrix d (unpackR d F) *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hzc : ∀ c : Fin d, (rowsMatrix d (unpackR d F) *ᵥ y) c = toVecD d (rowF d F c) ⬝ᵥ y :=
    fun c => mulVec_row F y c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact (hyw (by rw [Subsingleton.elim y 0]; exact Submodule.zero_mem _)).elim
  have hz0 : (rowsMatrix d (unpackR d F) *ᵥ y) ⟨0, hd⟩ = 0 := by
    rw [hzc]
    exact h0
  have hex : ∃ c, ∃ hc : c < d - 1, 0 < c ∧ (rowsMatrix d (unpackR d F) *ᵥ y) ⟨c, by omega⟩ = 1 := by
    by_contra hne
    apply hyw
    have hzm : ∀ c : Fin d, c.val < d - 1 → (rowsMatrix d (unpackR d F) *ᵥ y) c = 0 := by
      intro c hc
      rcases Nat.eq_zero_or_pos c.val with h0c | hpos
      · have e : c = ⟨0, hd⟩ := Fin.ext h0c
        rw [e]
        exact hz0
      · exact eq_zero_of_ne_one fun h1 => hne ⟨c.val, hc, hpos, h1⟩
    have hzs : rowsMatrix d (unpackR d F) *ᵥ y =
        (rowsMatrix d (unpackR d F) *ᵥ y) ⟨d - 1, by omega⟩ • toVecD d (2 ^ (d - 1)) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, toVecD_apply, Nat.testBit_two_pow]
      by_cases hi : i.val = d - 1
      · have e : i = ⟨d - 1, by omega⟩ := Fin.ext hi
        rw [e]
        simp
      · have hi' : ¬ (d - 1 = i.val) := fun e => hi e.symm
        rw [hzm i (by omega)]
        simp [hi']
    rw [Submodule.mem_span_singleton]
    refine ⟨(rowsMatrix d (unpackR d F) *ᵥ y) ⟨d - 1, by omega⟩, ?_⟩
    rw [← hlast, ← Matrix.mulVec_smul, ← hzs, ← hyD]
  obtain ⟨hk1, hk1pos, hzk⟩ := Nat.find_spec hex
  have hmin : ∀ c : Fin d, c.val < Nat.find hex → (rowsMatrix d (unpackR d F) *ᵥ y) c = 0 := by
    intro c hc
    rcases Nat.eq_zero_or_pos c.val with h0c | hpos
    · have e : c = ⟨0, hd⟩ := Fin.ext h0c
      rw [e]
      exact hz0
    · exact eq_zero_of_ne_one fun h1 => Nat.find_min hex hc ⟨by omega, hpos, h1⟩
  obtain ⟨k, hk, hkmin, hz1⟩ : ∃ k, ∃ _ : k < d - 2,
      (∀ c : Fin d, c.val ≤ k → (rowsMatrix d (unpackR d F) *ᵥ y) c = 0) ∧
      (rowsMatrix d (unpackR d F) *ᵥ y) ⟨k + 1, by omega⟩ = 1 :=
    ⟨Nat.find hex - 1, by omega, fun c hc => hmin c (by omega),
      (congrArg (rowsMatrix d (unpackR d F) *ᵥ y) (Fin.ext (Nat.sub_add_cancel hk1pos))).trans hzk⟩
  refine ⟨k, hk, ?_⟩
  have hNy : N k *ᵥ y ∈ Submodule.span (ZMod 2) {toVecD d w} := by
    rw [hyD, ← Finset.univ_sum_single (rowsMatrix d (unpackR d F) *ᵥ y), Matrix.mulVec_sum,
      Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hc : k + 1 ≤ c.val
    · have e : (Pi.single c ((rowsMatrix d (unpackR d F) *ᵥ y) c) : Fin d → ZMod 2) =
          (rowsMatrix d (unpackR d F) *ᵥ y) c • Pi.single c 1 := by
        funext j
        rcases eq_or_ne j c with rfl | hj
        · simp
        · simp [hj]
      rw [e, Matrix.mulVec_smul, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (hcol _ hk c hc)
    · rw [hkmin c (by omega), Pi.single_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  have hNyU := (Submodule.span_singleton_le_iff_mem _ _).2 hw hNy
  have h1 : toVecD d (rowF d F (k + 1)) ⬝ᵥ y = 1 := (hzc ⟨k + 1, by omega⟩).symm.trans hz1
  rw [hN _ hk y, h1, one_smul] at hNyU
  exact (Submodule.add_mem_iff_right U (hpres _ hk y hy)).1 hNyU

theorem vregK_spec (d : Nat) (GT : List Nat) {k : List Nat → Bool} :
    ∀ (tree : List (Nat × Nat)) (acc : List Nat), vregK d GT tree acc k = true →
      ∃ L, k L = true ∧ ∀ P : Nat → Prop, (∀ x ∈ acc, P x) → P 0 →
        (∀ g x, P x → P (vmF d (getL 0 GT g) x)) → ∀ x ∈ L, P x
  | [], acc, h => ⟨acc, h, fun _ hacc _ _ => hacc⟩
  | (o, g) :: tree, acc, h => by
    change strictB (vmF d (getL (nat_lit 0) GT g) (getL (nat_lit 0) acc o))
      (fun v => vregK d GT tree (v :: acc) k) = true at h
    rw [tsStrictB_eq] at h
    obtain ⟨L, hk, hL⟩ := vregK_spec d GT tree _ h
    refine ⟨L, hk, fun P hacc h0 hstep => hL P ?_ h0 hstep⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine hstep _ _ ?_
      rcases getL_mem_or acc o with he | he
      · rw [he]
        exact h0
      · exact hacc _ he
    · exact hacc x hx

theorem getL_trL : ∀ (d : Nat) (G : List Nat) (g : Nat),
    getL 0 (trL d G) g = 0 ∨ ∃ g' ∈ G, getL 0 (trL d G) g = trK d g'
  | _, [], _ => Or.inl rfl
  | d, a :: G, 0 => Or.inr ⟨a, List.mem_cons_self, rfl⟩
  | d, a :: G, g + 1 => by
    rcases getL_trL d G g with h | ⟨g', hg', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨g', List.mem_cons_of_mem a hg', h⟩

theorem toVecD_vmF (d M x : Nat) :
    toVecD d (vmF d M x) = toVecD d x ᵥ* rowsMatrix d (unpackR d M) := by
  rw [← vecMulN_unpackR, toVecD_vecMulN]

theorem toVecD_vmF_trK (d g x : Nat) :
    toVecD d (vmF d (trK d g) x) = rowsMatrix d (unpackR d g) *ᵥ toVecD d x := by
  rw [rowsMatrix_mulVec, transposeRows_unpackR, vecMulN_unpackR]

theorem packL_cons {d x : Nat} (hx : x < 2 ^ d) (L : List Nat) :
    packL d (x :: L) = x + packL d L * 2 ^ d := by
  change x ||| packL d L <<< d = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

theorem rowF_add_mul {d x Q : Nat} (hx : x < 2 ^ d) (i : Nat) :
    rowF d (x + Q * 2 ^ d) (i + 1) = rowF d Q i := by
  rw [rowF_eq, rowF_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (d * i)),
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos d), Nat.div_eq_of_lt hx,
    Nat.zero_add]

theorem rowF_add_mul_zero {d x Q : Nat} (hx : x < 2 ^ d) : rowF d (x + Q * 2 ^ d) 0 = x := by
  rw [rowF_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hx]

theorem rowF_packL {d : Nat} : ∀ {L : List Nat}, (∀ x ∈ L, x < 2 ^ d) → ∀ i < L.length,
    rowF d (packL d L) i = L.getD i 0
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | x :: L, hL, 0, _ => by
    rw [packL_cons (hL x List.mem_cons_self), rowF_add_mul_zero (hL x List.mem_cons_self)]
    rfl
  | x :: L, hL, i + 1, hi => by
    rw [packL_cons (hL x List.mem_cons_self), rowF_add_mul (hL x List.mem_cons_self),
      rowF_packL (fun y hy => hL y (List.mem_cons_of_mem x hy)) i (by simpa using hi)]
    rfl

theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

theorem spinK_facts {d : Nat} {G : List Nat} {tree : List (Nat × Nat)} {v e Ri : Nat}
    (h : spinK d G tree v e Ri = true) :
    ∃ R : Matrix (Fin d) (Fin d) (ZMod 2), R * rowsMatrix d (unpackR d Ri) = 1 ∧
      (∀ hd : 0 < d, R ⟨0, hd⟩ = toVecD d e) ∧
      ∀ U : Submodule (ZMod 2) (Fin d → ZMod 2),
        (∀ g ∈ G, ∀ u ∈ U, rowsMatrix d (unpackR d g) *ᵥ u ∈ U) → toVecD d v ∈ U →
        ∀ i : Fin d, i.val ≠ 0 → R i ∈ U := by
  unfold spinK at h
  simp only [tsAndB_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hv, he, hreg⟩ := h
  have hv' : v < 2 ^ d := by
    rw [show CFSG.KLie.CT.pw2 d = 2 ^ d from Nat.one_shiftLeft d] at hv
    exact hv
  have he' : e < 2 ^ d := by
    rw [show CFSG.KLie.CT.pw2 d = 2 ^ d from Nat.one_shiftLeft d] at he
    exact he
  obtain ⟨L, hk, hL⟩ := vregK_spec d (trL d G) tree [v] hreg
  simp only [tsAndB_eq, Bool.and_eq_true, Nat.beq_eq, lenL_eq] at hk
  obtain ⟨hlen, hinv⟩ := hk
  rw [Nat.pred_eq_sub_one] at hlen
  have hlt : ∀ x ∈ L, x < 2 ^ d := hL (fun x => x < 2 ^ d)
    (fun x hx => by rw [List.mem_singleton.1 hx]; exact hv') (Nat.two_pow_pos d)
    (fun g x _ => vmF_lt d _ x)
  have hlt' : ∀ x ∈ e :: L, x < 2 ^ d := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact he'
    · exact hlt x hx
  refine ⟨rowsMatrix d (unpackR d (packL d (e :: L))), ?_, fun hd => ?_, fun U hG hvU i hi => ?_⟩
  · rw [← rowsMatrix_mulRows, mulRows_unpackW, hinv, tsUnpackR_idF, rowsMatrix_idRows]
  · rw [rowsMatrix_row, rowF_packL hlt' 0 (by simp)]
    rfl
  · have hU : ∀ x ∈ L, toVecD d x ∈ U := hL (fun x => toVecD d x ∈ U)
      (fun x hx => by rw [List.mem_singleton.1 hx]; exact hvU) (by rw [toVecD_zero]; exact U.zero_mem)
      (fun g x hx => by
        rcases getL_trL d G g with h0 | ⟨g', hg', h1⟩
        · rw [h0, toVecD_vmF, rowsMatrix_unpackR_zero, Matrix.vecMul_zero]
          exact U.zero_mem
        · rw [h1, toVecD_vmF_trK]
          exact hG g' hg' _ hx)
    obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
    have hjL : j < L.length := by have := i.isLt; omega
    rw [rowsMatrix_row, hj, rowF_packL hlt' (j + 1) (by simp; omega)]
    change toVecD d (L.getD j 0) ∈ U
    rw [List.getD_eq_getElem _ _ hjL]
    exact hU _ (List.getElem_mem hjL)

theorem spinK_sound {d : Nat} {G : List Nat} {tree : List (Nat × Nat)} {v e Ri : Nat}
    (h : spinK d G tree v e Ri = true) (U : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hG : ∀ g ∈ G, ∀ u ∈ U, rowsMatrix d (unpackR d g) *ᵥ u ∈ U) (hv : toVecD d v ∈ U)
    (x : Fin d → ZMod 2) : ∃ a : ZMod 2, x + a • toVecD d e ∈ U := by
  obtain ⟨R, hR, h0, hU⟩ := spinK_facts h
  have hR' : rowsMatrix d (unpackR d Ri) * R = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin d) (Fin d) (ZMod 2) rfl).1 hR
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨0, by convert U.zero_mem⟩
  set c := x ᵥ* rowsMatrix d (unpackR d Ri) with hc
  have hx : x = c ᵥ* R := by
    rw [hc, Matrix.vecMul_vecMul, hR', Matrix.vecMul_one]
  have hsum : c ᵥ* R = ∑ i, c i • R i := by
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  have hs := Finset.add_sum_erase Finset.univ (fun i => c i • R i) (Finset.mem_univ ⟨0, hd⟩)
  beta_reduce at hs
  rw [h0 hd] at hs
  refine ⟨c ⟨0, hd⟩, ?_⟩
  have e : x + c ⟨0, hd⟩ • toVecD d e = ∑ i ∈ Finset.univ.erase ⟨0, hd⟩, c i • R i := by
    rw [hx, hsum, ← hs, add_right_comm, add_self_vec, zero_add]
  rw [e]
  refine Submodule.sum_mem _ fun i hi => U.smul_mem _ (hU U hG hv i fun h => ?_)
  exact Finset.ne_of_mem_erase hi (Fin.ext h)

end CFSG.KC.F2TriSep

end
