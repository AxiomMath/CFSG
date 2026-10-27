
module

public import CFSG.Certificates.Kernel.Co1FixCount
public import CFSG.Sporadic.Co1.Module.OddNativeBase
public import Certificates.Data.Kernel.Co1M.Odd73F

public section

namespace CFSG.KC.Odd73

open CFSG.KC.Co1Fix CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

theorem spanCnt_eq {p : Nat → Bool} {Q : (Fin 24 → ZMod 2) → Prop} [DecidablePred Q]
    (hpQ : ∀ x < 2 ^ 24, (p x = true ↔ Q (vecOf x))) :
    ∀ (F : List Nat) (n : Nat), F.length = n → (∀ f ∈ F, f < 2 ^ 24) → ∀ acc < 2 ^ 24,
      ((spanK F acc).filter p).length =
        (Finset.univ.filter fun c : Fin n → ZMod 2 => Q (vecOf acc + comb F n c)).card
  | [], n, hn, _, acc, hacc => by
    subst hn
    have hc : ∀ c : Fin 0 → ZMod 2, comb [] 0 c = 0 := fun c => by simp [comb]
    simp only [spanK, List.length_nil, hc, add_zero]
    by_cases h : p acc = true
    · rw [List.filter_cons_of_pos h, List.filter_nil]
      have hq := (hpQ acc hacc).1 h
      simp [hq]
    · rw [List.filter_cons_of_neg h, List.filter_nil]
      have hq : ¬ Q (vecOf acc) := fun hq => h ((hpQ acc hacc).2 hq)
      simp [hq]
  | f :: F, n, hn, hF, acc, hacc => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨F.length, by rw [← hn]; rfl⟩
    have hm : F.length = m := by simpa using hn
    have hf : f < 2 ^ 24 := hF f List.mem_cons_self
    have hF' : ∀ g ∈ F, g < 2 ^ 24 := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    rw [spanK, List.filter_append, List.length_append, spanCnt_eq hpQ F m hm hF' acc hacc,
      spanCnt_eq hpQ F m hm hF' (acc ^^^ f) (Nat.xor_lt_two_pow hacc hf)]
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ZMod 2).sum_comp, Fintype.sum_prod_type]
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [hu, Finset.sum_pair (by decide)]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have e : comb (f :: F) (m + 1) ((Fin.consEquiv fun _ => ZMod 2) (0, c)) = comb F m c := by
        rw [comb_cons]
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, zero_smul',
          zero_add]
      rw [e]
    · refine Finset.sum_congr rfl fun c _ => ?_
      have e : vecOf acc + comb (f :: F) (m + 1) ((Fin.consEquiv fun _ => ZMod 2) (1, c)) =
          vecOf (acc ^^^ f) + comb F m c := by
        rw [comb_cons]
        simp only [vecOf, toVecD_xor, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero,
          Fin.cons_succ, one_smul', add_assoc]
      rw [e]

@[expose] def bitZ (j b : Nat) : ZMod 2 := if j.testBit b then 1 else 0

theorem offK_succ (F : List Nat) (m j : Nat) :
    offK F (m + 1) j = if j.testBit m then offK F m j ^^^ F.getD m 0 else offK F m j := by
  change Bool.rec (motive := fun _ => Nat) (offK F m j) (Nat.xor (offK F m j) (getL 0 F m))
    (bit j m) = _
  rw [bit_eq']
  cases j.testBit m
  · rfl
  · change Nat.xor (offK F m j) (getL 0 F m) = _
    simp only [↓reduceIte]
    congr 1
    clear * -
    induction F generalizing m with
    | nil => rfl
    | cons a F ih =>
      cases m
      · rfl
      · exact ih _

theorem offK_vec (F : List Nat) (j : Nat) : ∀ m,
    vecOf (offK F m j) = comb F m fun b => bitZ j b
  | 0 => by
    change toVecD 24 0 = _
    simp [comb, toVecD_zero]
  | m + 1 => by
    rw [offK_succ, comb, Fin.sum_univ_castSucc]
    have ih := offK_vec F j m
    rw [comb] at ih
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    by_cases h : j.testBit m
    · simp only [h, ↓reduceIte, bitZ, one_smul']
      rw [vecOf, vecOf, toVecD_xor]
      rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte, bitZ, zero_smul', add_zero]

theorem bitZ_eq {j : Nat} (hj : j < 2 ^ 6) (b : Fin 6) :
    bitZ j b = (finFunctionFinEquiv.symm (⟨j, hj⟩ : Fin (2 ^ 6)) b : Fin 2) := by
  apply Fin.ext
  rw [finFunctionFinEquiv_symm_apply_val]
  unfold bitZ
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 := Nat.mod_lt (j / 2 ^ (b : ℕ)) (show 0 < 2 by norm_num)
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_lt h2) with h | h
  · rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · have : j / 2 ^ (b : ℕ) % 2 = 0 := by omega
      rw [this]
      rfl
    · rw [h']
      rfl
  · omega

theorem getD_drop73 (F : List Nat) (i : Nat) : (F.drop 6).getD i 0 = F.getD (6 + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem comb_append73 (F : List Nat) (a : Fin 6 → ZMod 2) (c : Fin 10 → ZMod 2) :
    comb F 16 (Fin.append a c) = comb F 6 a + comb (F.drop 6) 10 c := by
  unfold comb
  change ∑ i : Fin (6 + 10), Fin.append a c i • vecOf (F.getD i 0) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd, getD_drop73]

theorem slices_count {T : Nat} {F Y : List Nat} (hfix : fixK 24 T 0 F Y 16 65536 0 = true)
    (p : Nat → Bool) :
    CFSG.Sporadic.Co1.OddNative.countBelow (fun x => Nat.beq (vmF 24 T x) x && p x) 16777216 0 =
      ∑ j ∈ Finset.range 64, ((spanK (F.drop 6) (offK F 6 j)).filter p).length := by
  classical
  obtain ⟨hk, hlen, -, hF, hpF, hpY, -⟩ := fixK_spec hfix
  have hset := fixed_set (fun f hf => (hF f hf).2) hpF hpY (by omega)
  obtain ⟨hlowF, hndF⟩ := pivK_spec F 0 hpF
  have hinj := comb_injective (L := F) (n := F.length) le_rfl (fun v hv => (hlowF v hv).1) hndF
  rw [hk] at hset hinj
  let Q : (Fin 24 → ZMod 2) → Prop := fun v => ∃ x < 2 ^ 24, vecOf x = v ∧ p x = true
  have hpQ : ∀ x < 2 ^ 24, (p x = true ↔ Q (vecOf x)) := by
    intro x hx
    constructor
    · exact fun h => ⟨x, hx, rfl, h⟩
    · rintro ⟨y, hy, e, hp⟩
      rw [toVecD_injective hy hx e] at hp
      exact hp
  have hL : CFSG.Sporadic.Co1.OddNative.countBelow (fun x => Nat.beq (vmF 24 T x) x && p x)
      16777216 0 = {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 T) = v ∧ Q v}.ncard := by
    rw [CFSG.Sporadic.Co1.Module.Odd.ncard_eq_countBelow]
    intro x hx
    rw [Bool.and_eq_true, Nat.beq_eq]
    change _ ↔ vecOf x ᵥ* rowsMatrix 24 (unpackR 24 T) = vecOf x ∧ Q (vecOf x)
    rw [vecMul_eq, ← hpQ x hx]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨toVecD_injective (CFSG.KC.F2W.vmF_lt 24 T x) hx h1, h2⟩
  have hS : {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 T) = v ∧ Q v} =
      comb F 16 '' {c | Q (comb F 16 c)} := by
    ext v
    constructor
    · rintro ⟨h1, h2⟩
      have : v ∈ {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 T) = v} := h1
      rw [hset] at this
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, h2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      have : comb F 16 c ∈ Set.range (comb F 16) := ⟨c, rfl⟩
      rw [← hset] at this
      exact ⟨this, hc⟩
  rw [hL, hS, Set.ncard_image_of_injective _ hinj, Set.ncard_eq_toFinset_card']
  have hF10 : (F.drop 6).length = 10 := by rw [List.length_drop, hk]
  have hFlt : ∀ f ∈ F.drop 6, f < 2 ^ 24 := fun f hf => (hF f (List.mem_of_mem_drop hf)).1
  have hoff : ∀ j, offK F 6 j < 2 ^ 24 := by
    intro j
    induction (6 : Nat) with
    | zero => exact Nat.two_pow_pos 24
    | succ m ih =>
      rw [offK_succ]
      split_ifs
      · refine Nat.xor_lt_two_pow ih ?_
        by_cases hm : m < F.length
        · rw [List.getD_eq_getElem _ _ hm]
          exact (hF _ (List.getElem_mem hm)).1
        · rw [List.getD_eq_default _ _ (by omega)]
          exact Nat.two_pow_pos 24
      · exact ih
  have hslice : ∀ j < 64, ((spanK (F.drop 6) (offK F 6 j)).filter p).length =
      (Finset.univ.filter fun c : Fin 10 → ZMod 2 =>
        Q (comb F 16 (Fin.append (fun b => bitZ j b) c))).card := by
    intro j _
    rw [spanCnt_eq hpQ (F.drop 6) 10 hF10 hFlt _ (hoff j)]
    refine congrArg Finset.card (Finset.filter_congr fun c _ => ?_)
    rw [comb_append73, offK_vec]
  rw [Finset.sum_congr rfl fun j hj => hslice j (Finset.mem_range.1 hj)]
  let E : Fin (2 ^ 6) × (Fin 10 → ZMod 2) ≃ (Fin 16 → ZMod 2) :=
    (Equiv.prodCongr finFunctionFinEquiv.symm (Equiv.refl _)).trans (Fin.appendEquiv 6 10)
  have hE : ∀ q : Fin (2 ^ 6) × (Fin 10 → ZMod 2),
      E q = Fin.append (fun b => bitZ q.1 b) q.2 := by
    rintro ⟨j, c⟩
    have e : (finFunctionFinEquiv.symm j : Fin 6 → ZMod 2) = fun b : Fin 6 => bitZ (j : ℕ) b :=
      funext fun b => (bitZ_eq j.2 b).symm
    change Fin.append (finFunctionFinEquiv.symm j) c = _
    rw [e]
    rfl
  rw [Set.toFinset_ofPred, ← Finset.card_map E.symm.toEmbedding]
  have hmap : (Finset.univ.filter fun c : Fin 16 → ZMod 2 => Q (comb F 16 c)).map
      E.symm.toEmbedding = Finset.univ.filter fun q => Q (comb F 16 (E q)) := by
    ext q
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_symm]
  rw [hmap, Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_range (fun j => (Finset.univ.filter fun c : Fin 10 → ZMod 2 =>
    Q (comb F 16 (Fin.append (fun b => bitZ j b) c))).card)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hE]

@[expose] noncomputable def test7 (t4 : Nat → Bool) (T0 T1 T2 : Nat) (k x : Nat) : Bool :=
  match k with
  | 0 => t4 x
  | 1 => Nat.beq (vmF 24 T0 x) x
  | 2 => Nat.beq (vmF 24 T0 x) x && t4 x
  | 3 => Nat.beq (vmF 24 T1 x) x
  | 4 => Nat.beq (vmF 24 T1 x) x && t4 x
  | 5 => Nat.beq (vmF 24 T2 x) x
  | _ => Nat.beq (vmF 24 T2 x) x && t4 x

@[expose] def fields7 (c : Nat → Nat) : Nat :=
  c 0 + 4096 * (c 1 + 4096 * (c 2 + 4096 * (c 3 + 4096 * (c 4 + 4096 * (c 5 + 4096 * c 6)))))

theorem ind7K_eq (t4 : Nat → Bool) (T0 T1 T2 x : Nat) :
    ind7K t4 T0 T1 T2 x = fields7 fun k => if test7 t4 T0 T1 T2 k x then 1 else 0 := by
  unfold ind7K fields7 test7
  cases t4 x <;> cases Nat.beq (vmF 24 T0 x) x <;> cases Nat.beq (vmF 24 T1 x) x <;>
    cases Nat.beq (vmF 24 T2 x) x <;> rfl

theorem cnt7K_eq (t4 : Nat → Bool) (T0 T1 T2 : Nat) : ∀ (F : List Nat) (acc : Nat),
    cnt7K t4 T0 T1 T2 F acc =
      fields7 fun k => ((spanK F acc).filter (test7 t4 T0 T1 T2 k)).length
  | [], acc => by
    change ind7K t4 T0 T1 T2 acc = _
    rw [ind7K_eq]
    congr 1
    funext k
    simp only [spanK, List.filter_cons, List.filter_nil]
    split_ifs <;> rfl
  | f :: F, acc => by
    change CFSG.KC.Loop.strictN (cnt7K t4 T0 T1 T2 F acc) (fun a => CFSG.KC.Loop.strictN
      (cnt7K t4 T0 T1 T2 F (Nat.xor acc f)) fun b => Nat.add a b) = _
    have hx : Nat.xor acc f = acc ^^^ f := rfl
    simp only [CFSG.KC.Co1Fix.strictN_eq', cnt7K_eq t4 T0 T1 T2 F, spanK, List.filter_append,
      List.length_append, fields7, Nat.add_eq, hx]
    ring

theorem pack7_nil : pack7 [] = 0 := rfl

theorem pack7_cons (x : Nat) (t : List Nat) : pack7 (x :: t) = x + 4096 * pack7 t := by
  change (x + (pack7 t <<< 12) : Nat) = x + 4096 * pack7 t
  rw [Nat.shiftLeft_eq]
  ring

theorem pack7_eq (L : List Nat) (hL : L.length = 7) :
    pack7 L = fields7 fun k => L.getD k 0 := by
  match L, hL with
  | [a, b, c, d, e, f, g], _ =>
    simp only [pack7_cons, pack7_nil, fields7, List.getD_cons_zero, List.getD_cons_succ]
    ring

theorem cnt7_fields {c : Nat → Nat} {L : List Nat} (hL : L.length = 7)
    (hc : ∀ k < 7, c k < 4096) (hl : ∀ k < 7, L.getD k 0 < 4096)
    (h : fields7 c = pack7 L) : ∀ k < 7, c k = L.getD k 0 := by
  rw [pack7_eq L hL] at h
  unfold fields7 at h
  dsimp only at h
  have h0 := hc 0 (by norm_num)
  have h1 := hc 1 (by norm_num)
  have h2 := hc 2 (by norm_num)
  have h3 := hc 3 (by norm_num)
  have h4 := hc 4 (by norm_num)
  have h5 := hc 5 (by norm_num)
  have h6 := hc 6 (by norm_num)
  have l0 := hl 0 (by norm_num)
  have l1 := hl 1 (by norm_num)
  have l2 := hl 2 (by norm_num)
  have l3 := hl 3 (by norm_num)
  have l4 := hl 4 (by norm_num)
  have l5 := hl 5 (by norm_num)
  have l6 := hl 6 (by norm_num)
  intro k hk
  interval_cases k <;> omega

end CFSG.KC.Odd73

end
