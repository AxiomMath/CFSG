module

public import Certificates.Data.Kernel.Misc.Coset.ActNet
public import CFSG.Certificates.Kernel.Misc.Coset.ActSound
public import CFSG.Certificates.Kernel.YModel.NetSem

public section

namespace CFSG.KC.MiscCoset.Act

open CFSG.KC.YModel.Sem

theorem lineL_succ (A : ℕ → ℕ) (L c m : ℕ) :
    lineL A L c (m + 1) = lineL A L c m ||| (A (m * L + c) <<< (32 * m)) := by
  have e : lineL A L c (m + 1) = CFSG.KC.Loop.strictN (lineL A L c m) (fun a => Nat.lor a
      (Nat.shiftLeft (A (Nat.add (Nat.mul m L) c)) (Nat.mul (nat_lit 32) m))) := rfl
  rw [e, CFSG.KC.Benes.strictN_eq]
  rfl

theorem lineL_spec (A : ℕ → ℕ) (L c : ℕ) : ∀ m, (∀ i < m, A (i * L + c) < 2 ^ 32) →
    lineL A L c m < 2 ^ (32 * m) ∧ ∀ i < m, CFSG.KC.YModel.fieldAt 32 (lineL A L c m) i = A (i * L + c)
  | 0, _ => ⟨by simp [lineL], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | m + 1, hA => by
    obtain ⟨hlt, hf⟩ := lineL_spec A L c m fun i hi => hA i (by omega)
    have hv := hA m (by omega)
    have hle : ∀ t, 32 * m ≤ t → lineL A L c m < 2 ^ t := fun t ht =>
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) ht)
    rw [lineL_succ]
    refine ⟨?_, fun i hi => ?_⟩
    · apply Nat.or_lt_two_pow (hle _ (by omega))
      rw [Nat.shiftLeft_eq, show 32 * (m + 1) = 32 + 32 * m by ring, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_fieldAt, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hj : j < 32
      · by_cases him : i < m
        · have h1 : ¬ (32 * i + j ≥ 32 * m) := by omega
          rw [← hf i him, testBit_fieldAt]
          simp [hj, h1]
        · have e : i = m := by omega
          rw [e, Nat.testBit_lt_two_pow (hle (32 * m + j) (by omega))]
          simp [hj]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hA i hi) (Nat.pow_le_pow_right (by norm_num)
          (by omega : 32 ≤ j)))]
        simp [hj]

theorem invC_eq (c : ℕ) : invC c = if c % 2 = 0 then c + 1 else c - 1 := by
  unfold invC
  have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h, if_pos rfl]
    rfl
  · rw [h, if_neg (by norm_num)]
    rfl

theorem invRels_eq : ∀ rels : List (List ℕ), invRels rels = rels.map (fun r => r.map invC)
  | [] => rfl
  | r :: rels => by
    have e : ∀ w : List ℕ, (List.rec (motive := fun _ => List ℕ) List.nil
        (fun c _ ih' => List.cons (invC c) ih') w) = w.map invC := by
      intro w
      induction w with
      | nil => rfl
      | cons c w ih => exact congrArg (List.cons (invC c)) ih
    change List.cons _ (invRels rels) = _
    rw [invRels_eq rels, e]
    rfl

theorem relsOK_mem' {k m : ℕ} {Nf : ℕ → ℕ} : ∀ {rels : List (List ℕ)},
    CFSG.KC.YModel.relsOK k m Nf rels = true → ∀ r ∈ rels,
      CFSG.KC.YModel.wordAp k m Nf r (MonsterConv.Perm.idP k) = MonsterConv.Perm.idP k
  | [], _, r, hr => absurd hr List.not_mem_nil
  | r' :: rs, h, r, hr => by
    change andB (Nat.beq (CFSG.KC.YModel.wordAp k m Nf r' (MonsterConv.Perm.idP k))
      (MonsterConv.Perm.idP k)) (CFSG.KC.YModel.relsOK k m Nf rs) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KC.Benes.andB_true h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Nat.eq_of_beq_eq_true h1
    · exact relsOK_mem' h2 r hr

theorem walk_cons (A : ℕ → ℕ) (L c : ℕ) (r : List ℕ) (x : ℕ) :
    walk A L (c :: r) x = walk A L r (step A L x c) := rfl

theorem brec_true' {a b : Bool} (ha : a = true) (hb : b = true) : (Bool.rec false b a : Bool) = true := by
  subst ha
  exact hb

theorem allR_of {lo : ℕ} {p : ℕ → Bool} : ∀ n, (∀ x, lo ≤ x → x < lo + n → p x = true) →
    allR lo n p = true
  | 0, _ => rfl
  | n + 1, h => brec_true' (h _ (by simp only [Nat.add_eq]; omega) (by simp only [Nat.add_eq]; omega))
      (allR_of n fun x h1 h2 => h x h1 (by omega))

section
variable {A : ℕ → ℕ} {m N k : ℕ} {Nf : ℕ → ℕ}

theorem wF_walk (hL : ∀ x < N, LetOK A m N x)
    (hb : ∀ c < m + m, ∀ i < N, CFSG.KC.Benes.benesPerm k (Nf c) i = step A (m + m) i c) :
    ∀ r : List ℕ, (∀ c ∈ r, c < m + m) → ∀ y < N,
      wF k (m + m) Nf (r.map invC) (walk A (m + m) r y) = y ∧ walk A (m + m) r y < N
  | [], _, y, hy => ⟨rfl, hy⟩
  | c :: r, hr, y, hy => by
    have hc := hr c List.mem_cons_self
    have hy' := (hL y hy).1 c hc
    obtain ⟨ih, ihl⟩ := wF_walk hL hb r (fun d hd => hr d (List.mem_cons_of_mem _ hd)) _ hy'
    refine ⟨?_, by rw [walk_cons]; exact ihl⟩
    have hic : invC c < m + m := by
      rw [invC_eq]
      split_ifs with h
      · omega
      · omega
    rw [List.map_cons, walk_cons]
    simp only [wF]
    rw [if_pos hic, ih, hb _ hic _ hy', invC_eq]
    obtain ⟨g, rfl | rfl⟩ : ∃ g, c = g + g ∨ c = g + g + 1 := ⟨c / 2, by omega⟩
    · rw [if_pos (by omega)]
      exact ((hL y hy).2 g (by omega)).1
    · rw [if_neg (by omega), show g + g + 1 - 1 = g + g by omega]
      exact ((hL y hy).2 g (by omega)).2

theorem pointOK_all_of {rels : List (List ℕ)} (hk : k ≤ 32) (hN : N ≤ 2 ^ k)
    (h1 : allR 0 N (pointOK A m N []) = true)
    (h2 : ∀ c < m + m, CFSG.KC.YModel.letOK k N (lineL A (m + m) c N) (Nf c) = true)
    (h3 : CFSG.KC.YModel.relsOK k (m + m) Nf (invRels rels) = true)
    (hcodes : ∀ r ∈ rels, ∀ c ∈ r, c < m + m) :
    allR 0 N (pointOK A m N rels) = true := by
  have hP : ∀ x < N, pointOK A m N [] x = true := fun x hx =>
    allR_spec h1 x (Nat.zero_le x) (by omega)
  have hL : ∀ x < N, LetOK A m N x := fun x hx => (pointOK_spec (hP x hx)).1
  have hv : ∀ c < m + m, CFSG.KC.Benes.StagesValid k (Nf c) := fun c hc =>
    (letOK_spec hk (h2 c hc)).2.1
  have h32 : N ≤ 2 ^ 32 := le_trans hN (Nat.pow_le_pow_right (by norm_num) hk)
  have hb : ∀ c < m + m, ∀ i < N, CFSG.KC.Benes.benesPerm k (Nf c) i = step A (m + m) i c := by
    intro c hc i hi
    obtain ⟨-, -, hf, -⟩ := letOK_spec hk (h2 c hc)
    have hA : ∀ j < N, A (j * (m + m) + c) < 2 ^ 32 := fun j hj => by
      have := (hL j hj).1 c hc
      have e : step A (m + m) j c = A (j * (m + m) + c) := rfl
      rw [e] at this
      omega
    rw [← hf i hi, (lineL_spec A (m + m) c N hA).2 i hi]
    rfl
  apply allR_of
  intro x _ hx
  have hx' : x < N := by omega
  have hPx := hP x hx'
  unfold pointOK at hPx ⊢
  obtain ⟨p1, hp⟩ := CFSG.KC.Benes.andB_true hPx
  obtain ⟨p2, -⟩ := CFSG.KC.Benes.andB_true hp
  refine brec_true' p1 (brec_true' p2 (relsAt_of fun r hr => ?_))
  have hid := relsOK_mem' h3 (r.map invC) (by rw [invRels_eq]; exact List.mem_map_of_mem hr)
  have hwf := eq_of_idP (acts_wordAp hv (r.map invC)) (acts_id k k) hid
  obtain ⟨e1, e2⟩ := wF_walk hL hb r (hcodes r hr) x hx'
  rw [hwf _ (by omega)] at e1
  exact e1

end

end CFSG.KC.MiscCoset.Act

end
