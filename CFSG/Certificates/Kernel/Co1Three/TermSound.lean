module

public import CFSG.Certificates.Kernel.Co1Three.SlpSound

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2

@[expose] def matK (W : Nat) : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 (unpackR 24 W)

theorem mRep_iff (W : Nat) (g : GL24) : MRep (unpackR 24 W) g ↔ matK W = g := Iff.rfl

theorem matK_mulWK (A B : Nat) : matK (mulWK A B) = matK A * matK B := by
  rw [matK, ← mulWK_unpack, rowsMatrix_mulRows]
  rfl

theorem matK_oneK : matK oneK = 1 := by
  rw [matK, ← one_eq]
  exact rowsMatrix_idRows 24

@[expose] def epM {M : Type*} [Monoid M] (f : Nat → M) (p : Nat) : List Nat → Nat → M → M
  | [], _, acc => acc
  | g :: G, v, acc => epM f p G (v / p) (acc * f g ^ (v % p))

@[expose] def termM {M : Type*} [Monoid M] (f : Nat → M) (p : Nat) (GLs : List (List Nat)) (t : Nat) : M :=
  if t % 2 = 0 then f (t / 2) else epM f p (GLs.getD (t / 2 % 4) []) (t / 8) 1

theorem epM_map {M M' : Type*} [Monoid M] [Monoid M'] (φ : M →* M') (f : Nat → M) (p : Nat) :
    ∀ (G : List Nat) (v : Nat) (acc : M), epM (fun k => φ (f k)) p G v (φ acc) = φ (epM f p G v acc)
  | [], _, _ => rfl
  | g :: G, v, acc => by
    rw [epM, epM, ← map_pow, ← map_mul, epM_map φ f p G]

theorem termM_map {M M' : Type*} [Monoid M] [Monoid M'] (φ : M →* M') (f : Nat → M) (p : Nat)
    (GLs : List (List Nat)) (t : Nat) : termM (fun k => φ (f k)) p GLs t = φ (termM f p GLs t) := by
  unfold termM
  split_ifs
  · rfl
  · rw [← epM_map φ f p, map_one]

theorem epM_congr {M : Type*} [Monoid M] {f f' : Nat → M} (p : Nat) :
    ∀ (G : List Nat), (∀ g ∈ G, f g = f' g) → ∀ (v : Nat) (acc : M), epM f p G v acc = epM f' p G v acc
  | [], _, _, _ => rfl
  | g :: G, h, v, acc => by
    rw [epM, epM, h g List.mem_cons_self, epM_congr p G (fun x hx => h x (List.mem_cons_of_mem g hx))]

theorem getLL_eq (L : List (List Nat)) (i : Nat) : getLL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem powRec_mat (TS : Nat → Nat) (g acc : Nat) :
    ∀ e : Nat, matK (Nat.rec (motive := fun _ => Nat) acc (fun _ a => strictN a fun a => mulWK a (TS g)) e) =
      matK acc * matK (TS g) ^ e
  | 0 => by
    rw [pow_zero, mul_one]
    rfl
  | e + 1 => by
    change matK (strictN (Nat.rec (motive := fun _ => Nat) acc
      (fun _ a => strictN a fun a => mulWK a (TS g)) e) fun a => mulWK a (TS g)) = _
    rw [strictN_eq, matK_mulWK, powRec_mat TS g acc e, pow_succ, mul_assoc]

theorem epK_mat (TS : Nat → Nat) (p : Nat) :
    ∀ (G : List Nat) (v acc : Nat), matK (epK TS p G v acc) = epM (fun k => matK (TS k)) p G v (matK acc)
  | [], _, _ => rfl
  | g :: G, v, acc => by
    change matK (strictN (v % p) fun e => strictN (Nat.rec (motive := fun _ => Nat) acc
      (fun _ a => strictN a fun a => mulWK a (TS g)) e) fun acc' => epK TS p G (v / p) acc') = _
    rw [strictN_eq, strictN_eq, epK_mat TS p G, powRec_mat, epM]

theorem termK_mat (TS : Nat → Nat) (p : Nat) (GLs : List (List Nat)) (t : Nat) :
    matK (termK TS p GLs t) = termM (fun k => matK (TS k)) p GLs t := by
  have h1 : Nat.land t 1 = t % 2 := Nat.and_one_is_mod t
  have h2 : Nat.shiftRight t 1 = t / 2 := by
    change t >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have h3 : Nat.land (t / 2) 3 = t / 2 % 4 := Nat.and_two_pow_sub_one_eq_mod (t / 2) 2
  have h4 : Nat.shiftRight t 3 = t / 8 := Nat.shiftRight_eq_div_pow t 3
  change matK (Bool.rec (motive := fun _ => Nat) (epK TS p (getLL GLs (Nat.land (Nat.shiftRight t 1) 3))
    (Nat.shiftRight t 3) oneK) (TS (Nat.shiftRight t 1)) (Nat.beq (Nat.land t 1) 0)) = _
  rw [nrec_eq, h1, h2, h3, h4, getLL_eq, termM]
  by_cases ht : t % 2 = 0
  · rw [if_pos (Nat.beq_eq_true_eq _ _ ▸ ht), if_pos ht]
  · rw [if_neg (fun h => ht (Nat.eq_of_beq_eq_true h)), if_neg ht, epK_mat, matK_oneK]

theorem eqsK_sound {TS : Nat → Nat} {p : Nat} {GLs : List (List Nat)} :
    ∀ {Q : List (List Nat)}, eqsK TS p GLs Q = true → ∀ q ∈ Q, q.length = 4 ∧
      termM (fun k => matK (TS k)) p GLs (q.getD 0 0) * termM (fun k => matK (TS k)) p GLs (q.getD 1 0) =
        termM (fun k => matK (TS k)) p GLs (q.getD 2 0) * termM (fun k => matK (TS k)) p GLs (q.getD 3 0)
  | [], _, q, hq => absurd hq List.not_mem_nil
  | q₀ :: Q, h, q, hq => by
    have h' : Bool.rec (motive := fun _ => Bool) false (eqsK TS p GLs Q) (eqK TS p GLs q₀) = true := h
    rw [brec_eq_true] at h'
    simp only [Bool.false_eq_true, and_false, or_false] at h'
    rcases List.mem_cons.1 hq with rfl | hq
    · have he : Bool.rec (motive := fun _ => Bool) false (Nat.beq (mulWK (termK TS p GLs (getL 0 q 0))
          (termK TS p GLs (getL 0 q 1))) (mulWK (termK TS p GLs (getL 0 q 2)) (termK TS p GLs (getL 0 q 3))))
          (Nat.beq (lenL q) 4) = true := h'.1
      rw [brec_eq_true] at he
      simp only [Bool.false_eq_true, and_false, or_false] at he
      refine ⟨by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true he.1, ?_⟩
      have := congrArg matK (Nat.eq_of_beq_eq_true he.2)
      rwa [matK_mulWK, matK_mulWK, termK_mat, termK_mat, termK_mat, termK_mat, getL_eq, getL_eq, getL_eq,
        getL_eq] at this
    · exact eqsK_sound h'.2 q hq

theorem normRowsK_sound {TS : Nat → Nat} {p : Nat} {G : List Nat} {g : Nat} :
    ∀ {rows : List Nat} {j : Nat}, normRowsK TS p G g rows j = true → ∀ i < rows.length,
      matK (TS (G.getD (j + i) 0)) * matK (TS g) =
        matK (TS g) * epM (fun k => matK (TS k)) p G (rows.getD i 0) 1
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | v :: rows, j, h, i, hi => by
    have h' : strictB j (fun j => Bool.rec (motive := fun _ => Bool) false (normRowsK TS p G g rows (Nat.succ j))
        (Nat.beq (mulWK (TS (getL 0 G j)) (TS g)) (mulWK (TS g) (epK TS p G v oneK)))) = true := h
    rw [strictB_eq, brec_eq_true] at h'
    simp only [Bool.false_eq_true, and_false, or_false] at h'
    cases i with
    | zero =>
      have := congrArg matK (Nat.eq_of_beq_eq_true h'.1)
      rwa [matK_mulWK, matK_mulWK, epK_mat, matK_oneK, getL_eq] at this
    | succ i =>
      have := normRowsK_sound h'.2 i (Nat.lt_of_succ_lt_succ hi)
      rwa [Nat.succ_add_eq_add_succ] at this

theorem normK_sound {TS : Nat → Nat} {p : Nat} {GLs : List (List Nat)} :
    ∀ {NZ : List (Nat × List Nat)}, normK TS p GLs NZ = true → ∀ x ∈ NZ,
      x.2.length = (GLs.getD 0 []).length ∧ ∀ j < x.2.length,
        matK (TS ((GLs.getD 0 []).getD j 0)) * matK (TS x.1) =
          matK (TS x.1) * epM (fun k => matK (TS k)) p (GLs.getD 0 []) (x.2.getD j 0) 1
  | [], _, x, hx => absurd hx List.not_mem_nil
  | (g, rows) :: NZ, h, x, hx => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (normK TS p GLs NZ) (normRowsK TS p (getLL GLs 0) g rows 0))
        (Nat.beq (lenL rows) (lenL (getLL GLs 0))) = true := h
    simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [getLL_eq] at h'
      refine ⟨by rw [← lenL_eq, ← lenL_eq]; exact Nat.eq_of_beq_eq_true h'.1, fun j hj => ?_⟩
      have := normRowsK_sound h'.2.1 j hj
      rwa [Nat.zero_add] at this
    · exact normK_sound h'.2.2 x hx

theorem nzLen_eq (NZ : List (Nat × List Nat)) : nzLen NZ = NZ.length := by
  induction NZ with
  | nil => rfl
  | cons a L ih => exact congrArg Nat.succ ih

theorem memK_sound {c : Nat} : ∀ {L : List Nat}, memK c L = true → c ∈ L
  | [], h => absurd h (by simp [memK])
  | x :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memK c L) true (Nat.beq x c) = true := h
    rw [brec_eq_true] at h'
    rcases h' with ⟨h1, -⟩ | ⟨-, h1⟩
    · rw [Nat.eq_of_beq_eq_true h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem x (memK_sound h1)

theorem actK_zero (p n : Nat) : ∀ (rows : List Nat) (acc : Nat), actK p n rows 0 acc = acc
  | [], _ => rfl
  | r :: rows, acc => by
    change strictN (0 % p) (fun e => strictN (Nat.rec (motive := fun _ => Nat) acc
      (fun _ a => strictN a fun a => addVK p n a r) e) fun acc' => actK p n rows (0 / p) acc') = acc
    rw [strictN_eq, Nat.zero_mod, strictN_eq, Nat.zero_div]
    exact actK_zero p n rows acc

theorem forFromK_sound {p n P : Nat} {NZ : List (Nat × List Nat)} {RT : List Nat} {DP : Nat} :
    ∀ {FT : List Nat} {c : Nat}, forFromK p n P NZ RT DP FT c = true → ∀ c', c ≤ c' → c' < P →
      (depK DP c' = 0 ∧ c' ∈ RT) ∨
      (∃ pc < P, ∃ g < NZ.length, depK DP pc + 1 = depK DP c' ∧ actK p n (nzRows NZ g) pc 0 = c')
  | [], c, h, c', h1, h2 => by
    have : c = P := Nat.eq_of_beq_eq_true h
    omega
  | e :: FT, c, h, c', h1, h2 => by
    have h' : strictB c (fun c => strictB (depK DP c) fun d =>
        Bool.rec (motive := fun _ => Bool) false (forFromK p n P NZ RT DP FT (Nat.succ c))
          (Bool.rec (motive := fun _ => Bool)
            (strictB (e % P) fun pc => strictB (e / P) fun g =>
              Bool.rec (motive := fun _ => Bool) false
                (Bool.rec (motive := fun _ => Bool) false (Nat.beq (actK p n (nzRows NZ g) pc 0) c)
                  (Nat.beq (Nat.succ (depK DP pc)) d))
                (Nat.blt g (nzLen NZ)))
            (memK c RT) (Nat.beq d 0))) = true := h
    simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at h'
    obtain ⟨h3, h4⟩ := h'
    by_cases hc : c' = c
    · subst hc
      rcases h3 with ⟨h5, h6⟩ | ⟨-, h5, h6, h7⟩
      · exact Or.inl ⟨Nat.eq_of_beq_eq_true h5, memK_sound h6⟩
      · rw [Nat.blt_eq, nzLen_eq] at h5
        exact Or.inr ⟨e % P, Nat.mod_lt _ (by omega), e / P, h5, Nat.eq_of_beq_eq_true h6,
          Nat.eq_of_beq_eq_true h7⟩
    · exact forFromK_sound h4 c' (by omega) h2

theorem forestK_sound {p n : Nat} {NZ : List (Nat × List Nat)} {RT : List Nat} {DP : Nat} {FT : List Nat}
    (h : forestK p n NZ RT DP FT = true) :
    ∀ c, 1 ≤ c → c < p ^ n → ∃ r ∈ RT,
      Relation.ReflTransGen (fun a b => ∃ g < NZ.length, actK p n (nzRows NZ g) a 0 = b) r c := by
  have h' : forFromK p n (p ^ n) NZ RT DP FT 1 = true := by
    have h0 : strictB (Nat.pow p n) (fun P => forFromK p n P NZ RT DP FT 1) = true := h
    rwa [strictB_eq] at h0
  have key : ∀ d c, depK DP c = d → 1 ≤ c → c < p ^ n → ∃ r ∈ RT,
      Relation.ReflTransGen (fun a b => ∃ g < NZ.length, actK p n (nzRows NZ g) a 0 = b) r c := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro c hd h1 h2
      rcases forFromK_sound h' c h1 h2 with ⟨-, hr⟩ | ⟨pc, hpc, g, hg, hdp, hact⟩
      · exact ⟨c, hr, Relation.ReflTransGen.refl⟩
      · have hpc1 : 1 ≤ pc := by
          rcases Nat.eq_zero_or_pos pc with h0 | h0
          · rw [h0, actK_zero] at hact
            omega
          · exact h0
        obtain ⟨r, hr, hrt⟩ := ih (depK DP pc) (by omega) pc rfl hpc1 hpc
        exact ⟨r, hr, hrt.tail ⟨g, hg, hact⟩⟩
  exact fun c => key _ c rfl

end CFSG.KC.Co1Cl

end
