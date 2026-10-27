module

public import CFSG.Certificates.Kernel.NC2LiveSound
public import CFSG.Certificates.Kernel.NC2LMergeSound
import CFSG.Certificates.Kernel.OpsLayKSndP

public section

namespace CFSG.KC.NC2L

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KS.Ord CFSG.SectionRank.Native

section Pc

variable {M : Type*} [Monoid M]

@[expose] def nfG : List M → ℕ → M
  | [], _ => 1
  | g :: L, n => (if n % 2 = 1 then g else 1) * nfG L (n / 2)

@[expose] def nfSet (L : List M) : Set M := {x | ∃ n < 2 ^ L.length, nfG L n = x}

@[expose] def PcRel : List M → Prop
  | [] => True
  | g :: L => PcRel L ∧ g * g ∈ nfSet L ∧ ∀ h ∈ L, ∃ w ∈ nfSet L, h * g = g * w

theorem nfG_nil (n : ℕ) : nfG ([] : List M) n = 1 := rfl

theorem nfG_cons (g : M) (L : List M) (n : ℕ) :
    nfG (g :: L) n = (if n % 2 = 1 then g else 1) * nfG L (n / 2) := rfl

theorem nfG_zero : ∀ L : List M, nfG L 0 = 1
  | [] => rfl
  | g :: L => by
    rw [nfG_cons, Nat.zero_div, nfG_zero L, if_neg (by decide), one_mul]

theorem nfG_map {N : Type*} [Monoid N] (f : M →* N) :
    ∀ (L : List M) (n : ℕ), nfG (L.map f) n = f (nfG L n)
  | [], _ => by rw [List.map_nil, nfG_nil, nfG_nil, map_one]
  | g :: L, n => by
    rw [List.map_cons, nfG_cons, nfG_cons, nfG_map f L, map_mul]
    split
    · rfl
    · rw [map_one]

theorem getD_map_hom {N : Type*} [Monoid N] (f : M →* N) :
    ∀ (L : List M) (i : ℕ), (L.map f).getD i 1 = f (L.getD i 1)
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: L, i + 1 => by simpa using getD_map_hom f L i

theorem nfG_mem (K : Submonoid M) : ∀ {L : List M}, (∀ h ∈ L, h ∈ K) → ∀ n, nfG L n ∈ K
  | [], _, _ => K.one_mem
  | g :: L, hL, n => by
    rw [nfG_cons]
    refine K.mul_mem ?_ (nfG_mem K (fun h hh => hL h (List.mem_cons_of_mem _ hh)) _)
    split
    · exact hL g List.mem_cons_self
    · exact K.one_mem

theorem one_mem_nfSet (L : List M) : (1 : M) ∈ nfSet L := ⟨0, Nat.two_pow_pos _, nfG_zero L⟩

theorem mem_nfSet_cons {g x : M} {L : List M} :
    x ∈ nfSet (g :: L) ↔ ∃ s ∈ nfSet L, x = s ∨ x = g * s := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [List.length_cons, pow_succ] at hn
    refine ⟨nfG L (n / 2), ⟨n / 2, by omega, rfl⟩, ?_⟩
    rw [nfG_cons]
    split
    · exact Or.inr rfl
    · exact Or.inl (one_mul _)
  · rintro ⟨s, ⟨m, hm, rfl⟩, rfl | rfl⟩
    · refine ⟨2 * m, by rw [List.length_cons, pow_succ]; omega, ?_⟩
      rw [nfG_cons, if_neg (by omega), Nat.mul_div_cancel_left _ two_pos, one_mul]
    · refine ⟨2 * m + 1, by rw [List.length_cons, pow_succ]; omega, ?_⟩
      have e : (2 * m + 1) / 2 = m := by omega
      rw [nfG_cons, if_pos (by omega), e]

theorem nfSet_mul : ∀ {L : List M}, PcRel L → ∀ x ∈ nfSet L, ∀ y ∈ nfSet L, x * y ∈ nfSet L
  | [], _, x, ⟨_, _, hx⟩, y, ⟨_, _, hy⟩ => by
    rw [← hx, ← hy, nfG_nil, nfG_nil, one_mul]
    exact one_mem_nfSet []
  | g :: L, ⟨hL, hg, hrel⟩, x, hx, y, hy => by
    have ih := nfSet_mul hL
    let T : Submonoid M :=
      { carrier := {s | ∃ w ∈ nfSet L, s * g = g * w}
        mul_mem' := fun {a b} ⟨wa, ha, ea⟩ ⟨wb, hb, eb⟩ =>
          ⟨wa * wb, ih wa ha wb hb, by rw [mul_assoc, eb, ← mul_assoc, ea, mul_assoc]⟩
        one_mem' := ⟨1, one_mem_nfSet L, by rw [one_mul, mul_one]⟩ }
    have hA : ∀ s ∈ nfSet L, ∃ w ∈ nfSet L, s * g = g * w := by
      rintro s ⟨n, -, rfl⟩
      exact nfG_mem T (fun h hh => hrel h hh) n
    obtain ⟨s, hs, ex⟩ := mem_nfSet_cons.1 hx
    obtain ⟨t, ht, ey⟩ := mem_nfSet_cons.1 hy
    rcases ex with ex | ex <;> rcases ey with ey | ey <;> rw [ex, ey]
    · exact mem_nfSet_cons.2 ⟨s * t, ih s hs t ht, Or.inl rfl⟩
    · obtain ⟨w, hw, e⟩ := hA s hs
      exact mem_nfSet_cons.2 ⟨w * t, ih w hw t ht, Or.inr (by rw [← mul_assoc, e, mul_assoc])⟩
    · exact mem_nfSet_cons.2 ⟨s * t, ih s hs t ht, Or.inr (mul_assoc _ _ _)⟩
    · obtain ⟨w, hw, e⟩ := hA s hs
      refine mem_nfSet_cons.2 ⟨g * g * (w * t), ih _ hg _ (ih w hw t ht), Or.inl ?_⟩
      rw [mul_assoc g s, ← mul_assoc s, e]
      simp only [mul_assoc]

theorem isUnit_of_pcRel : ∀ {L : List M}, PcRel L → ∀ h ∈ L, IsUnit h
  | [], _, h, hh => by simp at hh
  | g :: L, ⟨hL, hg, _⟩, h, hh => by
    have ih := isUnit_of_pcRel hL
    rcases List.mem_cons.1 hh with rfl | hh
    · obtain ⟨n, -, e⟩ := hg
      have hu : IsUnit (h * h) := by
        rw [← e]
        exact (IsUnit.mem_submonoid_iff _).1
          (nfG_mem (IsUnit.submonoid M) (fun y hy => (IsUnit.mem_submonoid_iff _).2 (ih y hy)) n)
      rw [← pow_two] at hu
      exact (isUnit_pow_iff two_ne_zero).1 hu
    · exact ih h hh

theorem nfG_two_pow_mul : ∀ (k : ℕ) (L : List M) (m : ℕ), nfG L (2 ^ k * m) = nfG (L.drop k) m
  | 0, L, m => by rw [pow_zero, one_mul, List.drop_zero]
  | k + 1, [], m => rfl
  | k + 1, g :: L, m => by
    rw [nfG_cons, List.drop_succ_cons, ← nfG_two_pow_mul k L m]
    have e : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [e, if_neg (by rw [Nat.mul_mod_right]; decide), Nat.mul_div_cancel_left _ two_pos, one_mul]

theorem pcRel_of (gs : List M)
    (hsq : ∀ i < gs.length, ∃ m < 2 ^ gs.length, 2 ^ (i + 1) ∣ m ∧
      gs.getD i 1 * gs.getD i 1 = nfG gs m)
    (hcj : ∀ i j, i < j → j < gs.length → ∃ m < 2 ^ gs.length, 2 ^ (i + 1) ∣ m ∧
      gs.getD j 1 * gs.getD i 1 = gs.getD i 1 * nfG gs m) : PcRel gs := by
  have hset : ∀ i < gs.length, ∀ m < 2 ^ gs.length, 2 ^ (i + 1) ∣ m →
      nfG gs m ∈ nfSet (gs.drop (i + 1)) := by
    rintro i hi m hm ⟨q, rfl⟩
    refine ⟨q, ?_, (nfG_two_pow_mul _ _ _).symm⟩
    rw [List.length_drop]
    have e : 2 ^ gs.length = 2 ^ (i + 1) * 2 ^ (gs.length - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e] at hm
    exact Nat.lt_of_mul_lt_mul_left hm
  suffices h : ∀ t k, k + t = gs.length → PcRel (gs.drop k) by
    simpa using h gs.length 0 (by omega)
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [List.drop_eq_nil_of_le (by omega)]
    trivial
  | succ t ih =>
    intro k hk
    have hk' : k < gs.length := by omega
    rw [List.drop_eq_getElem_cons hk']
    refine ⟨ih (k + 1) (by omega), ?_, ?_⟩
    · obtain ⟨m, hm, hd, e⟩ := hsq k hk'
      rw [List.getD_eq_getElem _ _ hk'] at e
      rw [e]
      exact hset k hk' m hm hd
    · intro h hh
      obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hh
      rw [List.length_drop] at hu
      rw [List.getElem_drop]
      obtain ⟨m, hm, hd, e⟩ := hcj k (k + 1 + u) (by omega) (by omega)
      rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ (by omega)] at e
      exact ⟨nfG gs m, hset k hk' m hm hd, e⟩

end Pc

structure NC2Mat {p d : ℕ} (D : NC2LData) (M : ℕ → Matrix (Fin d) (Fin d) (ZMod p))
    (gs : List (Matrix (Fin d) (Fin d) (ZMod p))) : Prop where
  len : gs.length = D.a
  t_sq : M 0 * M 0 = 1
  t_ne : M 0 ≠ 1
  g_comm : M 1 * M 0 = M 0 * M 1
  x_comm : M 3 * M 0 = M 0 * M 3
  g_inv : M 1 * M 2 = 1
  odd : D.oddExp % 2 = 1
  x_pow : M 3 ^ D.oddExp = 1
  x_ne : M 3 ≠ 1
  extra : ∀ i < D.extra.length, (D.extra.getD i 0).Prime ∧ M (4 + i) * M 0 = M 0 * M (4 + i) ∧
    M (4 + i) ^ D.extra.getD i 0 = 1 ∧ M (4 + i) ≠ 1
  gens_comm : ∀ g ∈ gs, g * M 0 = M 0 * g
  sq : ∀ i < D.a, ∃ m < 2 ^ D.a, 2 ^ (i + 1) ∣ m ∧ gs.getD i 1 * gs.getD i 1 = nfG gs m
  cj : ∀ i j, i < j → j < D.a → ∃ m < 2 ^ D.a, 2 ^ (i + 1) ∣ m ∧
    gs.getD j 1 * gs.getD i 1 = gs.getD i 1 * nfG gs m
  inj : ∀ n < 2 ^ D.a, ∀ m < 2 ^ D.a, nfG gs n = nfG gs m → n = m
  inter : ∀ n < 2 ^ D.a, ∀ m < 2 ^ D.a, M 1 * nfG gs n * M 2 = nfG gs m →
    M 3 * (M 1 * nfG gs n * M 2) = M 1 * nfG gs n * M 2 * M 3

open scoped Matrix

private theorem nc2m_beq {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem nc2m_blt {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

private theorem nc2m_mapV (c : Lay) (M : ℕ) : ∀ (us : List ℕ) (k : List ℕ → Bool),
    mapV c M us k = k (us.map fun u => c.vec u M)
  | [], _ => rfl
  | u :: us, k => by
    have e : mapV c M (u :: us) k =
        strictB (c.vec u M) fun v => mapV c M us fun vs => k (v :: vs) := rfl
    rw [e, SecS.strictB_eq, nc2m_mapV c M us, List.map_cons]

private def nc2m_key (B : ℕ) (vs : List ℕ) : ℕ :=
  vs.foldl (fun acc v => Nat.add (Nat.mul acc B) v) 0

private theorem nc2m_keyRec (B : ℕ) (k : ℕ → Bool) : ∀ (vs : List ℕ) (acc : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun acc => k acc)
      (fun v _ ih acc => strictB (Nat.add (Nat.mul acc B) v) ih) vs acc =
    k (vs.foldl (fun acc v => Nat.add (Nat.mul acc B) v) acc)
  | [], _ => rfl
  | v :: vs, acc => by
    change strictB (Nat.add (Nat.mul acc B) v) (List.rec (motive := fun _ => ℕ → Bool)
      (fun acc => k acc) (fun v _ ih acc => strictB (Nat.add (Nat.mul acc B) v) ih) vs) = _
    rw [SecS.strictB_eq, nc2m_keyRec B k vs, List.foldl_cons]

private theorem nc2m_keyOf (B : ℕ) (vs : List ℕ) (k : ℕ → Bool) :
    keyOf B vs k = k (nc2m_key B vs) :=
  nc2m_keyRec B k vs 0

private noncomputable def nc2m_vt (c : Lay) (F : List ℕ → ℕ) : List ℕ → List ℕ → BT
  | [], us => BT.leaf (F us)
  | g :: gs, us => BT.node (nc2m_vt c F gs us) (nc2m_vt c F gs (us.map fun u => c.vec u g))

private theorem nc2m_vecsTree (c : Lay) {post : List ℕ → (ℕ → Bool) → Bool} {F : List ℕ → ℕ}
    (hpost : ∀ us k, post us k = k (F us)) :
    ∀ (gs us : List ℕ) (k : BT → Bool), vecsTree c post gs us k = k (nc2m_vt c F gs us)
  | [], us, k => by
    change post us (fun v => k (BT.leaf v)) = _
    rw [hpost]
    rfl
  | g :: gs, us, k => by
    change vecsTree c post gs us (fun l => mapV c g us fun us' =>
      vecsTree c post gs us' fun r => k (BT.node l r)) = _
    simp only [nc2m_vecsTree c hpost gs, nc2m_mapV, nc2m_vt]

private noncomputable def nc2m_vecN (c : Lay) : List ℕ → ℕ → ℕ → ℕ
  | [], u, _ => u
  | g :: gs, u, n => nc2m_vecN c gs (if n % 2 = 1 then c.vec u g else u) (n / 2)

private theorem nc2m_vecN_nil (c : Lay) (u n : ℕ) : nc2m_vecN c [] u n = u := rfl

private theorem nc2m_vecN_cons (c : Lay) (g : ℕ) (gs : List ℕ) (u n : ℕ) :
    nc2m_vecN c (g :: gs) u n = nc2m_vecN c gs (if n % 2 = 1 then c.vec u g else u) (n / 2) :=
  rfl

private theorem nc2m_get (c : Lay) (F : List ℕ → ℕ) : ∀ (gs us : List ℕ) (n : ℕ),
    (nc2m_vt c F gs us).get n = F (us.map fun u => nc2m_vecN c gs u n)
  | [], us, n => by
    change F us = _
    simp only [nc2m_vecN_nil, List.map_id']
  | g :: gs, us, n => by
    change Bool.rec (motive := fun _ => ℕ) ((nc2m_vt c F gs us).get (n / 2))
      ((nc2m_vt c F gs (us.map fun u => c.vec u g)).get (n / 2)) (Nat.beq (n % 2) 1) = _
    rw [nc2m_get c F gs, nc2m_get c F gs]
    cases hb : Nat.beq (n % 2) 1
    · have h : ¬ n % 2 = 1 := Nat.ne_of_beq_eq_false hb
      dsimp only
      congr 1
      refine List.map_congr_left fun u _ => ?_
      rw [nc2m_vecN_cons, if_neg h]
    · have h : n % 2 = 1 := Nat.eq_of_beq_eq_true hb
      dsimp only
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun u _ => ?_
      rw [Function.comp_apply, nc2m_vecN_cons, if_pos h]

private theorem nc2m_vecN_sound (c : Lay) (hc : c.ok = true) : ∀ {gs : List ℕ},
    (∀ g ∈ gs, Canon c.p c.d c.w g) → ∀ (n : ℕ) {u : ℕ}, SecS.VCanon c.p c.d c.w u →
      SecS.VCanon c.p c.d c.w (nc2m_vecN c gs u n) ∧
        SecS.toVec c.p c.d c.w (nc2m_vecN c gs u n) =
          SecS.toVec c.p c.d c.w u ᵥ* nfG (gs.map (ordMat c.p c.d c.w c.S)) n
  | [], _, n, u, hu => by
    rw [nc2m_vecN_nil, List.map_nil, nfG_nil, Matrix.vecMul_one]
    exact ⟨hu, rfl⟩
  | g :: gs, hg, n, u, hu => by
    have hg0 := hg g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, Canon c.p c.d c.w g' := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    rw [nc2m_vecN_cons, List.map_cons, nfG_cons]
    by_cases h : n % 2 = 1
    · rw [if_pos h, if_pos h]
      obtain ⟨h1, h2⟩ := SecS.vec_sound c hc hu hg0
      obtain ⟨h3, h4⟩ := nc2m_vecN_sound c hc hgs (n / 2) h1
      exact ⟨h3, by rw [h4, h2, Matrix.vecMul_vecMul]⟩
    · rw [if_neg h, if_neg h, one_mul]
      exact nc2m_vecN_sound c hc hgs (n / 2) hu

private theorem nc2m_nfL (c : Lay) (hc : c.ok = true) : ∀ {gs : List ℕ},
    (∀ g ∈ gs, Canon c.p c.d c.w g) → ∀ n, Canon c.p c.d c.w (nfL c gs n) ∧
      ordMat c.p c.d c.w c.S (nfL c gs n) = nfG (gs.map (ordMat c.p c.d c.w c.S)) n
  | [], _, n => ⟨(one_sound hc).1, by rw [List.map_nil, nfG_nil]; exact (one_sound hc).2⟩
  | g :: gs, hg, n => by
    have hg0 := hg g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, Canon c.p c.d c.w g' := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    obtain ⟨h1, h2⟩ := nc2m_nfL c hc hgs (n / 2)
    have e : nfL c (g :: gs) n = Bool.rec (motive := fun _ => ℕ) (nfL c gs (n / 2))
        (Bool.rec (motive := fun _ => ℕ) (c.mul g (nfL c gs (n / 2))) g (Nat.beq (n / 2) 0))
        (Nat.beq (n % 2) 1) := rfl
    rw [e, List.map_cons, nfG_cons]
    cases hb : Nat.beq (n % 2) 1
    · have h : ¬ n % 2 = 1 := Nat.ne_of_beq_eq_false hb
      rw [if_neg h, one_mul]
      exact ⟨h1, h2⟩
    · have h : n % 2 = 1 := Nat.eq_of_beq_eq_true hb
      rw [if_pos h]
      cases hb2 : Nat.beq (n / 2) 0
      · obtain ⟨h3, h4⟩ := SecS.mul_sound c hc hg0 h1
        exact ⟨h3, by dsimp only; rw [h4, h2]⟩
      · have h0 : n / 2 = 0 := Nat.eq_of_beq_eq_true hb2
        refine ⟨hg0, ?_⟩
        dsimp only
        rw [h0, nfG_zero, mul_one]

private theorem nc2m_getR {c : Lay} (hc : c.ok = true) {O : List ℕ}
    (hO : ∀ x ∈ O, Canon c.p c.d c.w x) (i : ℕ) : Canon c.p c.d c.w (getR c O i) := by
  unfold getR
  by_cases hi : i < O.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hO _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact (one_sound hc).1

private theorem nc2m_getD_map (c : Lay) {G : List ℕ} {i : ℕ} (hi : i < G.length) :
    (G.map (ordMat c.p c.d c.w c.S)).getD i 1 = ordMat c.p c.d c.w c.S (getR c G i) := by
  unfold getR
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

private theorem nc2m_prime {q : ℕ} (h : primeB q = true) : q.Prime := by
  unfold primeB at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [Nat.prime_def_lt']
  refine ⟨Nat.le_of_ble_eq_true h1, fun m hm2 hmq hdvd => ?_⟩
  have h3 := h2 m (List.mem_range.2 hmq)
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · exact absurd (nc2m_blt.1 h3) (by omega)
  · have h4 : Nat.beq (Nat.mod q m) 0 = false := by
      cases hb : Nat.beq (Nat.mod q m) 0
      · rfl
      · rw [hb] at h3
        exact absurd h3 (by decide)
    exact Nat.ne_of_beq_eq_false h4 (Nat.mod_eq_zero_of_dvd hdvd)

private theorem nc2m_moves {c : Lay} (hc : c.ok = true) {tests : List ℕ}
    (ht : ∀ k ∈ tests, k < c.d) {M : ℕ} (hM : Canon c.p c.d c.w M)
    (h : movesL c tests M = true) : ordMat c.p c.d c.w c.S M ≠ 1 := by
  unfold movesL at h
  rw [List.any_eq_true] at h
  obtain ⟨k, hk, hne⟩ := h
  intro h1
  have hu := SecS.unit_canon c hc (ht k hk)
  obtain ⟨w1, f1⟩ := SecS.vec_sound c hc hu hM
  have e := SecS.vec_inj (SecS.lay_w_pos c hc) w1 hu (by rw [f1, h1, Matrix.vecMul_one])
  rw [e, Nat.beq_refl] at hne
  exact absurd hne (by decide)

theorem nc2L_mat {c : Lay} (hc : c.ok = true) {O : List ℕ} {D : NC2LData}
    (hO : ∀ x ∈ O, Canon c.p c.d c.w x) (h : nc2L c O D = true) :
    NC2Mat D (fun i => ordMat c.p c.d c.w c.S (getR c O i))
      ((O.drop (4 + D.extra.length)).map (ordMat c.p c.d c.w c.S)) := by
  have hR := nc2m_getR hc hO
  have hone : ∀ {A B : ℕ}, Canon c.p c.d c.w A → Canon c.p c.d c.w B →
      Nat.beq (c.mul A B) c.ONE = true →
      ordMat c.p c.d c.w c.S A * ordMat c.p c.d c.w c.S B = 1 := by
    intro A B hA hB h
    have e := SecS.mat_of_beq c h
    rwa [(SecS.mul_sound c hc hA hB).2, (one_sound hc).2] at e
  have hcomm : ∀ {A B : ℕ}, Canon c.p c.d c.w A → Canon c.p c.d c.w B → commK c A B = true →
      ordMat c.p c.d c.w c.S A * ordMat c.p c.d c.w c.S B =
        ordMat c.p c.d c.w c.S B * ordMat c.p c.d c.w c.S A :=
    fun hA hB h => SecS.mul_eq_of c hc hA hB hB hA h
  have hpow : ∀ {X e : ℕ}, Canon c.p c.d c.w X → e < 65536 →
      Nat.beq (powK c X e) c.ONE = true → ordMat c.p c.d c.w c.S X ^ e = 1 := by
    intro X e hX he h
    have e1 := SecS.mat_of_beq c h
    rw [(one_sound hc).2] at e1
    change ordMat c.p c.d c.w c.S (powN c 17 X e) = 1 at e1
    rwa [(SndP.powN_spec hc 17 e hX (Nat.lt_trans he (by norm_num))).2] at e1
  unfold nc2L sigL at h
  set G := O.drop (4 + D.extra.length) with hG
  have hGc : ∀ g ∈ G, Canon c.p c.d c.w g := fun g hg => hO g (List.mem_of_mem_drop hg)
  have hRG := nc2m_getR hc hGc
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  have ht : ∀ k ∈ D.tests, k < c.d := fun k hk => nc2m_blt.1 (List.all_eq_true.1 h2 k hk)
  have hlen : G.length = D.a := by
    rw [hG, List.length_drop, nc2m_beq.1 h1]
    omega
  unfold pcL at h14
  simp only [Bool.and_eq_true] at h14
  obtain ⟨-, hpc⟩ := h14
  have hrow : ∀ i < D.a, _ := fun i hi => List.all_eq_true.1 hpc i (List.mem_range.2 hi)
  obtain ⟨hs1, hs2⟩ := SecS.andT h16
  have hpostC : ∀ (us : List ℕ) (k : ℕ → Bool),
      (fun (us : List ℕ) (k : ℕ → Bool) => keyOf (Nat.shiftLeft 1 c.S) (us.map fun u => c.vec u (getR c O 2)) k) us k =
        k (nc2m_key (Nat.shiftLeft 1 c.S) (us.map fun u => c.vec u (getR c O 2))) :=
    fun us k => nc2m_keyOf _ _ k
  simp only [nc2m_vecsTree c (F := nc2m_key (Nat.shiftLeft 1 c.S))
    (fun us k => nc2m_keyOf _ us k), nc2m_mapV, nc2m_vecsTree c hpostC] at hs2
  obtain ⟨hsort, hmerge⟩ := SecS.andT hs2
  have hU : ∀ u ∈ D.sig.map c.unit, SecS.VCanon c.p c.d c.w u := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hu
    exact SecS.unit_canon c hc (nc2m_blt.1 (List.all_eq_true.1 hs1 k hk))
  have hN : ∀ {n : ℕ}, n < 2 ^ D.a → n < Nat.pow 2 D.a := fun hn => by
    rw [Nat.pow_eq]
    exact hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map, hlen]
  · exact hone (hR 0) (hR 0) h3
  · exact nc2m_moves hc ht (hR 0) h4
  · exact hcomm (hR 1) (hR 0) h5
  · exact hcomm (hR 3) (hR 0) h6
  · exact hone (hR 1) (hR 2) h7
  · exact Nat.eq_of_beq_eq_true h8
  · exact hpow (hR 3) (nc2m_blt.1 h9) h10
  · exact nc2m_moves hc ht (hR 3) h11
  · intro i hi
    have e := List.all_eq_true.1 h12 i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := e
    exact ⟨nc2m_prime e1, hcomm (hR _) (hR 0) e3, hpow (hR _) (nc2m_blt.1 e2) e4,
      nc2m_moves hc ht (hR _) e5⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    exact hcomm (hGc x hx) (hR 0) (List.all_eq_true.1 h13 x hx)
  · intro i hi
    have e := hrow i hi
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, -⟩, -⟩ := e
    have hiG : i < G.length := by omega
    refine ⟨D.sq.getD i 0, ?_, ?_, ?_⟩
    · have := nc2m_blt.1 e1
      rwa [Nat.pow_eq] at this
    · apply Nat.dvd_of_mod_eq_zero
      have := Nat.eq_of_beq_eq_true e2
      rwa [Nat.pow_eq] at this
    · rw [nc2m_getD_map c hiG, ← (SecS.mul_sound c hc (hRG i) (hRG i)).2, SecS.mat_of_beq c e3,
        (nc2m_nfL c hc hGc _).2]
  · intro i j hij hj
    obtain ⟨t, rfl⟩ : ∃ t, j = i + 1 + t := ⟨j - (i + 1), by omega⟩
    have e := hrow i (by omega)
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨-, e4⟩, e5⟩ := e
    have hlt : t < (D.cj.getD i []).length := by
      rw [nc2m_beq.1 e4]
      omega
    have f := List.all_eq_true.1 e5 t (List.mem_range.2 hlt)
    simp only [Bool.and_eq_true] at f
    obtain ⟨⟨f1, f2⟩, f3⟩ := f
    refine ⟨(D.cj.getD i []).getD t 0, ?_, ?_, ?_⟩
    · have := nc2m_blt.1 f1
      rwa [Nat.pow_eq] at this
    · apply Nat.dvd_of_mod_eq_zero
      have := Nat.eq_of_beq_eq_true f2
      rwa [Nat.pow_eq] at this
    · rw [nc2m_getD_map c (by omega), nc2m_getD_map c (by omega), ← (nc2m_nfL c hc hGc _).2,
        ← (SecS.mul_sound c hc (hRG _) (hRG _)).2,
        ← (SecS.mul_sound c hc (hRG _) (nc2m_nfL c hc hGc _).1).2]
      exact SecS.mat_of_beq c f3
  · intro n hn m hm he
    refine SecS.sortRun_inj hsort (hN hn) (hN hm) ?_
    rw [nc2m_get, nc2m_get]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    obtain ⟨a1, a2⟩ := nc2m_vecN_sound c hc hGc n (hU u hu)
    obtain ⟨b1, b2⟩ := nc2m_vecN_sound c hc hGc m (hU u hu)
    exact SecS.vec_inj (SecS.lay_w_pos c hc) a1 b1 (by rw [a2, b2, he])
  · intro n hn m hm he
    have hk : n ∈ D.pairs.map Prod.fst := by
      refine merge_sound hsort hmerge (hN hn) (hN hm) ?_
      rw [nc2m_get, nc2m_get, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      simp only [Function.comp_apply]
      obtain ⟨c1, d1⟩ := SecS.vec_sound c hc (hU u hu) (hR 1)
      obtain ⟨c2, d2⟩ := nc2m_vecN_sound c hc hGc n c1
      obtain ⟨c3, d3⟩ := SecS.vec_sound c hc c2 (hR 2)
      obtain ⟨c4, d4⟩ := nc2m_vecN_sound c hc hGc m (hU u hu)
      refine SecS.vec_inj (SecS.lay_w_pos c hc) c3 c4 ?_
      rw [d3, d2, d1, d4, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← mul_assoc]
      exact congrArg _ he
    obtain ⟨p, hp, hpn⟩ := List.mem_map.1 hk
    have e := List.all_eq_true.1 h15 p hp
    simp only [Bool.and_eq_true] at e
    obtain ⟨-, e2⟩ := e
    obtain ⟨k1, l1⟩ := SecS.mul_sound c hc (hR 1) (nc2m_nfL c hc hGc p.1).1
    obtain ⟨k2, l2⟩ := SecS.mul_sound c hc k1 (hR 2)
    have hY : ordMat c.p c.d c.w c.S (c.mul (c.mul (getR c O 1) (nfL c G p.1)) (getR c O 2)) =
        ordMat c.p c.d c.w c.S (getR c O 1) * nfG (G.map (ordMat c.p c.d c.w c.S)) n *
          ordMat c.p c.d c.w c.S (getR c O 2) := by
      rw [l2, l1, (nc2m_nfL c hc hGc _).2, hpn]
    rw [← hY]
    exact hcomm (hR 3) k2 e2

theorem nc2L_facts {c : Lay} (hc : c.ok = true) {p d : ℕ} (hp : c.p = p) (hd : c.d = d)
    {A B : ℕ} {LA LB : List Char} {sA sB : String} (hA : decOK c A LA = true)
    (hB : decOK c B LB = true) (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB)
    {C : ℕ → LiveChunk} {S : ℕ → List ℕ} {m : ℕ} (h0 : S 0 = [A, B])
    (hch : ∀ i < m, liveL c (C i) (S i) (S (i + 1)) = true) {D : NC2LData}
    (h : nc2L c (S m) D = true)
    [Finite (CFSG.Blueprint.NativeSporadic.seedMonoid p d 1 sA sB)ˣ] :
    ∃ (t g x : (CFSG.Blueprint.NativeSporadic.seedMonoid p d 1 sA sB)ˣ)
      (H : Subgroup (CFSG.Blueprint.NativeSporadic.seedMonoid p d 1 sA sB)ˣ),
      orderOf t = 2 ∧ H ≤ Subgroup.centralizer {t} ∧ Nat.card H = 2 ^ D.a ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧
      Odd (orderOf x) ∧ (∀ s ∈ H ⊓ H.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
      ∀ q ∈ D.extra, q ∣ Nat.card (Subgroup.centralizer ({t} : Set _)) := by
  classical
  subst hp hd hsA hsB
  set Sm := CFSG.Blueprint.NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA)
    (String.ofList LB) with hSm
  set O := S m with hOdef
  have hone : Canon c.p c.d c.w c.ONE ∧ ordMat c.p c.d c.w c.S c.ONE ∈ Sm :=
    ⟨(one_sound hc).1, by rw [(one_sound hc).2]; exact Sm.one_mem⟩
  have hmul : ∀ x y, (Canon c.p c.d c.w x ∧ ordMat c.p c.d c.w c.S x ∈ Sm) →
      (Canon c.p c.d c.w y ∧ ordMat c.p c.d c.w c.S y ∈ Sm) →
      Canon c.p c.d c.w (c.mul x y) ∧ ordMat c.p c.d c.w c.S (c.mul x y) ∈ Sm := by
    rintro x y ⟨cx, mx⟩ ⟨cy, my⟩
    obtain ⟨cxy, exy⟩ := SecS.mul_sound c hc cx cy
    exact ⟨cxy, by rw [exy]; exact Sm.mul_mem mx my⟩
  have hS0 : ∀ x ∈ S 0, Canon c.p c.d c.w x ∧ ordMat c.p c.d c.w c.S x ∈ Sm := by
    rw [h0]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · obtain ⟨h1, h2⟩ := SecS.decOK_sound c hc hA
      exact ⟨h1, by rw [h2]; exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
    · obtain ⟨h1, h2⟩ := SecS.decOK_sound c hc hB
      exact ⟨h1, by rw [h2]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have hall := liveL_chain (P := fun x => Canon c.p c.d c.w x ∧ ordMat c.p c.d c.w c.S x ∈ Sm)
    hone hmul hS0 hch
  have hreg : ∀ i, ordMat c.p c.d c.w c.S (getR c O i) ∈ Sm := fun i =>
    (getD_mem (P := fun x => Canon c.p c.d c.w x ∧ ordMat c.p c.d c.w c.S x ∈ Sm) hone O i
      hall).2
  have F := nc2L_mat hc (fun x hx => (hall x hx).1) h
  set k := 4 + D.extra.length
  set Mi : ℕ → Matrix (Fin c.d) (Fin c.d) (ZMod c.p) := fun i => ordMat c.p c.d c.w c.S (getR c O i)
    with hMi
  set gs := (O.drop k).map (ordMat c.p c.d c.w c.S) with hgsdef
  let mS : ℕ → Sm := fun i => ⟨Mi i, hreg i⟩
  have units_ext : ∀ {u v : Smˣ}, (((u : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p))) =
      ((v : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) → u = v :=
    fun h => Units.ext (Subtype.ext h)
  have hm0 : D.oddExp ≠ 0 := by have := F.odd; omega
  let τ : Smˣ := Units.ofPowEqOne (mS 0) 2 (Subtype.ext (by
    rw [SubmonoidClass.coe_pow, pow_two]
    exact F.t_sq)) two_ne_zero
  let ξ : Smˣ := Units.ofPowEqOne (mS 3) D.oddExp (Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    exact F.x_pow)) hm0
  let γ : Smˣ := ⟨mS 1, mS 2, Subtype.ext F.g_inv, Subtype.ext (mul_eq_one_comm.1 F.g_inv)⟩
  have hτm : ((τ : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = Mi 0 := rfl
  have hξm : ((ξ : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = Mi 3 := rfl
  have hγm : ((γ : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = Mi 1 := rfl
  have hγim : (((γ⁻¹ : Smˣ) : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = Mi 2 := rfl
  have hgmem : ∀ x ∈ O.drop k, ordMat c.p c.d c.w c.S x ∈ Sm := fun x hx =>
    (hall x (List.mem_of_mem_drop hx)).2
  let gsS : List Sm := (O.drop k).pmap (fun x hx => ⟨ordMat c.p c.d c.w c.S x, hx⟩) hgmem
  have hgs : gsS.map Sm.subtype = gs := by
    rw [List.map_pmap]
    exact List.pmap_eq_map _
  have hlen : gsS.length = D.a := by rw [← F.len, ← hgs, List.length_map]
  have hcoeD : ∀ i, ((gsS.getD i 1 : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = gs.getD i 1 :=
    fun i => by rw [← hgs, getD_map_hom]; rfl
  have hcoeN : ∀ n, ((nfG gsS n : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = nfG gs n :=
    fun n => by rw [← hgs, nfG_map]; rfl
  have hpc : PcRel gsS := by
    refine pcRel_of gsS (fun i hi => ?_) (fun i j hij hj => ?_)
    · rw [hlen] at hi ⊢
      obtain ⟨m, hm, hd, e⟩ := F.sq i hi
      exact ⟨m, hm, hd, Subtype.ext (by rw [Submonoid.coe_mul, hcoeD, hcoeN]; exact e)⟩
    · rw [hlen] at hj ⊢
      obtain ⟨m, hm, hd, e⟩ := F.cj i j hij hj
      refine ⟨m, hm, hd, Subtype.ext ?_⟩
      rw [Submonoid.coe_mul, Submonoid.coe_mul, hcoeD, hcoeD, hcoeN]
      exact e
  have hmulS := nfSet_mul hpc
  have hunit : ∀ n, IsUnit (nfG gsS n) := fun n =>
    (IsUnit.mem_submonoid_iff _).1 (nfG_mem (IsUnit.submonoid Sm)
      (fun y hy => (IsUnit.mem_submonoid_iff _).2 (isUnit_of_pcRel hpc y hy)) n)
  let H : Subgroup Smˣ :=
    { carrier := {u | (u : Sm) ∈ nfSet gsS}
      mul_mem' := fun {a b} ha hb => by
        change ((a * b : Smˣ) : Sm) ∈ nfSet gsS
        rw [Units.val_mul]
        exact hmulS _ ha _ hb
      one_mem' := one_mem_nfSet gsS
      inv_mem' := fun {a} ha => by
        have hpow : ∀ j : ℕ, ((a ^ j : Smˣ) : Sm) ∈ nfSet gsS := by
          intro j
          induction j with
          | zero => exact one_mem_nfSet gsS
          | succ j ih =>
            rw [pow_succ, Units.val_mul]
            exact hmulS _ ih _ ha
        have e : a⁻¹ = a ^ (orderOf a - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos a),
            pow_orderOf_eq_one]
        change ((a⁻¹ : Smˣ) : Sm) ∈ nfSet gsS
        rw [e]
        exact hpow _ }
  have hHmem : ∀ u : Smˣ, u ∈ H ↔ (u : Sm) ∈ nfSet gsS := fun u => Iff.rfl
  have hcard : Nat.card H = 2 ^ D.a := by
    let f : Fin (2 ^ D.a) → H := fun n => ⟨(hunit n).unit, by
      rw [hHmem, IsUnit.unit_spec]
      exact ⟨n, by rw [hlen]; exact n.isLt, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => Fin.ext (F.inj a a.isLt b b.isLt ?_), ?_⟩
      · have e := congrArg (fun u : H => (((u : Smˣ) : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)))
          hab
        simp only [f, IsUnit.unit_spec] at e
        rwa [hcoeN, hcoeN] at e
      · rintro ⟨u, hu⟩
        obtain ⟨n, hn, e⟩ := (hHmem u).1 hu
        rw [hlen] at hn
        refine ⟨⟨n, hn⟩, Subtype.ext (Units.ext ?_)⟩
        simp only [f, IsUnit.unit_spec]
        exact e
    rw [← Nat.card_eq_of_bijective f hf, Nat.card_fin]
  have hcomm : ∀ n, nfG gs n * Mi 0 = Mi 0 * nfG gs n := by
    intro n
    have hK := nfG_mem (Submonoid.centralizer {Mi 0}) (L := gs) (fun g hg => by
      rw [Submonoid.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (F.gens_comm g hg).symm) n
    rw [Submonoid.mem_centralizer_iff] at hK
    exact (hK (Mi 0) rfl).symm
  refine ⟨τ, γ, ξ, H, ?_, ?_, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply orderOf_eq_prime (Units.pow_ofPowEqOne _ _)
    intro h1
    exact F.t_ne (by
      rw [← hτm]
      exact congrArg (fun u : Smˣ => ((u : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p))) h1)
  ·
    intro u hu
    obtain ⟨n, -, e⟩ := (hHmem u).1 hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply units_ext
    rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, ← e, hcoeN]
    exact hcomm n
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply units_ext
    rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, hγm]
    exact F.g_comm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply units_ext
    rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, hξm]
    exact F.x_comm
  · intro h1
    exact F.x_ne (by rw [← hξm, h1]; rfl)
  ·
    have hdvd : orderOf ξ ∣ D.oddExp := orderOf_dvd_of_pow_eq_one (Units.pow_ofPowEqOne _ _)
    exact Odd.of_dvd_nat (Nat.odd_iff.2 F.odd) hdvd
  ·
    rintro s ⟨hsH, ⟨y, hyH, rfl⟩⟩
    obtain ⟨n, hn, ey⟩ := (hHmem y).1 hyH
    obtain ⟨n', hn', es⟩ := (hHmem _).1 hsH
    rw [hlen] at hn hn'
    have hconj : ((((MulAut.conj γ).toMonoidHom y : Smˣ) : Sm) :
        Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = Mi 1 * nfG gs n * Mi 2 := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul,
        Submonoid.coe_mul, Submonoid.coe_mul, hγm, hγim, ← ey, hcoeN]
    have hm : Mi 1 * nfG gs n * Mi 2 = nfG gs n' := by rw [← hconj, ← es, hcoeN]
    apply units_ext
    rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hξm, hconj]
    exact F.inter n hn n' hn' hm
  ·
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨hpr, hcT, hpow, hne⟩ := F.extra i hi
    rw [List.getD_eq_getElem _ _ hi] at hpr hpow
    let υ : Smˣ := Units.ofPowEqOne (mS (4 + i)) D.extra[i] (Subtype.ext (by
      rw [SubmonoidClass.coe_pow]
      exact hpow)) hpr.ne_zero
    have hυm : ((υ : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p)) = Mi (4 + i) := rfl
    have hυC : υ ∈ Subgroup.centralizer ({τ} : Set Smˣ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply units_ext
      rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, hυm]
      exact hcT
    have hυo : orderOf υ = D.extra[i] := by
      have : Fact D.extra[i].Prime := ⟨hpr⟩
      apply orderOf_eq_prime (Units.pow_ofPowEqOne _ _)
      intro h1
      exact hne (by
        rw [← hυm]
        exact congrArg (fun u : Smˣ => ((u : Sm) : Matrix (Fin c.d) (Fin c.d) (ZMod c.p))) h1)
    have := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({τ} : Set Smˣ)) hυC
    rwa [hυo] at this

end CFSG.KC.NC2L

end
