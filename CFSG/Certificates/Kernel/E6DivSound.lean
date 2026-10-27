module

public import Certificates.Data.Kernel.E6Div
public import Certificates.Data.E6WeylMinors
public import CFSG.Certificates.Kernel.E6WKSound

public section

namespace CFSG.KC.E6Div

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.StandardType.TwE6RootKill CFSG.KC.E6WK CFSG.RankThree.E6 Certificates.E6WeylMinors

theorem exists_uv {vp ir rm : ℕ}
    {words : List (List ℕ)} {up vk : List ℕ} (htab : tabCheckWith vp ir rm = true)
    (hup : upCheckWith ir words up = true) (hk : kCheckWith up = true)
    (hv : vCheckWith ir vk (KTree.ofSorted vk) = true) (w : WeylGroup Tag.E6) :
    ∃ n < up.length, ∃ v ∈ vk, ∀ j : Fin Tag.E6.rank, lane (up.getD n 0) (lane v j) < 72 ∧
      e6Certificate.root (lane (up.getD n 0) (lane v j)) =
        w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  obtain ⟨u, ω, hω, hupos, rfl⟩ := exists_decomp w
  obtain ⟨c, hc, hvrep⟩ := exists_vk htab hv ω hω
  obtain ⟨p, hp, hurep⟩ := exists_up hk u hupos
  obtain ⟨n, hn, hpn⟩ := List.getElem_of_mem hp
  simp only [upCheckWith, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hup
  obtain ⟨hlen, hall⟩ := hup
  have hnw : n < words.length := by rw [hlen]; exact hn
  have hzip := hall (words[n], up[n]) (by
    rw [List.mem_iff_getElem]
    exact ⟨n, by rw [List.length_zip, hlen, min_self]; exact hn, by rw [List.getElem_zip]⟩)
  have hw6 : ∀ i ∈ words[n], i < 6 := hzip.1
  have hwp : wordPerm ir words[n] = up[n] := hzip.2
  obtain ⟨g, hg⟩ := exists_wordPerm_spec htab _ hw6
  rw [hwp, hpn] at hg
  have hug : u = g := by
    refine ext_single fun j => ?_
    have hj6 : (j : ℕ) < 6 := j.2
    have h1 := (hurep.2 j).2
    rw [getD_decodeT hj6, lane_mod_pow hj6] at h1
    rw [← h1, (hg j (by omega)).2, root_single]
  subst hug
  refine ⟨n, hn, c, hc, fun j => ?_⟩
  rw [List.getD_eq_getElem _ _ hn, hpn]
  have hj6 : (j : ℕ) < 6 := j.2
  have hcj := hvrep.2 j
  rw [getD_decodeT hj6, roots_length] at hcj
  refine ⟨(hg _ hcj.1).1, ?_⟩
  rw [(hg _ hcj.1).2, hcj.2, mul_smul]

theorem shl (x n : ℕ) : Nat.shiftLeft x n = x * 2 ^ n := Nat.shiftLeft_eq x n

theorem en_eq (cs i j : ℕ) : en cs i j = cs / 2 ^ (24 * j + 4 * i) % 16 :=
  congrArg (· % 16) (Nat.shiftRight_eq_div_pow cs (24 * j + 4 * i))

theorem rc_eq (vp r : ℕ) : rc vp r = vp / 2 ^ (24 * r) % 2 ^ 24 :=
  congrArg (· % 2 ^ 24) (Nat.shiftRight_eq_div_pow vp (24 * r))

theorem en_pack {a : ℕ → ℕ} (ha : ∀ k, a k < 16777216) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    en (a 0 + Nat.shiftLeft (a 1) 24 + Nat.shiftLeft (a 2) 48 + Nat.shiftLeft (a 3) 72 +
      Nat.shiftLeft (a 4) 96 + Nat.shiftLeft (a 5) 120) i j = a j / 16 ^ i % 16 := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have h4 := ha 4
  have h5 := ha 5
  rw [en_eq]
  simp only [shl]
  interval_cases i <;> interval_cases j <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega

theorem en_csOf {vp ir rm : ℕ} (htab : tabCheckWith vp ir rm = true) {p v : ℕ}
    {w : WeylGroup Tag.E6} (hcol : ∀ j : Fin Tag.E6.rank, lane p (lane v j) < 72 ∧
      e6Certificate.root (lane p (lane v j)) = w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
    (i j : Fin Tag.E6.rank) : (en (csOf vp p v) i j : ℤ) = weylMatrix w i j + 8 := by
  have hi : (i : ℕ) < 6 := i.2
  have hj : (j : ℕ) < 6 := j.2
  have hpack : en (csOf vp p v) i j = rc vp (lane p (lane v j)) / 16 ^ (i : ℕ) % 16 :=
    en_pack (a := fun k => rc vp (lane p (lane v k))) (fun _ => Nat.mod_lt _ (by norm_num)) hi hj
  have hrc : rc vp (lane p (lane v j)) = e6Certificate.roots.getD (lane p (lane v j)) 0 :=
    (rc_eq _ _).trans ((tab_parts htab).1 _ (hcol j).1)
  rw [hpack, hrc, weylMatrix_apply, ← (hcol j).2]
  simp only [RootCertificate.root, decodeVec]
  ring

theorem dl_eq (i j : ℕ) : dl i j = if i = j then 1 else 0 := by
  unfold dl
  cases h : Nat.beq i j
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

theorem dl_cast {r s : ℕ} (hr : r < 6) (hs : s < 6) :
    ((dl r s : ℕ) : ℤ) =
      (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) ⟨r, hr⟩ ⟨s, hs⟩ := by
  rw [dl_eq, Matrix.one_apply]
  by_cases h : r = s
  · rw [if_pos h, if_pos (Fin.ext h), Nat.cast_one]
  · rw [if_neg h, if_neg (fun h' => h (congrArg Fin.val h')), Nat.cast_zero]

theorem okN_spec {P N : ℕ} (h : okN P N = true) :
    (P : ℤ) - N ∈ ({1, -1, 2, -2} : Finset ℤ) := by
  simp only [okN, Bool.or_eq_true, Nat.beq_eq] at h
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem det3_spec {a b d e f g h i j : ℕ} (hd : det3N a b d e f g h i j = true) :
    ((a : ℤ) - 8) * ((f : ℤ) - 8) * ((j : ℤ) - 8) - ((a : ℤ) - 8) * ((g : ℤ) - 8) * ((i : ℤ) - 8) -
        ((b : ℤ) - 8) * ((e : ℤ) - 8) * ((j : ℤ) - 8) +
        ((b : ℤ) - 8) * ((g : ℤ) - 8) * ((h : ℤ) - 8) +
        ((d : ℤ) - 8) * ((e : ℤ) - 8) * ((i : ℤ) - 8) -
        ((d : ℤ) - 8) * ((f : ℤ) - 8) * ((h : ℤ) - 8) ∈ ({1, -1, 2, -2} : Finset ℤ) := by
  have := okN_spec hd
  convert this using 1
  simp only [tP, tN]
  push_cast
  ring

theorem det2_spec {a b e d : ℕ} (hd : det2N a b e d = true) :
    ((a : ℤ) - 8) * ((d : ℤ) - 8) - ((b : ℤ) - 8) * ((e : ℤ) - 8) ∈
      ({1, -1, 2, -2} : Finset ℤ) := by
  have := okN_spec hd
  convert this using 1
  push_cast
  ring

theorem strictMono3 {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : c < 6) :
    StrictMono (![⟨a, (hab.trans (hbc.trans hc) : a < 6)⟩, ⟨b, (hbc.trans hc : b < 6)⟩,
      ⟨c, hc⟩] : Fin 3 → Fin Tag.E6.rank) := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  · exact hab
  · exact hbc

theorem strictMono2 {a b : ℕ} (hab : a < b) (hb : b < 6) :
    StrictMono (![⟨a, (hab.trans hb : a < 6)⟩, ⟨b, hb⟩] : Fin 2 → Fin Tag.E6.rank) := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  exact hab

theorem smallMinor3_of {cs : ℕ} {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hM : ∀ i j : Fin Tag.E6.rank, (en cs i j : ℤ) = M i j + 8) {a b c x y z : ℕ}
    (ho : ord3 a b c = true) (ho' : ord3 x y z = true) (hm : m3 cs a b c x y z = true) :
    SmallMinor 3 (M + 1) := by
  simp only [ord3, Bool.and_eq_true, Nat.blt_eq] at ho ho'
  obtain ⟨hab, hbc, hc⟩ := ho
  obtain ⟨hxy, hyz, hz⟩ := ho'
  have e : ∀ (r s : ℕ) (hr : r < 6) (hs : s < 6),
      ((en cs r s + dl r s : ℕ) : ℤ) - 8 = (M + 1) ⟨r, hr⟩ ⟨s, hs⟩ := by
    intro r s hr hs
    have h1 : (en cs r s : ℤ) = M ⟨r, hr⟩ ⟨s, hs⟩ + 8 := hM ⟨r, hr⟩ ⟨s, hs⟩
    rw [Nat.cast_add, h1, dl_cast hr hs, Matrix.add_apply]
    ring
  unfold m3 at hm
  have hdet := det3_spec hm
  rw [e a x (by omega) (by omega), e a y (by omega) (by omega), e a z (by omega) (by omega),
    e b x (by omega) (by omega), e b y (by omega) (by omega), e b z (by omega) (by omega),
    e c x (by omega) (by omega), e c y (by omega) (by omega), e c z (by omega) (by omega)] at hdet
  refine ⟨_, _, strictMono3 hab hbc hc, strictMono3 hxy hyz hz, ?_⟩
  rw [Matrix.det_fin_three]
  exact hdet

theorem smallMinor2_of {cs : ℕ} {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hM : ∀ i j : Fin Tag.E6.rank, (en cs i j : ℤ) = M i j + 8)
    (hlo : ∀ i j : Fin Tag.E6.rank, -8 < M i j) {a b x y : ℕ}
    (ho : ord2 a b = true) (ho' : ord2 x y = true) (hm : m2 cs a b x y = true) :
    SmallMinor 2 (M - 1) := by
  simp only [ord2, Bool.and_eq_true, Nat.blt_eq] at ho ho'
  obtain ⟨hab, hb⟩ := ho
  obtain ⟨hxy, hy⟩ := ho'
  have e : ∀ (r s : ℕ) (hr : r < 6) (hs : s < 6),
      ((en cs r s - dl r s : ℕ) : ℤ) - 8 = (M - 1) ⟨r, hr⟩ ⟨s, hs⟩ := by
    intro r s hr hs
    have h1 : (en cs r s : ℤ) = M ⟨r, hr⟩ ⟨s, hs⟩ + 8 := hM ⟨r, hr⟩ ⟨s, hs⟩
    have hlo' := hlo ⟨r, hr⟩ ⟨s, hs⟩
    have hdl : dl r s ≤ 1 := by
      rw [dl_eq]
      split_ifs <;> omega
    have hle : dl r s ≤ en cs r s := by omega
    rw [Nat.cast_sub hle, h1, dl_cast hr hs, Matrix.sub_apply]
    ring
  unfold m2 at hm
  have hdet := det2_spec hm
  rw [e a x (by omega) (by omega), e a y (by omega) (by omega), e b x (by omega) (by omega),
    e b y (by omega) (by omega)] at hdet
  refine ⟨_, _, strictMono2 hab hb, strictMono2 hxy hy, ?_⟩
  rw [Matrix.det_fin_two]
  exact hdet

theorem sqOne_aux (cs : ℕ) : ∀ m : ℕ, Nat.rec (motive := fun _ => Bool) true
    (fun n ih => sqE cs (n / 6) (n % 6) && ih) m = true → ∀ n < m, sqE cs (n / 6) (n % 6) = true
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero n)
  | m + 1, h, n, hn => by
    have h' : (sqE cs (m / 6) (m % 6) && Nat.rec (motive := fun _ => Bool) true
        (fun n ih => sqE cs (n / 6) (n % 6) && ih) m) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hnm : n = m
    · rw [hnm]
      exact h'.1
    · exact sqOne_aux cs m h'.2 n (by omega)

theorem sum_six (f : Fin Tag.E6.rank → ℤ) :
    ∑ k, f k = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ :=
  Fin.sum_univ_six f

theorem sq_of_sqOne {cs : ℕ} {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hM : ∀ i j : Fin Tag.E6.rank, (en cs i j : ℤ) = M i j + 8) (h : sqOne cs = true) :
    M * M = 1 := by
  have hM' : ∀ i j : Fin Tag.E6.rank, M i j = (en cs i j : ℤ) - 8 := fun i j => by
    rw [hM i j]
    ring
  ext i j
  have hi : (i : ℕ) < 6 := i.2
  have hj : (j : ℕ) < 6 := j.2
  have E := sqOne_aux cs 36 h (6 * i + j) (by omega)
  have h1 : (6 * (i : ℕ) + j) / 6 = i := by omega
  have h2 : (6 * (i : ℕ) + j) % 6 = j := by omega
  rw [h1, h2] at E
  simp only [sqE, Nat.beq_eq] at E
  have E' := congrArg (Nat.cast : ℕ → ℤ) E
  push_cast at E'
  rw [Matrix.mul_apply, sum_six, ← dl_cast hi hj]
  simp only [hM']
  linear_combination E'

theorem good_of_witC {cs c : ℕ} {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hM : ∀ i j : Fin Tag.E6.rank, (en cs i j : ℤ) = M i j + 8)
    (hlo : ∀ i j : Fin Tag.E6.rank, -8 < M i j) (h : witC cs c = true) :
    M * M = 1 ∨ SmallMinor 3 (M + 1) ∧ SmallMinor 2 (M - 1) := by
  unfold witC at h
  cases hc : Nat.beq c 0
  · rw [hc] at h
    have h' : (m3c cs ((c - 1) % 262144) && m2c cs ((c - 1) / 262144)) = true := h
    rw [Bool.and_eq_true] at h'
    have h3 : ((ord3 ((c - 1) % 262144 % 8) ((c - 1) % 262144 / 8 % 8)
        ((c - 1) % 262144 / 64 % 8) && ord3 ((c - 1) % 262144 / 512 % 8)
        ((c - 1) % 262144 / 4096 % 8) ((c - 1) % 262144 / 32768 % 8)) &&
        m3 cs ((c - 1) % 262144 % 8) ((c - 1) % 262144 / 8 % 8) ((c - 1) % 262144 / 64 % 8)
          ((c - 1) % 262144 / 512 % 8) ((c - 1) % 262144 / 4096 % 8)
          ((c - 1) % 262144 / 32768 % 8)) = true := h'.1
    have h2 : ((ord2 ((c - 1) / 262144 % 8) ((c - 1) / 262144 / 8 % 8) &&
        ord2 ((c - 1) / 262144 / 64 % 8) ((c - 1) / 262144 / 512 % 8)) &&
        m2 cs ((c - 1) / 262144 % 8) ((c - 1) / 262144 / 8 % 8) ((c - 1) / 262144 / 64 % 8)
          ((c - 1) / 262144 / 512 % 8)) = true := h'.2
    simp only [Bool.and_eq_true] at h3 h2
    exact Or.inr ⟨smallMinor3_of hM h3.1.1 h3.1.2 h3.2, smallMinor2_of hM hlo h2.1.1 h2.1.2 h2.2⟩
  · rw [hc] at h
    exact Or.inl (sq_of_sqOne hM h)

theorem exists_wit_of_uCheckDiv {vp p : ℕ} {vk ws : List ℕ} (h : uCheckDiv vp p vk ws = true) :
    ∀ v ∈ vk, ∃ c, witC (csOf vp p v) c = true := by
  induction vk generalizing ws with
  | nil =>
    intro v hv
    simp at hv
  | cons v vk ih =>
    cases ws with
    | nil => exact absurd h Bool.false_ne_true
    | cons c ws' =>
      have h' : (witC (csOf vp p v) c && uCheckDiv vp p vk ws') = true := h
      rw [Bool.and_eq_true] at h'
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨c, h'.1⟩
      · exact ih (ws := ws') h'.2 x hx

theorem wkRho_getD' (j : Fin Tag.E6.rank) : wkRho.getD j 0 = (TwistTag.E6.perm j : ℕ) :=
  wkRho_getD j

theorem rho_entry (i j : Fin Tag.E6.rank) :
    rhoMatrix i j = if (i : ℕ) = wkRho.getD j 0 then 1 else 0 := by
  rw [wkRho_getD', rhoMatrix, Matrix.of_apply]
  by_cases h : i = TwistTag.E6.perm j
  · rw [if_pos (congrArg Fin.val h), if_pos ((Equiv.eq_symm_apply e6Rho).2 h.symm)]
  · rw [if_neg (fun h' => h (Fin.ext h')),
      if_neg (fun h' => h ((Equiv.eq_symm_apply e6Rho).1 h').symm)]

theorem exists_negRho {vp ir rm : ℕ}
    (htab : tabCheckWith vp ir rm = true) {ω : List ℕ} (h : w0Check vp ir ω = true) :
    ∃ g : WeylGroup Tag.E6, weylMatrix g = -rhoMatrix := by
  simp only [w0Check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hω, hneg⟩ := h
  obtain ⟨g, hg⟩ := exists_wordPerm_spec htab ω hω
  refine ⟨g, ?_⟩
  simp only [negRhoOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hneg
  ext i j
  have hi : (i : ℕ) < 6 := i.2
  have hj : (j : ℕ) < 6 := j.2
  have hgj := hg j (by omega)
  have h1 := hneg j hj
  rw [vecP_eq htab hgj.1, vecs_getD e6Certificate (by rw [roots_length]; exact hgj.1)] at h1
  have h2 := congrArg (fun l => l.getD i 0) h1
  beta_reduce at h2
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn,
    getD_range_map' _ _ hi, Fin.eta, hgj.2, root_single] at h2
  rw [weylMatrix_apply, Matrix.neg_apply, rho_entry, h2]
  split_ifs <;> simp

theorem smallMinor_neg (k : ℕ) (A : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) :
    SmallMinor k (-A) ↔ SmallMinor k A := by
  have key : ∀ R C : Fin k → Fin Tag.E6.rank,
      ((-A).submatrix R C).det = (-1) ^ k * (A.submatrix R C).det := by
    intro R C
    have hs : (-A).submatrix R C = -(A.submatrix R C) := rfl
    rw [hs, Matrix.det_neg, Fintype.card_fin]
  have hS : ∀ x : ℤ, (-1) ^ k * x ∈ ({1, -1, 2, -2} : Finset ℤ) ↔
      x ∈ ({1, -1, 2, -2} : Finset ℤ) := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> constructor <;> intro h' <;> omega
  simp only [SmallMinor, key, hS]

theorem root_gt {r : ℕ} (hr : r < 72) (i : Fin Tag.E6.rank) :
    -8 < e6Certificate.root r i := by
  have hd : ∀ r < 72, ∀ i < 6, 0 < e6Certificate.roots.getD r 0 / 16 ^ i % 16 := by
    decide +kernel
  have := hd r hr i i.2
  simp only [RootCertificate.root, decodeVec]
  omega

theorem e6div_of_checks {vp ir rm : ℕ}
    {words : List (List ℕ)} {up vk w0 : List ℕ} {wit : List (List ℕ)}
    (htab : tabCheckWith vp ir rm = true) (hup : upCheckWith ir words up = true)
    (hk : kCheckWith up = true) (hv : vCheckWith ir vk (KTree.ofSorted vk) = true)
    (hu : ∀ n < up.length, uCheckDiv vp (up.getD n 0) vk (wit.getD n []) = true)
    (h0 : w0Check vp ir w0 = true) (w : WeylGroup Tag.E6) :
    (weylMatrix w * weylMatrix w = 1 ∨
        SmallMinor 3 (weylMatrix w + 1) ∧ SmallMinor 2 (weylMatrix w - 1)) ∧
      (weylMatrix w * rhoMatrix * (weylMatrix w * rhoMatrix) = 1 ∨
        SmallMinor 3 (weylMatrix w * rhoMatrix - 1) ∧
          SmallMinor 2 (weylMatrix w * rhoMatrix + 1)) := by
  have good : ∀ x : WeylGroup Tag.E6, weylMatrix x * weylMatrix x = 1 ∨
      SmallMinor 3 (weylMatrix x + 1) ∧ SmallMinor 2 (weylMatrix x - 1) := by
    intro x
    obtain ⟨n, hn, v, hv', hcol⟩ := exists_uv htab hup hk hv x
    obtain ⟨c, hc⟩ := exists_wit_of_uCheckDiv (hu n hn) v hv'
    refine good_of_witC (en_csOf htab hcol) (fun i j => ?_) hc
    rw [weylMatrix_apply, ← (hcol j).2]
    exact root_gt (hcol j).1 i
  obtain ⟨g, hg⟩ := exists_negRho htab h0
  refine ⟨good w, ?_⟩
  have hN : weylMatrix w * rhoMatrix = -weylMatrix (w * g) := by
    rw [weylMatrix_mul, hg, Matrix.mul_neg, neg_neg]
  have e1 : -weylMatrix (w * g) - 1 = -(weylMatrix (w * g) + 1) := by abel
  have e2 : -weylMatrix (w * g) + 1 = -(weylMatrix (w * g) - 1) := by abel
  rw [hN, neg_mul_neg, e1, e2, smallMinor_neg, smallMinor_neg]
  exact good (w * g)

end CFSG.KC.E6Div
