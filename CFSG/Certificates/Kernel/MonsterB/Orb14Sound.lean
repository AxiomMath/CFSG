
module

public import CFSG.Certificates.Kernel.MonsterB.F4CodeSound
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputsBase
public import CFSG.Certificates.Kernel.MonsterB.Orb14NetSound

public section

namespace CFSG.KC.Orb14

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census CFSG.KLie.CT
  CFSG.KC.U6Orb CFSG.KC.Bfs

theorem beq_true_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem testBit_pw2 (a x : ℕ) : (pw2 a).testBit x = decide (a = x) := by
  rw [pw2_eq, Nat.testBit_two_pow]

theorem testBit_maskB (n : ℕ) (f : ℕ → Bool) (x : ℕ) :
    (maskB n f).testBit x = (decide (x < n) && f x) := by
  rw [Bool.eq_iff_iff, maskB, testBit_orN', Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    cases hf : f t
    · rw [hf] at h
      exact absurd (Nat.zero_testBit x ▸ h) (by decide)
    · rw [hf] at h
      change (pw2 t).testBit x = true at h
      rw [testBit_pw2, decide_eq_true_iff] at h
      subst h
      exact ⟨ht, hf⟩
  · rintro ⟨hx, hf⟩
    refine ⟨x, hx, ?_⟩
    rw [hf]
    change (pw2 x).testBit x = true
    rw [testBit_pw2, decide_eq_true rfl]

theorem testBit_bitsOf : ∀ (L : List ℕ) (x : ℕ), (bitsOf L).testBit x = true ↔ x ∈ L
  | [], x => by simp [bitsOf]
  | a :: L, x => by
    change (Nat.lor (pw2 a) (bitsOf L)).testBit x = true ↔ _
    rw [testBit_nlor, Bool.or_eq_true, testBit_pw2, decide_eq_true_iff, testBit_bitsOf L x,
      List.mem_cons]
    exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩

theorem testBit_maskF (A m w x : ℕ) :
    (maskF A m w).testBit x = true ↔ ∃ t < m, fget A t w = x := by
  rw [maskF, testBit_orN']
  simp only [testBit_pw2, decide_eq_true_iff]

theorem incOK_spec {A m w N : ℕ} (h : incOK A m w N = true) :
    (∀ t < m, fget A t w < N) ∧ ∀ a < m, ∀ b < m, a < b → fget A a w < fget A b w := by
  rw [incOK, allN_iff] at h
  have step : ∀ t < m, fget A t w < (if t + 1 = m then N else fget A (t + 1) w) := by
    intro t ht
    have := h t ht
    rw [Nat.blt_eq] at this
    by_cases e : t + 1 = m
    · rw [ite_eq_left e]
      have hb : Nat.beq (Nat.succ t) m = true := beq_true_iff.2 e
      rwa [hb] at this
    · rw [ite_eq_right e]
      have hb : Nat.beq (Nat.succ t) m = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact e (beq_true_iff.1 hc)
      rwa [hb] at this
  have mono : ∀ a b, a < b → b < m → fget A a w < fget A b w := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := step b (by omega)
      rw [ite_eq_right (by omega)] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact lt_trans (ih h' (by omega)) hs
      · exact hs
  refine ⟨fun t ht => ?_, fun a ha b hb hab => mono a b hab hb⟩
  have hl := step (m - 1) (by omega)
  rw [ite_eq_left (by omega)] at hl
  rcases Nat.lt_or_ge t (m - 1) with h' | h'
  · exact lt_trans (mono t (m - 1) h' (by omega)) hl
  · rwa [show t = m - 1 by omega]

theorem sumN_eq' (n : ℕ) (g : ℕ → ℕ) : sumN n g = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

theorem card_eq_popc (N X : ℕ) :
    (Finset.univ.filter fun y : Fin N => X.testBit y = true).card = popc N X := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun y => if X.testBit y = true then 1 else 0) N,
    popc, sumN_eq']
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Nat.land (Nat.shiftRight X j) 1 = (X >>> j) % 2 := Nat.and_one_is_mod _
  have e2 : X.testBit j = decide ((X >>> j) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e2, e]
  rcases Nat.mod_two_eq_zero_or_one (X >>> j) with h | h <;> rw [h] <;> rfl

theorem bindL_spec {L : Array ℕ} {X w n b : ℕ} (hb : b ≤ 2 ^ w) (h : bindL L.toList X w n b = true) :
    L.size = n ∧ ∀ j < n, L[j]! < b ∧ fget X j w = L[j]! := by
  simp only [bindL, andB_eq_true, Nat.beq_eq, lenL_eq, Array.length_toList] at h
  obtain ⟨hX, hn, hB⟩ := h
  refine ⟨hn, fun j hj => ?_⟩
  have hlt : ∀ x ∈ L.toList, x < b := (boundL_iff _ _).1 hB
  have hj' : j < L.size := by omega
  refine ⟨?_, ?_⟩
  · rw [getElem!_toList L hj']
    exact hlt _ (List.getElem_mem _)
  · rw [← hX]
    exact fget_packA (fun x hx => lt_of_lt_of_le (hlt x hx) hb) hj'

theorem packP_get' {P : Array (Array ℕ)} {n w b : ℕ} (hb : b ≤ 2 ^ w)
    (h : shapeL n b P.toList = true) {k : ℕ} (hk : k < P.size) {i : ℕ} (hi : i < n) :
    permTab n w (packP n w P.toList) i k = (P[k]!)[i]! := by
  have hall : ∀ a ∈ P.toList, a.size = n ∧ ∀ x ∈ a.toList, x < 2 ^ w := by
    intro a ha
    obtain ⟨h1, h2⟩ := (shapeL_iff _ _ _).1 h a ha
    exact ⟨h1, fun x hx => lt_of_lt_of_le (h2 x hx) hb⟩
  have hlt : ∀ x ∈ P.toList.map (fun a => packL w a.toList), x < 2 ^ (n * w) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have := packL_lt (w := w) (hall a ha).2
    rwa [Array.length_toList, (hall a ha).1, Nat.mul_comm] at this
  have hk' : P[k]! ∈ P.toList := by
    rw [getElem!_toList P hk]
    exact List.getElem_mem _
  rw [permTab, packP, mapL_eq]
  change fget (fget (packL (n * w) _) k (n * w)) i w = _
  rw [fget_packL hlt k (by simpa using hk), List.getElem_map, ← getElem!_toList P hk,
    fget_packA (hall _ hk').2 (by rw [(hall _ hk').1]; exact hi)]

theorem bindP_spec {P : Array (Array ℕ)} {X n w m b : ℕ} (hb : b ≤ 2 ^ w)
    (h : bindP P.toList X n w m b = true) :
    P.size = m ∧ ∀ k < m, ∀ i < n, (P[k]!)[i]! < b ∧ permTab n w X i k = (P[k]!)[i]! := by
  simp only [bindP, andB_eq_true, Nat.beq_eq, lenL_eq, Array.length_toList] at h
  obtain ⟨hX, hm, hS⟩ := h
  refine ⟨hm, fun k hk i hi => ⟨?_, ?_⟩⟩
  · have hk' : P[k]! ∈ P.toList := by
      rw [getElem!_toList P (by omega)]
      exact List.getElem_mem _
    obtain ⟨h1, h2⟩ := (shapeL_iff _ _ _).1 hS _ hk'
    rw [getElem!_toList _ (by omega)]
    exact h2 _ (List.getElem_mem _)
  · rw [← hX]
    exact packP_get' hb hS (by omega) hi

theorem eq_of_bits10 {a b : ℕ} (ha : a < 1024) (hb : b < 1024)
    (h : ∀ c < 10, a.testBit c = b.testBit c) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro c
  by_cases hc : c < 10
  · exact h c hc
  · have hle : 1024 ≤ 2 ^ c := le_trans (by decide : 1024 ≤ 2 ^ 10)
      (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem netPerm_of_tieN {NW P N : ℕ} (h : tieN NW P N = true) (hN : N ≤ 1024)
    (hlt : ∀ k < 17, ∀ x < N, permTab N 10 P x k < N) :
    ∀ k < 17, NetPerm (fun x => permTab N 10 P x k) N (nw NW k) := by
  intro k hk
  rw [tieN, allN_iff] at h
  obtain ⟨hok, hb⟩ := andB_eq_true.1 (h k hk)
  rw [allN_iff] at hb
  let G' : ℕ → ℕ := fun x => if x < N then permTab N 10 P x k else x
  have hG'lt : ∀ x < 1024, G' x < 1024 := by
    intro x hx
    by_cases h' : x < N
    · simp only [G', h', ite_true]
      exact lt_of_lt_of_le (fget_lt _ _ _) (by decide)
    · simp only [G', h', ite_false]
      exact hx
  have key : ∀ q < 1024, G' (phi (nw NW k) q) = q := by
    intro q hq
    have hp := phi_lt hok hq
    refine eq_of_bits10 (hG'lt _ hp) hq fun c hc => ?_
    have e := congrArg (fun z : ℕ => z.testBit q) (beq_true_iff.1 (hb c hc))
    rw [testBit_netK hok, permPl, testBit_maskB, idPl, testBit_maskB, decide_eq_true hp,
      decide_eq_true hq, Bool.true_and, Bool.true_and, bit_eq, bit_eq] at e
    rw [← e]
    by_cases h' : phi (nw NW k) q < N
    · have : Nat.blt (phi (nw NW k) q) N = true := by rw [Nat.blt_eq]; exact h'
      simp only [G', h', ite_true, this]
    · have : Nat.blt (phi (nw NW k) q) N = false := by
        rw [Bool.eq_false_iff]
        intro hc
        rw [Nat.blt_eq] at hc
        exact h' hc
      simp only [G', h', ite_false, this]
  have phiN : ∀ q < N, phi (nw NW k) q < N := by
    intro q hq
    by_contra hc
    have := key q (by omega)
    simp only [G', hc, ite_false] at this
    omega
  refine ⟨hok, hlt k hk, phiN, fun q hq => ?_⟩
  have := key q (by omega)
  simp only [G', phiN q hq, ite_true] at this
  exact this

theorem finRange_map_get {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    ((List.finRange n).toArray.map f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, List.getElem_toArray,
    List.getElem_finRange]
  rfl

theorem singGenArr_get {k i : ℕ} (hk : k < 17) (hi : i < 693) :
    (singGenArr[k]!)[i]! = (singGen ⟨k, hk⟩ ⟨i, hi⟩ : ℕ) := by
  unfold singGenArr
  rw [finRange_map_get _ hk, finRange_map_get _ hi]

theorem imV_zero (f : Bool) (rows : ℕ → ℕ) : imV f rows 0 = 0 := by
  have : barB f 0 = 0 := by
    cases f
    · rfl
    · exact barV_zero
  rw [imV, this, Matrix.zero_vecMul]

theorem singU_high {X M F k i : ℕ} (h : ∀ c < 12, (xp X c).testBit i = false) (t : ℕ) (ht : t < 6)
    {s : ℕ} (hs : s < 2) : (singU X M F k t s).testBit i = false := by
  have hX : PlanesAt X i 0 := fun t s hs => by rw [h _ (by omega), Pi.zero_apply, fb_zero']
  have hW : ∀ s' < 2, (imPl X M F k t s').testBit i = false := by
    intro s' hs'
    have e1 : (imPl X M F k t s').testBit i =
        fb (imV (bit F k) (fun r => permTab 6 12 M r k) 0 ⟨t, ht⟩) s' :=
      imPl_bit hX (bit F k) (fun r => permTab 6 12 M r k) ⟨t, ht⟩ hs'
    rw [e1, imV_zero, Pi.zero_apply, fb_zero']
  have h0 := hW 0 (by decide)
  have h1 := hW 1 (by decide)
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · have e : singU X M F k t 0 = Nat.xor
        (Nat.land (Nat.xor (leadPl (imPl X M F k) 0) (leadPl (imPl X M F k) 1)) (imPl X M F k t 0))
        (Nat.land (leadPl (imPl X M F k) 1) (imPl X M F k t 1)) := rfl
    rw [e, testBit_nxor, testBit_nland, testBit_nland, h0, h1]
    simp
  · have e : singU X M F k t 1 = Nat.xor (Nat.land (leadPl (imPl X M F k) 1) (imPl X M F k t 0))
        (Nat.land (Nat.xor (Nat.xor (leadPl (imPl X M F k) 0) (leadPl (imPl X M F k) 1))
          (leadPl (imPl X M F k) 1)) (imPl X M F k t 1)) := rfl
    rw [e, testBit_nxor, testBit_nland, testBit_nland, h0, h1]
    simp

theorem vec6_zero : vec6 0 = 0 := by
  funext t
  fin_cases t <;> rfl

theorem enc6_vec6 {a : ℕ} (ha : a < 4096) : enc6 (vec6 a) = a :=
  vec6_inj (vec6_enc6 _).2 ha (vec6_enc6 _).1

theorem netPerm_of_tieS {NW X M F : ℕ} (h : tieS NW X M F = true)
    (hX : ∀ (i : ℕ) (hi : i < 693), PlanesAt X i (singVec ⟨i, hi⟩))
    (hXh : ∀ i, 693 ≤ i → ∀ c < 12, (xp X c).testBit i = false)
    (hmap : ∀ (k : ℕ) (hk : k < 17) (v : V6),
      imV (bit F k) (fun r => permTab 6 12 M r k) v = b6Map ⟨k, hk⟩ v)
    (hsize : b6SingArr.size = 693) (hlt : ∀ q < 693, b6SingArr[q]! < 4096)
    (hnz : ∀ q < 693, b6SingArr[q]! ≠ 0) (hnd : b6SingArr.toList.Nodup) :
    ∀ k < 17, NetPerm (fun x => (singGenArr[k]!)[x]!) 693 (nw NW k) := by
  intro k hk
  rw [tieS, allN_iff] at h
  obtain ⟨hok, hc⟩ := andB_eq_true.1 (h k hk)
  rw [allN_iff] at hc
  have hc' : ∀ t < 6, ∀ s < 2, ∀ q, (singU X M F k t s).testBit (phi (nw NW k) q) =
      (xp X (t + t + s)).testBit q := by
    intro t ht s hs q
    have h2 := hc t ht
    rw [allN_iff] at h2
    rw [← testBit_netK hok, beq_true_iff.1 (h2 s hs)]
    rfl
  have hphi : ∀ q < 693, phi (nw NW k) q < 693 := by
    intro q hq
    by_contra hc2
    have hz : singVec ⟨q, hq⟩ = 0 := by
      funext t
      apply f4_ext
      · rw [← hX q hq t 0 (by decide), ← hc' t t.2 0 (by decide),
          singU_high (hXh _ (by omega)) t t.2 (by decide), Pi.zero_apply, fb_zero']
      · rw [← hX q hq t 1 (by decide), ← hc' t t.2 1 (by decide),
          singU_high (hXh _ (by omega)) t t.2 (by decide), Pi.zero_apply, fb_zero']
    have e : vec6 b6SingArr[q]! = vec6 0 := by
      rw [vec6_zero]
      exact hz
    exact hnz q hq (vec6_inj (hlt q hq) (by decide) e)
  have himg : ∀ (q : ℕ) (hq : q < 693),
      normV (b6Map ⟨k, hk⟩ (singVec ⟨phi (nw NW k) q, hphi q hq⟩)) = singVec ⟨q, hq⟩ := by
    intro q hq
    funext t
    have hp := hphi q hq
    apply f4_ext
    · rw [← hmap k hk, ← singU_bit hp (hX _ hp) t t.2 (by decide), hc' t t.2 0 (by decide),
        hX q hq t 0 (by decide)]
    · rw [← hmap k hk, ← singU_bit hp (hX _ hp) t t.2 (by decide), hc' t t.2 1 (by decide),
        hX q hq t 1 (by decide)]
  refine ⟨hok, fun x hx => ?_, hphi, fun q hq => ?_⟩
  · rw [singGenArr_get hk hx]
    exact (singGen _ _).2
  · rw [singGenArr_get hk (hphi q hq)]
    change (singLook _ : ℕ) = q
    unfold singLook
    change b6SingArr.toList.idxOf (enc6 (normV _)) % 693 = q
    rw [himg q hq]
    change b6SingArr.toList.idxOf (enc6 (vec6 b6SingArr[q]!)) % 693 = q
    rw [enc6_vec6 (hlt q hq)]
    have hq' : q < b6SingArr.toList.length := by rw [Array.length_toList, hsize]; exact hq
    have e : b6SingArr[q]! = b6SingArr.toList.get ⟨q, hq'⟩ := by
      rw [getElem!_toList _ (by rw [hsize]; exact hq)]
      rfl
    rw [e, List.get_idxOf hnd]
    exact Nat.mod_eq_of_lt hq

theorem natBfs_range {act : ℕ → ℕ → ℕ} {ngen N root fuel : ℕ} (hroot : root < N)
    (hact : ∀ k < ngen, ∀ x < N, act k x < N) (hfuel : N ≤ fuel) :
    natCertOK act ngen (fun x => decide (x < N)) root (natBfs act ngen root fuel) = true ∧
      ∀ y, (natBfs act ngen root fuel).pts.contains y = true ↔ Reach act ngen root y := by
  classical
  have hlt : ∀ x, Reach act ngen root x → x < N := by
    intro x hx
    induction hx with
    | root => exact hroot
    | step k hk _ ih => exact hact k hk _ ih
  let S : Finset ℕ := (Finset.range N).filter (Reach act ngen root)
  have hS : ∀ x, Reach act ngen root x ↔ x ∈ S := by
    intro x
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hlt x h, h⟩, fun h => h.2⟩
  have hcard : S.card ≤ fuel :=
    le_trans (le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])) hfuel
  obtain ⟨hok, hmem, -, -⟩ := natBfs_spec (valid := fun x => decide (x < N)) (fuel := fuel) S hS
    (fun x hx => by
    rw [decide_eq_true_iff]
    exact (Finset.mem_range.1 (Finset.mem_filter.1 hx).1)) hcard
  refine ⟨hok, fun y => ?_⟩
  rw [Array.contains_iff_mem, hmem, hS]

end CFSG.KC.Orb14

end
