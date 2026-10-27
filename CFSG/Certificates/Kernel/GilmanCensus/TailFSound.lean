module

public import CFSG.Certificates.Kernel.GilmanCensus.Fast2Sound
public import CFSG.Certificates.Kernel.GilmanCensus.TailOkSound
public import Certificates.Data.Kernel.GilmanCensus.TailF

public section

namespace Certificates.GilmanCensusK

theorem allR_zipWithR_at {α β : Type} (f : α → β → Bool) (l₁ : List α) (l₂ : List β)
    (h : allR id (zipWithR f l₁ l₂) = true) (i : Nat) (h₁ : i < l₁.length)
    (h₂ : i < l₂.length) : f l₁[i] l₂[i] = true := by
  rw [allR_eq, zipWithR_eq, List.all_eq_true] at h
  have hi : i < (List.zipWith f l₁ l₂).length := by
    rw [List.length_zipWith]
    exact Nat.lt_min.mpr ⟨h₁, h₂⟩
  have := h _ (List.getElem_mem hi)
  simpa using this

theorem gShapeR_spec {dk : DK} (h : gShapeR dk = true) :
    dk.G.length = dk.N ∧ ∀ i (hi : i < dk.G.length), dk.G[i].length = dk.N := by
  simp only [gShapeR, Bool.and_eq_true, natBeq_eq, beq_iff_eq, lenR_eq, allR_eq,
    List.all_eq_true] at h
  exact ⟨h.1, fun i hi => h.2 _ (List.getElem_mem hi)⟩

theorem foldl_add_sumF (f : Nat → Int) : ∀ (l : List Nat) (t : Int),
    l.foldl (fun t j => t + f j) t = t + (l.map f).sum
  | [], t => by simp
  | a :: l, t => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_sumF f l]
    omega

theorem sum_map_mul_leftF (c : Int) (f : Nat → Int) :
    ∀ l : List Nat, (l.map fun j => c * f j).sum = c * (l.map f).sum
  | [] => by simp
  | a :: l => by simp [sum_map_mul_leftF c f l, Int.mul_add]

theorem dotZR_eq : ∀ (v w : List Int), v.length = w.length →
    dotZR v w = ((List.range v.length).map fun i => v.getD i 0 * w.getD i 0).sum
  | [], _, _ => rfl
  | a :: v, [], h => by simp at h
  | a :: v, b :: w, h => by
    have ih := dotZR_eq v w (by simpa using h)
    change Int.add (Int.mul a b) (dotZR v w) = _
    rw [ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    simp [Function.comp_def]

theorem bvK_length (B : List (List Int)) (n : Nat) (s : List Int) : (bvK B n s).length = n := by
  simp [bvK]

theorem gramK_eq_dotZR (B : List (List Int)) (n : Nat) (r s : List Int) (hr : r.length = n) :
    gramK B r s = dotZR r (bvK B n s) := by
  rw [dotZR_eq r _ (by rw [bvK_length, hr])]
  unfold gramK
  simp only [foldl_add_sumF]
  rw [Int.zero_add, hr, ← List.range_eq_range']
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have e : (bvK B n s).getD i 0 =
      ((List.range n).map fun j => (B.getD i []).getD j 0 * s.getD j 0).sum := by
    simp [bvK, List.getD_eq_getElem?_getD, hi]
  rw [e, ← sum_map_mul_leftF]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [Int.mul_assoc]

theorem foldl_fixF {α β : Type} (f : β → α → β) (b : β) :
    ∀ l : List α, (∀ a ∈ l, f b a = b) → l.foldl f b = b
  | [], _ => rfl
  | a :: l, h => by
    rw [List.foldl_cons, h a (by simp)]
    exact foldl_fixF f b l (fun x hx => h x (by simp [hx]))

theorem fhOkK_of (F H : List (List Nat)) (g : Nat → Nat → Int) (N : Nat)
    (h : ∀ i j, i < N → j < N → ((dot3K (F.getD i []) (H.getD j []) : Int) = 2 * g i j / g j j % 3)) :
    fhOkK F H g N true = true := by
  unfold fhOkK
  apply foldl_fixF
  intro i hi
  rw [List.mem_range'] at hi
  apply foldl_fixF
  intro j hj
  rw [List.mem_range'] at hj
  rw [h i j (by omega) (by omega)]
  simp

theorem maskR_eq (P : Nat → Bool) : ∀ (g : List Nat) (k m : Nat),
    (∀ j < g.length, P (k + j) = (g.getD j 0 != 64)) →
    maskR g k m = (List.range' k g.length).foldl (fun m j => if P j = true then m ||| bitK j else m) m
  | [], _, _, _ => rfl
  | x :: g, k, m, h => by
    change maskR g (k + 1) (Bool.rec (motive := fun _ => Nat) (m ||| bitK k) m (Nat.beq x 64)) = _
    rw [List.length_cons, List.range'_succ, List.foldl_cons]
    have h0 : P k = (x != 64) := by simpa using h 0 (by simp)
    have e : Bool.rec (motive := fun _ => Nat) (m ||| bitK k) m (Nat.beq x 64) =
        (if P k = true then m ||| bitK k else m) := by
      rw [h0, natBeq_eq]
      cases hx : x == 64 <;> simp [bne, hx]
    rw [e]
    apply maskR_eq P g (k + 1)
    intro j hj
    have := h (j + 1) (by simp; omega)
    rw [show k + 1 + j = k + (j + 1) by omega, this]
    rfl

theorem digR_spec (q σ : Int) : ∀ (r s : List Int) (c : Nat), r.length = s.length →
    digR q σ r s c = true →
    ∀ t (ht : t < r.length) (hs : t < s.length), s[t] - q * r[t] = σ * ((c / 8 ^ t % 8 : Nat) : Int)
  | [], _, _, _, _, t, ht, _ => by simp at ht
  | _ :: _, [], _, h, _, _, _, _ => by simp at h
  | a :: r, b :: s, c, hl, h, t, ht, hs => by
    change ((b - q * a == σ * ((c % 8 : Nat) : Int)) && digR q σ r s (c / 8)) = true at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    cases t with
    | zero => simpa using h.1
    | succ t =>
      have := digR_spec q σ r s (c / 8) (by simpa using hl) h.2 t (by simpa using ht)
        (by simpa using hs)
      simp only [List.getElem_cons_succ]
      rw [this, Nat.div_div_eq_div_mul, Nat.pow_succ', Nat.mul_comm]

theorem codeN_lt : ∀ (r : List Nat), (∀ x ∈ r, x < 8) → codeN r < 8 ^ r.length
  | [], _ => by simp [codeN]
  | x :: r, h => by
    have := codeN_lt r (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [codeN, List.length_cons, Nat.pow_succ]
    have : 8 * codeN r + 8 ≤ 8 ^ r.length * 8 := by
      rw [Nat.mul_comm (8 ^ r.length)]
      omega
    omega

theorem codeN_digit : ∀ (r : List Nat), (∀ x ∈ r, x < 8) → ∀ t (ht : t < r.length),
    codeN r / 8 ^ t % 8 = r[t]
  | [], _, t, ht => by simp at ht
  | x :: r, h, t, ht => by
    have hx := h x (by simp)
    cases t with
    | zero => simp [codeN]; omega
    | succ t =>
      have := codeN_digit r (fun y hy => h y (by simp [hy])) t (by simpa using ht)
      simp only [codeN, List.getElem_cons_succ]
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        show (x + 8 * codeN r) / 8 = codeN r by omega, this]

theorem packF_lane (n : Nat) : ∀ (R : List (List Nat)), (∀ r ∈ R, codeN r < 2 ^ (3 * n)) →
    ∀ k (hk : k < R.length), (packF n R >>> (3 * n * k)) % 2 ^ (3 * n) = codeN R[k]
  | [], _, k, hk => by simp at hk
  | r :: R, h, k, hk => by
    have hr := h r (by simp)
    rw [Nat.shiftRight_eq_div_pow]
    cases k with
    | zero => simp [packF, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    | succ k =>
      have ih := packF_lane n R (fun x hx => h x (by simp [hx])) k (by simpa using hk)
      rw [Nat.shiftRight_eq_div_pow] at ih
      have e : (codeN r + 2 ^ (3 * n) * packF n R) / 2 ^ (3 * n * (k + 1)) =
          packF n R / 2 ^ (3 * n * k) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (3 * n * k)), ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]
      simp only [packF, List.getElem_cons_succ]
      rw [e, ih]

theorem reflRowR_spec (n N T : Nat) (r w : List Int) (b : Int) : ∀ (l : List (List Int)) (x : Nat),
    reflRowR n N T r w b l x = true →
    (∀ j (hj : j < l.length), reflCellR N r l[j] (2 * dotZR l[j] w) b (x / 128 ^ j % 128)
      (T >>> (3 * n * (x / 128 ^ j % 128)) % 2 ^ (3 * n)) = true) ∧ x / 128 ^ l.length = 0
  | [], x, h => by
    change Nat.beq x 0 = true at h
    rw [natBeq_eq, beq_iff_eq] at h
    simp [h]
  | s :: l, x, h => by
    change (reflCellR N r s (2 * dotZR s w) b (x % 128)
      (T >>> (3 * n * (x % 128)) % 2 ^ (3 * n)) && reflRowR n N T r w b l (x / 128)) = true at h
    rw [Bool.and_eq_true] at h
    have ih := reflRowR_spec n N T r w b l (x / 128) h.2
    refine ⟨fun j hj => ?_, ?_⟩
    · cases j with
      | zero => simpa using h.1
      | succ j =>
        have := ih.1 j (by simpa using hj)
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at this
        simpa using this
    · have := ih.2
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at this
      simpa using this

theorem find_getD_nonneg (p : Int → Bool) : ∀ (l : List Int), (∀ y ∈ l, 0 ≤ y) →
    0 ≤ (l.find? p).getD 0
  | [], _ => by simp
  | y :: l, h => by
    by_cases hp : p y = true
    · simp only [List.find?_cons, hp, Option.getD_some]
      exact h y (by simp)
    · simp only [List.find?_cons, Bool.not_eq_true] at hp ⊢
      rw [hp]
      exact find_getD_nonneg p l (fun z hz => h z (by simp [hz]))

theorem find_getD_neg : ∀ (l : List Int), (∀ y ∈ l, y ≤ 0) → (∃ y ∈ l, y ≠ 0) →
    (l.find? (· != 0)).getD 0 < 0
  | [], _, ⟨y, hy, _⟩ => by simp at hy
  | y :: l, h, hex => by
    by_cases hy : y = 0
    · subst hy
      simp only [List.find?_cons, bne_self_eq_false]
      apply find_getD_neg l (fun z hz => h z (by simp [hz]))
      obtain ⟨z, hz, hz0⟩ := hex
      rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd rfl hz0
      · exact ⟨z, hz, hz0⟩
    · have := h y (by simp)
      have hb : (y != 0) = true := by simpa using hy
      simp only [List.find?_cons, hb, Option.getD_some]
      omega

theorem reflZK_of_sign (n : Nat) (r s : List Int) (q σ : Int) (v : List Nat)
    (hσ : σ = 1 ∨ σ = -1) (hv : v.length = n) (hnz : ∃ x ∈ v, x ≠ 0)
    (h : ∀ t < n, s.getD t 0 - q * r.getD t 0 = σ * ((v.getD t 0 : Nat) : Int)) :
    reflZK n r s q = v.map Int.ofNat := by
  have hz : (List.range n).map (fun t => s.getD t 0 - q * r.getD t 0) =
      v.map (fun x : Nat => σ * (x : Int)) := by
    apply List.ext_getElem
    · simp [hv]
    · intro t h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [h t (by simpa using h1), getD_lt v 0 (by simpa using h2)]
  unfold reflZK
  dsimp only
  rw [hz]
  rcases hσ with rfl | rfl
  · split
    · rename_i hlt
      exact absurd hlt (Int.not_lt.mpr (find_getD_nonneg _ _ (fun y hy => by
        simp only [List.mem_map] at hy
        obtain ⟨x, _, rfl⟩ := hy
        omega)))
    · apply List.map_congr_left
      intro x _
      simp
  · split
    · rw [List.map_map]
      apply List.map_congr_left
      intro x _
      simp
    · rename_i hn
      obtain ⟨x0, hx0, hx0'⟩ := hnz
      exact absurd (find_getD_neg _ (fun y hy => by
        simp only [List.mem_map] at hy
        obtain ⟨x, _, rfl⟩ := hy
        omega) ⟨-1 * (x0 : Int), List.mem_map.mpr ⟨x0, hx0, rfl⟩, by omega⟩) hn

theorem idxIK_nodup (v : List Int) : ∀ (l : List (List Int)) (m k : Nat) (hk : k < l.length),
    l.Nodup → v = l[k] → idxIK v l m = some (m + k)
  | [], _, _, hk, _, _ => absurd hk (by simp)
  | r :: l, m, 0, _, _, hv => by
    subst hv
    simp [idxIK]
  | r :: l, m, k + 1, hk, hnd, hv => by
    rw [List.nodup_cons] at hnd
    have hv' : v = l[k]'(by simpa using hk) := by simpa using hv
    have hmem : v ∈ l := hv' ▸ List.getElem_mem _
    have hne : (r == v) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      exact hnd.1 (e ▸ hmem)
    simp only [idxIK, hne, Bool.false_eq_true, if_false]
    rw [idxIK_nodup v l (m + 1) k (by simpa using hk) hnd.2 hv']
    congr 1
    omega

theorem reflCell_spec (n N : Nat) (R : List (List Nat)) (r s : List Int) (a b : Int) (k : Nat)
    (hR : ∀ v ∈ R, (∀ x ∈ v, x < 8) ∧ ∃ x ∈ v, x ≠ 0) (hlen : ∀ v ∈ R, v.length = n)
    (hRN : R.length = N) (hr : r.length = n) (hs : s.length = n) (hnd : (toI R).Nodup)
    (h : reflCellR N r s a b k (packF n R >>> (3 * n * k) % 2 ^ (3 * n)) = true) :
    a % b = 0 ∧ idxIK (reflZK n r s (a / b)) (toI R) 0 = some k := by
  unfold reflCellR at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq] at h
  obtain ⟨⟨hm, hk⟩, hd⟩ := h
  refine ⟨hm, ?_⟩
  have hkR : k < R.length := hRN ▸ hk
  have hc : packF n R >>> (3 * n * k) % 2 ^ (3 * n) = codeN R[k] := by
    apply packF_lane n R _ k hkR
    intro v hv
    have := codeN_lt v (hR v hv).1
    rw [hlen v hv] at this
    rw [Nat.pow_mul]
    exact this
  rw [hc] at hd
  have hv := hR _ (List.getElem_mem hkR)
  have hlk := hlen _ (List.getElem_mem hkR)
  have key : ∀ σ : Int, digR (a / b) σ r s (codeN R[k]) = true → (σ = 1 ∨ σ = -1) →
      reflZK n r s (a / b) = R[k].map Int.ofNat := by
    intro σ hdσ hσ
    apply reflZK_of_sign n r s (a / b) σ R[k] hσ hlk hv.2
    intro t ht
    have := digR_spec _ _ r s _ (by rw [hr, hs]) hdσ t (by omega) (by omega)
    rw [codeN_digit _ hv.1 t (by omega)] at this
    rw [getD_lt s 0 (by omega), getD_lt r 0 (by omega), getD_lt R[k] 0 (by omega)]
    exact this
  have hkI : k < (toI R).length := by rw [toI_length]; exact hkR
  have hz : reflZK n r s (a / b) = (toI R)[k] := by
    have e : (toI R)[k] = R[k].map Int.ofNat := by simp [toI]
    rw [e]
    rcases hd with hd | hd
    · exact key 1 hd (Or.inl rfl)
    · exact key (-1) hd (Or.inr rfl)
  rw [idxIK_nodup _ (toI R) 0 k hkI hnd hz]
  simp

theorem reflK_of (R : List (List Int)) (g : Nat → Nat → Int) (n N : Nat) (K : Nat → Nat → Nat)
    (h : ∀ i j, i < N → j < N → 2 * g j i % g i i = 0 ∧
      idxIK (reflZK n (R.getD i []) (R.getD j []) (2 * g j i / g i i)) R 0 = some (K i j)) :
    reflK R g n N true = (true, (List.range N).map fun i => (List.range N).map (K i)) := by
  have row : ∀ i, i < N → ∀ ok, reflRowK R g n N i ok = (ok, (List.range N).map (K i)) := by
    intro i hi ok
    have gen : ∀ (l : List Nat) (acc : List Nat), (∀ j ∈ l, j < N) →
        l.foldl (reflStepK R g n i) (ok, acc) = (ok, acc ++ l.map (K i)) := by
      intro l
      induction l with
      | nil => intro acc _; simp
      | cons j l ih =>
        intro acc hl
        obtain ⟨h1, h2⟩ := h i j hi (hl j (by simp))
        have e : reflStepK R g n i (ok, acc) j = (ok, acc ++ [K i j]) := by
          unfold reflStepK
          dsimp only
          rw [h2]
          simp [h1]
        rw [List.foldl_cons, e, ih _ (fun x hx => hl x (by simp [hx]))]
        simp
    unfold reflRowK
    rw [gen _ [] (fun j hj => by rw [List.mem_range'_1] at hj; omega), ← List.range_eq_range']
    simp
  have gen : ∀ (l : List Nat) (acc : List (List Nat)), (∀ i ∈ l, i < N) →
      l.foldl (fun st i => let r := reflRowK R g n N i st.1; (r.1, st.2 ++ [r.2])) (true, acc) =
        (true, acc ++ l.map fun i => (List.range N).map (K i)) := by
    intro l
    induction l with
    | nil => intro acc _; simp
    | cons i l ih =>
      intro acc hl
      rw [List.foldl_cons]
      dsimp only
      rw [row i (hl i (by simp)) true]
      rw [ih _ (fun x hx => hl x (by simp [hx]))]
      simp
  unfold reflK
  rw [gen _ [] (fun j hj => by rw [List.mem_range'_1] at hj; omega), ← List.range_eq_range']
  simp

theorem lanesOkK_of (dk : DK) (K : Nat → Nat → Nat)
    (hK : ∀ i j, i < dk.N → j < dk.N → K i j = dk.reflP.getD i 0 / 128 ^ j % 128)
    (hz : ∀ i, i < dk.N → dk.reflP.getD i 0 / 128 ^ dk.N = 0) :
    lanesOkK dk ((List.range dk.N).map fun i => (List.range dk.N).map (K i)) = true := by
  unfold lanesOkK
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi j hj
  have e : (2 : Nat) ^ (7 * j) = 128 ^ j := by rw [Nat.pow_mul]
  rw [Nat.shiftRight_eq_div_pow, e,
    getD_lt ((List.range dk.N).map fun i => (List.range dk.N).map (K i)) _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases hjN : j < dk.N
  · have e2 : ((List.range dk.N).map (K i)).getD j 0 = K i j := by
      simp [List.getD_eq_getElem?_getD, hjN]
    rw [e2, hK i j hi hjN]
  · have e2 : ((List.range dk.N).map (K i)).getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [e2]
    have h0 := hz i hi
    rw [Nat.div_eq_zero_iff] at h0
    have hlt : dk.reflP.getD i 0 < 128 ^ j := by
      rcases h0 with h0 | h0
      · exact absurd h0 (Nat.ne_of_gt (Nat.pow_pos (a := 128) (n := dk.N) (by decide)))
      · exact Nat.lt_of_lt_of_le h0 (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt hlt]

theorem tailOkK_of_tailF (dk : DK) (n : Nat) (Bl : List (List Int)) (hb : tailBlockK dk n = true)
    (hg : gramF dk n Bl = true) (hf : fhF dk = true) (ha : adjF dk = true)
    (hr : reflF dk n Bl = true) (har : (dk.AR == dk.R && dk.aadj == dk.adj) = true)
    (hl : (linesK dk.d == dk.lines) = true) : tailOkK dk n Bl = true := by
  have hb' := hb
  simp only [tailBlockK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, c9⟩, -⟩, c11⟩, -⟩, -⟩ := hb'
  rw [List.all_eq_true] at c2
  have hlenI : (toI dk.R).length = dk.N := by rw [toI_length, c3]
  have hrowlen : ∀ i (hi : i < (toI dk.R).length), ((toI dk.R)[i]).length = n := by
    intro i hi
    have hi' : i < dk.R.length := by rwa [toI_length] at hi
    have := c2 _ (List.getElem_mem hi')
    simp [toI, beq_iff_eq.mp this]
  simp only [gramF, Bool.and_eq_true, toIR_eq, mapR_eq] at hg
  obtain ⟨hsh, hrows⟩ := hg
  have shape := gShapeR_spec hsh
  have hgram : ∀ i j, i < dk.N → j < dk.N →
      gramK Bl ((toI dk.R).getD i []) ((toI dk.R).getD j []) = gI dk i j := by
    intro i j hi hj
    have h1 := allR_zipWithR_at _ _ _ hrows i (by omega) (by omega)
    unfold gramRowR at h1
    have h2 := allR_zipWithR_at _ _ _ h1 j (by simp; omega)
      (by rw [shape.2 i (by omega)]; omega)
    simp only [List.getElem_map, beq_iff_eq] at h2
    rw [getD_lt _ _ (by omega), getD_lt _ _ (by omega),
      gramK_eq_dotZR Bl n _ _ (hrowlen i (by omega)), h2]
    unfold gI
    rw [getD_lt dk.G _ (by omega), getD_lt dk.G[i] _ (by rw [shape.2 i (by omega)]; omega)]
    rfl
  have hG : gramOkK dk Bl = true := by
    unfold gramOkK
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi j hj
    exact hgram i j hi hj
  have hF : fhOkK dk.F dk.H (gI dk) dk.N true = true := by
    simp only [fhF, Bool.and_eq_true, diagR, getDR_eq, rangeR_eq, lenR_eq] at hf
    obtain ⟨-, hrowsF⟩ := hf
    apply fhOkK_of
    intro i j hi hj
    have h1 := allR_zipWithR_at _ _ _ hrowsF i (by omega) (by omega)
    unfold fhRowR at h1
    have h2 := allR_zipWithR_at _ _ _ h1 j (by simp [zipWithR_eq]; omega)
      (by rw [shape.2 i (by omega)]; omega)
    simp only [zipWithR_eq, List.getElem_zipWith, List.getElem_range, dot3R_eq, beq_iff_eq] at h2
    unfold gI
    rw [getD_lt dk.F _ (by omega), getD_lt dk.H _ (by omega), getD_lt dk.G _ (by omega),
      getD_lt dk.G _ (by omega), getD_lt _ _ (by rw [shape.2 i (by omega)]; omega),
      getD_lt _ _ (by rw [shape.2 j (by omega)]; omega)]
    rw [getD_lt _ _ (by rw [shape.2 j (by omega)]; omega)] at h2
    exact h2
  have hA : (adjK (gI dk) dk.N == dk.adj) = true := by
    simp only [adjF, Bool.and_eq_true, natBeq_eq, beq_iff_eq, lenR_eq] at ha
    obtain ⟨⟨-, hlen⟩, hrowsA⟩ := ha
    rw [beq_iff_eq]
    apply List.ext_getElem
    · simp [adjK, hlen]
    · intro i h1 h2
      have hi : i < dk.N := by simpa [adjK] using h1
      have hiG : i < dk.G.length := by omega
      have := allR_zipWithR_at _ _ _ hrowsA i hiG (by omega)
      rw [beq_iff_eq, maskR_eq (fun j => gI dk i j != 0) dk.G[i] 0 0, shape.2 i hiG,
        ← List.range_eq_range'] at this
      · rw [← this]
        simp only [adjK, List.getElem_map, List.getElem_range]
      · intro j hj
        rw [Nat.zero_add, gI, getD_lt dk.G _ hiG, Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
        omega
  have hAA : (adjK (fun i j => gramK Bl ((toI dk.AR).getD i []) ((toI dk.AR).getD j []))
      dk.AR.length == dk.aadj) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq] at har
    rw [har.1, har.2, c3, adjK_congr _ (gI dk) _ hgram]
    exact hA
  simp only [reflF, Bool.and_eq_true, natBeq_eq, beq_iff_eq, lenR_eq, toIR_eq, mapR_eq] at hr
  obtain ⟨⟨hR8, hlenP⟩, hrowsR⟩ := hr
  rw [allR_eq, List.all_eq_true] at hR8
  have hR : ∀ v ∈ dk.R, (∀ x ∈ v, x < 8) ∧ ∃ x ∈ v, x ≠ 0 := by
    intro v hv
    have := hR8 v hv
    simpa [allR_eq, anyR_eq, natBeq_eq, Nat.blt_eq] using this
  have hlenR : ∀ v ∈ dk.R, v.length = n := fun v hv => beq_iff_eq.mp (c2 v hv)
  have hnd := distinctK_nodup _ c1
  have hcell : ∀ i, i < dk.N →
      (∀ j, j < dk.N → 2 * gI dk j i % gI dk i i = 0 ∧
        idxIK (reflZK n ((toI dk.R).getD i []) ((toI dk.R).getD j []) (2 * gI dk j i / gI dk i i))
          (toI dk.R) 0 = some (dk.reflP.getD i 0 / 128 ^ j % 128)) ∧
      dk.reflP.getD i 0 / 128 ^ dk.N = 0 := by
    intro i hi
    have h1 := allR_zipWithR_at _ _ _ hrowsR i (by simp [zipWithR_eq]; omega) (by omega)
    simp only [zipWithR_eq, List.getElem_zipWith, List.getElem_map] at h1
    have hs := reflRowR_spec n dk.N (packF n dk.R) _ _ _ _ _ h1
    have hs2 := hs.2
    rw [hlenI] at hs2
    refine ⟨fun j hj => ?_, by rw [getD_lt dk.reflP _ (by omega)]; exact hs2⟩
    have hc := reflCell_spec n dk.N dk.R _ _ _ _ _ hR hlenR c3 (hrowlen i (by omega))
      (hrowlen j (by omega)) hnd (hs.1 j (by omega))
    rw [← gramK_eq_dotZR Bl n _ _ (hrowlen i (by omega)),
      ← gramK_eq_dotZR Bl n _ _ (hrowlen j (by omega))] at hc
    rw [getD_lt _ _ (by omega), getD_lt _ _ (by omega), getD_lt _ _ (by omega),
      ← hgram j i hj hi, ← hgram i i hi hi, getD_lt _ _ (by omega), getD_lt _ _ (by omega)]
    exact hc
  have hRK := reflK_of (toI dk.R) (gI dk) n dk.N (fun i j => dk.reflP.getD i 0 / 128 ^ j % 128)
    (fun i j hi hj => (hcell i hi).1 j hj)
  have hlanes := lanesOkK_of dk (fun i j => dk.reflP.getD i 0 / 128 ^ j % 128)
    (fun _ _ _ _ => rfl) (fun i hi => (hcell i hi).2)
  have e : tailOkK dk n Bl = (tailBlockK dk n && gramOkK dk Bl &&
      fhOkK dk.F dk.H (gI dk) dk.N true && (adjK (gI dk) dk.N == dk.adj) &&
      (adjK (fun i j => gramK Bl ((toI dk.AR).getD i []) ((toI dk.AR).getD j [])) dk.AR.length ==
        dk.aadj) &&
      (reflK (toI dk.R) (gI dk) n dk.N true).1 &&
      lanesOkK dk (reflK (toI dk.R) (gI dk) n dk.N true).2 && (linesK dk.d == dk.lines)) := rfl
  rw [e, hb, hG, hF, hA, hAA, hRK, hl]
  simp only [hlanes, Bool.and_self]

end Certificates.GilmanCensusK

end
