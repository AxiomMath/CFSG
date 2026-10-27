module

public import Certificates.Data.Kernel.D5TwistK

public section

namespace Certificates.D5TwistK

open Certificates.D5Twist

theorem dg_eq (x k : Nat) : dg x k = x / 4 ^ k % 4 := rfl

theorem pk_lt (f : Nat → Nat) : ∀ n k, pk f k n < 4 ^ n := by
  intro n
  induction n with
  | zero => intro k; simp [pk]
  | succ n ih =>
    intro k
    have h1 := Nat.mod_lt (f k) (by decide : 4 > 0)
    have h2 := ih (k + 1)
    simp only [pk, Nat.pow_succ]
    generalize 4 ^ n = M at *
    omega

theorem dg_pk (f : Nat → Nat) : ∀ n k m, m < n → dg (pk f k n) m = f (k + m) % 4 := by
  intro n
  induction n with
  | zero => intro k m h; omega
  | succ n ih =>
    intro k m hm
    cases m with
    | zero =>
      simp only [pk, dg_eq, Nat.pow_zero, Nat.div_one, Nat.add_zero]
      omega
    | succ m =>
      have e1 : dg (pk f k (n + 1)) (m + 1) = dg (pk f (k + 1) n) m := by
        simp only [pk, dg_eq]
        rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        congr 2
        omega
      rw [e1, ih (k + 1) m (by omega)]
      congr 2
      omega

theorem pk_dg : ∀ n k x, x / 4 ^ k < 4 ^ n → pk (dg x) k n = x / 4 ^ k := by
  intro n
  induction n with
  | zero =>
    intro k x h
    simp only [Nat.pow_zero] at h
    simp only [pk]
    generalize x / 4 ^ k = y at *
    omega
  | succ n ih =>
    intro k x h
    have e : x / 4 ^ (k + 1) = x / 4 ^ k / 4 := by rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    simp only [pk]
    rw [ih (k + 1) x (by rw [e]; rw [Nat.pow_succ] at h; generalize 4 ^ n = M at *; omega), e]
    simp only [dg_eq]
    generalize x / 4 ^ k = y
    omega

theorem pk_congr (f g : Nat → Nat) :
    ∀ n k, (∀ i, k ≤ i → i < k + n → f i = g i) → pk f k n = pk g k n := by
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k h
    simp only [pk]
    rw [h k (by omega) (by omega), ih (k + 1) (fun i h1 h2 => h i (by omega) (by omega))]

theorem decN_get (n x i : Nat) (h : i < n) : (decN n x)[i]! = dg x i := by
  simp [decN, h]

theorem decN_inj {n x y : Nat} (hx : x < 4 ^ n) (hy : y < 4 ^ n) (h : decN n x = decN n y) :
    x = y := by
  have hd : ∀ i, i < n → dg x i = dg y i := fun i hi => by
    rw [← decN_get n x i hi, ← decN_get n y i hi, h]
  have ex := pk_dg n 0 x (by simpa using hx)
  have ey := pk_dg n 0 y (by simpa using hy)
  simp only [Nat.pow_zero, Nat.div_one] at ex ey
  rw [← ex, ← ey]
  exact pk_congr _ _ n 0 (fun i _ hi => hd i (by omega))

theorem decN_beq {n x y : Nat} (hx : x < 4 ^ n) (hy : y < 4 ^ n) :
    (decN n x == decN n y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨decN_inj hx hy, fun h => h ▸ rfl⟩

theorem contains_decN {n : Nat} {l : List Nat} {t : Nat} (hl : ∀ x ∈ l, x < 4 ^ n)
    (ht : t < 4 ^ n) : (l.map (decN n)).contains (decN n t) = l.contains t := by
  rw [Bool.eq_iff_iff]
  have e1 : (l.map (decN n)).contains (decN n t) = true ↔ decN n t ∈ l.map (decN n) := by simp
  have e2 : l.contains t = true ↔ t ∈ l := by simp
  rw [e1, e2, List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    rwa [decN_inj (hl a ha) ht he] at ha
  · intro h
    exact ⟨t, h, rfl⟩

theorem entK_lt (x y k : Nat) : entK x y k < 4 := by
  unfold entK
  exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

theorem entV_lt (a v i : Nat) : entV a v i < 4 := by
  unfold entV
  exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

theorem mulK_lt (x y : Nat) : mulK x y < 4 ^ 25 := pk_lt _ 25 0

theorem mvK_lt (a v : Nat) : mvK a v < 4 ^ 5 := pk_lt _ 5 0

theorem decN_def (n x : Nat) : decN n x = Array.ofFn (n := n) fun k => dg x k.val := rfl

theorem mulM_decN (x y : Nat) : mulM (decN 25 x) (decN 25 y) = decN 25 (mulK x y) := by
  unfold mulM
  rw [decN_def 25 (mulK x y)]
  refine congrArg (Array.ofFn (n := 25)) (funext fun k => ?_)
  have hk := k.2
  simp (disch := omega) only [decN_get]
  rw [mulK, dg_pk _ 25 0 _ hk, Nat.zero_add, Nat.mod_eq_of_lt (entK_lt _ _ _)]
  rfl

theorem mulV_decN (a v : Nat) : mulV (decN 25 a) (decN 5 v) = decN 5 (mvK a v) := by
  unfold mulV
  rw [decN_def 5 (mvK a v)]
  refine congrArg (Array.ofFn (n := 5)) (funext fun i => ?_)
  have hi := i.2
  simp (disch := omega) only [decN_get]
  rw [mvK, dg_pk _ 5 0 _ hi, Nat.zero_add, Nat.mod_eq_of_lt (entV_lt _ _ _)]
  rfl

abbrev stepN (seen : List Nat) : List Nat → Nat → List Nat :=
  fun acc t => if seen.contains t || acc.contains t then acc else acc ++ [t]

theorem fold_mem (seen L : List Nat) :
    ∀ (acc : List Nat) (t : Nat), t ∈ L.foldl (stepN seen) acc → t ∈ acc ∨ t ∈ L := by
  induction L with
  | nil =>
    intro acc t ht
    exact Or.inl (by simpa using ht)
  | cons a L ih =>
    intro acc t ht
    simp only [List.foldl_cons] at ht
    rcases ih _ t ht with h | h
    · by_cases hc : (seen.contains a || acc.contains a) = true
      · simp only [stepN] at h
        rw [if_pos hc] at h
        exact Or.inl h
      · simp only [stepN] at h
        rw [if_neg hc] at h
        rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton.mp h]
          exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem fold_sim (seen : List Nat) (hs : ∀ x ∈ seen, x < 4 ^ 25) :
    ∀ (L acc : List Nat), (∀ x ∈ L, x < 4 ^ 25) → (∀ x ∈ acc, x < 4 ^ 25) →
      (L.map (decN 25)).foldl (fun acc t => if (seen.map (decN 25)).contains t || acc.contains t
        then acc else acc ++ [t]) (acc.map (decN 25)) = (L.foldl (stepN seen) acc).map (decN 25) := by
  intro L
  induction L with
  | nil => intro acc _ _; rfl
  | cons a L ih =>
    intro acc hL hacc
    have ha := hL a List.mem_cons_self
    have hL' : ∀ x ∈ L, x < 4 ^ 25 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.foldl_cons]
    rw [contains_decN hs ha, contains_decN hacc ha]
    by_cases hc : (seen.contains a || acc.contains a) = true
    · simp only [stepN, hc, if_true]
      exact ih acc hL' hacc
    · simp only [stepN, hc]
      have e : acc.map (decN 25) ++ [decN 25 a] = (acc ++ [a]).map (decN 25) := by simp
      rw [if_neg (by simpa using hc), e]
      refine ih (acc ++ [a]) hL' ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hacc x hx
      · rw [List.mem_singleton.mp hx]
        exact ha

theorem cca_sim (gens : List Nat) : ∀ n front seen, (∀ x ∈ seen, x < 4 ^ 25) →
    conjClosureAux (gens.map (decN 25)) n (front.map (decN 25)) (seen.map (decN 25)) =
      (ccaK gens n front seen).map (decN 25) ∧ ∀ x ∈ ccaK gens n front seen, x < 4 ^ 25 := by
  intro n
  induction n with
  | zero => intro front seen hs; exact ⟨by simp [conjClosureAux, ccaK], by simpa [ccaK] using hs⟩
  | succ n ih =>
    intro front seen hs
    cases front with
    | nil => exact ⟨by simp [conjClosureAux, ccaK], by simpa [ccaK] using hs⟩
    | cons r front =>
      have hmap : (gens.map (decN 25)).map (fun s => mulM (mulM s (decN 25 r)) s) =
          (gens.map fun s => mulK (mulK s r) s).map (decN 25) := by
        simp only [List.map_map, Function.comp_def, mulM_decN]
      have hLb : ∀ x ∈ gens.map (fun s => mulK (mulK s r) s), x < 4 ^ 25 := by
        intro x hx
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
        exact mulK_lt _ _
      have hfold := fold_sim seen hs _ [] hLb (by simp)
      simp only [List.map_nil] at hfold
      have hnb : ∀ x ∈ (gens.map fun s => mulK (mulK s r) s).foldl (stepN seen) [], x < 4 ^ 25 := by
        intro x hx
        rcases fold_mem seen _ [] x hx with h | h
        · simp at h
        · exact hLb x h
      have hsb : ∀ x ∈ seen ++ (gens.map fun s => mulK (mulK s r) s).foldl (stepN seen) [],
          x < 4 ^ 25 := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hs x h
        · exact hnb x h
      obtain ⟨ih1, ih2⟩ := ih (front ++ (gens.map fun s => mulK (mulK s r) s).foldl (stepN seen) [])
        (seen ++ (gens.map fun s => mulK (mulK s r) s).foldl (stepN seen) []) hsb
      have eK : ccaK gens (n + 1) (r :: front) seen =
          ccaK gens n (front ++ (gens.map fun s => mulK (mulK s r) s).foldl (stepN seen) [])
            (seen ++ (gens.map fun s => mulK (mulK s r) s).foldl (stepN seen) []) := rfl
      rw [eK]
      refine ⟨?_, ih2⟩
      rw [List.map_cons]
      simp only [conjClosureAux]
      rw [hmap, hfold, ← List.map_append, ← List.map_append, ih1]

theorem cc_sim (seed gens : List Nat) (hs : ∀ x ∈ seed, x < 4 ^ 25) :
    conjClosure (seed.map (decN 25)) (gens.map (decN 25)) = (ccK seed gens).map (decN 25) ∧
      ∀ x ∈ ccK seed gens, x < 4 ^ 25 :=
  cca_sim gens 500 seed seed hs

theorem allVK_lt : ∀ v ∈ allVK, v < 4 ^ 5 := by
  intro v hv
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
  exact pk_lt _ 5 0

theorem fixedVK_sub (S : List Nat) : ∀ v ∈ fixedVK S, v ∈ allVK := fun _ hv =>
  (List.mem_filter.mp hv).1

theorem all_map_eq {α β : Type} {l : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ a ∈ l, p (f a) = q a) : (l.map f).all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filter_map_eq {α β : Type} {l : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ a ∈ l, p (f a) = q a) : (l.map f).filter p = (l.filter q).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.filter_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    cases q a <;> simp

theorem flatMap_map_eq {α β γ δ : Type} {l : List α} {d : α → β} {F : β → List γ}
    {G : α → List δ} {e : δ → γ} (h : ∀ a ∈ l, F (d a) = (G a).map e) :
    (l.map d).flatMap F = (l.flatMap G).map e := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem fixedVecs_sim (hV : allVecs () = allVK.map (decN 5)) (S : List Nat) :
    fixedVecs (S.map (decN 25)) = (fixedVK S).map (decN 5) := by
  unfold fixedVecs fixedVK
  rw [hV]
  apply filter_map_eq
  intro v hv
  apply all_map_eq
  intro s _
  rw [mulV_decN, decN_beq (mvK_lt _ _) (allVK_lt v hv)]

theorem prodWordK_lt (gs : List Nat) :
    ∀ (w : List Nat) (acc : Nat), acc < 4 ^ 25 →
      w.foldl (fun acc i => mulK acc gs[i]!) acc < 4 ^ 25 := by
  intro w
  induction w with
  | nil => intro acc h; exact h
  | cons i w ih =>
    intro acc _
    rw [List.foldl_cons]
    exact ih (mulK acc gs[i]!) (mulK_lt acc gs[i]!)

theorem getBang_map (l : List Nat) (i : Nat) (h : i < l.length) :
    (l.map (decN 25))[i]! = decN 25 l[i]! := by
  have h' : i < (l.map (decN 25)).length := by simpa using h
  rw [getElem!_pos (l.map (decN 25)) i h', getElem!_pos l i h, List.getElem_map]

theorem prodWord_sim (gs : List Nat) :
    ∀ (w : List Nat) (acc : Nat), (∀ i ∈ w, i < gs.length) →
      w.foldl (fun acc i => mulM acc (gs.map (decN 25))[i]!) (decN 25 acc) =
        decN 25 (w.foldl (fun acc i => mulK acc gs[i]!) acc) := by
  intro w
  induction w with
  | nil => intro acc _; rfl
  | cons i w ih =>
    intro acc h
    simp only [List.foldl_cons]
    rw [getBang_map gs i (h i List.mem_cons_self), mulM_decN]
    exact ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))

structure LFacts : Prop where
  s5 : simple5 () = simple5K.map (decN 25)
  s4 : sRefl 4 = decN 25 simple5K[4]!
  s5b : ∀ x ∈ simple5K, x < 4 ^ 25
  id : idM = decN 25 idK
  idb : idK < 4 ^ 25
  mo : minusOneM = decN 25 minusOneK
  xv : xv = decN 5 xvK
  xvb : xvK < 4 ^ 5
  zero : #[0, 0, 0, 0, 0] = decN 5 0
  vecs : allVecs () = allVK.map (decN 5)
  line : ∀ z ∈ allVK, lineOf (decN 5 z) = decN 5 (lineK z)
  zline : ∀ z ∈ allVK, zline (decN 5 z) = (zlineK z).map (decN 5)
  zlineb : ∀ z ∈ allVK, ∀ v ∈ zlineK z, v < 4 ^ 5

theorem S0_sim (hL : LFacts) : S0 () = (S0K ()).map (decN 25) ∧ ∀ x ∈ S0K (), x < 4 ^ 25 := by
  unfold S0 S0K
  rw [hL.s5]
  exact cc_sim simple5K simple5K hL.s5b

theorem lineK_lt (z : Nat) : lineK z < 4 ^ 5 := pk_lt _ 5 0

theorem caseOk_of (hL : LFacts) (b : Nat) (gam : Array Nat) (lam c : Nat) (neg : Bool)
    (w : List Nat) (g : Nat) (hgb : g < 4 ^ 25) (hg : cG gam lam c = decN 25 g)
    (hW : wjGens b = (wjGensK b).map (decN 25)) (hWb : ∀ x ∈ wjGensK b, x < 4 ^ 25)
    (hA : caseAK3 (cG gam lam c) g (invK g) b neg w = true)
    (hB : BK b (raK g (invK g)) = true) : caseOk b gam lam c neg w = true := by
  have inv_sim : ∀ n cur prev, cur < 4 ^ 25 →
      invAux (decN 25 g) n (decN 25 cur) (decN 25 prev) = decN 25 (invAuxK g n cur prev) := by
    intro n
    induction n with
    | zero => intro cur prev _; rfl
    | succ n ih =>
      intro cur prev hc
      simp only [invAux, invAuxK]
      rw [hL.id, decN_beq hc hL.idb, mulM_decN, ih _ _ (mulK_lt _ _)]
      cases (cur == idK) <;> rfl
  have eGi : cGi gam lam c = decN 25 (invK g) := by
    unfold cGi invM invK
    rw [hg, hL.id, inv_sim 1000 g idK hgb]
  have eRa : cRa gam lam c = decN 25 (raK g (invK g)) := by
    unfold cRa raK
    rw [eGi, hg, hL.s4, mulM_decN, mulM_decN]
  have eGs : cGs gam lam c = (gsK (raK g (invK g))).map (decN 25) := by
    unfold cGs gsK
    rw [hL.s5, eRa, List.map_append]
    rfl
  have hgsb : ∀ x ∈ gsK (raK g (invK g)), x < 4 ^ 25 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hL.s5b x h
    · rw [List.mem_singleton.mp h]
      exact mulK_lt _ _
  obtain ⟨eSp, hspb0⟩ := cc_sim _ _ hgsb
  have hspb : ∀ x ∈ spK (raK g (invK g)), x < 4 ^ 25 := hspb0
  have eSp' : cSp gam lam c = (spK (raK g (invK g))).map (decN 25) := by
    unfold cSp spK
    rw [eGs]
    exact eSp
  obtain ⟨eWj, hwjb⟩ := cc_sim _ _ hWb
  have eWj' : cWj b = (wjK b).map (decN 25) := by
    unfold cWj wjK
    rw [hW]
    exact eWj
  have hlinesV : ∀ z ∈ linesK b, z ∈ allVK := fun z hz =>
    fixedVK_sub _ z (List.mem_filter.mp hz).1
  have eLines : cLines b = (linesK b).map (decN 5) := by
    unfold cLines linesK
    rw [eWj', fixedVecs_sim hL.vecs]
    apply filter_map_eq
    intro z hz
    have hzV := fixedVK_sub _ z hz
    have hzb := allVK_lt z hzV
    rw [hL.zero, hL.line z hzV, bne, decN_beq hzb (by decide), decN_beq (lineK_lt z) hzb]
    rfl
  have eRz : ∀ z, z < 4 ^ 5 → cRz gam lam c (decN 5 z) = (rzK (raK g (invK g)) z).map (decN 25) := by
    intro z hz
    unfold cRz rzK
    rw [eSp']
    apply filter_map_eq
    intro r _
    rw [mulV_decN, decN_beq (mvK_lt _ _) hz]
  have eOz : ∀ z, z < 4 ^ 5 →
      cOz b gam lam c (decN 5 z) = (ozK b (raK g (invK g)) z).map (decN 25) ∧
        ∀ x ∈ ozK b (raK g (invK g)) z, x < 4 ^ 25 := by
    intro z hz
    unfold cOz ozK
    rw [eWj', eRz z hz]
    exact cc_sim _ _ hwjb
  have eL15 : cLines15 b gam lam c = (lines15K b (raK g (invK g))).map (decN 5) := by
    unfold cLines15 lines15K
    rw [eLines]
    apply filter_map_eq
    intro z hz
    rw [(eOz z (allVK_lt z (hlinesV z hz))).1, List.length_map]
  have hl15V : ∀ z ∈ lines15K b (raK g (invK g)), z ∈ allVK := fun z hz =>
    hlinesV z (List.mem_filter.mp hz).1
  have eF : cForced b gam lam c = (forcedK b (raK g (invK g))).map (decN 25) := by
    unfold cForced forcedK
    rw [eL15]
    apply flatMap_map_eq
    intro z hz
    exact (eOz z (allVK_lt z (hl15V z hz))).1
  have hFb : ∀ x ∈ forcedK b (raK g (invK g)), x < 4 ^ 25 := by
    intro x hx
    obtain ⟨z, hz, hx⟩ := List.mem_flatMap.mp hx
    exact (eOz z (allVK_lt z (hl15V z hz))).2 x hx
  obtain ⟨eS0, hS0b⟩ := S0_sim hL
  have hSFb : ∀ x ∈ S0K () ++ forcedK b (raK g (invK g)), x < 4 ^ 25 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hS0b x h
    · exact hFb x h
  obtain ⟨eCl, hclb0⟩ := cc_sim _ _ hSFb
  have hclb : ∀ x ∈ clK b (raK g (invK g)), x < 4 ^ 25 := hclb0
  have eCl' : cCl b gam lam c = (clK b (raK g (invK g))).map (decN 25) := by
    unfold cCl clK
    rw [eS0, eF, ← List.map_append]
    exact eCl
  unfold caseOk
  rw [eGi, eGs, eSp', eWj', eLines, eL15, eF, eCl', hg]
  unfold caseAK3 at hA
  unfold BK restK at hB
  simp only [Bool.and_eq_true] at hA hB
  obtain ⟨⟨⟨⟨_, hA1⟩, hA2⟩, hA3⟩, hA4⟩ := hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hB4, hB5⟩, hB6⟩, hB7⟩, hB8⟩, hB9⟩, hB10⟩, hB11⟩, hB12⟩, hB13⟩ := hB
  have hwl : ∀ i ∈ w, i < (gsK (raK g (invK g))).length := by
    intro i hi
    have := List.all_eq_true.mp hA2 i hi
    simp only [decide_eq_true_eq] at this
    simp only [gsK, List.length_append, List.length_cons, List.length_nil, simple5K]
    omega
  unfold caseCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hA2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [mulM_decN, hL.id, decN_beq (mulK_lt _ _) hL.idb]
    exact hA1
  · unfold prodWord
    rw [hL.id, prodWord_sim _ w idK hwl]
    have hpb := prodWordK_lt (gsK (raK g (invK g))) w idK hL.idb
    unfold prodWordK at hA3
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte] at hA3 ⊢
      rw [decN_beq hpb hgb]
      exact hA3
    · simp only [↓reduceIte] at hA3 ⊢
      unfold negM
      rw [hL.mo, mulM_decN, decN_beq hpb (mulK_lt _ _)]
      exact hA3
  · refine Eq.trans (all_map_eq ?_) hB4
    intro s _
    rw [mulM_decN, hL.id, decN_beq (mulK_lt _ _) hL.idb]
  · refine Eq.trans (all_map_eq ?_) hB5
    intro s _
    rw [mulM_decN, hL.id, decN_beq (mulK_lt _ _) hL.idb]
  · refine Eq.trans (all_map_eq ?_) hB6
    intro r _
    apply all_map_eq
    intro s _
    rw [mulM_decN, mulM_decN, contains_decN hspb (mulK_lt _ _)]
  · rw [List.length_map]
    exact hB7
  · rw [List.length_map]
    exact hB8
  · rw [List.length_map]
    exact hB9
  · refine Eq.trans (all_map_eq ?_) hB10
    intro z hz
    have hzV := hl15V z hz
    rw [hL.line z hzV, hL.xv, bne, bne, decN_beq (lineK_lt z) hL.xvb]
  · refine Eq.trans (all_map_eq ?_) hB11
    intro z hz
    have hzV := hl15V z hz
    rw [(eOz z (allVK_lt z hzV)).1, fixedVecs_sim hL.vecs, hL.zline z hzV]
    apply all_map_eq
    intro v hv
    exact contains_decN (hL.zlineb z hzV) (allVK_lt v (fixedVK_sub _ v hv))
  · refine Eq.trans (all_map_eq ?_) hB12
    intro s _
    rw [mulM_decN, hL.id, decN_beq (mulK_lt _ _) hL.idb]
  · refine Eq.trans (all_map_eq ?_) hB13
    intro r hr
    exact contains_decN hclb (hspb r hr)

theorem check_of_twin (hL : LFacts) (hS : ch712503S () = true) (hA : ch712503A () = true)
    (hWj : ∀ b ∈ [0, 2, 3], wjGens b = (wjGensK b).map (decN 25) ∧ ∀ x ∈ wjGensK b, x < 4 ^ 25)
    (hP : ∀ b r, (b, r) ∈ pairsK → b ∈ [0, 2, 3])
    (hB : ∀ b r, (b, r) ∈ pairsK → BK b r = true) : check () = true := by
  obtain ⟨eS0, _⟩ := S0_sim hL
  unfold ch712503S at hS
  simp only [Bool.and_eq_true] at hS
  obtain ⟨⟨hS1, hS2⟩, hS3⟩ := hS
  unfold check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, hS3⟩, ?_⟩
  · rw [eS0, List.length_map]
    exact hS1
  · rw [eS0]
    refine Eq.trans (all_map_eq ?_) hS2
    intro s _
    rw [mulM_decN, hL.id, decN_beq (mulK_lt _ _) hL.idb]
  · apply List.all_eq_true.mpr
    intro e he
    have h := List.all_eq_true.mp hA e he
    unfold caseAK caseAK2 at h
    have h' := h
    unfold caseAK3 at h'
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨h0, _⟩, _⟩, _⟩, h4⟩ := h'
    have hgb : encA (cG #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1) < 4 ^ 25 :=
      pk_lt _ 25 0
    have hg := (beq_iff_eq.mp h0).symm
    have hp : (e.1, raK (encA (cG #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1))
        (invK (encA (cG #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1)))) ∈ pairsK :=
      List.contains_iff_mem.mp h4
    obtain ⟨hW, hWb⟩ := hWj e.1 (hP _ _ hp)
    exact caseOk_of hL e.1 #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1
      e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2 _ hgb hg hW hWb h (hB _ _ hp)

end Certificates.D5TwistK

end
