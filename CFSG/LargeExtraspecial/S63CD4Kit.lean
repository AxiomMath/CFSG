module

public import CFSG.LargeExtraspecial.S63CD4Check
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (allLt_spec)

variable {H : Type*} [Group H] (E : H →* Matrix (Fin 24) (Fin 24) (ZMod 2))

@[expose] def RepE (R : Array ℕ) (h : H) : Prop := rowsMatrix 24 R = E h

variable {E}

theorem repE_mul {R S : Array ℕ} {g h : H} (hR : RepE E R g) (hS : RepE E S h) :
    RepE E (mulR R S) (g * h) := by
  unfold RepE mulR at *
  rw [rowsMatrix_mulRows, hR, hS, map_mul]

theorem repE_one : RepE E oneR (1 : H) := by
  unfold RepE oneR
  rw [rowsMatrix_idRows, map_one]

theorem repE_conjR {G X : Array ℕ} {g x : H} (hG : RepE E G g) (hX : RepE E X x)
    (hg : g * g = 1) : RepE E (conjR G X) (g * x * g⁻¹) := by
  rw [show g⁻¹ = g from (eq_inv_of_mul_eq_one_left hg).symm]
  exact repE_mul (repE_mul hG hX) hG

theorem repE_powRows {X : Array ℕ} {x : H} (hX : RepE E X x) (e : ℕ) :
    RepE E (powRows 24 X e) (x ^ e) := by
  unfold RepE at *
  rw [rowsMatrix_powRows, hX, map_pow]

theorem repE_sq12R {X : Array ℕ} {x : H} (hX : RepE E X x) : RepE E (sq12R X) (x ^ 4096) := by
  have key : ∀ (k : ℕ) (Y : Array ℕ) (y : H), RepE E Y y →
      RepE E ((List.range k).foldl (fun acc _ => mulR acc acc) Y) (y ^ 2 ^ k) := by
    intro k
    induction k with
    | zero => intro Y y hY; simpa using hY
    | succ k ih =>
      intro Y y hY
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ,
        pow_mul, sq]
      exact repE_mul (ih Y y hY) (ih Y y hY)
  exact key 12 X x hX

theorem repE_wordR {gs : Array (Array ℕ)} {gH : ℕ → H} {w : List ℕ}
    (hw : ∀ k ∈ w, RepE E gs[k]! (gH k)) : RepE E (wordR gs w) (w.map gH).prod := by
  induction w with
  | nil => exact repE_one
  | cons k w ih =>
    rw [wordR, List.foldr_cons, List.map_cons, List.prod_cons]
    exact repE_mul (hw k List.mem_cons_self) (ih fun k' hk' => hw k' (List.mem_cons_of_mem k hk'))

theorem eq_of_repE (hE : Function.Injective E) {R : Array ℕ} {g h : H} (hg : RepE E R g)
    (hh : RepE E R h) : g = h :=
  hE (hg.symm.trans hh)

theorem arr_eq_of_repE {R S : Array ℕ} {g : H} (hR : validR R = true) (hS : validR S = true)
    (hRg : RepE E R g) (hSg : RepE E S g) : R = S :=
  eq_of_rowsMatrix_eq hR hS (hRg.trans hSg.symm)

section Tree

variable {gs : Array (Array ℕ)} {x : Array ℕ} {T : Array (Array ℕ)} {P K : Array ℕ}
  {idx : Array ℕ → ℕ}

theorem classTreeOK_parts (h : classTreeOK gs x T P K idx = true) :
    0 < T.size ∧ T[0]! = x ∧ ∀ i < T.size, validR T[i]! = true ∧ idx T[i]! = i ∧
      (i = 0 ∨ (P[i]! < i ∧ K[i]! < gs.size ∧ T[i]! = conjR gs[K[i]!]! T[P[i]!]!)) := by
  simp only [classTreeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h0, hx⟩, hall⟩ := h
  refine ⟨h0, hx, fun i hi => ?_⟩
  have := allLt_spec hall hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem exists_conj_of_classTreeOK {gH : ℕ → H}
    (hgs : ∀ k < gs.size, RepE E gs[k]! (gH k) ∧ gH k * gH k = 1) {x₀ : H}
    (hx : RepE E x x₀) (h : classTreeOK gs x T P K idx = true) :
    ∀ i < T.size, ∃ c : H, RepE E T[i]! (c * x₀ * c⁻¹) := by
  obtain ⟨-, h0, hall⟩ := classTreeOK_parts h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases (hall i hi).2.2 with rfl | ⟨hP, hK, hT⟩
    · exact ⟨1, by rw [h0]; simpa using hx⟩
    · obtain ⟨c, hc⟩ := ih _ hP (hP.trans hi)
      refine ⟨gH K[i]! * c, ?_⟩
      rw [hT]
      have := repE_conjR (hgs _ hK).1 hc (hgs _ hK).2
      rwa [show gH K[i]! * (c * x₀ * c⁻¹) * (gH K[i]!)⁻¹ =
        gH K[i]! * c * x₀ * (gH K[i]! * c)⁻¹ by group] at this

theorem card_centralizer_mul_le_of_classTreeOK [Finite H] {gH : ℕ → H}
    (hgs : ∀ k < gs.size, RepE E gs[k]! (gH k) ∧ gH k * gH k = 1) {x₀ : H}
    (hx : RepE E x x₀) (h : classTreeOK gs x T P K idx = true) :
    Nat.card (Subgroup.centralizer ({x₀} : Set H)) * T.size ≤ Nat.card H := by
  classical
  obtain ⟨-, -, hall⟩ := classTreeOK_parts h
  have hconj := exists_conj_of_classTreeOK hgs hx h
  choose! c hc using hconj
  have hle : T.size ≤ (conjugatesOf x₀).ncard := by
    let f : Fin T.size → H := fun i => c i * x₀ * (c i)⁻¹
    have hf : Function.Injective f := by
      intro i j hij
      have h1 : T[i.val]! = T[j.val]! := by
        refine arr_eq_of_repE (hall i i.2).1 (hall j j.2).1 (hc i i.2) ?_
        rw [show c i * x₀ * (c i)⁻¹ = c j * x₀ * (c j)⁻¹ from hij]
        exact hc j j.2
      apply Fin.ext
      rw [← (hall i i.2).2.1, ← (hall j j.2).2.1, h1]
    have hsub : Set.range f ⊆ conjugatesOf x₀ := by
      rintro _ ⟨i, rfl⟩
      exact isConj_iff.2 ⟨c i, rfl⟩
    calc T.size = Nat.card (Fin T.size) := (Nat.card_fin _).symm
      _ = (Set.range f).ncard := by
          rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hf]
      _ ≤ (conjugatesOf x₀).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hidx := Subgroup.card_mul_index (Subgroup.centralizer ({x₀} : Set H))
  rw [Subgroup.index_centralizer_eq_ncard] at hidx
  calc Nat.card (Subgroup.centralizer ({x₀} : Set H)) * T.size ≤
        Nat.card (Subgroup.centralizer ({x₀} : Set H)) * (conjugatesOf x₀).ncard :=
        Nat.mul_le_mul_left _ hle
    _ = Nat.card H := hidx

end Tree

section Enum

variable {gs : Array (Array ℕ)} {El : Array (Array ℕ)} {P K : Array ℕ} {idx : Array ℕ → ℕ}

theorem enumOK_parts (h : enumOK gs El P K idx = true) :
    0 < El.size ∧ El[0]! = oneR ∧ ∀ i < El.size, validR El[i]! = true ∧ idx El[i]! = i ∧
      (i = 0 ∨ (P[i]! < i ∧ K[i]! < gs.size ∧ El[i]! = mulR gs[K[i]!]! El[P[i]!]!)) ∧
      ∀ k < gs.size, idx (mulR gs[k]! El[i]!) < El.size ∧
        El[idx (mulR gs[k]! El[i]!)]! = mulR gs[k]! El[i]! := by
  simp only [enumOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h0, hx⟩, hall⟩ := h
  refine ⟨h0, hx, fun i hi => ?_⟩
  have := allLt_spec hall hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  refine ⟨this.1.1.1, this.1.1.2, this.1.2.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩,
    fun k hk => ?_⟩
  have h2 := allLt_spec this.2 hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  exact h2

variable {gH : ℕ → H}

@[expose] def genSet (gH : ℕ → H) (n : ℕ) : Set H := gH '' {k | k < n}

theorem exists_of_enumOK (hgs : ∀ k < gs.size, RepE E gs[k]! (gH k))
    (h : enumOK gs El P K idx = true) :
    ∀ i < El.size, ∃ a ∈ Subgroup.closure (genSet gH gs.size), RepE E El[i]! a := by
  obtain ⟨-, h0, hall⟩ := enumOK_parts h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases (hall i hi).2.2.1 with rfl | ⟨hP, hK, hT⟩
    · exact ⟨1, Subgroup.one_mem _, by rw [h0]; exact repE_one⟩
    · obtain ⟨a, ha, hc⟩ := ih _ hP (hP.trans hi)
      refine ⟨gH K[i]! * a, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hK, rfl⟩) ha, ?_⟩
      rw [hT]
      exact repE_mul (hgs _ hK) hc

theorem exists_mem_of_enumOK (hgs : ∀ k < gs.size, RepE E gs[k]! (gH k) ∧ gH k * gH k = 1)
    (h : enumOK gs El P K idx = true) {a : H}
    (ha : a ∈ Subgroup.closure (genSet gH gs.size)) : ∃ i < El.size, RepE E El[i]! a := by
  obtain ⟨h00, h0, hall⟩ := enumOK_parts h
  have step : ∀ x ∈ genSet gH gs.size, ∀ y : H, (∃ i < El.size, RepE E El[i]! y) →
      ∃ i < El.size, RepE E El[i]! (x * y) := by
    rintro _ ⟨k, hk, rfl⟩ y ⟨i, hi, hy⟩
    obtain ⟨hlt, heq⟩ := (hall i hi).2.2.2 k hk
    exact ⟨_, hlt, by rw [heq]; exact repE_mul (hgs k hk).1 hy⟩
  induction ha using Subgroup.closure_induction_left with
  | one => exact ⟨0, h00, by rw [h0]; exact repE_one⟩
  | mul_left x hx y _ hy => exact step x hx y hy
  | inv_mul_cancel x hx y _ hy =>
    obtain ⟨k, hk, rfl⟩ := hx
    rw [show (gH k)⁻¹ = gH k from (eq_inv_of_mul_eq_one_left (hgs k hk).2).symm]
    exact step _ ⟨k, hk, rfl⟩ y hy

theorem card_of_enumOK (hE : Function.Injective E)
    (hgs : ∀ k < gs.size, RepE E gs[k]! (gH k) ∧ gH k * gH k = 1)
    (h : enumOK gs El P K idx = true) :
    Nat.card (Subgroup.closure (genSet gH gs.size)) = El.size := by
  classical
  obtain ⟨-, -, hall⟩ := enumOK_parts h
  have hex := exists_of_enumOK (fun k hk => (hgs k hk).1) h
  choose! a ha hra using hex
  let f : Fin El.size → Subgroup.closure (genSet gH gs.size) := fun i => ⟨a i, ha i i.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hij' : a i = a j := congrArg Subtype.val hij
      have h1 : El[i.val]! = El[j.val]! := by
        refine arr_eq_of_repE (hall i i.2).1 (hall j j.2).1 (hra i i.2) ?_
        rw [hij']
        exact hra j j.2
      apply Fin.ext
      rw [← (hall i i.2).2.1, ← (hall j j.2).2.1, h1]
    · rintro ⟨b, hb⟩
      obtain ⟨i, hi, hrb⟩ := exists_mem_of_enumOK hgs h hb
      exact ⟨⟨i, hi⟩, Subtype.ext (eq_of_repE hE (hra i hi) hrb)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fin]

end Enum

theorem memR_spec {El : Array (Array ℕ)} {idx : Array ℕ → ℕ} {y : Array ℕ}
    (h : memR El idx y = true) : idx y < El.size ∧ El[idx y]! = y := by
  simpa [memR] using h

theorem marks_size (n : ℕ) (idx : Array ℕ → ℕ) (ps : List (Array ℕ)) :
    (marks n idx ps).size = n := by
  have : ∀ (ps : List (Array ℕ)) (m : Array Bool),
      (ps.foldl (fun m p => m.set! (idx p) true) m).size = m.size := by
    intro ps
    induction ps with
    | nil => intro m; rfl
    | cons p ps ih =>
      intro m
      rw [List.foldl_cons, ih]
      exact Array.size_setIfInBounds
  rw [marks, this, Array.size_replicate]

theorem getElem!_set!_true (m : Array Bool) (i j : ℕ) :
    (m.set! i true)[j]! = (if i = j ∧ j < m.size then true else m[j]!) := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < m.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj, Array.getElem_setIfInBounds hj]
    by_cases hij : i = j <;> simp [hij, hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg _ j hj]
    simp [hj]

theorem mem_of_marks {n : ℕ} {idx : Array ℕ → ℕ} {ps : List (Array ℕ)} {j : ℕ} (hj : j < n)
    (h : (marks n idx ps)[j]! = true) : ∃ p ∈ ps, idx p = j := by
  have key : ∀ (ps : List (Array ℕ)) (m : Array Bool), j < m.size →
      (ps.foldl (fun m p => m.set! (idx p) true) m)[j]! = true →
        m[j]! = true ∨ ∃ p ∈ ps, idx p = j := by
    intro ps
    induction ps with
    | nil => intro m _ h; exact Or.inl h
    | cons p ps ih =>
      intro m hm h
      rw [List.foldl_cons] at h
      have hm' : j < (m.set! (idx p) true).size := by
        rw [show m.set! (idx p) true = m.setIfInBounds (idx p) true from rfl,
          Array.size_setIfInBounds]
        exact hm
      rcases ih _ hm' h with h1 | ⟨q, hq, hqj⟩
      · rw [getElem!_set!_true] at h1
        split_ifs at h1 with hpj
        · exact Or.inr ⟨p, List.mem_cons_self, hpj.1⟩
        · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem p hq, hqj⟩
  rcases key ps _ (by rw [Array.size_replicate]; exact hj) h with h1 | h1
  · rw [getElem!_pos _ j (by rw [Array.size_replicate]; exact hj), Array.getElem_replicate] at h1
    exact absurd h1 (by decide)
  · exact h1

theorem exists_of_coverOK {El : Array (Array ℕ)} {idx : Array ℕ → ℕ} {ps : List (Array ℕ)}
    (h : coverOK El idx ps = true) : ∀ j < El.size, ∃ p ∈ ps, El[j]! = p := by
  simp only [coverOK, Bool.and_eq_true, List.all_eq_true] at h
  intro j hj
  obtain ⟨p, hp, hpj⟩ := mem_of_marks hj (allLt_spec h.2 hj)
  refine ⟨p, hp, ?_⟩
  rw [← hpj]
  exact (memR_spec (h.1 p hp)).2

theorem exists_mem_of_mem_subProds {M : Subgroup H} {ys : List (Array ℕ)}
    (hys : ∀ y ∈ ys, ∃ a ∈ M, RepE E y a) : ∀ p ∈ subProds ys, ∃ a ∈ M, RepE E p a := by
  induction ys with
  | nil =>
    intro p hp
    simp only [subProds, List.mem_singleton] at hp
    exact ⟨1, M.one_mem, hp ▸ repE_one⟩
  | cons y ys ih =>
    have ih' := ih fun y' hy' => hys y' (List.mem_cons_of_mem y hy')
    intro p hp
    simp only [subProds, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨p', hp', rfl⟩
    · exact ih' p hp
    · obtain ⟨a, ha, hra⟩ := hys y List.mem_cons_self
      obtain ⟨b, hb, hrb⟩ := ih' p' hp'
      exact ⟨a * b, M.mul_mem ha hb, repE_mul hra hrb⟩

end CFSG.LargeExtraspecial.S63
