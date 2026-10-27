module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinE

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TablePin

open Subgroup

theorem maskOf_testBit {l : List ℕ} {a : ℕ} : (maskOf l).testBit a = true ↔ a ∈ l := by
  unfold maskOf
  rw [foldl_or_testBit l (fun a => a)]
  simp

theorem testBit_conjMask {n : ℕ} {mul : ℕ → ℕ → ℕ} {a x : ℕ} :
    (conjMask n mul a).testBit x = true ↔ ∃ g < n, mul (mul g a) (invIdx n mul g) = x := by
  unfold conjMask
  rw [foldl_or_testBit (List.range n) (fun g => mul (mul g a) (invIdx n mul g))]
  simp [List.mem_range]

theorem mono_nclAux {n : ℕ} {mul : ℕ → ℕ → ℕ} {C : ℕ} :
    ∀ (k S x : ℕ), S.testBit x = true → (nclAux n mul C k S).testBit x = true := by
  intro k
  induction k with
  | zero => intro S x h; exact h
  | succ k ih =>
    intro S x h
    simp only [nclAux]
    split_ifs with h'
    · exact h
    · apply ih
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact Or.inl h

def Good {X : Type*} [Group X] (n : ℕ) (elt : ℕ → X) (E : Subgroup X) (S : ℕ) : Prop :=
  ∀ x, S.testBit x = true → x < n ∧ elt x ∈ E

theorem good_or {X : Type*} [Group X] {n : ℕ} {elt : ℕ → X} {E : Subgroup X} {M N : ℕ}
    (hM : Good n elt E M) (hN : Good n elt E N) : Good n elt E (M ||| N) := by
  intro x hx
  rw [Nat.testBit_or, Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · exact hM x hx
  · exact hN x hx

namespace TableSpec

variable {X : Type*} [Group X] {T : Subgroup X} {t : X} {n : ℕ} {elt : ℕ → X}
  {mul : ℕ → ℕ → ℕ} {tI : ℕ} (hT : TableSpec T t n elt mul tI)
include hT

theorem one_mul' {a : ℕ} (ha : a < n) : mul 0 a = a := by
  obtain ⟨hlt, hel⟩ := hT.mul_spec 0 a hT.pos ha
  apply hT.inj _ _ hlt ha
  rw [← hel, hT.zero, one_mul]

theorem mul_one' {a : ℕ} (ha : a < n) : mul a 0 = a := by
  obtain ⟨hlt, hel⟩ := hT.mul_spec a 0 ha hT.pos
  apply hT.inj _ _ hlt ha
  rw [← hel, hT.zero, mul_one]

theorem exists_inv {g : ℕ} (hg : g < n) : ∃ b < n, mul g b = 0 := by
  obtain ⟨b, hb, hbe⟩ := hT.surj (elt g)⁻¹ (inv_mem (hT.memT g hg))
  refine ⟨b, hb, ?_⟩
  obtain ⟨hlt, hel⟩ := hT.mul_spec g b hg hb
  apply hT.inj _ _ hlt hT.pos
  rw [← hel, hbe, mul_inv_cancel, hT.zero]

theorem invIdx_spec {g : ℕ} (hg : g < n) : invIdx n mul g < n ∧ mul g (invIdx n mul g) = 0 := by
  obtain ⟨b, hb, hgb⟩ := hT.exists_inv hg
  have hsome : ((List.range n).find? fun b => mul g b == 0).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨b, List.mem_range.2 hb, by simpa using hgb⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hsome
  have hc1 := List.find?_some hc
  have hc2 := List.mem_of_find?_eq_some hc
  simp only [invIdx, hc, Option.getD_some]
  exact ⟨List.mem_range.1 hc2, by simpa using hc1⟩

theorem elt_conj {g a : ℕ} (hg : g < n) (ha : a < n) :
    mul (mul g a) (invIdx n mul g) < n ∧
      elt (mul (mul g a) (invIdx n mul g)) = elt g * elt a * (elt g)⁻¹ := by
  obtain ⟨hi, hgi⟩ := hT.invIdx_spec hg
  obtain ⟨h1, e1⟩ := hT.mul_spec g a hg ha
  obtain ⟨h2, e2⟩ := hT.mul_spec (mul g a) (invIdx n mul g) h1 hi
  refine ⟨h2, ?_⟩
  have hinv : elt (invIdx n mul g) = (elt g)⁻¹ := by
    have := (hT.mul_spec g (invIdx n mul g) hg hi).2
    rw [hgi, hT.zero] at this
    exact eq_inv_of_mul_eq_one_right (by rw [← this])
  rw [← e2, ← e1, hinv]

theorem good_prodMask {E : Subgroup X} {M N : ℕ} (hM : Good n elt E M) (hN : Good n elt E N) :
    Good n elt E (prodMask n mul M N) := by
  intro x hx
  obtain ⟨m, c, hm, hc, hmM, hcN, rfl⟩ := testBit_prodMask.1 hx
  obtain ⟨hlt, hel⟩ := hT.mul_spec m c hm hc
  exact ⟨hlt, by rw [← hel]; exact mul_mem (hM m hmM).2 (hN c hcN).2⟩


theorem good_conjMask {E : Subgroup X} (hnorm : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E) {a : ℕ}
    (ha : a < n) (haE : elt a ∈ E) : Good n elt E (conjMask n mul a) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := testBit_conjMask.1 hx
  obtain ⟨hlt, hel⟩ := hT.elt_conj hg ha
  exact ⟨hlt, by rw [hel]; exact hnorm _ (hT.memT g hg) _ haE⟩

theorem good_nclAux {E : Subgroup X} {C : ℕ} (hC : Good n elt E C) :
    ∀ (k S : ℕ), Good n elt E S → Good n elt E (nclAux n mul C k S) := by
  intro k
  induction k with
  | zero => intro S hS; exact hS
  | succ k ih =>
    intro S hS
    simp only [nclAux]
    split_ifs with h
    · exact hS
    · exact ih _ (good_or hS (good_prodMask hT hS hC))

theorem sub_nclAux {C : ℕ} (hCn : ∀ x, C.testBit x = true → x < n) {S : ℕ}
    (hS0 : S.testBit 0 = true) (k : ℕ) :
    ∀ x, C.testBit x = true → (nclAux n mul C (k + 1) S).testBit x = true := by
  intro x hx
  have hx' : (S ||| prodMask n mul S C).testBit x = true := by
    rw [Nat.testBit_or, Bool.or_eq_true]
    exact Or.inr (testBit_prodMask.2 ⟨0, x, hT.pos, hCn x hx, hS0, hx, hT.one_mul' (hCn x hx)⟩)
  simp only [nclAux]
  split_ifs with h
  · rw [beq_iff_eq] at h
    rw [← h]
    exact hx'
  · exact mono_nclAux k _ x hx'

theorem conjMask_self {a : ℕ} (ha : a < n) : (conjMask n mul a).testBit a = true := by
  refine testBit_conjMask.2 ⟨0, hT.pos, ?_⟩
  have h0 : invIdx n mul 0 = 0 := by
    obtain ⟨hi, hgi⟩ := hT.invIdx_spec hT.pos
    have := hT.one_mul' hi
    rw [this] at hgi
    exact hgi
  rw [h0, hT.one_mul' ha, hT.mul_one' ha]

theorem lt_conjMask {a x : ℕ} (hx : (conjMask n mul a).testBit x = true) (ha : a < n) :
    x < n := by
  obtain ⟨g, hg, rfl⟩ := testBit_conjMask.1 hx
  exact (hT.elt_conj hg ha).1

omit [Group X] hT in
theorem mem_nclVals {a : ℕ} (ha : a < n) : nclMask n mul a ∈ nclVals n mul := by
  simp only [nclVals, List.mem_dedup, List.mem_map, List.mem_range]
  exact ⟨a, ha, rfl⟩

theorem good_one {E : Subgroup X} : Good n elt E 1 := by
  intro x hx
  have : x = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.1 hx
  subst this
  exact ⟨hT.pos, by rw [hT.zero]; exact one_mem E⟩

theorem good_nclMask {E : Subgroup X} (hnorm : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E) {a : ℕ}
    (ha : a < n) (haE : elt a ∈ E) : Good n elt E (nclMask n mul a) :=
  good_nclAux hT (good_conjMask hT hnorm ha haE) _ _ (good_one hT)

omit [Group X] hT in
theorem bit_zero_nclMask (a : ℕ) : (nclMask n mul a).testBit 0 = true :=
  mono_nclAux _ _ _ (by decide)

theorem bit_self_nclMask {a : ℕ} (ha : a < n) : (nclMask n mul a).testBit a = true :=
  sub_nclAux hT (fun x hx => hT.lt_conjMask hx ha) (S := 1) (by decide) n a (hT.conjMask_self ha)

theorem exists_lattice_member {E : Subgroup X} (hnorm : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hL1 : 1 ∈ lattice n mul)
    (hLc : ∀ M ∈ lattice n mul, ∀ NC ∈ nclVals n mul, prodMask n mul M NC ∈ lattice n mul) :
    ∃ M ∈ lattice n mul, ∀ a < n, (M.testBit a = true ↔ elt a ∈ E) := by
  have key : ∀ k ≤ n, ∃ M ∈ lattice n mul, M.testBit 0 = true ∧ Good n elt E M ∧
      ∀ a < k, elt a ∈ E → M.testBit a = true := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, hL1, by decide, good_one hT,
        fun a ha => absurd ha (Nat.not_lt_zero a)⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hML, hM0, hMg, hMk⟩ := ih (Nat.le_of_succ_le hk)
      have hkn : k < n := hk
      by_cases hkE : elt k ∈ E
      · refine ⟨prodMask n mul M (nclMask n mul k), hLc M hML _ (mem_nclVals hkn), ?_,
          good_prodMask hT hMg (good_nclMask hT hnorm hkn hkE), ?_⟩
        · exact testBit_prodMask.2 ⟨0, 0, hT.pos, hT.pos, hM0, bit_zero_nclMask k,
            hT.one_mul' hT.pos⟩
        · intro a ha haE
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with hlt | rfl
          · exact testBit_prodMask.2 ⟨a, 0, hlt.trans hkn, hT.pos, hMk a hlt haE,
              bit_zero_nclMask k, hT.mul_one' (hlt.trans hkn)⟩
          · exact testBit_prodMask.2 ⟨0, a, hT.pos, hkn, hM0, bit_self_nclMask hT hkn,
              hT.one_mul' hkn⟩
      · refine ⟨M, hML, hM0, hMg, fun a ha haE => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with hlt | rfl
        · exact hMk a hlt haE
        · exact absurd haE hkE
  obtain ⟨M, hML, -, hMg, hMk⟩ := key n le_rfl
  exact ⟨M, hML, fun a ha => ⟨fun h => (hMg a h).2, hMk a ha⟩⟩

theorem shape_of {E : Subgroup X} (htc : ∀ x ∈ T, x * t = t * x) (hET : E ≤ T) (htE : t ∈ E)
    (hnab : ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ * e₂ ≠ e₂ * e₁)
    (hcomm : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t)
    (hcen : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t)
    (hcent : ∀ s ∈ T, (∀ e ∈ E, s * e = e * s) → s = 1 ∨ s = t) {M : ℕ}
    (hM : ∀ a < n, (M.testBit a = true ↔ elt a ∈ E)) : shape n mul tI M = true := by
  have hmem : ∀ a, a ∈ members n M ↔ a < n ∧ elt a ∈ E := fun a => by
    rw [mem_members]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hM a h1).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hM a h1).2 h2⟩
  have hE : ∀ e ∈ E, ∃ a ∈ members n M, elt a = e := fun e he => by
    obtain ⟨a, ha, rfl⟩ := hT.surj e (hET he)
    exact ⟨a, (hmem a).2 ⟨ha, he⟩, rfl⟩
  have hmulE : ∀ a b, a < n → b < n → elt (mul a b) = elt a * elt b := fun a b ha hb =>
    ((hT.mul_spec a b ha hb).2).symm
  rw [shape_iff]
  refine ⟨(hmem tI).2 ⟨hT.tI_lt, by rw [hT.tI_elt]; exact htE⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hnab
    obtain ⟨a, ha, rfl⟩ := hE e₁ he₁
    obtain ⟨b, hb, rfl⟩ := hE e₂ he₂
    refine ⟨a, ha, b, hb, fun h => hne ?_⟩
    have ha' := ((hmem a).1 ha).1
    have hb' := ((hmem b).1 hb).1
    rw [← hmulE a b ha' hb', ← hmulE b a hb' ha', h]
  · intro a ha b hb
    have ha' := (hmem a).1 ha
    have hb' := (hmem b).1 hb
    have hab := hT.mul_spec a b ha'.1 hb'.1
    have hba := hT.mul_spec b a hb'.1 ha'.1
    have habt := hT.mul_spec (mul b a) tI hba.1 hT.tI_lt
    have hTa := hT.memT a ha'.1
    have hTb := hT.memT b hb'.1
    rcases hcomm _ ha'.2 _ hb'.2 with h | h
    · left
      apply hT.inj _ _ hab.1 hba.1
      rw [← hab.2, ← hba.2]
      calc elt a * elt b = (elt a * elt b * (elt a)⁻¹ * (elt b)⁻¹) * (elt b * elt a) := by group
        _ = elt b * elt a := by rw [h, one_mul]
    · right
      apply hT.inj _ _ hab.1 habt.1
      rw [← hab.2, ← habt.2, ← hba.2, hT.tI_elt]
      calc elt a * elt b = (elt a * elt b * (elt a)⁻¹ * (elt b)⁻¹) * (elt b * elt a) := by group
        _ = t * (elt b * elt a) := by rw [h]
        _ = elt b * elt a * t := (htc _ (mul_mem hTb hTa)).symm
  · intro y hy hall
    have hy' := (hmem y).1 hy
    have h1 := hcen _ hy'.2 (fun f hf => by
      obtain ⟨b, hb, rfl⟩ := hE f hf
      have hb' := ((hmem b).1 hb).1
      have := hall b hb
      rw [(hT.mul_spec b y hb' hy'.1).2, (hT.mul_spec y b hy'.1 hb').2, this])
    rcases h1 with h | h
    · left; exact hT.inj _ _ hy'.1 hT.pos (by rw [h, hT.zero])
    · right; exact hT.inj _ _ hy'.1 hT.tI_lt (by rw [h, hT.tI_elt])
  · intro a ha hall
    have h1 := hcent _ (hT.memT a ha) (fun e he => by
      obtain ⟨b, hb, rfl⟩ := hE e he
      have hb' := ((hmem b).1 hb).1
      have := hall b hb
      rw [(hT.mul_spec a b ha hb').2, (hT.mul_spec b a hb' ha).2, this])
    rcases h1 with h | h
    · left; exact hT.inj _ _ ha hT.pos (by rw [h, hT.zero])
    · right; exact hT.inj _ _ ha hT.tI_lt (by rw [h, hT.tI_elt])


omit [Group X] hT in
theorem lt_of_mem_eList' {a : ℕ} (hpos : 0 < n) (hm : ∀ a b, a < n → b < n → mul a b < n)
    (ha : a ∈ TableE.eList n mul tI) : a < n := by
  simp only [TableE.eList, TableE.sqrtList, List.mem_dedup, List.mem_cons, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at ha
  rcases ha with (rfl | ⟨hr, -⟩) | ⟨x, ⟨hx, -⟩, y, ⟨hy, -⟩, rfl⟩
  · exact hpos
  · exact hr
  · exact hm x y hx hy

theorem lt_of_mem_eList {a : ℕ} (ha : a ∈ TableE.eList n mul tI) : a < n :=
  lt_of_mem_eList' hT.pos (fun a b ha hb => (hT.mul_spec a b ha hb).1) ha

theorem pin {E : Subgroup X} (htc : ∀ x ∈ T, x * t = t * x) (hcheck : pinCheck n mul tI = true)
    (hET : E ≤ T) (htE : t ∈ E) (hnab : ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ * e₂ ≠ e₂ * e₁)
    (hcomm : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t)
    (hcen : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t)
    (hnorm : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hcent : ∀ s ∈ T, (∀ e ∈ E, s * e = e * s) → s = 1 ∨ s = t) :
    ∀ a < n, elt a ∈ E ↔ a ∈ TableE.eList n mul tI := by
  simp only [pinCheck, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hcheck
  obtain ⟨⟨⟨-, hL1⟩, hLc⟩, hLs⟩ := hcheck
  obtain ⟨M, hML, hM⟩ := hT.exists_lattice_member hnorm hL1 fun M hM NC hNC => hLc M hM NC hNC
  have hsh := hT.shape_of htc hET htE hnab hcomm hcen hcent hM
  have hMe : M = maskOf (TableE.eList n mul tI) := by
    rcases hLs M hML with h | h
    · rw [hsh] at h
      exact absurd h (by decide)
    · exact h
  intro a ha
  rw [← hM a ha, hMe, maskOf_testBit]

theorem pin_eq {E : Subgroup X} (htc : ∀ x ∈ T, x * t = t * x)
    (hcheck : pinCheck n mul tI = true) (hET : E ≤ T) (htE : t ∈ E)
    (hnab : ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ * e₂ ≠ e₂ * e₁)
    (hcomm : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t)
    (hcen : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t)
    (hnorm : ∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hcent : ∀ s ∈ T, (∀ e ∈ E, s * e = e * s) → s = 1 ∨ s = t) :
    E = closure (elt '' {a | a ∈ TableE.eList n mul tI}) := by
  have hiff := hT.pin htc hcheck hET htE hnab hcomm hcen hnorm hcent
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hT.surj x (hET hx)
    exact subset_closure ⟨a, (hiff a ha).1 hx, rfl⟩
  · rw [closure_le]
    rintro _ ⟨a, ha, rfl⟩
    exact (hiff a (hT.lt_of_mem_eList ha)).2 ha

theorem eCheck_facts (hcheck : pinCheck n mul tI = true) :
    closure (elt '' {a | a ∈ TableE.eList n mul tI}) = closure {x | x ∈ T ∧ x * x = t} ∧
      20 ≤ Set.ncard {x | x ∈ T ∧ x * x = t} := by
  have hec : TableE.eCheck n mul tI = true := by
    simp only [pinCheck, Bool.and_eq_true] at hcheck
    exact hcheck.1.1.1
  simp only [TableE.eCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, List.contains_iff_mem,
    List.mem_range, List.mem_filter] at hec
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hR20, h0E⟩, htE⟩, hRE⟩, hmulE⟩, hinvE⟩, hRprod⟩, hIprod⟩, ht⟩, hnab⟩,
    hcomm⟩, hcen'⟩, -⟩, hsqrt⟩, hnormT⟩, hcentT⟩ := hec
  have hRlt : ∀ a ∈ TableE.sqrtList n mul tI, a < n ∧ mul a a = tI := by
    intro a ha
    simpa [TableE.sqrtList] using ha
  have hroot : ∀ a ∈ TableE.sqrtList n mul tI, elt a ∈ {x | x ∈ T ∧ x * x = t} := by
    intro a ha
    obtain ⟨hlt, hmm⟩ := hRlt a ha
    refine ⟨hT.memT a hlt, ?_⟩
    rw [(hT.mul_spec a a hlt hlt).2, hmm, hT.tI_elt]
  constructor
  · apply le_antisymm
    · rw [closure_le]
      rintro _ ⟨a, ha, rfl⟩
      have halt := hT.lt_of_mem_eList ha
      rcases hRprod a ha with (h | h) | ⟨x, hx, y, hy, hxy⟩
      · rw [h, hT.zero]; exact one_mem _
      · exact subset_closure (hroot a h)
      · rw [← hxy, ← (hT.mul_spec x y (hRlt x hx).1 (hRlt y hy).1).2]
        exact mul_mem (subset_closure (hroot x hx)) (subset_closure (hroot y hy))
    · rw [closure_le]
      rintro x ⟨hxT, hxx⟩
      obtain ⟨a, ha, rfl⟩ := hT.surj x hxT
      have hmm : mul a a = tI := by
        apply hT.inj _ _ (hT.mul_spec a a ha ha).1 hT.tI_lt
        rw [← (hT.mul_spec a a ha ha).2, hT.tI_elt]
        exact hxx
      exact subset_closure ⟨a, hRE a (by simp [TableE.sqrtList, ha, hmm]), rfl⟩
  · have hfin : {x | x ∈ T ∧ x * x = t}.Finite := by
      have : {x | x ∈ T ∧ x * x = t} ⊆ elt '' {a | a < n} := by
        rintro x ⟨hxT, -⟩
        obtain ⟨a, ha, rfl⟩ := hT.surj x hxT
        exact ⟨a, ha, rfl⟩
      exact ((Set.finite_Iio n).image elt).subset this
    classical
    have hnd : (TableE.sqrtList n mul tI).Nodup := List.nodup_range.filter _
    have hinj : Set.InjOn elt ((TableE.sqrtList n mul tI).toFinset : Set ℕ) := by
      intro a ha b hb h
      exact hT.inj a b (hRlt a (by simpa using ha)).1 (hRlt b (by simpa using hb)).1 h
    have hsub : ((TableE.sqrtList n mul tI).toFinset.image elt : Set X) ⊆
        {x | x ∈ T ∧ x * x = t} := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ : ∃ a ∈ TableE.sqrtList n mul tI, elt a = x := by simpa using hx
      exact hroot a ha
    calc 20 ≤ (TableE.sqrtList n mul tI).length := hR20
      _ = (TableE.sqrtList n mul tI).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = ((TableE.sqrtList n mul tI).toFinset.image elt).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ = (((TableE.sqrtList n mul tI).toFinset.image elt : Finset X) : Set X).ncard :=
        (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub hfin

end TableSpec

end CFSG.EvenSporadicStandard.Fin76b.TablePin
