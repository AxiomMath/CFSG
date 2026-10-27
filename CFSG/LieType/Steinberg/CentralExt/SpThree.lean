module

public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.LiftRelations
public import CFSG.LieType.Steinberg.CentralExt.PosLiftGen
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem CFSG.LieType.Steinberg.CentralExt.SpTorus
open CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpThree

attribute [local instance] TorusLift.centerCommGroup

variable {n : ℕ} {F : Type} [Field F]

theorem two_nsmul_single (i : Fin n) (s : ℤ) :
    (2 • Pi.single i s : Fin n → ℤ) = Pi.single i (2 * s) := by
  rw [two_nsmul, ← Pi.single_add, two_mul]

theorem root_cases {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    (∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ toStd n γ = Pi.single i (2 * s)) ∨
      ∃ (i j : Fin n), i ≠ j ∧ ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
        toStd n γ = Pi.single i s + Pi.single j t := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  rw [← hr]
  cases r with
  | positiveLong i =>
    exact Or.inl ⟨i, 1, Or.inl rfl, by rw [stdVec, two_nsmul_single]⟩
  | negativeLong i =>
    exact Or.inl ⟨i, -1, Or.inr rfl, by rw [stdVec, two_nsmul_single, ← Pi.single_neg]; ring_nf⟩
  | difference i j hij =>
    exact Or.inr ⟨i, j, hij, 1, -1, Or.inl rfl, Or.inr rfl, by
      rw [stdVec, sub_eq_add_neg, ← Pi.single_neg]⟩
  | positiveSum i j hij => exact Or.inr ⟨i, j, hij.ne, 1, 1, Or.inl rfl, Or.inl rfl, rfl⟩
  | negativeSum i j hij =>
    exact Or.inr ⟨i, j, hij.ne, -1, -1, Or.inr rfl, Or.inr rfl, by
      rw [stdVec, neg_add, ← Pi.single_neg, ← Pi.single_neg]⟩

theorem exists_root_short {i j : Fin n} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) :
    ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = Pi.single i s + Pi.single j t := by
  have key : ∃ r : RootSubgroupIndex n, stdVec r = Pi.single i s + Pi.single j t := by
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨.positiveSum i j h, rfl⟩
    · exact ⟨.positiveSum j i h, by rw [stdVec, add_comm]⟩
    · exact ⟨.difference i j hij, by rw [stdVec, sub_eq_add_neg, ← Pi.single_neg]⟩
    · exact ⟨.difference i j hij, by rw [stdVec, sub_eq_add_neg, ← Pi.single_neg]⟩
    · exact ⟨.difference j i hij.symm, by rw [stdVec, sub_eq_add_neg, ← Pi.single_neg, add_comm]⟩
    · exact ⟨.difference j i hij.symm, by rw [stdVec, sub_eq_add_neg, ← Pi.single_neg, add_comm]⟩
    · exact ⟨.negativeSum i j h, by rw [stdVec, neg_add, ← Pi.single_neg, ← Pi.single_neg]⟩
    · exact ⟨.negativeSum j i h, by
        rw [stdVec, neg_add, ← Pi.single_neg, ← Pi.single_neg, add_comm]⟩
  obtain ⟨r, hr⟩ := key
  obtain ⟨γ, hγ, he⟩ := Sp.exists_root_of_stdVec (n := n) r
  exact ⟨γ, hγ, he.trans hr⟩

theorem exists_root_long (i : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = Pi.single i (2 * s) := by
  have key : ∃ r : RootSubgroupIndex n, stdVec r = Pi.single i (2 * s) := by
    rcases hs with rfl | rfl
    · exact ⟨.positiveLong i, by rw [stdVec, two_nsmul_single]⟩
    · exact ⟨.negativeLong i, by rw [stdVec, two_nsmul_single, ← Pi.single_neg]; ring_nf⟩
  obtain ⟨r, hr⟩ := key
  obtain ⟨γ, hγ, he⟩ := Sp.exists_root_of_stdVec (n := n) r
  exact ⟨γ, hγ, he.trans hr⟩

theorem notMem_roots_of_add {v : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (h : 3 ≤ |toStd n v i| + |toStd n v j|) : v ∉ roots (isFiniteType_cartanC n) ∅ := fun hv => by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  have := abs_stdVec_add_le r hij
  rw [hr] at this
  linarith

theorem stdVec_three (r : RootSubgroupIndex n) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : stdVec r a = 0 ∨ stdVec r b = 0 ∨ stdVec r c = 0 := by
  cases r <;> simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.single_apply] <;> split_ifs <;> simp_all

theorem notMem_roots_of_three {v : Fin n → ℤ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : toStd n v a ≠ 0) (hb : toStd n v b ≠ 0) (hc : toStd n v c ≠ 0) :
    v ∉ roots (isFiniteType_cartanC n) ∅ := fun hv => by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  rw [← hr] at ha hb hc
  rcases stdVec_three r hab hac hbc with h | h | h <;> contradiction

theorem single_add_single_apply_left {i j : Fin n} (hij : i ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) i = a := by
  simp [hij]

theorem single_add_single_apply_right {i j : Fin n} (hij : i ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) j = b := by
  simp [hij.symm]

theorem single_add_single_apply_of_ne {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) k = 0 := by
  simp [hki, hkj]

theorem abs_sign {s : ℤ} (hs : s = 1 ∨ s = -1) : |s| = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem toStd_comb_at (p q : ℕ) (α β : Fin n → ℤ) (a : Fin n) :
    toStd n (p • α + q • β) a = p * toStd n α a + q * toStd n β a := by
  rw [toStd_add', toStd_nsmul', toStd_nsmul', Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    nsmul_eq_mul, nsmul_eq_mul]

theorem toStd_add_at (α β : Fin n → ℤ) (a : Fin n) :
    toStd n (α + β) a = toStd n α a + toStd n β a := by
  rw [toStd_add', Pi.add_apply]

theorem ne_zero_of_toStd_at {v : Fin n → ℤ} {a : Fin n} (h : toStd n v a ≠ 0) : v ≠ 0 := by
  rintro rfl
  rw [toStd_zero'] at h
  exact h rfl

theorem list_eq_nil_of (O : CommOrder (Sp.Φ n F)) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) (h1 : α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅) : O.list α β = [] :=
  ChainPairing.list_eq_nil fun p hp => by
    obtain ⟨hpS, hr⟩ :=
      ((O.mem_iff α hα β hβ hαβ p).trans (Sp.mem_expPairs_iff hα hβ hαβ p)).1 hp
    simp only [Sp.expS, Finset.mem_insert, Finset.mem_singleton] at hpS
    rcases hpS with rfl | rfl | rfl
    · exact h1 (by simpa using hr)
    · exact h2 (by simpa using hr)
    · exact h3 (by simpa using hr)

theorem list_eq_single_of (O : CommOrder (Sp.Φ n F)) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) (h1 : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅) : O.list α β = [(1, 1)] :=
  ChainPairing.list_eq_singleton (O.nodup α β) fun p => by
    refine ((O.mem_iff α hα β hβ hαβ p).trans (Sp.mem_expPairs_iff hα hβ hαβ p)).trans
      ⟨fun ⟨hpS, hr⟩ => ?_, fun hp => ?_⟩
    · simp only [Sp.expS, Finset.mem_insert, Finset.mem_singleton] at hpS
      rcases hpS with rfl | rfl | rfl
      · rfl
      · exact absurd (by simpa using hr) h2
      · exact absurd (by simpa using hr) h3
    · subst hp
      exact ⟨by simp [Sp.expS], by simpa using h1⟩

theorem list_eq_pair {α : Type*} {l : List α} (hl : l.Nodup) {a b : α} (hab : a ≠ b)
    (h : ∀ p, p ∈ l ↔ p = a ∨ p = b) : l = [a, b] ∨ l = [b, a] := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · exact absurd ((h a).2 (Or.inl rfl)) List.not_mem_nil
  · have ha := (h a).2 (Or.inl rfl)
    have hb := (h b).2 (Or.inr rfl)
    rw [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · have hx := (h x).1 List.mem_cons_self
    have hy := (h y).1 (List.mem_cons_of_mem _ List.mem_cons_self)
    have hxy : x ≠ y := fun e => (List.nodup_cons.1 hl).1 (e ▸ List.mem_cons_self)
    have hl0 : l = [] := by
      rcases l with _ | ⟨z, l⟩
      · rfl
      · have hz := (h z).1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        have hzx : z ≠ x := fun e => (List.nodup_cons.1 hl).1
          (e ▸ List.mem_cons_of_mem _ List.mem_cons_self)
        have hzy : z ≠ y := fun e => (List.nodup_cons.1 (List.nodup_cons.1 hl).2).1
          (e ▸ List.mem_cons_self)
        exfalso
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
          simp_all
    subst hl0
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hxy

theorem list_eq_pair_of (O : CommOrder (Sp.Φ n F)) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) (h1 : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅) :
    O.list α β = [(1, 1), (2, 1)] ∨ O.list α β = [(2, 1), (1, 1)] :=
  list_eq_pair (O.nodup α β) (by decide) fun p => by
    refine ((O.mem_iff α hα β hβ hαβ p).trans (Sp.mem_expPairs_iff hα hβ hαβ p)).trans
      ⟨fun ⟨hpS, hr⟩ => ?_, fun hp => ?_⟩
    · simp only [Sp.expS, Finset.mem_insert, Finset.mem_singleton] at hpS
      rcases hpS with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (by simpa using hr) h3
    · rcases hp with rfl | rfl
      · exact ⟨by simp [Sp.expS], by simpa using h1⟩
      · exact ⟨by simp [Sp.expS], by simpa using h2⟩

theorem commute_x_of {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (h1 : α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅) (c d : F) :
    Sp.x n F α c * Sp.x n F β d = Sp.x n F β d * Sp.x n F α c := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  exact ChainPairing.commute_of_list_eq_nil (Sp.commutatorFormula O) hα hβ hαβ
    (list_eq_nil_of O hα hβ hαβ h1 h2 h3) c d

theorem comm_x_of {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (h1 : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅) (c d : F) :
    ⁅Sp.x n F α c, Sp.x n F β d⁆ = Sp.x n F (α + β) ((Sp.commC α β (1, 1) : F) * c * d) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  exact ChainPairing.commutatorElement_of_list_eq_single (Sp.commutatorFormula O) hα hβ hαβ
    (list_eq_single_of O hα hβ hαβ h1 h2 h3) c d

theorem comm_x_pair_of {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (h1 : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅)
    (hc : ∀ c d, Sp.x n F (α + β) c * Sp.x n F (2 • α + β) d =
      Sp.x n F (2 • α + β) d * Sp.x n F (α + β) c) (c d : F) :
    ⁅Sp.x n F α c, Sp.x n F β d⁆ = Sp.x n F (α + β) ((Sp.commC α β (1, 1) : F) * c * d) *
      Sp.x n F (2 • α + β) ((Sp.commC α β (2, 1) : F) * c ^ 2 * d) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  have hC := Sp.commutatorFormula O α hα β hβ hαβ c d
  rcases list_eq_pair_of O hα hβ hαβ h1 h2 h3 with h | h <;>
    rw [h] at hC <;> simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, one_smul, pow_one] at hC
  · exact hC
  · rw [hC, hc]

theorem commC_ne_zero {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (h1 : α + β ∈ roots (isFiniteType_cartanC n) ∅) (h2 : (2 : F) ≠ 0) :
    (Sp.commC α β (1, 1) : F) ≠ 0 := by
  have hp : (1, 1) ∈ expPairs (Sp.Φ n F) α β :=
    (Sp.mem_expPairs_iff hα hβ hαβ (1, 1)).2 ⟨by simp [Sp.expS], by simpa using h1⟩
  rcases Sp.commC_natAbs (F := F) hα hβ hp with h | h <;>
    rcases Int.natAbs_eq_iff.1 h with h' | h' <;> rw [h'] <;> push_cast
  · exact one_ne_zero
  · exact neg_ne_zero.2 one_ne_zero
  · exact h2
  · exact neg_ne_zero.2 h2

@[expose] def negAt (p : Fin n) : Fin n → Fˣ := Function.update 1 p (-1)

theorem chi_negAt (v : Fin n → ℤ) (p : Fin n) : chi v (negAt (F := F) p) = (-1 : Fˣ) ^ v p :=
  chi_update v p (-1)

theorem neg_one_units_ne_one [Finite F] (hF : Nat.card F = 3) : (-1 : Fˣ) ≠ 1 := fun h => by
  have h2 := FieldThree.two_ne_zero_of_card_three hF
  have h' : ((-1 : Fˣ) : F) = 1 := by rw [h, Units.val_one]
  rw [Units.val_neg, Units.val_one] at h'
  exact h2 (by linear_combination -h')

theorem chi_negAt_of_odd [Finite F] (hF : Nat.card F = 3) {v : Fin n → ℤ} {p : Fin n}
    (hp : v p = 1 ∨ v p = -1) : chi v (negAt (F := F) p) ≠ 1 := by
  rw [chi_negAt]
  rcases hp with h | h <;> rw [h]
  · rw [zpow_one]
    exact neg_one_units_ne_one hF
  · rw [zpow_neg, zpow_one, inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg] :
      (-1 : Fˣ) * -1 = 1)]
    exact neg_one_units_ne_one hF

theorem chi_negAt_of_even {v : Fin n → ℤ} {p : Fin n} (hp : v p = 0 ∨ v p = 2 ∨ v p = -2) :
    chi v (negAt (F := F) p) = 1 := by
  rw [chi_negAt]
  rcases hp with h | h | h <;> rw [h] <;> norm_num

open _root_.Classical in
@[expose] noncomputable def ofStd (v : Fin n → ℤ) : Fin n → ℤ :=
  if h : ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = v then h.choose else 0

theorem ofStd_spec {v : Fin n → ℤ} (h : ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = v) :
    ofStd v ∈ roots (isFiniteType_cartanC n) ∅ ∧ toStd n (ofStd v) = v := by
  classical
  rw [ofStd, dite_eq_left h]
  exact h.choose_spec

theorem ofStd_toStd {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    ofStd (toStd n γ) = γ :=
  toStd_inj (ofStd_spec ⟨γ, hγ, rfl⟩).2

noncomputable abbrev sR (i j : Fin n) (s t : ℤ) : Fin n → ℤ :=
  ofStd (Pi.single i s + Pi.single j t)

noncomputable abbrev lR (i : Fin n) (s : ℤ) : Fin n → ℤ := ofStd (Pi.single i (2 * s))

theorem sR_mem {i j : Fin n} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    sR i j s t ∈ roots (isFiniteType_cartanC n) ∅ :=
  (ofStd_spec (exists_root_short hij hs ht)).1

theorem toStd_sR {i j : Fin n} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : toStd n (sR i j s t) = Pi.single i s + Pi.single j t :=
  (ofStd_spec (exists_root_short hij hs ht)).2

theorem lR_mem (i : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    lR i s ∈ roots (isFiniteType_cartanC n) ∅ :=
  (ofStd_spec (exists_root_long i hs)).1

theorem toStd_lR (i : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    toStd n (lR i s) = Pi.single i (2 * s) :=
  (ofStd_spec (exists_root_long i hs)).2

theorem sR_comm {i j : Fin n} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : sR j i t s = sR i j s t :=
  toStd_inj (by rw [toStd_sR hij.symm ht hs, toStd_sR hij hs ht, add_comm])

theorem sR_add_sR {i j : Fin n} (hij : i ≠ j) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    sR i j s 1 + sR i j s (-1) = lR i s :=
  toStd_inj (by
    rw [toStd_add', toStd_sR hij hs (Or.inl rfl), toStd_sR hij hs (Or.inr rfl), toStd_lR i hs]
    funext a
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring)

theorem sign_cases {s : ℤ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem neg_sign {s : ℤ} (hs : s = 1 ∨ s = -1) : -s = 1 ∨ -s = -1 := by
  rcases hs with rfl | rfl <;> norm_num

@[expose] noncomputable def j₀ (i : Fin n) : Fin n := by
  classical
  exact if h : ∃ j : Fin n, j ≠ i then h.choose else i

theorem j₀_ne (hn : 2 ≤ n) (i : Fin n) : j₀ i ≠ i := by
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have h : ∃ j : Fin n, j ≠ i := exists_ne i
  rw [j₀, dite_eq_left h]
  exact h.choose_spec

section Lift

variable {E : Type*} [Group E] {π : E →* StatedSp n F} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π)

include hcen hπ in
theorem isRootLift_short [Finite F] (hF : Nat.card F = 3) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) {p : Fin n}
    (hp : toStd n γ p = 1 ∨ toStd n γ p = -1) : SpClosed.IsRootLift π γ (SpClosed.X π γ) :=
  SpClosed.X_isRootLift (SpClosed.exists_isRootLift_of_pairing hcen hπ hγ
    (LiftRel.commPairing_eq_zero_of_card_three hcen hF hπ (SpClosed.x_add hγ))
    (chi_negAt_of_odd hF hp))

include hcen hπ in
theorem commute_lifts {ρ σ : Fin n → ℤ} {Xρ Xσ : F → E} (hρ : SpClosed.IsRootLift π ρ Xρ)
    (hσ : SpClosed.IsRootLift π σ Xσ)
    (hxx : ∀ c d, Sp.x n F ρ c * Sp.x n F σ d = Sp.x n F σ d * Sp.x n F ρ c) {p : Fin n}
    (h1 : chi (toStd n ρ) (negAt (F := F) p) ≠ 1) (h2 : chi (toStd n σ) (negAt (F := F) p) = 1)
    (a b : F) : Xρ a * Xσ b = Xσ b * Xρ a :=
  PosLift.commute_of_rev_sep hcen hρ.1 hρ.2.1 hσ.2.1 hxx
    (e := TorusLift.lift hπ (tor F (negAt p))) (fun h => h1 (Units.val_eq_one.1 h))
    (fun s => hρ.2.2 _ _ (TorusLift.map_lift hπ _) s)
    (fun t => by rw [hσ.2.2 _ _ (TorusLift.map_lift hπ _) t, h2, Units.val_one, one_mul]) a b

include hcen hπ in
theorem commute_lift_elem {ρ ℓ : Fin n → ℤ} {Xρ : F → E}
    (hℓ : ℓ ∈ roots (isFiniteType_cartanC n) ∅) (hρ : SpClosed.IsRootLift π ρ Xρ)
    (hxx : ∀ c d, Sp.x n F ρ c * Sp.x n F ℓ d = Sp.x n F ℓ d * Sp.x n F ρ c) {p : Fin n}
    (h1 : chi (toStd n ρ) (negAt (F := F) p) ≠ 1) (h2 : chi (toStd n ℓ) (negAt (F := F) p) = 1)
    {z : E} {d : F} (hz : π z = Sp.x n F ℓ d) (a : F) : Xρ a * z = z * Xρ a :=
  LiftRel.commute_of_rev_sep_elem hcen hρ.1 hρ.2.1 (z := z) (fun s => by rw [hz]; exact hxx s d)
    (e := TorusLift.lift hπ (tor F (negAt p))) (fun h => h1 (Units.val_eq_one.1 h))
    (fun s => hρ.2.2 _ _ (TorusLift.map_lift hπ _) s)
    (by rw [map_mul, map_mul, map_inv, TorusLift.map_lift, hz, tor_conj_x hℓ, h2, Units.val_one,
      one_mul]) a

include hcen hπ in
theorem comm_lift_of_sep {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (h1 : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h2 : 2 • α + β ∉ roots (isFiniteType_cartanC n) ∅)
    (h3 : α + 2 • β ∉ roots (isFiniteType_cartanC n) ∅) {Xα Xβ Xγ : F → E}
    (hXα : SpClosed.IsRootLift π α Xα) (hXβ : SpClosed.IsRootLift π β Xβ)
    (hXγ : SpClosed.IsRootLift π (α + β) Xγ) (hβγ : ∀ v w, Xβ v * Xγ w = Xγ w * Xβ v)
    {p : Fin n} (hp1 : chi (toStd n α) (negAt (F := F) p) = 1)
    (hp2 : chi (toStd n β) (negAt (F := F) p) ≠ 1) (u v : F) :
    ⁅Xα u, Xβ v⁆ = Xγ ((Sp.commC α β (1, 1) : F) * u * v) := by
  have hγp : chi (toStd n (α + β)) (negAt (F := F) p) = chi (toStd n β) (negAt (F := F) p) := by
    rw [toStd_add', chi_add, hp1, one_mul]
  refine LiftRel.commutatorElement_eq_of_sep hcen hXβ.1 hXγ.1 (fun u v => ?_) hβγ
    (e := TorusLift.lift hπ (tor F (negAt p))) (b := (chi (toStd n β) (negAt (F := F) p) : F))
    (fun h => hp2 (Units.val_eq_one.1 h)) (fun u => ?_) (fun v => hXβ.2.2 _ _
      (TorusLift.map_lift hπ _) v) (fun w => ?_) u v
  · rw [map_commutatorElement, hXα.2.1, hXβ.2.1, hXγ.2.1, comm_x_of hα hβ hαβ h1 h2 h3]
  · rw [hXα.2.2 _ _ (TorusLift.map_lift hπ _) u, hp1, Units.val_one, one_mul]
  · rw [hXγ.2.2 _ _ (TorusLift.map_lift hπ _) w, hγp]

section Long

variable [Finite F] (hF : Nat.card F = 3)

omit [Finite F] in
include hF in
theorem units_sq_eq_one [Finite F] (u : Fˣ) : u ^ 2 = 1 := by
  rcases WeylLift.eq_zero_or_one_or_neg_one hF (u : F) with h | h | h
  · exact absurd h u.ne_zero
  · rw [show u = 1 from Units.ext (by rw [h, Units.val_one]), one_pow]
  · rw [show u = -1 from Units.ext (by rw [h, Units.val_neg, Units.val_one])]
    norm_num

include hF in
theorem chi_lR (i : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1) (t : Fin n → Fˣ) :
    chi (toStd n (lR i s)) t = 1 := by
  rw [toStd_lR i hs, chi, Finset.prod_eq_single i
    (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_mul,
    show ((t i) ^ (2 : ℤ)) = (t i) ^ 2 from zpow_natCast _ 2, units_sq_eq_one hF, one_zpow]

variable (π) in
@[expose] noncomputable def Yf (i j : Fin n) (s : ℤ) (a b : F) : E :=
  ⁅SpClosed.X π (sR i j s 1) a, SpClosed.X π (sR i j s (-1)) b⁆

@[expose] noncomputable def cY (i j : Fin n) (s : ℤ) : F :=
  (Sp.commC (sR i j s 1) (sR i j s (-1)) (1, 1) : F)

variable {i j : Fin n} (hij : i ≠ j) {s : ℤ} (hs : s = 1 ∨ s = -1)
include hij hs

theorem sR_add_ne_zero : sR i j s 1 + sR i j s (-1) ≠ 0 := by
  rw [sR_add_sR hij hs]
  refine ne_zero_of_toStd_at (a := i) ?_
  rw [toStd_lR i hs, Pi.single_eq_same]
  rcases hs with rfl | rfl <;> norm_num

theorem two_sR_add_notMem :
    2 • sR i j s 1 + sR i j s (-1) ∉ roots (isFiniteType_cartanC n) ∅ :=
  SpClosed.notMem_roots_of_three_le (i := i) (by
    rw [show (2 • sR i j s 1 + sR i j s (-1)) = 2 • sR i j s 1 + 1 • sR i j s (-1) by
      rw [one_smul], toStd_comb_at, toStd_sR hij hs (Or.inl rfl), toStd_sR hij hs (Or.inr rfl),
      single_add_single_apply_left hij, single_add_single_apply_left hij]
    rcases hs with rfl | rfl <;> norm_num)

theorem sR_add_two_notMem :
    sR i j s 1 + 2 • sR i j s (-1) ∉ roots (isFiniteType_cartanC n) ∅ :=
  SpClosed.notMem_roots_of_three_le (i := i) (by
    rw [show (sR i j s 1 + 2 • sR i j s (-1)) = 1 • sR i j s 1 + 2 • sR i j s (-1) by
      rw [one_smul], toStd_comb_at, toStd_sR hij hs (Or.inl rfl), toStd_sR hij hs (Or.inr rfl),
      single_add_single_apply_left hij, single_add_single_apply_left hij]
    rcases hs with rfl | rfl <;> norm_num)

omit [Finite F] hF in
theorem comm_x_sR (a b : F) :
    ⁅Sp.x n F (sR i j s 1) a, Sp.x n F (sR i j s (-1)) b⁆ =
      Sp.x n F (lR i s) (cY i j s * a * b) := by
  rw [comm_x_of (sR_mem hij hs (Or.inl rfl)) (sR_mem hij hs (Or.inr rfl)) (sR_add_ne_zero hij hs)
    (by rw [sR_add_sR hij hs]; exact lR_mem i hs) (two_sR_add_notMem hij hs)
    (sR_add_two_notMem hij hs), sR_add_sR hij hs, cY]

omit [Finite F] hF in
theorem cY_ne_zero (h2 : (2 : F) ≠ 0) : cY (F := F) i j s ≠ 0 :=
  commC_ne_zero (sR_mem hij hs (Or.inl rfl)) (sR_mem hij hs (Or.inr rfl)) (sR_add_ne_zero hij hs)
    (by rw [sR_add_sR hij hs]; exact lR_mem i hs) h2

include hcen hπ hF in
theorem isRootLift_sR_one :
    SpClosed.IsRootLift π (sR i j s 1) (SpClosed.X π (sR i j s 1)) :=
  isRootLift_short hcen hπ hF (sR_mem hij hs (Or.inl rfl)) (p := j)
    (Or.inl (by rw [toStd_sR hij hs (Or.inl rfl), single_add_single_apply_right hij]))

include hcen hπ hF in
theorem isRootLift_sR_neg :
    SpClosed.IsRootLift π (sR i j s (-1)) (SpClosed.X π (sR i j s (-1))) :=
  isRootLift_short hcen hπ hF (sR_mem hij hs (Or.inr rfl)) (p := j)
    (Or.inr (by rw [toStd_sR hij hs (Or.inr rfl), single_add_single_apply_right hij]))

include hcen hπ hF in
theorem map_Yf (a b : F) : π (Yf π i j s a b) = Sp.x n F (lR i s) (cY i j s * a * b) := by
  rw [Yf, map_commutatorElement, (isRootLift_sR_one hcen hπ hF hij hs).2.1,
    (isRootLift_sR_neg hcen hπ hF hij hs).2.1, comm_x_sR hij hs]

omit hij hs in
include hcen hπ hF in
theorem commute_short_lift {ρ : Fin n → ℤ} (hρ : ρ ∈ roots (isFiniteType_cartanC n) ∅)
    {p q : Fin n} (hpq : p ≠ q) {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hρe : toStd n ρ = Pi.single p a + Pi.single q b) (i : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hi : (p ≠ i ∧ q ≠ i) ∨ (p = i ∧ a = s) ∨ (q = i ∧ b = s)) {z : E} {d : F}
    (hz : π z = Sp.x n F (lR i s) d) (c : F) :
    SpClosed.X π ρ c * z = z * SpClosed.X π ρ c := by
  have hl := lR_mem i hs
  have hlr := toStd_lR (n := n) i hs
  have ev : ∀ (u v : ℕ) (m : Fin n), toStd n (u • ρ + v • lR i s) m =
      u * (Pi.single p a + Pi.single q b : Fin n → ℤ) m + v * (Pi.single i (2 * s) : Fin n → ℤ) m :=
    fun u v m => by rw [toStd_comb_at, hρe, hlr]
  have e1 : ρ + lR i s = 1 • ρ + 1 • lR i s := by rw [one_smul, one_smul]
  have e2 : 2 • ρ + lR i s = 2 • ρ + 1 • lR i s := by rw [one_smul]
  have e3 : ρ + 2 • lR i s = 1 • ρ + 2 • lR i s := by rw [one_smul]
  have hsa := abs_sign hs
  have hxx : ∀ c d, Sp.x n F ρ c * Sp.x n F (lR i s) d = Sp.x n F (lR i s) d * Sp.x n F ρ c := by
    rcases hi with ⟨hpi, hqi⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have cp : ∀ u v : ℕ, toStd n (u • ρ + v • lR i s) p = u * a := fun u v => by
        rw [ev]; simp [hpq, hpi]
      have cq : ∀ u v : ℕ, toStd n (u • ρ + v • lR i s) q = u * b := fun u v => by
        rw [ev]; simp [hpq.symm, hqi]
      have ci : ∀ u v : ℕ, toStd n (u • ρ + v • lR i s) i = v * (2 * s) := fun u v => by
        rw [ev]; simp [hpi.symm, hqi.symm]
      have nz : ∀ u : ℕ, u ≠ 0 → ∀ w : ℤ, (w = 1 ∨ w = -1) → (u : ℤ) * w ≠ 0 := fun u hu w hw => by
        rcases hw with rfl | rfl <;> simp [hu]
      have hs0 : ∀ v : ℕ, v ≠ 0 → (v : ℤ) * (2 * s) ≠ 0 := fun v hv => by
        rcases hs with rfl | rfl <;> simp [hv]
      refine commute_x_of hρ hl (ne_zero_of_toStd_at (a := p) ?_) ?_ ?_ ?_
      · rw [e1, cp]; exact nz 1 one_ne_zero a ha
      · rw [e1]
        exact notMem_roots_of_three hpq hpi hqi (by rw [cp]; exact nz 1 one_ne_zero a ha)
          (by rw [cq]; exact nz 1 one_ne_zero b hb) (by rw [ci]; exact hs0 1 one_ne_zero)
      · rw [e2]
        exact notMem_roots_of_three hpq hpi hqi (by rw [cp]; exact nz 2 two_ne_zero a ha)
          (by rw [cq]; exact nz 2 two_ne_zero b hb) (by rw [ci]; exact hs0 1 one_ne_zero)
      · rw [e3]
        exact notMem_roots_of_three hpq hpi hqi (by rw [cp]; exact nz 1 one_ne_zero a ha)
          (by rw [cq]; exact nz 1 one_ne_zero b hb) (by rw [ci]; exact hs0 2 two_ne_zero)
    · have cp : ∀ u v : ℕ, toStd n (u • ρ + v • lR p a) p = u * a + v * (2 * a) := fun u v => by
        rw [toStd_comb_at, hρe, toStd_lR p hs]; simp [hpq]
      refine commute_x_of hρ hl (ne_zero_of_toStd_at (a := p) ?_) ?_ ?_ ?_
      · rw [e1, cp]; rcases hs with rfl | rfl <;> norm_num
      · rw [e1]
        exact SpClosed.notMem_roots_of_three_le (i := p) (by
          rw [cp]; rcases hs with rfl | rfl <;> norm_num)
      · rw [e2]
        exact SpClosed.notMem_roots_of_three_le (i := p) (by
          rw [cp]; rcases hs with rfl | rfl <;> norm_num)
      · rw [e3]
        exact SpClosed.notMem_roots_of_three_le (i := p) (by
          rw [cp]; rcases hs with rfl | rfl <;> norm_num)
    · have cq : ∀ u v : ℕ, toStd n (u • ρ + v • lR q b) q = u * b + v * (2 * b) := fun u v => by
        rw [toStd_comb_at, hρe, toStd_lR q hs]; simp [hpq.symm]
      refine commute_x_of hρ hl (ne_zero_of_toStd_at (a := q) ?_) ?_ ?_ ?_
      · rw [e1, cq]; rcases hs with rfl | rfl <;> norm_num
      · rw [e1]
        exact SpClosed.notMem_roots_of_three_le (i := q) (by
          rw [cq]; rcases hs with rfl | rfl <;> norm_num)
      · rw [e2]
        exact SpClosed.notMem_roots_of_three_le (i := q) (by
          rw [cq]; rcases hs with rfl | rfl <;> norm_num)
      · rw [e3]
        exact SpClosed.notMem_roots_of_three_le (i := q) (by
          rw [cq]; rcases hs with rfl | rfl <;> norm_num)
  obtain ⟨r, hr⟩ : ∃ r : Fin n, toStd n ρ r = 1 ∨ toStd n ρ r = -1 := by
    rcases hi with ⟨hpi, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨p, by rw [hρe, single_add_single_apply_left hpq]; exact ha⟩
    · exact ⟨q, by rw [hρe, single_add_single_apply_right hpq]; exact hb⟩
    · exact ⟨p, by rw [hρe, single_add_single_apply_left hpq]; exact ha⟩
  exact commute_lift_elem hcen hπ hl (isRootLift_short hcen hπ hF hρ hr) hxx (p := r)
    (chi_negAt_of_odd hF hr) (chi_lR hF i hs _) hz c

include hcen hπ hF in
theorem commute_sR_lift {t : ℤ} (ht : t = 1 ∨ t = -1) {z : E} {d : F}
    (hz : π z = Sp.x n F (lR i s) d) (c : F) :
    SpClosed.X π (sR i j s t) c * z = z * SpClosed.X π (sR i j s t) c :=
  commute_short_lift hcen hπ hF (sR_mem hij hs ht) hij hs ht (toStd_sR hij hs ht) i hs
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) hz c

include hcen hπ hF in
theorem Yf_add_left (a a' b : F) : Yf π i j s (a + a') b = Yf π i j s a b * Yf π i j s a' b := by
  have key : ∀ a a', Yf π i j s (a + a') b = Yf π i j s a' b * Yf π i j s a b := fun a a' => by
    have hc := commute_sR_lift hcen hπ hF hij hs (Or.inl rfl) (map_Yf hcen hπ hF hij hs a' b) a
    rw [Yf] at hc
    rw [Yf, (isRootLift_sR_one hcen hπ hF hij hs).1, show ∀ x y w : E,
      ⁅x * y, w⁆ = x * ⁅y, w⁆ * x⁻¹ * ⁅x, w⁆ from fun x y w => by
        simp only [commutatorElement_def]; group, hc, mul_inv_cancel_right]
    rfl
  rw [add_comm, key a' a]

include hcen hπ hF in
theorem Yf_add_right (a b b' : F) : Yf π i j s a (b + b') = Yf π i j s a b * Yf π i j s a b' := by
  have hc := commute_sR_lift hcen hπ hF hij hs (Or.inr rfl) (map_Yf hcen hπ hF hij hs a b') b
  rw [Yf] at hc
  rw [Yf, (isRootLift_sR_neg hcen hπ hF hij hs).1, show ∀ v x y : E,
    ⁅v, x * y⁆ = ⁅v, x⁆ * (x * ⁅v, y⁆ * x⁻¹) from fun v x y => by
      simp only [commutatorElement_def]; group, hc, mul_inv_cancel_right]
  rfl

include hcen hπ hF in
theorem Yf_zero_left (b : F) : Yf π i j s 0 b = 1 := by
  have h := Yf_add_left hcen hπ hF hij hs 0 0 b
  rw [add_zero] at h
  exact left_eq_mul.1 h

include hcen hπ hF in
theorem Yf_zero_right (a : F) : Yf π i j s a 0 = 1 := by
  have h := Yf_add_right hcen hπ hF hij hs a 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

include hcen hπ hF in
theorem Yf_neg_left (a b : F) : Yf π i j s (-a) b = (Yf π i j s a b)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Yf_add_left hcen hπ hF hij hs, neg_add_cancel, Yf_zero_left hcen hπ hF hij hs]

include hcen hπ hF in
theorem Yf_neg_right (a b : F) : Yf π i j s a (-b) = (Yf π i j s a b)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Yf_add_right hcen hπ hF hij hs, neg_add_cancel, Yf_zero_right hcen hπ hF hij hs]

include hcen hπ hF in
theorem Yf_mul (a b : F) : Yf π i j s a b = Yf π i j s (a * b) 1 := by
  rcases WeylLift.eq_zero_or_one_or_neg_one hF b with rfl | rfl | rfl
  · rw [Yf_zero_right hcen hπ hF hij hs, mul_zero, Yf_zero_left hcen hπ hF hij hs]
  · rw [mul_one]
  · rw [Yf_neg_right hcen hπ hF hij hs, mul_neg_one, Yf_neg_left hcen hπ hF hij hs]

end Long

section LongLift

variable [Finite F] (hF : Nat.card F = 3)

variable (π) in
@[expose] noncomputable def XL (i : Fin n) (s : ℤ) (c : F) : E :=
  Yf π i (j₀ i) s ((cY i (j₀ i) s)⁻¹ * c) 1

variable (hn : 2 ≤ n) (i : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1)
include hn hs

include hcen hπ hF in
theorem XL_add (c c' : F) : XL π i s (c + c') = XL π i s c * XL π i s c' := by
  rw [XL, XL, XL, mul_add, Yf_add_left hcen hπ hF (j₀_ne hn i).symm hs]

include hcen hπ hF in
theorem Yf_j₀_eq_XL (a b : F) :
    Yf π i (j₀ i) s a b = XL π i s (cY i (j₀ i) s * a * b) := by
  have hc := cY_ne_zero (F := F) (j₀_ne hn i).symm hs (FieldThree.two_ne_zero_of_card_three hF)
  rw [XL, Yf_mul hcen hπ hF (j₀_ne hn i).symm hs, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc,
    one_mul]

include hcen hπ hF in
theorem map_XL (c : F) : π (XL π i s c) = Sp.x n F (lR i s) c := by
  have hc := cY_ne_zero (F := F) (j₀_ne hn i).symm hs (FieldThree.two_ne_zero_of_card_three hF)
  rw [XL, map_Yf hcen hπ hF (j₀_ne hn i).symm hs, mul_one, ← mul_assoc, mul_inv_cancel₀ hc,
    one_mul]

include hcen hπ hF in
theorem isRootLift_XL : SpClosed.IsRootLift π (lR i s) (XL π i s) := by
  have hij := (j₀_ne hn i).symm
  refine ⟨XL_add hcen hπ hF hn i hs, map_XL hcen hπ hF hn i hs, fun t e he c => ?_⟩
  rw [chi_lR hF i hs t, Units.val_one, one_mul]
  have hA := isRootLift_sR_one hcen hπ hF hij hs
  have hB := isRootLift_sR_neg hcen hπ hF hij hs
  have hχ : ((chi (toStd n (sR i (j₀ i) s 1)) t : Fˣ) : F) *
      ((chi (toStd n (sR i (j₀ i) s (-1))) t : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, ← chi_add, ← toStd_add', sR_add_sR hij hs, chi_lR hF i hs t,
      Units.val_one]
  rw [XL, Yf, conjugate_commutatorElement, hA.2.2 t e he, hB.2.2 t e he, mul_one]
  change Yf π i (j₀ i) s _ _ = Yf π i (j₀ i) s _ _
  rw [Yf_mul hcen hπ hF hij hs, show ∀ a b c : F, a * c * b = (a * b) * c from fun a b c => by
    ring, hχ, one_mul]

include hcen hπ hF in
theorem XL_zero : XL π i s 0 = 1 := by
  have h := XL_add hcen hπ hF hn i hs 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

include hcen hπ hF in
theorem XL_neg (c : F) : XL π i s (-c) = (XL π i s c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← XL_add hcen hπ hF hn i hs, neg_add_cancel, XL_zero hcen hπ hF hn i hs]

include hcen hπ hF in
theorem eq_XL_of_map {g : E} {e : F} (hg : ∃ e', g = XL π i s e')
    (he : π g = Sp.x n F (lR i s) e) : g = XL π i s e := by
  obtain ⟨e', rfl⟩ := hg
  rw [map_XL hcen hπ hF hn i hs] at he
  rw [(Sp.isParametrization (lR i s) (lR_mem i hs)).2.2 he]

set_option linter.unusedSimpArgs false in
include hcen hπ hF in
theorem Yf_eq_XL {j : Fin n} (hij : i ≠ j) (a b : F) :
    Yf π i j s a b = XL π i s (cY i j s * a * b) := by
  have hi₀ : i ≠ j₀ i := (j₀_ne hn i).symm
  by_cases hjj : j = j₀ i
  · subst hjj
    exact Yf_j₀_eq_XL hcen hπ hF hn i hs a b
  set j' := j₀ i with hj'
  have hj'i : j' ≠ i := hi₀.symm
  have hji : j ≠ i := hij.symm
  have hj'j : j' ≠ j := Ne.symm hjj
  have hα₀ := sR_mem hi₀ hs (Or.inl rfl)
  have hβ₀ := sR_mem hi₀ hs (Or.inr rfl)
  have hα := sR_mem hij hs (Or.inl rfl)
  have hβ := sR_mem hij hs (Or.inr rfl)
  have hc₁ := sR_mem hjj (Or.inl rfl) (Or.inr rfl)
  have eα₀ := toStd_sR hi₀ hs (Or.inl rfl)
  have eβ₀ := toStd_sR hi₀ hs (Or.inr rfl)
  have eα := toStd_sR hij hs (Or.inl rfl)
  have eβ := toStd_sR hij hs (Or.inr rfl)
  have ec₁ := toStd_sR hjj (Or.inl rfl) (Or.inr rfl)
  have Lα₀ := isRootLift_sR_one hcen hπ hF hi₀ hs
  have Lβ₀ := isRootLift_sR_neg hcen hπ hF hi₀ hs
  have Lα := isRootLift_sR_one hcen hπ hF hij hs
  have Lβ := isRootLift_sR_neg hcen hπ hF hij hs
  have Lc₁ := isRootLift_sR_neg hcen hπ hF hjj (Or.inl rfl)
  set α₀ := sR i j' s 1
  set β₀ := sR i j' s (-1)
  set α := sR i j s 1
  set β := sR i j s (-1)
  set c₁ := sR j j' 1 (-1)
  have hsum1 : α₀ + c₁ = α := toStd_inj (by
    rw [toStd_add', eα₀, ec₁, eα, add_add_add_comm, ← Pi.single_add, add_neg_cancel,
      Pi.single_zero, add_zero])
  have hsum3 : c₁ + β = β₀ := toStd_inj (by
    rw [toStd_add', ec₁, eβ, eβ₀, show (Pi.single j 1 + Pi.single j' (-1) : Fin n → ℤ) +
      (Pi.single i s + Pi.single j (-1)) = (Pi.single j 1 + Pi.single j (-1)) +
        (Pi.single i s + Pi.single j' (-1)) by abel, ← Pi.single_add, add_neg_cancel,
      Pi.single_zero, zero_add])
  have one_two : ∀ x y : Fin n → ℤ, x + y = 1 • x + 1 • y := fun x y => by
    rw [one_smul, one_smul]
  have two_one : ∀ x y : Fin n → ℤ, 2 • x + y = 2 • x + 1 • y := fun x y => by rw [one_smul]
  have one_two' : ∀ x y : Fin n → ℤ, x + 2 • y = 1 • x + 2 • y := fun x y => by rw [one_smul]
  have cα₀ : ∀ m, toStd n α₀ m = (if m = i then s else 0) + (if m = j' then 1 else 0) :=
    fun m => by rw [eα₀]; simp [Pi.single_apply]
  have cβ₀ : ∀ m, toStd n β₀ m = (if m = i then s else 0) + (if m = j' then -1 else 0) :=
    fun m => by rw [eβ₀]; simp [Pi.single_apply]
  have cα : ∀ m, toStd n α m = (if m = i then s else 0) + (if m = j then 1 else 0) :=
    fun m => by rw [eα]; simp [Pi.single_apply]
  have cβ : ∀ m, toStd n β m = (if m = i then s else 0) + (if m = j then -1 else 0) :=
    fun m => by rw [eβ]; simp [Pi.single_apply]
  have cc₁ : ∀ m, toStd n c₁ m = (if m = j then 1 else 0) + (if m = j' then -1 else 0) :=
    fun m => by rw [ec₁]; simp [Pi.single_apply]
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have xc₁α : ∀ c d, Sp.x n F c₁ c * Sp.x n F α d = Sp.x n F α d * Sp.x n F c₁ c := by
    refine commute_x_of hc₁ hα (ne_zero_of_toStd_at (a := i) ?_) ?_ ?_ ?_
    · rw [toStd_add_at, cc₁, cα]
      simpa [hij, hji, hi₀, hj'i, hjj, hj'j] using hs0
    · refine notMem_roots_of_add hjj ?_
      rw [toStd_add_at, toStd_add_at, cc₁, cα, cc₁, cα]
      simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := j) ?_
      rw [two_one, toStd_comb_at, cc₁, cα]
      simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := j) ?_
      rw [one_two', toStd_comb_at, cc₁, cα]
      simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have xββ₀ : ∀ c d, Sp.x n F β c * Sp.x n F β₀ d = Sp.x n F β₀ d * Sp.x n F β c := by
    refine commute_x_of hβ hβ₀ (ne_zero_of_toStd_at (a := i) ?_) ?_ ?_ ?_
    · rw [toStd_add_at, cβ, cβ₀]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine notMem_roots_of_add hij ?_
      rw [toStd_add_at, toStd_add_at, cβ, cβ₀, cβ, cβ₀]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := i) ?_
      rw [two_one, toStd_comb_at, cβ, cβ₀]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := i) ?_
      rw [one_two', toStd_comb_at, cβ, cβ₀]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have xα₀β : ∀ c d, Sp.x n F α₀ c * Sp.x n F β d = Sp.x n F β d * Sp.x n F α₀ c := by
    refine commute_x_of hα₀ hβ (ne_zero_of_toStd_at (a := i) ?_) ?_ ?_ ?_
    · rw [toStd_add_at, cα₀, cβ]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine notMem_roots_of_add hi₀ ?_
      rw [toStd_add_at, toStd_add_at, cα₀, cβ, cα₀, cβ]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := i) ?_
      rw [two_one, toStd_comb_at, cα₀, cβ]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := i) ?_
      rw [one_two', toStd_comb_at, cα₀, cβ]
      rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have xc₁β₀ : ∀ c d, Sp.x n F c₁ c * Sp.x n F β₀ d = Sp.x n F β₀ d * Sp.x n F c₁ c := by
    refine commute_x_of hc₁ hβ₀ (ne_zero_of_toStd_at (a := i) ?_) ?_ ?_ ?_
    · rw [toStd_add_at, cc₁, cβ₀]
      simpa [hij, hji, hi₀, hj'i, hjj, hj'j] using hs0
    · refine notMem_roots_of_add hjj ?_
      rw [toStd_add_at, toStd_add_at, cc₁, cβ₀, cc₁, cβ₀]
      simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := j') ?_
      rw [two_one, toStd_comb_at, cc₁, cβ₀]
      simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · refine SpClosed.notMem_roots_of_three_le (i := j') ?_
      rw [one_two', toStd_comb_at, cc₁, cβ₀]
      simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have Xc₁α : ∀ v w, SpClosed.X π c₁ v * SpClosed.X π α w =
      SpClosed.X π α w * SpClosed.X π c₁ v := by
    refine commute_lifts hcen hπ Lc₁ Lα xc₁α (p := j') (chi_negAt_of_odd hF (Or.inr ?_))
      (chi_negAt_of_even (Or.inl ?_))
    · rw [cc₁]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · rw [cα]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have Xββ₀ : ∀ v w, SpClosed.X π β v * SpClosed.X π β₀ w =
      SpClosed.X π β₀ w * SpClosed.X π β v := by
    refine commute_lifts hcen hπ Lβ Lβ₀ xββ₀ (p := j) (chi_negAt_of_odd hF (Or.inr ?_))
      (chi_negAt_of_even (Or.inl ?_))
    · rw [cβ]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · rw [cβ₀]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have Xα₀β : ∀ v w, SpClosed.X π α₀ v * SpClosed.X π β w =
      SpClosed.X π β w * SpClosed.X π α₀ v := by
    refine commute_lifts hcen hπ Lα₀ Lβ xα₀β (p := j') (chi_negAt_of_odd hF (Or.inl ?_))
      (chi_negAt_of_even (Or.inl ?_))
    · rw [cα₀]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · rw [cβ]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have Xc₁β₀ : ∀ v w, SpClosed.X π c₁ v * SpClosed.X π β₀ w =
      SpClosed.X π β₀ w * SpClosed.X π c₁ v := by
    refine commute_lifts hcen hπ Lc₁ Lβ₀ xc₁β₀ (p := j) (chi_negAt_of_odd hF (Or.inl ?_))
      (chi_negAt_of_even (Or.inl ?_))
    · rw [cc₁]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
    · rw [cβ₀]; simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have hne1 : α₀ + c₁ ≠ 0 := by
    rw [hsum1]
    refine ne_zero_of_toStd_at (a := i) ?_
    rw [cα]
    simpa [hij, hji, hi₀, hj'i, hjj, hj'j] using hs0
  have hne3 : c₁ + β ≠ 0 := by
    rw [hsum3]
    refine ne_zero_of_toStd_at (a := i) ?_
    rw [cβ₀]
    simpa [hij, hji, hi₀, hj'i, hjj, hj'j] using hs0
  have h2a : 2 • α₀ + c₁ ∉ roots (isFiniteType_cartanC n) ∅ := by
    refine notMem_roots_of_add hi₀ ?_
    rw [two_one, toStd_comb_at, toStd_comb_at, cα₀, cc₁, cα₀, cc₁]
    rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have h3a : α₀ + 2 • c₁ ∉ roots (isFiniteType_cartanC n) ∅ := by
    refine notMem_roots_of_add hjj ?_
    rw [one_two', toStd_comb_at, toStd_comb_at, cα₀, cc₁, cα₀, cc₁]
    simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have h2b : 2 • c₁ + β ∉ roots (isFiniteType_cartanC n) ∅ := by
    refine notMem_roots_of_add hjj ?_
    rw [two_one, toStd_comb_at, toStd_comb_at, cc₁, cβ, cc₁, cβ]
    simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have h3b : c₁ + 2 • β ∉ roots (isFiniteType_cartanC n) ∅ := by
    refine notMem_roots_of_add hij ?_
    rw [one_two', toStd_comb_at, toStd_comb_at, cc₁, cβ, cc₁, cβ]
    rcases hs with rfl | rfl <;> simp [hij, hji, hi₀, hj'i, hjj, hj'j]
  have L1 := comm_lift_of_sep hcen hπ hα₀ hc₁ hne1 (by rw [hsum1]; exact hα) h2a h3a Lα₀ Lc₁
    (Xγ := SpClosed.X π α) (by rw [hsum1]; exact Lα) Xc₁α (p := j)
    (chi_negAt_of_even (Or.inl (by rw [cα₀]; simp [hij, hji, hi₀, hj'i, hjj, hj'j])))
    (chi_negAt_of_odd hF (Or.inl (by rw [cc₁]; simp [hij, hji, hi₀, hj'i, hjj, hj'j])))
  have L3 := comm_lift_of_sep hcen hπ hc₁ hβ hne3 (by rw [hsum3]; exact hβ₀) h2b h3b Lc₁ Lβ
    (Xγ := SpClosed.X π β₀) (by rw [hsum3]; exact Lβ₀) Xββ₀ (p := i)
    (chi_negAt_of_even (Or.inl (by rw [cc₁]; simp [hij, hji, hi₀, hj'i, hjj, hj'j])))
    (chi_negAt_of_odd hF (by rw [cβ]; simpa [hij, hji, hi₀, hj'i, hjj, hj'j] using hs))
  have h2F : (2 : F) ≠ 0 := FieldThree.two_ne_zero_of_card_three hF
  set C₁ : F := (Sp.commC α₀ c₁ (1, 1) : F) with hC₁
  set C₃ : F := (Sp.commC c₁ β (1, 1) : F) with hC₃
  have hC₁0 : C₁ ≠ 0 := commC_ne_zero hα₀ hc₁ hne1 (by rw [hsum1]; exact hα) h2F
  set u : F := C₁⁻¹
  have hAB : ⁅SpClosed.X π α₀ u, SpClosed.X π c₁ 1⁆ = SpClosed.X π α 1 := by
    rw [L1, mul_one, mul_inv_cancel₀ hC₁0]
  have hAinv : (SpClosed.X π α₀ u)⁻¹ = SpClosed.X π α₀ (-u) :=
    (TorusLift.x_neg Lα₀.1 u).symm
  have hz : π ⁅(SpClosed.X π α₀ u)⁻¹, SpClosed.X π β₀ (-(C₃ * 1 * 1))⁆ =
      Sp.x n F (lR i s) (cY i j' s * -u * -(C₃ * 1 * 1)) := by
    rw [hAinv]
    exact map_Yf hcen hπ hF hi₀ hs _ _
  have key := LiftRel.commutatorElement_commutatorElement_eq (A := SpClosed.X π α₀ u)
    (B := SpClosed.X π c₁ 1) (D := SpClosed.X π β 1) (W := SpClosed.X π β₀) (c := C₃ * 1 * 1)
    (Xα₀β u 1) (fun w => Xc₁β₀ 1 w) (L3 1 1)
    (by rw [← TorusLift.x_neg Lc₁.1, L3, show C₃ * -1 * 1 = -(C₃ * 1 * 1) by ring])
    (by rw [← Lβ₀.1, neg_add_cancel, TorusLift.x_zero Lβ₀.1])
    (commute_sR_lift hcen hπ hF hi₀ hs (Or.inl rfl) hz u)
    (commute_short_lift hcen hπ hF hc₁ hjj (Or.inl rfl) (Or.inr rfl) ec₁ i hs
      (Or.inl ⟨hji, hj'i⟩) hz 1)
  rw [hAB, hAinv] at key
  have h11 : Yf π i j s 1 1 = XL π i s (cY i j' s * -u * -(C₃ * 1 * 1)) := by
    rw [← Yf_j₀_eq_XL hcen hπ hF hn i hs]
    exact key
  have hex : ∃ e, Yf π i j s a b = XL π i s e := by
    rw [Yf_mul hcen hπ hF hij hs a b]
    rcases WeylLift.eq_zero_or_one_or_neg_one hF (a * b) with h | h | h <;> rw [h]
    · exact ⟨0, by rw [Yf_zero_left hcen hπ hF hij hs, XL_zero hcen hπ hF hn i hs]⟩
    · exact ⟨_, h11⟩
    · exact ⟨_, by rw [Yf_neg_left hcen hπ hF hij hs, h11, ← XL_neg hcen hπ hF hn i hs]⟩
  obtain ⟨e, he⟩ := hex
  rw [he]
  refine eq_XL_of_map hcen hπ hF hn i hs ⟨e, rfl⟩ ?_
  rw [← he, map_Yf hcen hπ hF hij hs]

end LongLift

section Relations

variable [Finite F] (hF : Nat.card F = 3)

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X₂ (γ : Fin n → ℤ) : F → E :=
  if h : ∃ p : Fin n × ℤ, (p.2 = 1 ∨ p.2 = -1) ∧ toStd n γ = Pi.single p.1 (2 * p.2) then
    XL π h.choose.1 h.choose.2
  else SpClosed.X π γ

omit [Finite F] in
theorem single_two_mul_inj {i i' : Fin n} {s s' : ℤ} (hs : s = 1 ∨ s = -1)
    (h : (Pi.single i (2 * s) : Fin n → ℤ) = Pi.single i' (2 * s')) : i = i' ∧ s = s' := by
  have h1 := congrFun h i
  rw [Pi.single_eq_same] at h1
  by_cases hii : i = i'
  · subst hii
    rw [Pi.single_eq_same] at h1
    exact ⟨rfl, by omega⟩
  · rw [Pi.single_eq_of_ne hii] at h1
    rcases hs with rfl | rfl <;> omega

omit [Finite F] in
theorem X₂_long {γ : Fin n → ℤ} {i : Fin n} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (h : toStd n γ = Pi.single i (2 * s)) : X₂ π γ = XL π i s := by
  classical
  have hex : ∃ p : Fin n × ℤ, (p.2 = 1 ∨ p.2 = -1) ∧ toStd n γ = Pi.single p.1 (2 * p.2) :=
    ⟨(i, s), hs, h⟩
  rw [X₂, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := single_two_mul_inj hs (h.symm.trans hex.choose_spec.2)
  rw [← h1, ← h2]

omit [Finite F] in
theorem X₂_short {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (h : toStd n γ = Pi.single i s + Pi.single j t) : X₂ π γ = SpClosed.X π γ := by
  classical
  refine dite_eq_right fun ⟨⟨p, s'⟩, hs', hp⟩ => ?_
  have h1 := congrFun (h.symm.trans hp) i
  rw [single_add_single_apply_left hij, Pi.single_apply] at h1
  split_ifs at h1 <;> rcases hs with rfl | rfl <;> omega

include hcen hπ hF in
theorem isRootLift_X₂ (hn : 2 ≤ n) {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    SpClosed.IsRootLift π γ (X₂ π γ) := by
  rcases root_cases hγ with ⟨i, s, hs, h⟩ | ⟨i, j, hij, s, t, hs, ht, h⟩
  · rw [X₂_long hs h, show γ = lR i s from toStd_inj (h.trans (toStd_lR i hs).symm)]
    exact isRootLift_XL hcen hπ hF hn i hs
  · rw [X₂_short hij hs h]
    exact isRootLift_short hcen hπ hF hγ (p := i)
      (by rw [h, single_add_single_apply_left hij]; exact hs)

include hcen hπ hF in
theorem commute_XL_lift (hn3 : 3 ≤ n) {i k : Fin n} (hik : i ≠ k) {s u : ℤ}
    (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1) {z : E} {d : F}
    (hz : π z = Sp.x n F (lR k u) d) (a : F) : XL π i s a * z = z * XL π i s a := by
  have hn : 2 ≤ n := by omega
  obtain ⟨m, hmi, hmk⟩ := Spin.exists_ne_and_ne hn3 i k
  have hc := cY_ne_zero (F := F) hmi.symm hs (FieldThree.two_ne_zero_of_card_three hF)
  have hXL : XL π i s a = Yf π i m s ((cY i m s)⁻¹ * a) 1 := by
    rw [Yf_eq_XL hcen hπ hF hn i hs hmi.symm, mul_one, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hA := commute_short_lift hcen hπ hF (sR_mem hmi.symm hs (Or.inl rfl)) hmi.symm hs
    (Or.inl rfl) (toStd_sR hmi.symm hs (Or.inl rfl)) k hu (Or.inl ⟨hik, hmk⟩) hz
    ((cY i m s)⁻¹ * a)
  have hB := commute_short_lift hcen hπ hF (sR_mem hmi.symm hs (Or.inr rfl)) hmi.symm hs
    (Or.inr rfl) (toStd_sR hmi.symm hs (Or.inr rfl)) k hu (Or.inl ⟨hik, hmk⟩) hz 1
  have hA' : Commute _ z := hA
  have hB' : Commute _ z := hB
  rw [hXL, Yf, commutatorElement_def]
  exact (((hA'.mul_left hB').mul_left hA'.inv_left).mul_left hB'.inv_left).eq

include hcen hπ hF in
theorem comm_same_support (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (a b : F) :
    ∃ e, ⁅SpClosed.X π (sR i j s t) a, SpClosed.X π (sR i j s (-t)) b⁆ = XL π i s e := by
  rcases ht with rfl | rfl
  · exact ⟨_, Yf_eq_XL hcen hπ hF hn i hs hij a b⟩
  · refine ⟨-(cY i j s * b * a), ?_⟩
    rw [neg_neg, ← commutatorElement_inv, XL_neg hcen hπ hF hn i hs]
    exact congrArg (·⁻¹) (Yf_eq_XL hcen hπ hF hn i hs hij b a)

omit [Finite F] in
include hF in
theorem eq_one_of_add_of_neg [Finite F] {G' : Type*} [Group G'] {d : F → G'}
    (hadd : ∀ a a', d (a + a') = d a * d a') (hneg : ∀ a, d (-a) = d a) (a : F) : d a = 1 := by
  have h0 : d 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have h2 : d a * d a = 1 := by
    calc d a * d a = d (-a) * d a := by rw [hneg]
      _ = 1 := by rw [← hadd, neg_add_cancel, h0]
  have h3 : d a * d a * d a = 1 := by
    rw [← hadd, ← hadd, show a + a + a = 3 * a by ring, WeylLift.three_eq_zero hF, zero_mul, h0]
  calc d a = d a * d a * d a * (d a * d a)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

omit [Finite F] in
theorem neg_one_zpow_sign {t : ℤ} (ht : t = 1 ∨ t = -1) :
    (((-1 : Fˣ) ^ t : Fˣ) : F) = -1 := by
  rcases ht with rfl | rfl
  · simp
  · rw [zpow_neg, zpow_one, inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg] :
      (-1 : Fˣ) * -1 = 1)]
    simp

set_option linter.unusedSimpArgs false in
include hcen hπ hF in
theorem conj_short_long (hn3 : 3 ≤ n) {k l : Fin n} (hkl : k ≠ l) {u t : ℤ}
    (hu : u = 1 ∨ u = -1) (ht : t = 1 ∨ t = -1) (a b : F) :
    SpClosed.X π (sR k l (-u) t) a * XL π k u b * (SpClosed.X π (sR k l (-u) t) a)⁻¹ =
      XL π k u b * SpClosed.X π (sR k l u t)
          ((Sp.commC (sR k l (-u) t) (lR k u) (1, 1) : F) * a * b) *
        XL π l t ((Sp.commC (sR k l (-u) t) (lR k u) (2, 1) : F) * a ^ 2 * b) := by
  have hn : 2 ≤ n := by omega
  have hlk : l ≠ k := hkl.symm
  have hnu := neg_sign hu
  have hγ := sR_mem hkl hnu ht
  have eγ := toStd_sR hkl hnu ht
  have hρ := sR_mem hkl hu ht
  have eρ := toStd_sR hkl hu ht
  have hδ := lR_mem (n := n) k hu
  have eδ := toStd_lR (n := n) k hu
  have hμ := lR_mem (n := n) l ht
  have eμ := toStd_lR (n := n) l ht
  have eγ' : sR k l (-u) t = sR l k t (-u) := (sR_comm hkl hnu ht).symm
  have eρ' : sR k l u t = sR l k t (-(-u)) := by rw [neg_neg]; exact (sR_comm hkl hu ht).symm
  set γ := sR k l (-u) t
  set ρ := sR k l u t
  set δ := lR k u
  set μ := lR l t
  have hsum1 : γ + δ = ρ := toStd_inj (by
    rw [toStd_add', eγ, eδ, eρ, add_right_comm, ← Pi.single_add, show -u + 2 * u = u by ring])
  have hsum2 : 2 • γ + δ = μ := toStd_inj (by
    rw [toStd_add', toStd_nsmul', eγ, eδ, eμ, smul_add, two_nsmul_single, two_nsmul_single,
      add_right_comm, ← Pi.single_add, show 2 * -u + 2 * u = 0 by ring, Pi.single_zero, zero_add])
  have cγ : ∀ m, toStd n γ m = (if m = k then -u else 0) + (if m = l then t else 0) :=
    fun m => by rw [eγ]; simp [Pi.single_apply]
  have cρ : ∀ m, toStd n ρ m = (if m = k then u else 0) + (if m = l then t else 0) :=
    fun m => by rw [eρ]; simp [Pi.single_apply]
  have cδ : ∀ m, toStd n δ m = if m = k then 2 * u else 0 := fun m => by
    rw [eδ]; simp [Pi.single_apply]
  have cμ : ∀ m, toStd n μ m = if m = l then 2 * t else 0 := fun m => by
    rw [eμ]; simp [Pi.single_apply]
  have two_one : ∀ x y : Fin n → ℤ, 2 • x + y = 2 • x + 1 • y := fun x y => by rw [one_smul]
  have one_two' : ∀ x y : Fin n → ℤ, x + 2 • y = 1 • x + 2 • y := fun x y => by rw [one_smul]
  have h3 : γ + 2 • δ ∉ roots (isFiniteType_cartanC n) ∅ := by
    refine SpClosed.notMem_roots_of_three_le (i := k) ?_
    rw [one_two', toStd_comb_at, cγ, cδ]
    rcases hu with rfl | rfl <;> simp [hkl, hlk]
  have hγδ : γ + δ ≠ 0 := by
    rw [hsum1]
    refine ne_zero_of_toStd_at (a := l) ?_
    rw [cρ]
    rcases ht with rfl | rfl <;> simp [hkl, hlk]
  have xρμ : ∀ c d, Sp.x n F ρ c * Sp.x n F μ d = Sp.x n F μ d * Sp.x n F ρ c := by
    refine commute_x_of hρ hμ (ne_zero_of_toStd_at (a := k) ?_) ?_ ?_ ?_
    · rw [toStd_add_at, cρ, cμ]
      rcases hu with rfl | rfl <;> simp [hkl, hlk]
    · refine SpClosed.notMem_roots_of_three_le (i := l) ?_
      rw [toStd_add_at, cρ, cμ]
      rcases ht with rfl | rfl <;> simp [hkl, hlk]
    · refine SpClosed.notMem_roots_of_three_le (i := l) ?_
      rw [two_one, toStd_comb_at, cρ, cμ]
      rcases ht with rfl | rfl <;> simp [hkl, hlk]
    · refine SpClosed.notMem_roots_of_three_le (i := l) ?_
      rw [one_two', toStd_comb_at, cρ, cμ]
      rcases ht with rfl | rfl <;> simp [hkl, hlk]
  set C₁ : F := (Sp.commC γ δ (1, 1) : F)
  set C₂ : F := (Sp.commC γ δ (2, 1) : F)
  have hG : ∀ a b, ⁅Sp.x n F γ a, Sp.x n F δ b⁆ =
      Sp.x n F ρ (C₁ * a * b) * Sp.x n F μ (C₂ * a ^ 2 * b) := fun a b => by
    have h := comm_x_pair_of hγ hδ hγδ (by rw [hsum1]; exact hρ) (by rw [hsum2]; exact hμ) h3
      (by rw [hsum1, hsum2]; exact xρμ) a b
    rwa [hsum1, hsum2] at h
  have Lγ := isRootLift_short hcen hπ hF hγ (p := l) (by rw [cγ]; simpa [hkl, hlk] using ht)
  have Lρ := isRootLift_short hcen hπ hF hρ (p := l) (by rw [cρ]; simpa [hkl, hlk] using ht)
  have Lδ := isRootLift_XL hcen hπ hF hn k hu
  have Lμ := isRootLift_XL hcen hπ hF hn l ht
  have cρδ : ∀ c d, SpClosed.X π ρ c * XL π k u d = XL π k u d * SpClosed.X π ρ c :=
    fun c d => commute_short_lift hcen hπ hF hρ hkl hu ht eρ k hu (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (map_XL hcen hπ hF hn k hu d) c
  have cρμ : ∀ c d, SpClosed.X π ρ c * XL π l t d = XL π l t d * SpClosed.X π ρ c :=
    fun c d => commute_short_lift hcen hπ hF hρ hkl hu ht eρ l ht (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (map_XL hcen hπ hF hn l ht d) c
  have cδμ : ∀ c d, XL π k u c * XL π l t d = XL π l t d * XL π k u c :=
    fun c d => commute_XL_lift hcen hπ hF hn3 hkl hu ht (map_XL hcen hπ hF hn l ht d) c
  have cγμ : ∀ c d, SpClosed.X π γ c * XL π l t d = XL π l t d * SpClosed.X π γ c :=
    fun c d => commute_short_lift hcen hπ hF hγ hkl hnu ht eγ l ht (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (map_XL hcen hπ hF hn l ht d) c
  have R1 : ∀ a c, ∃ e, ⁅SpClosed.X π γ a, SpClosed.X π ρ c⁆ = XL π l t e := fun a c => by
    rw [show γ = sR l k t (-u) from eγ', show ρ = sR l k t (-(-u)) from eρ']
    exact comm_same_support hcen hπ hF hn hlk ht hnu a c
  set H3 : F → F → F → E := fun c₁ c₂ c₃ => XL π k u c₁ * SpClosed.X π ρ c₂ * XL π l t c₃
  have hH3mul : ∀ c₁ c₂ c₃ c₁' c₂' c₃', H3 c₁ c₂ c₃ * H3 c₁' c₂' c₃' =
      H3 (c₁ + c₁') (c₂ + c₂') (c₃ + c₃') := fun c₁ c₂ c₃ c₁' c₂' c₃' => by
    simp only [H3]
    rw [Lδ.1, Lρ.1, Lμ.1]
    calc XL π k u c₁ * SpClosed.X π ρ c₂ * XL π l t c₃ *
          (XL π k u c₁' * SpClosed.X π ρ c₂' * XL π l t c₃') =
        XL π k u c₁ * (SpClosed.X π ρ c₂ * (XL π l t c₃ * XL π k u c₁')) *
          SpClosed.X π ρ c₂' * XL π l t c₃' := by group
      _ = XL π k u c₁ * ((SpClosed.X π ρ c₂ * XL π k u c₁') * XL π l t c₃) *
          SpClosed.X π ρ c₂' * XL π l t c₃' := by rw [← cδμ c₁' c₃]; group
      _ = XL π k u c₁ * XL π k u c₁' * SpClosed.X π ρ c₂ * (XL π l t c₃ * SpClosed.X π ρ c₂') *
          XL π l t c₃' := by rw [cρδ c₂ c₁']; group
      _ = XL π k u c₁ * XL π k u c₁' * (SpClosed.X π ρ c₂ * SpClosed.X π ρ c₂') *
          (XL π l t c₃ * XL π l t c₃') := by rw [← cρμ c₂' c₃]; group
  have hH3zero : H3 0 0 0 = 1 := by
    simp only [H3]
    rw [TorusLift.x_zero Lδ.1, TorusLift.x_zero Lρ.1, TorusLift.x_zero Lμ.1, mul_one, mul_one]
  have hH3inv : ∀ c₁ c₂ c₃, (H3 c₁ c₂ c₃)⁻¹ = H3 (-c₁) (-c₂) (-c₃) := fun c₁ c₂ c₃ =>
    inv_eq_of_mul_eq_one_left (by rw [hH3mul, neg_add_cancel, neg_add_cancel, neg_add_cancel,
      hH3zero])
  have hH3μ : ∀ c, H3 0 0 c = XL π l t c := fun c => by
    simp only [H3]
    rw [TorusLift.x_zero Lδ.1, TorusLift.x_zero Lρ.1, one_mul, one_mul]
  have xδρ : ∀ c d, Sp.x n F ρ c * Sp.x n F δ d = Sp.x n F δ d * Sp.x n F ρ c := fun c d => by
    have h := congrArg π (cρδ c d)
    rwa [map_mul, map_mul, Lρ.2.1, Lδ.2.1] at h
  have xδμ : ∀ c d, Sp.x n F δ c * Sp.x n F μ d = Sp.x n F μ d * Sp.x n F δ c := fun c d => by
    have h := congrArg π (cδμ c d)
    rwa [map_mul, map_mul, Lδ.2.1, Lμ.2.1] at h
  set W : F → E := fun a => SpClosed.X π γ a * XL π k u b * (SpClosed.X π γ a)⁻¹
  set h : F → E := fun a => H3 b (C₁ * a * b) (C₂ * a ^ 2 * b)
  set d : F → E := fun a => W a * (h a)⁻¹
  have hπW : ∀ a, π (W a) = π (h a) := fun a => by
    simp only [W, h, H3, map_mul, map_inv, Lγ.2.1, Lδ.2.1, Lρ.2.1, Lμ.2.1]
    have e : Sp.x n F γ a * Sp.x n F δ b * (Sp.x n F γ a)⁻¹ =
        ⁅Sp.x n F γ a, Sp.x n F δ b⁆ * Sp.x n F δ b := by
      simp only [commutatorElement_def]; group
    rw [e, hG, mul_assoc, ← xδμ, ← mul_assoc, ← xδρ, mul_assoc]
  have hdk : ∀ a, π (d a) = 1 := fun a => by
    simp only [d]
    rw [map_mul, map_inv, hπW, mul_inv_cancel]
  have hdc : ∀ a, d a ∈ Subgroup.center E := fun a => hcen (MonoidHom.mem_ker.2 (hdk a))
  have hdz : ∀ a g, g * d a = d a * g := fun a g => Subgroup.mem_center_iff.1 (hdc a) g
  have hWd : ∀ a, W a = d a * h a := fun a => by simp only [d, inv_mul_cancel_right]
  have hadd : ∀ a a', d (a + a') = d a * d a' := fun a a' => by
    obtain ⟨e, he⟩ := R1 a (C₁ * a' * b)
    have e1 : W (a + a') = SpClosed.X π γ a * W a' * (SpClosed.X π γ a)⁻¹ := by
      simp only [W, Lγ.1]
      group
    have e2 : SpClosed.X π γ a * h a' * (SpClosed.X π γ a)⁻¹ =
        W a * H3 0 (C₁ * a' * b) (e + C₂ * a' ^ 2 * b) := by
      have e3 : SpClosed.X π γ a * SpClosed.X π ρ (C₁ * a' * b) * (SpClosed.X π γ a)⁻¹ =
          XL π l t e * SpClosed.X π ρ (C₁ * a' * b) := by
        rw [← he]; simp only [commutatorElement_def]; group
      have e4 : SpClosed.X π γ a * XL π l t (C₂ * a' ^ 2 * b) * (SpClosed.X π γ a)⁻¹ =
          XL π l t (C₂ * a' ^ 2 * b) := by rw [cγμ, mul_inv_cancel_right]
      calc SpClosed.X π γ a * h a' * (SpClosed.X π γ a)⁻¹ =
          W a * (SpClosed.X π γ a * SpClosed.X π ρ (C₁ * a' * b) * (SpClosed.X π γ a)⁻¹) *
            (SpClosed.X π γ a * XL π l t (C₂ * a' ^ 2 * b) * (SpClosed.X π γ a)⁻¹) := by
              simp only [W, h, H3]; group
        _ = W a * (XL π l t e * SpClosed.X π ρ (C₁ * a' * b)) * XL π l t (C₂ * a' ^ 2 * b) := by
              rw [e3, e4]
        _ = W a * H3 0 (C₁ * a' * b) (e + C₂ * a' ^ 2 * b) := by
              simp only [H3]
              rw [TorusLift.x_zero Lδ.1, one_mul, Lμ.1, ← cρμ]
              group
    have e5 : W (a + a') = d a' * d a *
        H3 b (C₁ * (a + a') * b) (C₂ * a ^ 2 * b + (e + C₂ * a' ^ 2 * b)) := by
      have e8 : SpClosed.X π γ a * (d a' * h a') * (SpClosed.X π γ a)⁻¹ =
          d a' * (SpClosed.X π γ a * h a' * (SpClosed.X π γ a)⁻¹) := by
        rw [← mul_assoc, hdz a' (SpClosed.X π γ a)]
        group
      rw [e1, hWd a', e8, e2, hWd a, show (d a * h a) * H3 0 (C₁ * a' * b)
          (e + C₂ * a' ^ 2 * b) = d a * (h a * H3 0 (C₁ * a' * b) (e + C₂ * a' ^ 2 * b)) by group]
      simp only [h]
      rw [hH3mul, add_zero, show C₁ * a * b + C₁ * a' * b = C₁ * (a + a') * b by ring]
      group
    have e6 : d (a + a') = d a' * d a *
        XL π l t (C₂ * a ^ 2 * b + (e + C₂ * a' ^ 2 * b) - C₂ * (a + a') ^ 2 * b) := by
      simp only [d]
      rw [e5]
      simp only [h]
      rw [hH3inv, mul_assoc (d a' * d a), hH3mul, add_neg_cancel, add_neg_cancel, ← sub_eq_add_neg,
        hH3μ]
    set f := C₂ * a ^ 2 * b + (e + C₂ * a' ^ 2 * b) - C₂ * (a + a') ^ 2 * b
    have e7 : XL π l t f = 1 := by
      have h1 : π (d (a + a')) = π (d a' * d a * XL π l t f) := congrArg π e6
      rw [hdk (a + a'), map_mul, map_mul, hdk a', hdk a, one_mul, one_mul, Lμ.2.1] at h1
      have hf : f = 0 := (Sp.isParametrization μ hμ).2.2
        (h1.symm.trans (TorusLift.x_zero (SpClosed.x_add (F := F) hμ)).symm)
      rw [hf]
      exact TorusLift.x_zero Lμ.1
    rw [e6, e7, mul_one, hdz a (d a')]
  have hneg : ∀ a, d (-a) = d a := fun a => by
    set e := TorusLift.lift hπ (tor F (negAt (F := F) l))
    have he : π e = tor F (negAt l) := TorusLift.map_lift hπ _
    have hcγ : ((chi (toStd n γ) (negAt (F := F) l) : Fˣ) : F) = -1 := by
      rw [chi_negAt, cγ]
      simpa [hkl, hlk] using neg_one_zpow_sign (F := F) ht
    have hcρ : ((chi (toStd n ρ) (negAt (F := F) l) : Fˣ) : F) = -1 := by
      rw [chi_negAt, cρ]
      simpa [hkl, hlk] using neg_one_zpow_sign (F := F) ht
    have e1 : e * d a * e⁻¹ = d (-a) := by
      have : e * d a * e⁻¹ = (e * SpClosed.X π γ a * e⁻¹) * (e * XL π k u b * e⁻¹) *
          (e * SpClosed.X π γ a * e⁻¹)⁻¹ * ((e * XL π k u b * e⁻¹) *
            (e * SpClosed.X π ρ (C₁ * a * b) * e⁻¹) * (e * XL π l t (C₂ * a ^ 2 * b) * e⁻¹))⁻¹ := by
        simp only [d, W, h, H3]
        group
      rw [this, Lγ.2.2 _ e he, Lδ.2.2 _ e he, Lρ.2.2 _ e he, Lμ.2.2 _ e he, hcγ, hcρ,
        chi_lR hF k hu, chi_lR hF l ht, Units.val_one, one_mul, one_mul, neg_one_mul, neg_one_mul]
      simp only [d, W, h, H3]
      rw [show C₁ * -a * b = -(C₁ * a * b) by ring, show C₂ * (-a) ^ 2 * b = C₂ * a ^ 2 * b by ring]
    rw [← e1, hdz a e, mul_inv_cancel_right]
  have hd1 := eq_one_of_add_of_neg hF hadd hneg a
  have hfin : W a = h a := by rw [hWd a, hd1, one_mul]
  exact hfin

omit [Finite F] in
theorem mem_iSup_X₂ {γ δ ε : Fin n → ℤ} (hε : ε ∈ roots (isFiniteType_cartanC n) ∅)
    (h : ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ) (c : F) :
    X₂ π ε c ∈ ⨆ (ε' : Fin n → ℤ) (_ : ε' ∈ roots (isFiniteType_cartanC n) ∅ ∧
      (ε' = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε' = p.1 • γ + p.2 • δ)), chevRoot (X₂ π) ε' :=
  Subgroup.mem_iSup_of_mem ε (Subgroup.mem_iSup_of_mem ⟨hε, h⟩
    (CFSG.LieType.Steinberg.xh_mem_chevRoot ε c))

omit [Finite F] in
theorem toStd_ne_of_linIndepPair {γ δ : Fin n → ℤ} (hli : LinIndepPair γ δ) :
    toStd n δ ≠ toStd n γ ∧ toStd n δ ≠ -toStd n γ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hδ := toStd_inj h
    subst hδ
    exact absurd (hli 1 (-1) (by simp)).2 (by norm_num)
  · rw [← toStd_neg'] at h
    have hδ := toStd_inj h
    subst hδ
    exact absurd (hli 1 1 (by simp)).2 (by norm_num)

set_option linter.unusedSimpArgs false in
include hcen hπ hF in
theorem mem_of_conj_short_long (hn3 : 3 ≤ n) {k l : Fin n} (hkl : k ≠ l) {u t : ℤ}
    (hu : u = 1 ∨ u = -1) (ht : t = 1 ∨ t = -1) (a b : F) :
    X₂ π (sR k l (-u) t) a * X₂ π (lR k u) b * (X₂ π (sR k l (-u) t) a)⁻¹ ∈
      ⨆ (ε : Fin n → ℤ) (_ : ε ∈ roots (isFiniteType_cartanC n) ∅ ∧ (ε = lR k u ∨
        ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • sR k l (-u) t + p.2 • lR k u)),
          chevRoot (X₂ π) ε := by
  have hnu := neg_sign hu
  have eγ := toStd_sR hkl hnu ht
  have eρ := toStd_sR hkl hu ht
  have eδ := toStd_lR (n := n) k hu
  have eμ := toStd_lR (n := n) l ht
  have hsum1 : sR k l (-u) t + lR k u = sR k l u t := toStd_inj (by
    rw [toStd_add', eγ, eδ, eρ, add_right_comm, ← Pi.single_add, show -u + 2 * u = u by ring])
  have hsum2 : 2 • sR k l (-u) t + lR k u = lR l t := toStd_inj (by
    rw [toStd_add', toStd_nsmul', eγ, eδ, eμ, smul_add, two_nsmul_single, two_nsmul_single,
      add_right_comm, ← Pi.single_add, show 2 * -u + 2 * u = 0 by ring, Pi.single_zero, zero_add])
  rw [X₂_short hkl hnu eγ, X₂_long hu eδ, conj_short_long hcen hπ hF hn3 hkl hu ht a b]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · rw [← X₂_long hu eδ]
    exact mem_iSup_X₂ (lR_mem k hu) (Or.inl rfl) b
  · rw [← X₂_short hkl hu eρ]
    exact mem_iSup_X₂ (sR_mem hkl hu ht) (Or.inr ⟨(1, 1), one_pos, one_pos, by
      rw [one_smul, one_smul, hsum1]⟩) _
  · rw [← X₂_long ht eμ]
    exact mem_iSup_X₂ (lR_mem l ht) (Or.inr ⟨(2, 1), two_pos, one_pos, by
      rw [one_smul, hsum2]⟩) _

set_option linter.unusedSimpArgs false in
include hcen hπ hF in
theorem mem_of_same_support (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (a b : F) :
    X₂ π (sR i j s t) a * X₂ π (sR i j s (-t)) b * (X₂ π (sR i j s t) a)⁻¹ ∈
      ⨆ (ε : Fin n → ℤ) (_ : ε ∈ roots (isFiniteType_cartanC n) ∅ ∧ (ε = sR i j s (-t) ∨
        ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • sR i j s t + p.2 • sR i j s (-t))),
          chevRoot (X₂ π) ε := by
  have hnt := neg_sign ht
  have eγ := toStd_sR hij hs ht
  have eδ := toStd_sR hij hs hnt
  have hsum : sR i j s t + sR i j s (-t) = lR i s := toStd_inj (by
    rw [toStd_add', eγ, eδ, toStd_lR i hs, add_add_add_comm, ← Pi.single_add, ← Pi.single_add,
      add_neg_cancel, Pi.single_zero, add_zero, two_mul])
  obtain ⟨e, he⟩ := comm_same_support hcen hπ hF hn hij hs ht a b
  rw [X₂_short hij hs eγ, X₂_short hij hs eδ, show ∀ x y : E, x * y * x⁻¹ = ⁅x, y⁆ * y from
    fun x y => by simp only [commutatorElement_def]; group, he]
  refine Subgroup.mul_mem _ ?_ ?_
  · rw [← X₂_long hs (toStd_lR i hs)]
    exact mem_iSup_X₂ (lR_mem i hs) (Or.inr ⟨(1, 1), one_pos, one_pos, by
      rw [one_smul, one_smul, hsum]⟩) _
  · rw [← X₂_short hij hs eδ]
    exact mem_iSup_X₂ (sR_mem hij hs hnt) (Or.inl rfl) _

set_option linter.unusedSimpArgs false in
include hcen hπ hF in
theorem sep_or_conj (hn3 : 3 ≤ n) {γ δ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅)
    (hδ : δ ∈ roots (isFiniteType_cartanC n) ∅) (hli : LinIndepPair γ δ) :
    (∃ t : Fin n → Fˣ, ((chi (toStd n γ) t : Fˣ) : F) = 1 ∧ ((chi (toStd n δ) t : Fˣ) : F) ≠ 1) ∨
      ∀ a b, X₂ π γ a * X₂ π δ b * (X₂ π γ a)⁻¹ ∈ ⨆ (ε : Fin n → ℤ)
        (_ : ε ∈ roots (isFiniteType_cartanC n) ∅ ∧
          (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)),
            chevRoot (X₂ π) ε := by
  have hn : 2 ≤ n := by omega
  obtain ⟨hne, hne'⟩ := toStd_ne_of_linIndepPair hli
  have sep : ∀ p : Fin n, (toStd n γ p = 0 ∨ toStd n γ p = 2 ∨ toStd n γ p = -2) →
      (toStd n δ p = 1 ∨ toStd n δ p = -1) →
      ∃ t : Fin n → Fˣ, ((chi (toStd n γ) t : Fˣ) : F) = 1 ∧ ((chi (toStd n δ) t : Fˣ) : F) ≠ 1 :=
    fun p h1 h2 => ⟨negAt p, by rw [chi_negAt_of_even h1, Units.val_one],
      fun h => chi_negAt_of_odd hF h2 (Units.val_eq_one.1 h)⟩
  rcases root_cases hδ with ⟨k, u, hu, eδ⟩ | ⟨k, l, hkl, u, v, hu, hv, eδ⟩
  ·
    have hδl : δ = lR k u := toStd_inj (eδ.trans (toStd_lR k hu).symm)
    have hzδ : ∀ b, π (X₂ π δ b) = Sp.x n F (lR k u) b := fun b => by
      rw [X₂_long hu eδ, map_XL hcen hπ hF hn k hu]
    right
    intro a b
    have hcomm : X₂ π γ a * X₂ π δ b = X₂ π δ b * X₂ π γ a →
        X₂ π γ a * X₂ π δ b * (X₂ π γ a)⁻¹ ∈ ⨆ (ε : Fin n → ℤ)
          (_ : ε ∈ roots (isFiniteType_cartanC n) ∅ ∧
            (ε = δ ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • γ + p.2 • δ)),
              chevRoot (X₂ π) ε := fun h => by
      rw [h, mul_inv_cancel_right]
      exact mem_iSup_X₂ hδ (Or.inl rfl) b
    rcases root_cases hγ with ⟨i, s, hs, eγ⟩ | ⟨i, j, hij, s, t, hs, ht, eγ⟩
    ·
      have hik : i ≠ k := fun hik => by
        subst hik
        rcases hs with rfl | rfl <;> rcases hu with rfl | rfl
        · exact hne (eδ.trans eγ.symm)
        · exact hne' (by rw [eδ, eγ, ← Pi.single_neg]; norm_num)
        · exact hne' (by rw [eδ, eγ, ← Pi.single_neg]; norm_num)
        · exact hne (eδ.trans eγ.symm)
      exact hcomm (by rw [X₂_long hs eγ]; exact commute_XL_lift hcen hπ hF hn3 hik hs hu (hzδ b) a)
    ·
      have hc : ((i ≠ k ∧ j ≠ k) ∨ (i = k ∧ s = u) ∨ (j = k ∧ t = u)) →
          X₂ π γ a * X₂ π δ b = X₂ π δ b * X₂ π γ a := fun h => by
        rw [X₂_short hij hs eγ]
        exact commute_short_lift hcen hπ hF hγ hij hs ht eγ k hu h (hzδ b) a
      by_cases hk : i ≠ k ∧ j ≠ k
      · exact hcomm (hc (Or.inl hk))
      by_cases hik : i = k
      · subst hik
        by_cases hsu : s = u
        · exact hcomm (hc (Or.inr (Or.inl ⟨rfl, hsu⟩)))
        have hs' : s = -u := by
          rcases hs with h1 | h1 <;> rcases hu with h2 | h2 <;> omega
        have hγ' : γ = sR i j (-u) t :=
          toStd_inj (by rw [eγ, toStd_sR hij (neg_sign hu) ht, hs'])
        subst hγ' hδl
        exact mem_of_conj_short_long hcen hπ hF hn3 hij hu ht a b
      · have hjk : j = k := by
          by_contra h
          exact hk ⟨hik, h⟩
        subst hjk
        by_cases htu : t = u
        · exact hcomm (hc (Or.inr (Or.inr ⟨rfl, htu⟩)))
        have ht' : t = -u := by
          rcases ht with h1 | h1 <;> rcases hu with h2 | h2 <;> omega
        have hγ' : γ = sR j i (-u) s :=
          toStd_inj (by rw [eγ, toStd_sR hij.symm (neg_sign hu) hs, ht', add_comm])
        subst hγ' hδl
        exact mem_of_conj_short_long hcen hπ hF hn3 hij.symm hu hs a b
  ·
    rcases root_cases hγ with ⟨i, s, hs, eγ⟩ | ⟨i, j, hij, s, t, hs, ht, eγ⟩
    ·
      refine Or.inl (sep k ?_ (by rw [eδ, single_add_single_apply_left hkl]; exact hu))
      rw [eγ, Pi.single_apply]
      split_ifs <;> rcases hs with rfl | rfl <;> simp
    · by_cases hk : k ≠ i ∧ k ≠ j
      · refine Or.inl (sep k (Or.inl ?_) (by rw [eδ, single_add_single_apply_left hkl]; exact hu))
        rw [eγ, single_add_single_apply_of_ne hk.1 hk.2]
      by_cases hl : l ≠ i ∧ l ≠ j
      · refine Or.inl (sep l (Or.inl ?_) (by rw [eδ, single_add_single_apply_right hkl]; exact hv))
        rw [eγ, single_add_single_apply_of_ne hl.1 hl.2]
      right
      obtain ⟨u', v', hu', hv', eδ'⟩ : ∃ u' v' : ℤ, (u' = 1 ∨ u' = -1) ∧ (v' = 1 ∨ v' = -1) ∧
          toStd n δ = Pi.single i u' + Pi.single j v' := by
        have hk' : k = i ∨ k = j := by
          by_contra h
          exact hk ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
        have hl' : l = i ∨ l = j := by
          by_contra h
          exact hl ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
        rcases hk' with hki | hkj <;> rcases hl' with hli' | hlj
        · exact absurd (hki.trans hli'.symm) hkl
        · rw [hki, hlj] at eδ
          exact ⟨u, v, hu, hv, eδ⟩
        · rw [hkj, hli'] at eδ
          exact ⟨v, u, hv, hu, by rw [eδ, add_comm]⟩
        · exact absurd (hkj.trans hlj.symm) hkl
      have hcase : (u' = s ∧ v' = -t) ∨ (u' = -s ∧ v' = t) := by
        by_cases hus : u' = s <;> by_cases hvt : v' = t
        · exact absurd (by rw [eδ', eγ, hus, hvt]) hne
        · exact Or.inl ⟨hus, by rcases hv' with h1 | h1 <;> rcases ht with h2 | h2 <;> omega⟩
        · exact Or.inr ⟨by rcases hu' with h1 | h1 <;> rcases hs with h2 | h2 <;> omega, hvt⟩
        · have h1 : u' = -s := by rcases hu' with h1 | h1 <;> rcases hs with h2 | h2 <;> omega
          have h2 : v' = -t := by rcases hv' with h1 | h1 <;> rcases ht with h2 | h2 <;> omega
          exact absurd (by rw [eδ', eγ, h1, h2, neg_add, ← Pi.single_neg, ← Pi.single_neg]) hne'
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hγ' : γ = sR i j s t := toStd_inj (by rw [eγ, toStd_sR hij hs ht])
        have hδ' : δ = sR i j s (-t) :=
          toStd_inj (by rw [eδ', toStd_sR hij hs (neg_sign ht), h1, h2])
        subst hγ' hδ'
        exact mem_of_same_support hcen hπ hF hn hij hs ht
      · have hγ' : γ = sR j i t s :=
          toStd_inj (by rw [eγ, toStd_sR hij.symm ht hs, add_comm])
        have hδ' : δ = sR j i t (-s) :=
          toStd_inj (by rw [eδ', toStd_sR hij.symm ht (neg_sign hs), add_comm, h1, h2])
        subst hγ' hδ'
        exact mem_of_same_support hcen hπ hF hn hij.symm ht hs

end Relations


end Lift

theorem sp_three_exists_section_of_central [Finite F] (hF : Nat.card F = 3) (hn3 : 3 ≤ n)
    {E : Type*} [Group E] {π : E →* StatedSp n F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : StatedSp n F →* E, ∀ g, π (σ g) = g := by
  have hn : 2 ≤ n := by omega
  have hspec := fun γ (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) =>
    isRootLift_X₂ hcen hπ hF hn hγ
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  exact HalfSpaceLift.exists_section_of_lift' hcen rfl
    (Sp.chevalleyExtras hn O Sp.commC (Sp.commutatorFormula O)) (Sp.presentationB hn)
    (X := X₂ π) (tor := fun t : Fin n → Fˣ => TorusLift.lift hπ (tor F t))
    (χ := fun t γ => (chi (toStd n γ) t : F)) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun t γ hγ c => (hspec γ hγ).2.2 t _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => sep_or_conj hcen hπ hF hn3 hγ hδ hli

open CFSG.LocalAnalysis.ComponentInitial in
theorem psp_three_hopfMultiplier {K : Type} [Field K] [Finite K] {n : ℕ} (hn3 : 3 ≤ n)
    (hK : Nat.card K = 3) :
    commutator (StatedProj (StatedSp n K)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp n K)) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  set Z := SymplecticHigher.spScalars n K
  set q : StatedSp n K →* StatedProj (StatedSp n K) := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Z := QuotientGroup.ker_mk' _
  have hZc : Z ≤ Subgroup.center (StatedSp n K) := SymplecticHigher.spScalars_le_center
  have : Group.IsPerfect (StatedSp n K) := by
    have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin K n
        (Or.inr (Or.inl ⟨hK, by omega⟩))
    let e : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
      (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).trans
        (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
          (n := n) (K := K)).symm)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hperf : Group.IsPerfect (StatedProj (StatedSp n K)) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSp n K)) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq (hker ▸ hZc)
      fun π hπ hcen => sp_three_exists_section_of_central hK hn3 hπ hcen)
  have hcard : Nat.card Z = Nat.gcd 2 (Nat.card K - 1) := card_spScalars_eq_gcd K (by omega)
  have hcard2 : Nat.card Z = 2 := by rw [hcard, hK]; rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hcard2
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hker).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SpThree
