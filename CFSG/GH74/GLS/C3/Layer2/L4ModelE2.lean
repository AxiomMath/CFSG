module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

theorem klein_existsE2 {G : Type*} [Group G] (x y : G) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) :
    ∃ R : Subgroup G, ∀ g, g ∈ R ↔ (g = 1 ∨ g = x ∨ g = y ∨ g = x * y) := by
  have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have h2 : y * (x * y) = x := by rw [hxy, ← mul_assoc, hy, one_mul]
  have h3 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  have h4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have h5 : x * y * (x * y) = 1 := by rw [← mul_assoc, h3, hy]
  have h6 : y * x = x * y := hxy.symm
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  refine ⟨{ carrier := {g | g = 1 ∨ g = x ∨ g = y ∨ g = x * y}
            mul_mem' := ?_
            one_mem' := Or.inl rfl
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (Or.inl (one_mul _))
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr h6))
    · exact Or.inl hy
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl h4)
    · exact Or.inl h5
  · rintro a (rfl | rfl | rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl hxi)
    · exact Or.inr (Or.inr (Or.inl hyi))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, hxi, hyi, h6]

namespace Tab

variable {n : ℕ} [NeZero n] (T : Tab n)

@[expose] def aVecE2 (a : Tbl) : Vector Bool 64 :=
  let E0 := T.eVecE1 a
  Vector.ofFn fun i => (List.finRange 64).all fun j => imp (E0.get j) (T.mulT i j == T.mulT j i)

@[expose] def bVecE2 (a : Tbl) : Vector Bool 64 :=
  let E0 := T.eVecE1 a
  let A0 := T.aVecE2 a
  let X0 := T.reach a T.x0i
  Vector.ofFn fun i => T.isInv i && A0.get i && X0.get i && !E0.get i

@[expose] def bListE2 (a : Tbl) : List (Fin 64) :=
  let B0 := T.bVecE2 a
  (List.finRange 64).filter fun i => B0.get i

@[expose] def prodB4E2 (b0 b1 b2 b3 : Fin 64) (m : ℕ) : Fin 64 :=
  T.mulT (T.mulT (if m % 2 = 1 then b0 else T.one) (if m / 2 % 2 = 1 then b1 else T.one))
    (T.mulT (if m / 4 % 2 = 1 then b2 else T.one) (if m / 8 % 2 = 1 then b3 else T.one))

@[expose] def kleinOkE2 (A0 : Vector Bool 64) (r1 r2 : Fin 64) : Bool :=
  decide (T.isInv r1 = true ∧ T.isInv r2 = true ∧ T.mulT r1 r2 = T.mulT r2 r1 ∧
    A0.get r1 = false ∧ A0.get r2 = false ∧ A0.get (T.mulT r1 r2) = false ∧
    ∀ t : Fin 64, A0.get t = true ∨ A0.get (T.mulT t (T.inv.get r1)) = true ∨
      A0.get (T.mulT t (T.inv.get r2)) = true ∨
      A0.get (T.mulT t (T.inv.get (T.mulT r1 r2))) = true)

@[expose] def inKleinE2 (r1 r2 s : Fin 64) : Bool :=
  s == T.one || s == r1 || s == r2 || s == T.mulT r1 r2

@[expose] def conjE2 (a : Tbl) (t0 r : Fin 64) : Fin 64 :=
  T.mulT (T.mulT t0 (a.get r)) (T.inv.get t0)

@[expose] def stableE2 (a : Tbl) (t0 r1 r2 : Fin 64) : Bool :=
  T.inKleinE2 r1 r2 (T.conjE2 a t0 T.one) && T.inKleinE2 r1 r2 (T.conjE2 a t0 r1) &&
    T.inKleinE2 r1 r2 (T.conjE2 a t0 r2) &&
    T.inKleinE2 r1 r2 (T.conjE2 a t0 (T.mulT r1 r2))

theorem stableE2_spec (a : Tbl) (t0 r1 r2 : Fin 64) (h : T.stableE2 a t0 r1 r2 = true) :
    ∀ r : Fin 64, (r = T.one ∨ r = r1 ∨ r = r2 ∨ r = T.mulT r1 r2) →
      (T.conjE2 a t0 r = T.one ∨ T.conjE2 a t0 r = r1 ∨ T.conjE2 a t0 r = r2 ∨
        T.conjE2 a t0 r = T.mulT r1 r2) := by
  simp only [stableE2, inKleinE2, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  intro r hr
  rcases hr with hr | hr | hr | hr
  · rw [hr]; exact or_assoc.1 (or_assoc.1 h0)
  · rw [hr]; exact or_assoc.1 (or_assoc.1 h1)
  · rw [hr]; exact or_assoc.1 (or_assoc.1 h2)
  · rw [hr]; exact or_assoc.1 (or_assoc.1 h3)

@[expose] def e2P1 (a : Tbl) (_u : Fin 64) : Bool :=
  let A0 := T.aVecE2 a
  decide (
    (∀ i j : Fin 64, T.isInv i = true → T.isInv j = true → T.mulT i j = T.mulT j i → i ≠ j →
        T.isInv (T.mulT i j) = true) ∧
    T.isInv (T.vIE1 a) = true ∧
    ((Finset.univ.filter fun i : Fin 64 => A0.get i = true).card = 16) ∧
    (∀ i j : Fin 64, A0.get i = true → A0.get j = true → T.mulT i j = T.mulT j i) ∧
    (∀ i : Fin 64, A0.get i = true → T.mulT i i = T.one))

@[expose] def e2P2 (a : Tbl) (_u : Fin 64) : Bool :=
  let A0 := T.aVecE2 a
  let bl := T.bListE2 a
  decide (bl.length = 4 ∧ ∀ i : Fin 64, A0.get i = true → ∃ m : Fin 16,
    i = T.prodB4E2 (bl.getD 0 T.one) (bl.getD 1 T.one) (bl.getD 2 T.one) (bl.getD 3 T.one) m.1)

@[expose] def e2P3 (a : Tbl) (u : Fin 64) : Bool :=
  let A0 := T.aVecE2 a
  decide (∀ t0 : Fin 64, T.mulT (T.mulT t0 (a.get t0)) u = T.one →
    ∃ r1 : Fin 64, ∃ r2 : Fin 64, r1 < r2 ∧ T.stableE2 a t0 r1 r2 = true ∧
      T.kleinOkE2 A0 r1 r2 = true)

@[expose] def e2P4 (a : Tbl) (_u : Fin 64) : Bool :=
  let vi := T.vIE1 a
  decide (∀ s : Fin 64, (∀ t : Fin 64, T.mulT s t = T.mulT t s) → a.get s = s →
    T.isInv s = true → s = vi)

theorem aVecE2_get (a : Tbl) (i : Fin 64) :
    (T.aVecE2 a).get i = true ↔
      ∀ j : Fin 64, (T.eVecE1 a).get j = true → T.mulT i j = T.mulT j i := by
  simp only [aVecE2, vget_ofFn, List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true,
    beq_iff_eq]

theorem bVecE2_get (a : Tbl) (i : Fin 64) :
    (T.bVecE2 a).get i = true ↔ (T.isInv i = true ∧ (T.aVecE2 a).get i = true ∧
      (T.reach a T.x0i).get i = true ∧ (T.eVecE1 a).get i = false) := by
  simp only [bVecE2, vget_ofFn, Bool.and_eq_true, Bool.not_eq_true', and_assoc]

theorem mem_bListE2 (a : Tbl) (i : Fin 64) : i ∈ T.bListE2 a ↔ (T.bVecE2 a).get i = true := by
  simp only [bListE2, List.mem_filter, List.mem_finRange, true_and]

theorem iT_prodB4E2
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (b0 b1 b2 b3 : Fin 64) (m : ℕ) :
    T.iT hn hv (T.prodB4E2 b0 b1 b2 b3 m) =
      (if m % 2 = 1 then T.iT hn hv b0 else 1) * (if m / 2 % 2 = 1 then T.iT hn hv b1 else 1) *
        ((if m / 4 % 2 = 1 then T.iT hn hv b2 else 1) *
          (if m / 8 % 2 = 1 then T.iT hn hv b3 else 1)) := by
  simp only [prodB4E2, T.iT_mul hn hv, apply_ite (T.iT hn hv), T.iT_one hn hv]

theorem aVecE2_iff
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (E : Subgroup (T0 n)) (a : Tbl)
    (hEi : ∀ i, (T.eVecE1 a).get i = true ↔ T.iT hn hv i ∈ E) (i : Fin 64) :
    (T.aVecE2 a).get i = true ↔ T.iT hn hv i ∈ Subgroup.centralizer (E : Set (T0 n)) := by
  rw [aVecE2_get, Subgroup.mem_centralizer_iff]
  constructor
  · intro h e he
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv e
    have h2 := congrArg (T.iT hn hv) (h j ((hEi j).2 he))
    rw [T.iT_mul hn hv, T.iT_mul hn hv] at h2
    exact h2.symm
  · intro h j hj
    apply T.iT_injective hn hv
    rw [T.iT_mul hn hv, T.iT_mul hn hv]
    exact (h _ ((hEi j).1 hj)).symm

theorem card_A_E2
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (E : Subgroup (T0 n)) (a : Tbl)
    (hEi : ∀ i, (T.eVecE1 a).get i = true ↔ T.iT hn hv i ∈ E)
    (hcard : (Finset.univ.filter fun i : Fin 64 => (T.aVecE2 a).get i = true).card = 16) :
    Nat.card ↥(Subgroup.centralizer (E : Set (T0 n))) = 16 := by
  have e : ↥(Subgroup.centralizer (E : Set (T0 n))) ≃ {i : Fin 64 // (T.aVecE2 a).get i = true} :=
    Equiv.subtypeEquiv (T.eT hn hv).symm (fun x => by
      rw [T.aVecE2_iff hn hv E a hEi, T.iT_eT_symmE1 hn hv])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcard

theorem E2_b
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (X : Set (T0 n)) (a : Tbl)
    (hXc : ∀ i, T.isInv i = true → ((T.reach a T.x0i).get i = true ↔ T.iT hn hv i ∈ X))
    (E : Subgroup (T0 n)) (hEi : ∀ i, (T.eVecE1 a).get i = true ↔ T.iT hn hv i ∈ E)
    (hbl : (T.bListE2 a).length = 4)
    (hgen : ∀ i : Fin 64, (T.aVecE2 a).get i = true → ∃ m : Fin 16,
      i = T.prodB4E2 ((T.bListE2 a).getD 0 T.one) ((T.bListE2 a).getD 1 T.one)
        ((T.bListE2 a).getD 2 T.one) ((T.bListE2 a).getD 3 T.one) m.1) :
    ∃ b : Fin 4 → T0 n, Function.Injective b ∧
      (∀ i, b i ∈ Subgroup.centralizer (E : Set (T0 n)) ∧ orderOf (b i) = 2 ∧ b i ∈ X ∧
        b i ∉ E) ∧
      (∀ t ∈ Subgroup.centralizer (E : Set (T0 n)), orderOf t = 2 → t ∈ X → t ∉ E →
        ∃ i, t = b i) ∧
      (∀ t ∈ Subgroup.centralizer (E : Set (T0 n)), t ∈ Subgroup.closure (Set.range b)) := by
  classical
  have hmem : ∀ i, i ∈ T.bListE2 a ↔ (T.bVecE2 a).get i = true := T.mem_bListE2 a
  have hnodup : (T.bListE2 a).Nodup := by
    have h := List.Nodup.filter (fun i => (T.bVecE2 a).get i) (List.nodup_finRange 64)
    exact h
  generalize T.bListE2 a = bl at hbl hgen hmem hnodup
  let bi : Fin 4 → Fin 64 := fun k => bl.get (Fin.cast hbl.symm k)
  have hbi_mem : ∀ k, (T.bVecE2 a).get (bi k) = true := fun k =>
    (hmem _).1 (List.get_mem bl _)
  have hinj_get : Function.Injective bl.get := List.nodup_iff_injective_get.1 hnodup
  refine ⟨fun k => T.iT hn hv (bi k), ?_, ?_, ?_, ?_⟩
  · intro k k' h
    have h1 := T.iT_injective hn hv h
    have h2 := hinj_get h1
    exact Fin.cast_injective hbl.symm h2
  · intro k
    obtain ⟨hinv, hA, hX0, hE0⟩ := (T.bVecE2_get a (bi k)).1 (hbi_mem k)
    refine ⟨(T.aVecE2_iff hn hv E a hEi _).1 hA, T.orderOf_iT_of_isInv hn hv hinv,
      (hXc _ hinv).1 hX0, ?_⟩
    intro hm
    have h1 := (hEi _).2 hm
    rw [h1] at hE0
    exact absurd hE0 (by decide)
  · intro t ht ho hX hE
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv t
    have hinv : T.isInv j = true := T.isInv_of_orderOf_iTE1 hn hv ho
    have hB : (T.bVecE2 a).get j = true :=
      (T.bVecE2_get a j).2 ⟨hinv, (T.aVecE2_iff hn hv E a hEi j).2 ht, (hXc j hinv).2 hX,
        Bool.eq_false_iff.2 fun h => hE ((hEi j).1 h)⟩
    obtain ⟨k, hk⟩ := List.mem_iff_get.1 ((hmem j).2 hB)
    refine ⟨Fin.cast hbl k, ?_⟩
    have hkk : Fin.cast hbl.symm (Fin.cast hbl k) = k := Fin.ext rfl
    show T.iT hn hv j = T.iT hn hv (bl.get (Fin.cast hbl.symm (Fin.cast hbl k)))
    rw [hkk, hk]
  · intro t ht
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv t
    obtain ⟨m, hm⟩ := hgen j ((T.aVecE2_iff hn hv E a hEi j).2 ht)
    rw [hm, T.iT_prodB4E2 hn hv]
    have hb : ∀ k : ℕ, (hk : k < 4) → T.iT hn hv (bl.getD k T.one) ∈
        Subgroup.closure (Set.range fun k : Fin 4 => T.iT hn hv (bi k)) := by
      intro k hk
      rw [← List.getElem_eq_getD (h := (by omega : k < bl.length)) T.one]
      exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩
    have hfac : ∀ (k : ℕ) (c : Prop) [Decidable c], k < 4 →
        (if c then T.iT hn hv (bl.getD k T.one) else (1 : T0 n)) ∈
          Subgroup.closure (Set.range fun k : Fin 4 => T.iT hn hv (bi k)) := by
      intro k c _ hk
      split_ifs
      · exact hb k hk
      · exact one_mem _
    exact mul_mem (mul_mem (hfac 0 _ (by omega)) (hfac 1 _ (by omega)))
      (mul_mem (hfac 2 _ (by omega)) (hfac 3 _ (by omega)))

theorem isInv_mul_E2 {i : Fin 64} (h : T.isInv i = true) : T.mulT i i = T.one := by
  simp only [isInv, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem E2_split
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (α : T0 n ≃* T0 n) (a : Tbl)
    (ha : ∀ i, T.iT hn hv (a.get i) = α (T.iT hn hv i)) (ui : Fin 64) (u : T0 n)
    (hui : T.iT hn hv ui = u) (E : Subgroup (T0 n))
    (hEi : ∀ i, (T.eVecE1 a).get i = true ↔ T.iT hn hv i ∈ E)
    (hP3 : ∀ t0 : Fin 64, T.mulT (T.mulT t0 (a.get t0)) ui = T.one →
      ∃ r1 : Fin 64, ∃ r2 : Fin 64, r1 < r2 ∧ T.stableE2 a t0 r1 r2 = true ∧
        T.kleinOkE2 (T.aVecE2 a) r1 r2 = true) :
    ∀ t₀ : T0 n, t₀ * α t₀ * u = 1 → ∃ R : Subgroup (T0 n),
      R ⊓ Subgroup.centralizer (E : Set (T0 n)) = ⊥ ∧
      (∀ r ∈ R, t₀ * α r * t₀⁻¹ ∈ R) ∧
      Subgroup.centralizer (E : Set (T0 n)) ⊔ R = ⊤ := by
  intro t₀ ht₀
  obtain ⟨i₀, rfl⟩ := T.iT_surjective hn hv t₀
  have hi₀ : T.mulT (T.mulT i₀ (a.get i₀)) ui = T.one := by
    apply T.iT_injective hn hv
    rw [T.iT_mul hn hv, T.iT_mul hn hv, ha, hui, T.iT_one hn hv]
    exact ht₀
  obtain ⟨r1, r2, -, hst, hk⟩ := hP3 i₀ hi₀
  simp only [kleinOkE2, decide_eq_true_eq] at hk
  obtain ⟨hinv1, hinv2, hcomm, hA1, hA2, hA12, hcov⟩ := hk
  obtain ⟨x, hx⟩ : ∃ x : T0 n, x = T.iT hn hv r1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : T0 n, y = T.iT hn hv r2 := ⟨_, rfl⟩
  have hr12 : T.iT hn hv (T.mulT r1 r2) = x * y := by
    rw [T.iT_mul hn hv, hx, hy]
  have hxx : x * x = 1 := by
    rw [hx, ← T.iT_mul hn hv, T.isInv_mul_E2 hinv1, T.iT_one hn hv]
  have hyy : y * y = 1 := by
    rw [hy, ← T.iT_mul hn hv, T.isInv_mul_E2 hinv2, T.iT_one hn hv]
  have hxy : x * y = y * x := by
    rw [hx, hy, ← T.iT_mul hn hv, ← T.iT_mul hn hv, hcomm]
  obtain ⟨R, hRmem⟩ := klein_existsE2 x y hxx hyy hxy
  have hxR : x ∈ R := (hRmem x).2 (Or.inr (Or.inl rfl))
  have hyR : y ∈ R := (hRmem y).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hxyR : x * y ∈ R := (hRmem _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hnot : ∀ s : Fin 64, (T.aVecE2 a).get s = false →
      T.iT hn hv s ∉ Subgroup.centralizer (E : Set (T0 n)) := by
    intro s hs hm
    have h1 := (T.aVecE2_iff hn hv E a hEi s).2 hm
    rw [hs] at h1
    exact absurd h1 (by decide)
  have hA_of : ∀ s : Fin 64, (T.aVecE2 a).get s = true →
      T.iT hn hv s ∈ Subgroup.centralizer (E : Set (T0 n)) := fun s hs =>
    (T.aVecE2_iff hn hv E a hEi s).1 hs
  have hconj : ∀ r' : Fin 64, T.iT hn hv i₀ * α (T.iT hn hv r') * (T.iT hn hv i₀)⁻¹ =
      T.iT hn hv (T.conjE2 a i₀ r') := by
    intro r'
    show _ = T.iT hn hv (T.mulT (T.mulT i₀ (a.get r')) (T.inv.get i₀))
    rw [T.iT_mul hn hv, T.iT_mul hn hv, ha, T.iT_inv hn hv]
  have hidx : ∀ s : Fin 64, (s = T.one ∨ s = r1 ∨ s = r2 ∨ s = T.mulT r1 r2) →
      T.iT hn hv s ∈ R := by
    intro s hs
    rcases hs with h | h | h | h
    · rw [h, T.iT_one hn hv]; exact one_mem _
    · rw [h, ← hx]; exact hxR
    · rw [h, ← hy]; exact hyR
    · rw [h, hr12]; exact hxyR
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hgR, hgA⟩
    rcases (hRmem g).1 hgR with h | h | h | h
    · rw [h]; exact one_mem _
    · refine absurd ?_ (hnot r1 hA1)
      rw [← hx, ← h]; exact hgA
    · refine absurd ?_ (hnot r2 hA2)
      rw [← hy, ← h]; exact hgA
    · refine absurd ?_ (hnot (T.mulT r1 r2) hA12)
      rw [hr12, ← h]; exact hgA
  · intro r hr
    rcases (hRmem r).1 hr with h | h | h | h
    · rw [h, map_one, mul_one, mul_inv_cancel]; exact one_mem _
    · rw [h, hx, hconj r1]
      exact hidx _ (T.stableE2_spec a i₀ r1 r2 hst r1 (by simp))
    · rw [h, hy, hconj r2]
      exact hidx _ (T.stableE2_spec a i₀ r1 r2 hst r2 (by simp))
    · rw [h, ← hr12, hconj (T.mulT r1 r2)]
      exact hidx _ (T.stableE2_spec a i₀ r1 r2 hst _ (by simp))
  · rw [eq_top_iff]
    rintro t -
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv t
    rcases hcov j with h | h | h | h
    · exact Subgroup.mem_sup_left (hA_of j h)
    · have h1 := hA_of _ h
      rw [T.iT_mul hn hv, T.iT_inv hn hv, ← hx] at h1
      have h2 := Subgroup.mul_mem_sup h1 hxR
      rwa [inv_mul_cancel_right] at h2
    · have h1 := hA_of _ h
      rw [T.iT_mul hn hv, T.iT_inv hn hv, ← hy] at h1
      have h2 := Subgroup.mul_mem_sup h1 hyR
      rwa [inv_mul_cancel_right] at h2
    · have h1 := hA_of _ h
      rw [T.iT_mul hn hv, T.iT_inv hn hv, hr12] at h1
      have h2 := Subgroup.mul_mem_sup h1 hxyR
      rwa [inv_mul_cancel_right] at h2

theorem E2_zc
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (α : T0 n ≃* T0 n) (a : Tbl)
    (ha : ∀ i, T.iT hn hv (a.get i) = α (T.iT hn hv i))
    (hP4 : ∀ s : Fin 64, (∀ t : Fin 64, T.mulT s t = T.mulT t s) → a.get s = s →
      T.isInv s = true → s = T.vIE1 a) :
    ∀ s : T0 n, (∀ t : T0 n, s * t = t * s) → α s = s → s * s = 1 → s ≠ 1 →
      s = vHat n α := by
  intro s hc hα hs2 hs1
  obtain ⟨j, rfl⟩ := T.iT_surjective hn hv s
  have hord : orderOf (T.iT hn hv j) = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  have hinv := T.isInv_of_orderOf_iTE1 hn hv hord
  have hj := hP4 j (fun t => by
      apply T.iT_injective hn hv
      rw [T.iT_mul hn hv, T.iT_mul hn hv]
      exact hc _) (by
      apply T.iT_injective hn hv
      rw [ha]; exact hα) hinv
  rw [hj]
  exact T.iT_vIE1 hn hv α a ha

end Tab

theorem model_E2_aux
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (T : Tab n) (hv : T.Valid)
    (hcB : T.claimB = true) (hc1 : T.claimG T.e2P1 = true) (hc2 : T.claimG T.e2P2 = true)
    (hc3 : T.claimG T.e2P3 = true) (hc4 : T.claimG T.e2P4 = true)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V)
    (E : Subgroup (T0 n))
    (hE : ∀ t : T0 n, t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
      (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X))) :
    ∃ A : Subgroup (T0 n),
      (∀ t : T0 n, t ∈ A ↔ ∀ e ∈ E, t * e = e * t) ∧
      Nat.card A = 16 ∧ (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧ (∀ a ∈ A, a * a = 1) ∧
      (∃ b : Fin 4 → T0 n, Function.Injective b ∧
        (∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ X ∧ b i ∉ E) ∧
        (∀ t ∈ A, orderOf t = 2 → t ∈ X → t ∉ E → ∃ i, t = b i) ∧
        (∀ t ∈ A, t ∈ Subgroup.closure (Set.range b))) ∧
      (∀ t₀ : T0 n, t₀ * α t₀ * u = 1 → ∃ R : Subgroup (T0 n), R ⊓ A = ⊥ ∧
        (∀ r ∈ R, t₀ * α r * t₀⁻¹ ∈ R) ∧ A ⊔ R = ⊤) ∧
      (∀ s : T0 n, (∀ t : T0 n, s * t = t * s) → α s = s → s * s = 1 → s ≠ 1 →
        s = vHat n α) := by
  obtain ⟨_, -, hP1, hXc, -⟩ := T.facts_of_claimG hn hv hcB T.e2P1 hc1 α u X V hx hu hsq hext hX
    hV hdisj hclX hclV hQ
  obtain ⟨_, -, hP2, -, -⟩ := T.facts_of_claimG hn hv hcB T.e2P2 hc2 α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ
  obtain ⟨ui3, hui3, hP3, -, -⟩ := T.facts_of_claimG hn hv hcB T.e2P3 hc3 α u X V hx hu hsq hext hX
    hV hdisj hclX hclV hQ
  obtain ⟨_, -, hP4, -, -⟩ := T.facts_of_claimG hn hv hcB T.e2P4 hc4 α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ
  have ha : ∀ i, T.iT hn hv ((T.tabOf hn hv α).get i) = α (T.iT hn hv i) :=
    T.iT_tabOf hn hv α
  have hclX' := Tab.edge_closed T hn hv α X hclX
  have hX0 := Tab.reach_sound T hn hv (T.tabOf hn hv α) X hclX' T.x0i
    (by rw [Tab.iT_x0]; exact hX)
  unfold Tab.e2P1 at hP1
  simp only [decide_eq_true_eq] at hP1
  obtain ⟨hF1, hvinv, hcardA, hcommA, hsqA⟩ := hP1
  unfold Tab.e2P2 at hP2
  simp only [decide_eq_true_eq] at hP2
  obtain ⟨hbl, hgen⟩ := hP2
  unfold Tab.e2P3 at hP3
  simp only [decide_eq_true_eq] at hP3
  unfold Tab.e2P4 at hP4
  simp only [decide_eq_true_eq] at hP4
  have hEi : ∀ i, (T.eVecE1 (T.tabOf hn hv α)).get i = true ↔ T.iT hn hv i ∈ E := fun i =>
    (T.eVecE1_iff hn hv α X _ ha hXc hX0 hF1 hvinv i).trans (hE _).symm
  refine ⟨Subgroup.centralizer (E : Set (T0 n)), fun t => ⟨fun h e he =>
      (Subgroup.mem_centralizer_iff.1 h e he).symm, fun h => Subgroup.mem_centralizer_iff.2
      fun e he => (h e he).symm⟩, T.card_A_E2 hn hv E _ hEi hcardA, ?_, ?_,
    T.E2_b hn hv X _ hXc E hEi hbl hgen, T.E2_split hn hv α _ ha _ u hui3 E hEi hP3,
    T.E2_zc hn hv α _ ha hP4⟩
  · intro x hx y hy
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv x
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv y
    have h1 := hcommA i j ((T.aVecE2_iff hn hv E _ hEi i).2 hx)
      ((T.aVecE2_iff hn hv E _ hEi j).2 hy)
    rw [← Tab.iT_mul, ← Tab.iT_mul, h1]
  · intro x hx
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv x
    rw [← Tab.iT_mul, hsqA i ((T.aVecE2_iff hn hv E _ hEi i).2 hx), Tab.iT_one]

end CFSG.GH74.GLS.C3.Layer2.Model
