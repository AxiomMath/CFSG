
module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelGen
public import CFSG.GH74.GLS.C3.Layer2.L4ModelDefs

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

@[expose] def vStdE1 (n : ℕ) [NeZero n] : Amb n := (swap 0 1 * swap 2 3, x4)

@[expose] def wStdE1 (n : ℕ) [NeZero n] : Amb n := (swap 4 5 * swap 5 6, 1)

@[expose] def repListE1 (n : ℕ) [NeZero n] : List (Amb n) :=
  if n = 7 then [1, wStdE1 n, wStdE1 n * wStdE1 n] else [1]

@[expose] def cfSetE1 (n : ℕ) [NeZero n] : Finset (Amb n) :=
  Finset.univ.filter fun g : Amb n =>
    g * vStdE1 n = vStdE1 n * g ∧ g.2 * x4 = x4 * g.2 ∧ sign g.1 = sign g.2

@[expose] def allAmbE1 (n : ℕ) : List (Amb n) :=
  (permsOfList (List.finRange n)).flatMap fun σ =>
    (permsOfList (List.finRange 4)).map fun d => (σ, d)

theorem mem_allAmbE1 (n : ℕ) (g : Amb n) : g ∈ allAmbE1 n := by
  simp only [allAmbE1, List.mem_flatMap, List.mem_map]
  exact ⟨g.1, mem_permsOfList_of_mem fun x _ => List.mem_finRange x, g.2,
    mem_permsOfList_of_mem fun x _ => List.mem_finRange x, rfl⟩

@[expose] def cfListE1 (n : ℕ) [NeZero n] : List (Amb n) :=
  (allAmbE1 n).filter fun g =>
    decide (g * vStdE1 n = vStdE1 n * g ∧ g.2 * x4 = x4 * g.2 ∧ sign g.1 = sign g.2)

theorem mem_cfListE1 (n : ℕ) [NeZero n] (g : Amb n) :
    g ∈ cfListE1 n ↔ g * vStdE1 n = vStdE1 n * g ∧ g.2 * x4 = x4 * g.2 ∧ sign g.1 = sign g.2 := by
  constructor
  · intro h
    simpa only [decide_eq_true_eq] using (List.mem_filter.1 h).2
  · intro h
    exact List.mem_filter.2 ⟨mem_allAmbE1 n g, by simpa only [decide_eq_true_eq] using h⟩

theorem keyA_injectiveE1 (n : ℕ) : Function.Injective (keyA n) := by
  intro g h hgh
  simp only [keyA] at hgh
  obtain ⟨h1, h2⟩ := List.append_inj hgh (by simp)
  have e1 : ∀ i : Fin n, g.1 i = h.1 i := fun i =>
    Fin.ext (List.map_inj_left.1 h1 i (List.mem_finRange i))
  have e2 : ∀ j : Fin 4, g.2 j = h.2 j := fun j =>
    Fin.ext (List.map_inj_left.1 h2 j (List.mem_finRange j))
  exact Prod.ext (Equiv.ext e1) (Equiv.ext e2)

@[expose] def EsetE1 (n : ℕ) [NeZero n] (α : T0 n ≃* T0 n) (X : Set (T0 n)) : Set (T0 n) :=
  {x | x = 1 ∨ x = vHat n α ∨
    (orderOf x = 2 ∧ x ∈ X ∧ x * vHat n α = vHat n α * x ∧ x * vHat n α ∈ X)}

theorem card_Hgrp_vStdE1 (n : ℕ) [NeZero n] : Nat.card ↥(Hgrp n (vStdE1 n)) = (cfSetE1 n).card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  simp only [Hgrp, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, cfSetE1,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1.1, h.1.2⟩, fun h => ⟨⟨h.2.1, h.2.2⟩, h.1⟩⟩

namespace Tab

variable {n : ℕ} [NeZero n] (T : Tab n)

@[expose] def vIE1 (a : Tbl) : Fin 64 := T.mulT T.x0i (a.get T.x0i)

@[expose] def eVecE1 (a : Tbl) : Vector Bool 64 :=
  let X0 := T.reach a T.x0i
  let vi := T.vIE1 a
  Vector.ofFn fun i => i == T.one || i == vi ||
    (T.isInv i && X0.get i && T.mulT i vi == T.mulT vi i && X0.get (T.mulT i vi))

@[expose] def e1P1 (a : Tbl) (_u : Fin 64) : Bool :=
  let E0 := T.eVecE1 a
  decide (
    (∀ i j : Fin 64, T.isInv i = true → T.isInv j = true → T.mulT i j = T.mulT j i → i ≠ j →
        T.isInv (T.mulT i j) = true) ∧
    T.isInv T.x0i = true ∧ (∀ i : Fin 64, T.mulT T.x0i i = T.mulT i T.x0i) ∧
    T.isInv (T.vIE1 a) = true ∧ T.el.get (T.vIE1 a) = vStdE1 n ∧
    (∀ i j : Fin 64, E0.get i = true → E0.get j = true →
        E0.get (T.mulT i j) = true ∧ T.mulT i j = T.mulT j i) ∧
    (∀ i : Fin 64, E0.get i = true → T.mulT i i = T.one) ∧
    ((Finset.univ.filter fun i : Fin 64 => E0.get i = true).card = 8) ∧
    (∀ s i : Fin 64, E0.get i = true → E0.get (T.mulT (T.mulT s i) (T.inv.get s)) = true) ∧
    (∀ i : Fin 64, E0.get i = true → E0.get (a.get i) = true))

@[expose] def e1P2 (a : Tbl) (_u : Fin 64) : Bool :=
  let X0 := T.reach a T.x0i
  let V0 := T.reach a (T.vIE1 a)
  decide (∀ i j : Fin 64, T.isInv i = true → T.isInv j = true → V0.get i = true →
    V0.get j = true → X0.get (T.mulT T.x0i i) = true → X0.get (T.mulT T.x0i j) = true →
    T.cls.get i = T.cls.get j)

@[expose] def e1P3 (a : Tbl) (_u : Fin 64) : Bool :=
  let E0 := T.eVecE1 a
  (repListE1 n).all fun r => decide (∀ i : Fin 64, E0.get i = true →
    ∃ j : Fin 64, E0.get j = true ∧ T.el.get j = r * T.el.get i * r⁻¹)

@[expose] def cfCoverE1 : Bool :=
  let ks : List (List ℕ) := (List.finRange 64).flatMap fun i =>
    (repListE1 n).map fun r => keyA n (T.el.get i * r)
  (cfListE1 n).all fun g => decide (keyA n g ∈ ks)

theorem cfCoverE1_spec (h : T.cfCoverE1 = true) :
    ∀ g ∈ cfListE1 n, ∃ i : Fin 64, ∃ r ∈ repListE1 n, g = T.el.get i * r := by
  unfold cfCoverE1 at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  intro g hg
  have hk := h g hg
  simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hk
  obtain ⟨i, r, hr, hkey⟩ := hk
  exact ⟨i, r, hr, (keyA_injectiveE1 n hkey).symm⟩

theorem eVecE1_get (a : Tbl) (i : Fin 64) :
    (T.eVecE1 a).get i = (i == T.one || i == T.vIE1 a ||
      (T.isInv i && (T.reach a T.x0i).get i && T.mulT i (T.vIE1 a) == T.mulT (T.vIE1 a) i &&
        (T.reach a T.x0i).get (T.mulT i (T.vIE1 a)))) := by
  simp only [eVecE1, vget_ofFn]

theorem iT_vIE1
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (α : T0 n ≃* T0 n) (a : Tbl)
    (ha : ∀ i, T.iT hn hv (a.get i) = α (T.iT hn hv i)) :
    T.iT hn hv (T.vIE1 a) = vHat n α := by
  simp only [vIE1]
  rw [iT_mul, ha, iT_x0]
  rfl

theorem iT_eT_symmE1 (hn : n = 6 ∨ n = 7) (hv : T.Valid) (x : T0 n) :
    T.iT hn hv ((T.eT hn hv).symm x) = x := (T.eT hn hv).apply_symm_apply x

theorem isInv_of_orderOf_iTE1
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) {i : Fin 64}
    (h : orderOf (T.iT hn hv i) = 2) : T.isInv i = true := by
  have := T.isInv_of_orderOf hn hv h
  rwa [eT_symm_iT] at this

theorem eVecE1_iff
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (α : T0 n ≃* T0 n) (X : Set (T0 n))
    (a : Tbl) (ha : ∀ i, T.iT hn hv (a.get i) = α (T.iT hn hv i))
    (hXc : ∀ i, T.isInv i = true → ((T.reach a T.x0i).get i = true ↔ T.iT hn hv i ∈ X))
    (hX0 : ∀ j, (T.reach a T.x0i).get j = true → T.iT hn hv j ∈ X)
    (hF1 : ∀ i j : Fin 64, T.isInv i = true → T.isInv j = true → T.mulT i j = T.mulT j i →
      i ≠ j → T.isInv (T.mulT i j) = true)
    (hvinv : T.isInv (T.vIE1 a) = true) (i : Fin 64) :
    (T.eVecE1 a).get i = true ↔ T.iT hn hv i ∈ EsetE1 n α X := by
  have hiv : T.iT hn hv (T.vIE1 a) = vHat n α := T.iT_vIE1 hn hv α a ha
  rw [eVecE1_get]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ((h | h) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩)
    · left
      rw [h, iT_one]
    · right; left
      rw [h, hiv]
    · right; right
      refine ⟨orderOf_iT_of_isInv T hn hv h1, (hXc i h1).1 h2, ?_, ?_⟩
      · rw [← hiv, ← iT_mul, ← iT_mul, h3]
      · have := hX0 _ h4
        rwa [iT_mul, hiv] at this
  · rintro (h | h | ⟨h1, h2, h3, h4⟩)
    · left; left
      apply T.iT_injective hn hv
      rw [h, iT_one]
    · left; right
      apply T.iT_injective hn hv
      rw [h, hiv]
    · by_cases hiv' : i = T.vIE1 a
      · left; right; exact hiv'
      · right
        have hinv : T.isInv i = true := isInv_of_orderOf_iTE1 T hn hv h1
        have hcomm : T.mulT i (T.vIE1 a) = T.mulT (T.vIE1 a) i := by
          apply T.iT_injective hn hv
          rw [iT_mul, iT_mul, hiv]
          exact h3
        have hprod : T.isInv (T.mulT i (T.vIE1 a)) = true := hF1 i (T.vIE1 a) hinv hvinv hcomm hiv'
        refine ⟨⟨⟨hinv, (hXc i hinv).2 h2⟩, hcomm⟩, (hXc _ hprod).2 ?_⟩
        rw [iT_mul, hiv]
        exact h4

theorem E1_sub
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (α : T0 n ≃* T0 n) (X : Set (T0 n)) (a : Tbl)
    (ha : ∀ i, T.iT hn hv (a.get i) = α (T.iT hn hv i))
    (hE : ∀ i, (T.eVecE1 a).get i = true ↔ T.iT hn hv i ∈ EsetE1 n α X)
    (hmul : ∀ i j : Fin 64, (T.eVecE1 a).get i = true → (T.eVecE1 a).get j = true →
      (T.eVecE1 a).get (T.mulT i j) = true ∧ T.mulT i j = T.mulT j i)
    (hsqE : ∀ i : Fin 64, (T.eVecE1 a).get i = true → T.mulT i i = T.one)
    (hcardE : (Finset.univ.filter fun i : Fin 64 => (T.eVecE1 a).get i = true).card = 8)
    (hnorm : ∀ s i : Fin 64, (T.eVecE1 a).get i = true →
      (T.eVecE1 a).get (T.mulT (T.mulT s i) (T.inv.get s)) = true)
    (hαE : ∀ i : Fin 64, (T.eVecE1 a).get i = true → (T.eVecE1 a).get (a.get i) = true) :
    ∃ E : Subgroup (T0 n), (∀ x, x ∈ E ↔ (T.eVecE1 a).get ((T.eT hn hv).symm x) = true) ∧
      (∀ x, x ∈ E ↔ x ∈ EsetE1 n α X) ∧ Nat.card E = 8 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x * x = 1) ∧ (∀ s : T0 n, ∀ x ∈ E, s * x * s⁻¹ ∈ E) ∧ (∀ x ∈ E, α x ∈ E) := by
  have hmemE : ∀ x : T0 n, x ∈ EsetE1 n α X ↔ (T.eVecE1 a).get ((T.eT hn hv).symm x) = true := by
    intro x
    rw [hE ((T.eT hn hv).symm x), T.iT_eT_symmE1 hn hv]
  have hmulE : ∀ x y : T0 n, x ∈ EsetE1 n α X → y ∈ EsetE1 n α X →
      x * y ∈ EsetE1 n α X ∧ x * y = y * x := by
    intro x y hx hy
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv x
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv y
    obtain ⟨h1, h2⟩ := hmul i j ((hE i).2 hx) ((hE j).2 hy)
    refine ⟨?_, ?_⟩
    · rw [← iT_mul]
      exact (hE _).1 h1
    · rw [← iT_mul, ← iT_mul, h2]
  have hsqE' : ∀ x : T0 n, x ∈ EsetE1 n α X → x * x = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv x
    rw [← iT_mul, hsqE i ((hE i).2 hx), iT_one]
  let E : Subgroup (T0 n) :=
    { carrier := EsetE1 n α X
      mul_mem' := fun {x y} hx hy => (hmulE x y hx hy).1
      one_mem' := Or.inl rfl
      inv_mem' := fun {x} hx => by
        rw [inv_eq_of_mul_eq_one_right (hsqE' x hx)]
        exact hx }
  refine ⟨E, fun x => hmemE x, fun x => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ↥E ≃ {i : Fin 64 // (T.eVecE1 a).get i = true} :=
      Equiv.subtypeEquiv (T.eT hn hv).symm (fun x => hmemE x)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hcardE
  · exact fun x hx y hy => (hmulE x y hx hy).2
  · exact fun x hx => hsqE' x hx
  · intro s x hx
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv x
    obtain ⟨k, rfl⟩ := T.iT_surjective hn hv s
    have := (hE _).1 (hnorm k i ((hE i).2 hx))
    rwa [iT_mul, iT_mul, iT_inv] at this
  · intro x hx
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv x
    have := (hE _).1 (hαE i ((hE i).2 hx))
    rwa [ha] at this

theorem E1_F
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (α : T0 n ≃* T0 n) (a : Tbl)
    (E : Subgroup (T0 n))
    (hEmem : ∀ x, x ∈ E ↔ (T.eVecE1 a).get ((T.eT hn hv).symm x) = true)
    (hnormE : ∀ s : T0 n, ∀ x ∈ E, s * x * s⁻¹ ∈ E)
    (hvstd : ((vHat n α : T0 n) : Amb n) = vStdE1 n)
    (hcover : ∀ g ∈ cfListE1 n, ∃ i : Fin 64, ∃ r ∈ repListE1 n, g = T.el.get i * r)
    (hP3 : ∀ r ∈ repListE1 n, ∀ i : Fin 64, (T.eVecE1 a).get i = true →
      ∃ j : Fin 64, (T.eVecE1 a).get j = true ∧ T.el.get j = r * T.el.get i * r⁻¹) :
    ∀ g ∈ Fgrp n, g * ((vHat n α : T0 n) : Amb n) = ((vHat n α : T0 n) : Amb n) * g →
      ∀ e ∈ E, g * (e : Amb n) * g⁻¹ ∈ liftT n E := by
  intro g hgF hgc e he
  rw [hvstd] at hgc
  have hg : g ∈ cfListE1 n := (mem_cfListE1 n g).2 ⟨hgc, hgF.1, hgF.2⟩
  obtain ⟨i, r, hr, rfl⟩ := hcover g hg
  obtain ⟨k, rfl⟩ := T.iT_surjective hn hv e
  have hk : (T.eVecE1 a).get k = true := by
    have := (hEmem _).1 he
    rwa [eT_symm_iT] at this
  obtain ⟨j, hj, hjeq⟩ := hP3 r hr k hk
  have hjE : T.iT hn hv j ∈ E := (hEmem _).2 (by rw [eT_symm_iT]; exact hj)
  refine ⟨T.iT hn hv i * T.iT hn hv j * (T.iT hn hv i)⁻¹, hnormE _ _ hjE, ?_⟩
  have e1 : ((T.iT hn hv i : T0 n) : Amb n) = T.el.get i := rfl
  have e2 : ((T.iT hn hv j : T0 n) : Amb n) = T.el.get j := rfl
  have e3 : ((T.iT hn hv k : T0 n) : Amb n) = T.el.get k := rfl
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, e1, e2, e3, hjeq]
  group

theorem E1_sigma
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (X V : Set (T0 n)) (hX : x0T n ∈ X)
    (hdisj : Disjoint X V) (a : Tbl)
    (hXc : ∀ i, T.isInv i = true → ((T.reach a T.x0i).get i = true ↔ T.iT hn hv i ∈ X))
    (hVc : ∀ i, T.isInv i = true → ((T.reach a (T.vIE1 a)).get i = true ↔ T.iT hn hv i ∈ V))
    (hF1 : ∀ i j : Fin 64, T.isInv i = true → T.isInv j = true → T.mulT i j = T.mulT j i →
      i ≠ j → T.isInv (T.mulT i j) = true)
    (hx0inv : T.isInv T.x0i = true) (hx0c : ∀ i : Fin 64, T.mulT T.x0i i = T.mulT i T.x0i)
    (hP2 : ∀ i j : Fin 64, T.isInv i = true → T.isInv j = true →
      (T.reach a (T.vIE1 a)).get i = true → (T.reach a (T.vIE1 a)).get j = true →
      (T.reach a T.x0i).get (T.mulT T.x0i i) = true →
      (T.reach a T.x0i).get (T.mulT T.x0i j) = true → T.cls.get i = T.cls.get j) :
    ∀ s s' : T0 n, orderOf s = 2 → orderOf s' = 2 → s ∈ V → s' ∈ V → x0T n * s ∈ X →
      x0T n * s' ∈ X → ∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (s' : Amb n) := by
  have hne : ∀ y : T0 n, y ∈ V → y ≠ x0T n := fun y hyV hy =>
    Set.disjoint_left.1 hdisj hX (hy ▸ hyV)
  have key : ∀ i : Fin 64, orderOf (T.iT hn hv i) = 2 → T.iT hn hv i ∈ V →
      x0T n * T.iT hn hv i ∈ X → T.isInv i = true ∧ (T.reach a (T.vIE1 a)).get i = true ∧
        (T.reach a T.x0i).get (T.mulT T.x0i i) = true := by
    intro i hi hiV hxi
    have hinv : T.isInv i = true := T.isInv_of_orderOf_iTE1 hn hv hi
    have hne_i : i ≠ T.x0i := by
      intro h
      apply hne _ hiV
      rw [h, iT_x0]
    have hprod : T.isInv (T.mulT T.x0i i) = true :=
      hF1 T.x0i i hx0inv hinv (hx0c i) (Ne.symm hne_i)
    refine ⟨hinv, (hVc i hinv).2 hiV, (hXc _ hprod).2 ?_⟩
    rw [iT_mul, iT_x0]
    exact hxi
  intro s s' hs hs' hsV hs'V hxs hxs'
  obtain ⟨i, rfl⟩ := T.iT_surjective hn hv s
  obtain ⟨j, rfl⟩ := T.iT_surjective hn hv s'
  obtain ⟨hinv_i, hVi, hXi⟩ := key i hs hsV hxs
  obtain ⟨hinv_j, hVj, hXj⟩ := key j hs' hs'V hxs'
  obtain ⟨g, hg, hgc⟩ := exists_conj T hv hinv_i hinv_j (hP2 i j hinv_i hinv_j hVi hVj hXi hXj)
  exact ⟨g, hg, hgc⟩

end Tab

theorem model_E1_aux
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (T : Tab n) (hv : T.Valid)
    (hcB : T.claimB = true) (hc1 : T.claimG T.e1P1 = true) (hc2 : T.claimG T.e1P2 = true)
    (hc3 : T.claimG T.e1P3 = true) (hcov : T.cfCoverE1 = true)
    (hcf : (cfSetE1 n).card = if n = 6 then 64 else 192)
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
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V) :
    ∃ E : Subgroup (T0 n),
      (∀ t : T0 n, t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
        (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X))) ∧
      Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
      (∀ t : T0 n, ∀ e ∈ E, t * e * t⁻¹ ∈ E) ∧ (∀ e ∈ E, α e ∈ E) ∧
      (∀ g ∈ Fgrp n, g * ((vHat n α : T0 n) : Amb n) = ((vHat n α : T0 n) : Amb n) * g →
        ∀ e ∈ E, g * (e : Amb n) * g⁻¹ ∈ liftT n E) ∧
      (∀ s t : T0 n, orderOf s = 2 → orderOf t = 2 → s ∈ V → t ∈ V → x0T n * s ∈ X →
        x0T n * t ∈ X → ∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∧
      Nat.card (Hgrp n ((vHat n α : T0 n) : Amb n)) = (if n = 6 then 64 else 192) := by
  obtain ⟨_, -, hP1, hXc, hVc⟩ := T.facts_of_claimG hn hv hcB T.e1P1 hc1 α u X V hx hu hsq hext hX
    hV hdisj hclX hclV hQ
  obtain ⟨_, -, hP2, -, -⟩ := T.facts_of_claimG hn hv hcB T.e1P2 hc2 α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ
  obtain ⟨_, -, hP3, -, -⟩ := T.facts_of_claimG hn hv hcB T.e1P3 hc3 α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ
  have ha : ∀ i, T.iT hn hv ((T.tabOf hn hv α).get i) = α (T.iT hn hv i) :=
    T.iT_tabOf hn hv α
  have hclX' := Tab.edge_closed T hn hv α X hclX
  have hX0 := Tab.reach_sound T hn hv (T.tabOf hn hv α) X hclX' T.x0i
    (by rw [Tab.iT_x0]; exact hX)
  unfold Tab.e1P1 at hP1
  simp only [decide_eq_true_eq] at hP1
  obtain ⟨hF1, hx0inv, hx0c, hvinv, hvel, hmul, hsqE, hcardE, hnorm, hαE⟩ := hP1
  unfold Tab.e1P2 at hP2
  simp only [decide_eq_true_eq] at hP2
  unfold Tab.e1P3 at hP3
  simp only [List.all_eq_true, decide_eq_true_eq] at hP3
  have hE := T.eVecE1_iff hn hv α X _ ha hXc hX0 hF1 hvinv
  obtain ⟨E, hEmem, hEset, hcard, hcomm, hsq1, hnormE, hαstab⟩ :=
    T.E1_sub hn hv α X _ ha hE hmul hsqE hcardE hnorm hαE
  have hiv : T.iT hn hv (T.vIE1 (T.tabOf hn hv α)) = vHat n α := T.iT_vIE1 hn hv α _ ha
  have hvstd : ((vHat n α : T0 n) : Amb n) = vStdE1 n := by
    rw [← hiv]
    exact hvel
  refine ⟨E, fun x => (hEset x).trans Iff.rfl, hcard, hcomm, hsq1, hnormE, hαstab,
    T.E1_F hn hv α _ E hEmem hnormE hvstd (T.cfCoverE1_spec hcov) hP3,
    T.E1_sigma hn hv X V hX hdisj _ hXc hVc hF1 hx0inv hx0c hP2, ?_⟩
  rw [hvstd, card_Hgrp_vStdE1, hcf]

end CFSG.GH74.GLS.C3.Layer2.Model
