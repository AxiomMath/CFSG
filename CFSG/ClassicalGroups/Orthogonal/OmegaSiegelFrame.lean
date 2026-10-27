module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open QuadraticMap Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {Q : QuadraticForm K N}

structure IsListFrame (Q : QuadraticForm K N) (e f p p' : N) (w : ℕ → N) (k j₁ : ℕ) : Prop where
  e_sing : Q e = 0
  f_sing : Q f = 0
  p_sing : Q p = 0
  p'_sing : Q p' = 0
  ef : polar Q e f = 1
  pp' : polar Q p p' = 1
  ep : polar Q e p = 0
  ep' : polar Q e p' = 0
  fp : polar Q f p = 0
  fp' : polar Q f p' = 0
  w_sing : ∀ j < k, Q (w j) = 0
  w_ne : ∀ j < k, w j ≠ 0
  w_e : ∀ j < k, polar Q e (w j) = 0
  w_f : ∀ j < k, polar Q f (w j) = 0
  w_p : ∀ j < k, polar Q p (w j) = 0
  w_p' : ∀ j < k, polar Q p' (w j) = 0
  span : ∀ x, polar Q e x = 0 → polar Q f x = 0 → polar Q p x = 0 → polar Q p' x = 0 →
    x ∈ Submodule.span K (w '' Set.Iio k)
  pos : 0 < k
  j₁_lt : j₁ < k
  hyp : polar Q (w 0) (w j₁) = 1

@[expose] def IsCertified (Q : QuadraticForm K N) (w : ℕ → N) (j : ℕ) : Prop :=
  ∃ i < j, polar Q (w i) (w j) = 0 ∧ w i + w j ≠ 0

variable [CharP K 2] [FiniteDimensional K N]

omit [FiniteDimensional K N] in
private theorem polar_self_char_two (x : N) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

omit [CharP K 2] [FiniteDimensional K N] in
private theorem linearIndependent_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] {t g : ι → N}
    (h : ∀ i j, polar Q (t i) (g j) = if i = j then 1 else 0) : LinearIndependent K t := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have key : ∀ s : Finset ι, polar Q (∑ i ∈ s, c i • t i) (g j) =
      ∑ i ∈ s, c i * polar Q (t i) (g j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, polar_add_left, ih, polar_smul_left,
        smul_eq_mul]
  have h1 : ∑ i, c i * polar Q (t i) (g j) = 0 := by
    rw [← key, hc, polar_zero_left]
  simpa [h] using h1

omit [CharP K 2] [FiniteDimensional K N] in
private theorem perp4_span {T : Set N} {e f p p' : N}
    (hT : ∀ s ∈ T, polar Q e s = 0 ∧ polar Q f s = 0 ∧ polar Q p s = 0 ∧ polar Q p' s = 0) :
    ∀ s ∈ Submodule.span K T,
      polar Q e s = 0 ∧ polar Q f s = 0 ∧ polar Q p s = 0 ∧ polar Q p' s = 0 := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact hT x hx
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_add_right, hx.1, hy.1, add_zero]
    · rw [polar_add_right, hx.2.1, hy.2.1, add_zero]
    · rw [polar_add_right, hx.2.2.1, hy.2.2.1, add_zero]
    · rw [polar_add_right, hx.2.2.2, hy.2.2.2, add_zero]
  | smul a x _ hx =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_smul_right, hx.1, smul_zero]
    · rw [polar_smul_right, hx.2.1, smul_zero]
    · rw [polar_smul_right, hx.2.2.1, smul_zero]
    · rw [polar_smul_right, hx.2.2.2, smul_zero]

omit [FiniteDimensional K N] in
private theorem eq_zero_of_mem_span_pair4 {e f p p' a : N}
    (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1) (hep : polar Q e p = 0)
    (hep' : polar Q e p' = 0) (hfp : polar Q f p = 0) (hfp' : polar Q f p' = 0)
    (ha : a ∈ Submodule.span K ({e, f, p, p'} : Set N)) (h1 : polar Q e a = 0)
    (h2 : polar Q f a = 0) (h3 : polar Q p a = 0) (h4 : polar Q p' a = 0) : a = 0 := by
  obtain ⟨α, z1, hz1, rfl⟩ := Submodule.mem_span_insert.mp ha
  obtain ⟨β, z2, hz2, rfl⟩ := Submodule.mem_span_insert.mp hz1
  obtain ⟨γ, z3, hz3, rfl⟩ := Submodule.mem_span_insert.mp hz2
  obtain ⟨δ, rfl⟩ := Submodule.mem_span_singleton.mp hz3
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hpe : polar Q p e = 0 := by rw [polar_comm, hep]
  have hpe' : polar Q p' e = 0 := by rw [polar_comm, hep']
  have hpf : polar Q p f = 0 := by rw [polar_comm, hfp]
  have hpf' : polar Q p' f = 0 := by rw [polar_comm, hfp']
  have hp'p : polar Q p' p = 1 := by rw [polar_comm, hpp']
  simp only [polar_add_right, polar_smul_right, polar_self_char_two, hef, hpp', hfe, hpe, hpe',
    hpf, hpf', hp'p, hep, hep', hfp, hfp', smul_eq_mul, mul_one, mul_zero, zero_add,
    add_zero] at h1 h2 h3 h4
  subst h1 h2 h3 h4
  simp

omit [FiniteDimensional K N] in
private theorem mem_of_perp4_of_sup {S : Submodule K N} {e f p p' : N}
    (hS : ∀ s ∈ S, polar Q e s = 0 ∧ polar Q f s = 0 ∧ polar Q p s = 0 ∧ polar Q p' s = 0)
    (hsup : S ⊔ Submodule.span K ({e, f, p, p'} : Set N) = ⊤)
    (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1) (hep : polar Q e p = 0)
    (hep' : polar Q e p' = 0) (hfp : polar Q f p = 0) (hfp' : polar Q f p' = 0) {x : N}
    (h1 : polar Q e x = 0) (h2 : polar Q f x = 0) (h3 : polar Q p x = 0)
    (h4 : polar Q p' x = 0) : x ∈ S := by
  have hx : x ∈ S ⊔ Submodule.span K ({e, f, p, p'} : Set N) := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨s1, s2, s3, s4⟩ := hS s hs
  have ha0 : a = 0 := by
    refine eq_zero_of_mem_span_pair4 hef hpp' hep hep' hfp hfp' ha ?_ ?_ ?_ ?_
    · rwa [polar_add_right, s1, zero_add] at h1
    · rwa [polar_add_right, s2, zero_add] at h2
    · rwa [polar_add_right, s3, zero_add] at h3
    · rwa [polar_add_right, s4, zero_add] at h4
  rw [ha0, add_zero]
  exact hs

private theorem mem_span_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] {t g : ι → N}
    (hdual : ∀ i j, polar Q (t i) (g j) = if i = j then 1 else 0)
    (hcard : Fintype.card ι = finrank K N) {S : Submodule K N} {e f p p' : N}
    (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1) (hep : polar Q e p = 0)
    (hep' : polar Q e p' = 0) (hfp : polar Q f p = 0) (hfp' : polar Q f p' = 0)
    (hS : ∀ s ∈ S, polar Q e s = 0 ∧ polar Q f s = 0 ∧ polar Q p s = 0 ∧ polar Q p' s = 0)
    (hmem : ∀ i, t i ∈ S ⊔ Submodule.span K ({e, f, p, p'} : Set N)) {x : N}
    (h1 : polar Q e x = 0) (h2 : polar Q f x = 0) (h3 : polar Q p x = 0)
    (h4 : polar Q p' x = 0) : x ∈ S := by
  have htop : Submodule.span K (Set.range t) = ⊤ :=
    (linearIndependent_of_dual hdual).span_eq_top_of_card_eq_finrank' hcard
  have hsup : S ⊔ Submodule.span K ({e, f, p, p'} : Set N) = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  exact mem_of_perp4_of_sup hS hsup hef hpp' hep hep' hfp hfp' h1 h2 h3 h4

omit [CharP K 2] [FiniteDimensional K N] in
private theorem isCertified_of {w : ℕ → N} {i j : ℕ} (hij : i < j)
    (h1 : polar Q (w i) (w j) = 0) (z : N) (h2 : polar Q (w i) z + polar Q (w j) z ≠ 0) :
    IsCertified Q w j :=
  ⟨i, hij, h1, fun h => h2 (by rw [← polar_add_left, h, polar_zero_left])⟩

omit [FiniteDimensional K N] in
private theorem dual_pairs {n : ℕ} (Pn : ℕ → HypPair Q)
    (hPo : ∀ a b, a < n → b < n → a ≠ b → (Pn a).Orth (Pn b)) (i j : Fin n × Bool) :
    polar Q (if i.2 then (Pn i.1).e else (Pn i.1).f)
      (if j.2 then (Pn j.1).f else (Pn j.1).e) = if i = j then 1 else 0 := by
  obtain ⟨a, b⟩ := i
  obtain ⟨c, d⟩ := j
  by_cases hac : a = c
  · subst hac
    cases b <;> cases d <;> simp only [Prod.mk.injEq, and_false,
      Bool.false_eq_true, if_true, if_false, HypPair.polar_ef, HypPair.polar_fe,
      polar_self_char_two, Bool.true_eq_false]
  · have ho := hPo a c a.isLt c.isLt (fun h => hac (Fin.ext h))
    cases b <;> cases d <;> simp only [Prod.mk.injEq, hac, false_and, and_false, if_false,
      ho.ee, ho.ef, ho.fe, ho.ff, Bool.false_eq_true, Bool.true_eq_false, if_true]

private theorem isListFrame_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {e f p p' : N}
    {w : ℕ → N} {k j₁ : ℕ} (he : Q e = 0) (hf : Q f = 0) (hp : Q p = 0) (hp' : Q p' = 0)
    (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1) (hep : polar Q e p = 0)
    (hep' : polar Q e p' = 0) (hfp : polar Q f p = 0) (hfp' : polar Q f p' = 0)
    (hwQ : ∀ j, j < k → Q (w j) = 0) (hwne : ∀ j, j < k → w j ≠ 0)
    (hwperp : ∀ j, j < k → polar Q e (w j) = 0 ∧ polar Q f (w j) = 0 ∧
      polar Q p (w j) = 0 ∧ polar Q p' (w j) = 0)
    {t g : ι → N} (hdual : ∀ i j, polar Q (t i) (g j) = if i = j then 1 else 0)
    (hcard : Fintype.card ι = finrank K N)
    (hmem : ∀ i, t i ∈ Submodule.span K (w '' Set.Iio k) ⊔
      Submodule.span K ({e, f, p, p'} : Set N))
    (hk : 0 < k) (hj₁ : j₁ < k) (hyp : polar Q (w 0) (w j₁) = 1) :
    IsListFrame Q e f p p' w k j₁ :=
  { e_sing := he
    f_sing := hf
    p_sing := hp
    p'_sing := hp'
    ef := hef
    pp' := hpp'
    ep := hep
    ep' := hep'
    fp := hfp
    fp' := hfp'
    w_sing := hwQ
    w_ne := hwne
    w_e := fun j hj => (hwperp j hj).1
    w_f := fun j hj => (hwperp j hj).2.1
    w_p := fun j hj => (hwperp j hj).2.2.1
    w_p' := fun j hj => (hwperp j hj).2.2.2
    span := fun x h1 h2 h3 h4 =>
      mem_span_of_dual hdual hcard hef hpp' hep hep' hfp hfp'
        (perp4_span (fun s hs => by
          obtain ⟨j, hj, rfl⟩ := hs
          exact hwperp j (Set.mem_Iio.mp hj))) hmem h1 h2 h3 h4
    pos := hk
    j₁_lt := hj₁
    hyp := hyp }

omit [CharP K 2] [FiniteDimensional K N] in
private theorem chain_mem {n c L k : ℕ} {Pn : ℕ → HypPair Q} {w : ℕ → N}
    (hn : n = c + 2) (hL : L = 2 * c) (hLk : L ≤ k)
    (hwE : ∀ j, j < c → w j = (Pn (j + 2)).e)
    (hwF : ∀ j, c ≤ j → j < L → w j = (Pn (j - c + 2)).f) {a : ℕ} (ha2 : 2 ≤ a) (han : a < n) :
    (Pn a).e ∈ Submodule.span K (w '' Set.Iio k) ∧
      (Pn a).f ∈ Submodule.span K (w '' Set.Iio k) := by
  constructor
  · have h := hwE (a - 2) (by omega)
    rw [show a - 2 + 2 = a by omega] at h
    rw [← h]
    exact Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by omega)))
  · have h := hwF (a - 2 + c) (by omega) (by omega)
    rw [show a - 2 + c - c + 2 = a by omega] at h
    rw [← h]
    exact Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by omega)))

omit [CharP K 2] [FiniteDimensional K N] in
private theorem chain_basis_mem {n c L k : ℕ} {Pn : ℕ → HypPair Q} {w : ℕ → N}
    (hn : n = c + 2) (hL : L = 2 * c) (hLk : L ≤ k)
    (hwE : ∀ j, j < c → w j = (Pn (j + 2)).e)
    (hwF : ∀ j, c ≤ j → j < L → w j = (Pn (j - c + 2)).f) (i : Fin n × Bool) :
    (if i.2 then (Pn i.1).e else (Pn i.1).f) ∈ Submodule.span K (w '' Set.Iio k) ⊔
      Submodule.span K ({(Pn 0).e, (Pn 0).f, (Pn 1).e, (Pn 1).f} : Set N) := by
  obtain ⟨⟨a, ha⟩, b⟩ := i
  by_cases ha2 : 2 ≤ a
  · obtain ⟨h1, h2⟩ := chain_mem hn hL hLk hwE hwF ha2 ha
    cases b
    · exact Submodule.mem_sup_left h2
    · exact Submodule.mem_sup_left h1
  · obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    · cases b <;> exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    · cases b <;> exact Submodule.mem_sup_right (Submodule.subset_span (by simp))

omit [CharP K 2] [FiniteDimensional K N] in
private theorem chain_certified {n c L : ℕ} {Pn : ℕ → HypPair Q}
    (hPo : ∀ a b, a < n → b < n → a ≠ b → (Pn a).Orth (Pn b)) {w : ℕ → N}
    (hn : n = c + 2) (hL : L = 2 * c) (hc : 2 ≤ c)
    (hwE : ∀ j, j < c → w j = (Pn (j + 2)).e)
    (hwF : ∀ j, c ≤ j → j < L → w j = (Pn (j - c + 2)).f) :
    ∀ j, 0 < j → j < L → IsCertified Q w j := by
  intro j hj0 hj
  have h0 : w 0 = (Pn 2).e := hwE 0 (by omega)
  by_cases h1 : j < c
  · refine isCertified_of (i := 0) (by omega) ?_ (Pn (j + 2)).f ?_
    · rw [h0, hwE j h1]
      exact (hPo 2 (j + 2) (by omega) (by omega) (by omega)).ee
    · rw [h0, hwE j h1, (hPo 2 (j + 2) (by omega) (by omega) (by omega)).ef,
        (Pn (j + 2)).polar_ef]
      simp
  · by_cases hj2 : j = c
    · have h1' : w 1 = (Pn 3).e := hwE 1 (by omega)
      have hj' : w j = (Pn 2).f := by
        have h := hwF j (by omega) hj
        rwa [show j - c + 2 = 2 by omega] at h
      refine isCertified_of (i := 1) (by omega) ?_ (Pn 3).f ?_
      · rw [h1', hj']
        exact (hPo 3 2 (by omega) (by omega) (by omega)).ef
      · rw [h1', hj', (Pn 3).polar_ef, (hPo 2 3 (by omega) (by omega) (by omega)).ff]
        simp
    · have hwj : w j = (Pn (j - c + 2)).f := hwF j (by omega) hj
      refine isCertified_of (i := 0) (by omega) ?_ (Pn (j - c + 2)).e ?_
      · rw [h0, hwj]
        exact (hPo 2 (j - c + 2) (by omega) (by omega) (by omega)).ef
      · rw [h0, hwj, (hPo 2 (j - c + 2) (by omega) (by omega) (by omega)).ee,
          (Pn (j - c + 2)).polar_fe]
        simp

omit [CharP K 2] [FiniteDimensional K N] in
private theorem perp_e_of_pair {n : ℕ} (Pn : ℕ → HypPair Q)
    (hPo : ∀ a b, a < n → b < n → a ≠ b → (Pn a).Orth (Pn b)) {r : ℕ} (h2 : 2 ≤ r)
    (hr : r < n) : polar Q (Pn 0).e (Pn r).e = 0 ∧ polar Q (Pn 0).f (Pn r).e = 0 ∧
      polar Q (Pn 1).e (Pn r).e = 0 ∧ polar Q (Pn 1).f (Pn r).e = 0 := by
  have h0 := hPo 0 r (by omega) hr (by omega)
  have h1 := hPo 1 r (by omega) hr (by omega)
  exact ⟨h0.ee, h0.fe, h1.ee, h1.fe⟩

omit [CharP K 2] [FiniteDimensional K N] in
private theorem perp_f_of_pair {n : ℕ} (Pn : ℕ → HypPair Q)
    (hPo : ∀ a b, a < n → b < n → a ≠ b → (Pn a).Orth (Pn b)) {r : ℕ} (h2 : 2 ≤ r)
    (hr : r < n) : polar Q (Pn 0).e (Pn r).f = 0 ∧ polar Q (Pn 0).f (Pn r).f = 0 ∧
      polar Q (Pn 1).e (Pn r).f = 0 ∧ polar Q (Pn 1).f (Pn r).f = 0 := by
  have h0 := hPo 0 r (by omega) hr (by omega)
  have h1 := hPo 1 r (by omega) hr (by omega)
  exact ⟨h0.ef, h0.ff, h1.ef, h1.ff⟩

theorem exists_listFrame_plus {m : ℕ} (hdim : finrank K N = 2 * m) (hm : 4 ≤ m)
    (P : Fin m → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∃ e f p p' : N, ∃ w : ℕ → N, ∃ j₁ : ℕ, IsListFrame Q e f p p' w (2 * m - 4) j₁ ∧
      ∀ j, 0 < j → j < 2 * m - 4 → IsCertified Q w j := by
  obtain ⟨Pn, hPn⟩ : ∃ Pn : ℕ → HypPair Q, ∀ r (h : r < m), Pn r = P ⟨r, h⟩ :=
    ⟨fun r => if h : r < m then P ⟨r, h⟩ else P ⟨0, by omega⟩, fun r h => by simp [h]⟩
  have hPo : ∀ a b, a < m → b < m → a ≠ b → (Pn a).Orth (Pn b) := fun a b ha hb hab => by
    rw [hPn a ha, hPn b hb]
    exact hP _ _ (fun h => hab (congrArg Fin.val h))
  obtain ⟨w, hwE, hwF⟩ : ∃ w : ℕ → N, (∀ j, j < m - 2 → w j = (Pn (j + 2)).e) ∧
      (∀ j, m - 2 ≤ j → j < 2 * m - 4 → w j = (Pn (j - (m - 2) + 2)).f) :=
    ⟨fun j => if j < m - 2 then (Pn (j + 2)).e
        else if j < 2 * m - 4 then (Pn (j - (m - 2) + 2)).f else 0,
      fun j h => by simp [h],
      fun j h1 h2 => by simp [show ¬ j < m - 2 by omega, h2]⟩
  have hwperp : ∀ j, j < 2 * m - 4 → polar Q (Pn 0).e (w j) = 0 ∧
      polar Q (Pn 0).f (w j) = 0 ∧ polar Q (Pn 1).e (w j) = 0 ∧ polar Q (Pn 1).f (w j) = 0 := by
    intro j hj
    by_cases h1 : j < m - 2
    · rw [hwE j h1]; exact perp_e_of_pair Pn hPo (by omega) (by omega)
    · rw [hwF j (by omega) hj]; exact perp_f_of_pair Pn hPo (by omega) (by omega)
  have hwQ : ∀ j, j < 2 * m - 4 → Q (w j) = 0 := by
    intro j hj
    by_cases h1 : j < m - 2
    · rw [hwE j h1]; exact (Pn (j + 2)).Q_e
    · rw [hwF j (by omega) hj]; exact (Pn (j - (m - 2) + 2)).Q_f
  have hwne : ∀ j, j < 2 * m - 4 → w j ≠ 0 := by
    intro j hj
    by_cases h1 : j < m - 2
    · rw [hwE j h1]; exact (Pn (j + 2)).e_ne_zero
    · rw [hwF j (by omega) hj]; exact (Pn (j - (m - 2) + 2)).f_ne_zero
  have hcard : Fintype.card (Fin m × Bool) = finrank K N := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hdim]
    ring
  have hyp : polar Q (w 0) (w (m - 2)) = 1 := by
    have h0 : w 0 = (Pn 2).e := hwE 0 (by omega)
    have h2 : w (m - 2) = (Pn 2).f := by
      have h := hwF (m - 2) le_rfl (by omega)
      rwa [show m - 2 - (m - 2) + 2 = 2 by omega] at h
    rw [h0, h2]
    exact (Pn 2).polar_ef
  have h01 := hPo 0 1 (by omega) (by omega) (by omega)
  exact ⟨(Pn 0).e, (Pn 0).f, (Pn 1).e, (Pn 1).f, w, m - 2,
    isListFrame_of_basis (Pn 0).Q_e (Pn 0).Q_f (Pn 1).Q_e (Pn 1).Q_f (Pn 0).polar_ef
      (Pn 1).polar_ef h01.ee h01.ef h01.fe h01.ff hwQ hwne hwperp (dual_pairs Pn hPo) hcard
      (chain_basis_mem (n := m) (c := m - 2) (L := 2 * m - 4) (k := 2 * m - 4) (by omega)
        (by omega) (by omega) hwE hwF) (by omega) (by omega) hyp,
    fun j hj0 hj => chain_certified hPo (by omega) (by omega) (by omega) hwE hwF j hj0 hj⟩

omit [FiniteDimensional K N] in
private theorem minus_new_vectors {e₂ f₂ u v : N} (he₂ : Q e₂ = 0) (hf₂ : Q f₂ = 0)
    (hef₂ : polar Q e₂ f₂ = 1) (heu : polar Q e₂ u = 0) (hfu : polar Q f₂ u = 0)
    (hev : polar Q e₂ v = 0) (hfv : polar Q f₂ v = 0) (hQu : Q u = 1) (hpuv : polar Q u v ≠ 0) :
    Q (e₂ + u + f₂) = 0 ∧ Q (e₂ + v + Q v • f₂) = 0 ∧ e₂ + u + f₂ ≠ 0 ∧
      e₂ + v + Q v • f₂ ≠ 0 := by
  have huf : polar Q u f₂ = 0 := by rw [polar_comm]; exact hfu
  have hvf : polar Q v f₂ = 0 := by rw [polar_comm]; exact hfv
  have hvu : polar Q v u = polar Q u v := polar_comm Q v u
  have hAQ : Q (e₂ + u + f₂) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, he₂, hf₂, hQu, polar_add_left, heu,
      hef₂, huf]
    simp only [zero_add, add_zero]
    exact CharTwo.add_self_eq_zero 1
  have hBQ : Q (e₂ + v + Q v • f₂) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul Q, he₂, hf₂,
      polar_smul_right, polar_add_left, hev, hef₂, hvf]
    simp only [zero_add, add_zero, smul_eq_mul, mul_one, mul_zero]
    exact CharTwo.add_self_eq_zero (Q v)
  have hAne : e₂ + u + f₂ ≠ 0 := by
    intro h
    have key : polar Q (e₂ + u + f₂) ((polar Q u v)⁻¹ • v) = 1 := by
      rw [polar_smul_right, polar_add_left, polar_add_left, hev, hfv, zero_add, add_zero,
        smul_eq_mul, inv_mul_cancel₀ hpuv]
    rw [h, polar_zero_left] at key
    exact zero_ne_one key
  have hBne : e₂ + v + Q v • f₂ ≠ 0 := by
    intro h
    have key : polar Q (e₂ + v + Q v • f₂) ((polar Q u v)⁻¹ • u) = 1 := by
      simp only [polar_smul_right, polar_add_left, polar_smul_left, heu, hvu, hfu, smul_eq_mul,
        zero_add, add_zero, mul_zero, inv_mul_cancel₀ hpuv]
    rw [h, polar_zero_left] at key
    exact zero_ne_one key
  exact ⟨hAQ, hBQ, hAne, hBne⟩

omit [CharP K 2] [FiniteDimensional K N] in
private theorem exists_minus_list {m : ℕ} (hm : 5 ≤ m) (Pn : ℕ → HypPair Q) (u v : N) :
    ∃ w : ℕ → N, (∀ j, j < m - 3 → w j = (Pn (j + 2)).e) ∧
      (∀ j, m - 3 ≤ j → j < 2 * m - 6 → w j = (Pn (j - (m - 3) + 2)).f) ∧
      w (2 * m - 6) = (Pn 2).e + u + (Pn 2).f ∧
      w (2 * m - 5) = (Pn 2).e + v + Q v • (Pn 2).f := by
  refine ⟨fun j => if j < m - 3 then (Pn (j + 2)).e
    else if j < 2 * m - 6 then (Pn (j - (m - 3) + 2)).f
    else if j = 2 * m - 6 then (Pn 2).e + u + (Pn 2).f
    else (Pn 2).e + v + Q v • (Pn 2).f, ?_, ?_, ?_, ?_⟩
  · intro j h; simp [h]
  · intro j h1 h2; simp [show ¬ j < m - 3 by omega, h2]
  · simp [show ¬ (2 * m - 6 < m - 3) by omega]
  · simp [show ¬ (2 * m - 5 < m - 3) by omega, show ¬ (2 * m - 5 < 2 * m - 6) by omega,
      show ¬ (2 * m - 5 = 2 * m - 6) by omega]

omit [CharP K 2] [FiniteDimensional K N] in
private theorem perp_new_of {e₂ f₂ u v x : N} (h1 : polar Q x e₂ = 0) (h2 : polar Q x f₂ = 0)
    (hu : polar Q x u = 0) (hv : polar Q x v = 0) :
    polar Q x (e₂ + u + f₂) = 0 ∧ polar Q x (e₂ + v + Q v • f₂) = 0 := by
  constructor
  · simp only [polar_add_right, h1, h2, hu, add_zero]
  · simp only [polar_add_right, polar_smul_right, h1, h2, hv, smul_zero, add_zero]

omit [CharP K 2] [FiniteDimensional K N] in
private theorem perp_new_right {e₂ f₂ u v y : N} (h1 : polar Q e₂ y = 0) (h2 : polar Q f₂ y = 0)
    (hu : polar Q u y = 0) (hv : polar Q v y = 0) :
    polar Q (e₂ + u + f₂) y = 0 ∧ polar Q (e₂ + v + Q v • f₂) y = 0 := by
  constructor
  · simp only [polar_add_left, h1, h2, hu, add_zero]
  · simp only [polar_add_left, polar_smul_left, h1, h2, hv, smul_zero, add_zero]

omit [CharP K 2] [FiniteDimensional K N] in
private theorem cert_of_perp_pair {w : ℕ → N} {i j : ℕ} {a b x : N} (hij : i < j)
    (hwi : w i = a) (hwj : w j = x) (hx : polar Q a x = 0) (hab : polar Q a b = 1)
    (hxb : polar Q x b = 0) : IsCertified Q w j :=
  isCertified_of hij (by rw [hwi, hwj]; exact hx) b
    (by rw [hwi, hwj, hab, hxb, add_zero]; exact one_ne_zero)

omit [FiniteDimensional K N] in
private theorem minus_dual {n : ℕ} (Pn : ℕ → HypPair Q)
    (hPo : ∀ a b, a < n → b < n → a ≠ b → (Pn a).Orth (Pn b)) {u v : N}
    (huP : ∀ r, r < n → polar Q (Pn r).e u = 0 ∧ polar Q (Pn r).f u = 0 ∧
      polar Q (Pn r).e v = 0 ∧ polar Q (Pn r).f v = 0) (hpuv : polar Q u v ≠ 0) :
    ∀ i j : (Fin n × Bool) ⊕ Bool,
      polar Q (Sum.elim (fun k : Fin n × Bool => if k.2 then (Pn k.1).e else (Pn k.1).f)
        (fun b : Bool => if b then v else u) i)
        (Sum.elim (fun k : Fin n × Bool => if k.2 then (Pn k.1).f else (Pn k.1).e)
          (fun b : Bool => if b then (polar Q u v)⁻¹ • u else (polar Q u v)⁻¹ • v) j) =
      if i = j then 1 else 0 := by
  rintro (⟨a, b⟩ | b) (⟨c, d⟩ | d)
  · simpa using dual_pairs Pn hPo (a, b) (c, d)
  · have ha := huP (a : ℕ) a.2
    cases b <;> cases d <;> simp [polar_smul_right, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
  · have hc := huP (c : ℕ) c.2
    rw [polar_comm]
    cases b <;> cases d <;> simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  · cases b <;> cases d
    · show polar Q u ((polar Q u v)⁻¹ • v) =
        if (Sum.inr false : (Fin n × Bool) ⊕ Bool) = Sum.inr false then 1 else 0
      rw [if_pos rfl, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hpuv]
    · show polar Q u ((polar Q u v)⁻¹ • u) =
        if (Sum.inr false : (Fin n × Bool) ⊕ Bool) = Sum.inr true then 1 else 0
      rw [if_neg (by simp), polar_smul_right, polar_self_char_two, smul_zero]
    · show polar Q v ((polar Q u v)⁻¹ • v) =
        if (Sum.inr true : (Fin n × Bool) ⊕ Bool) = Sum.inr false then 1 else 0
      rw [if_neg (by simp), polar_smul_right, polar_self_char_two, smul_zero]
    · show polar Q v ((polar Q u v)⁻¹ • u) =
        if (Sum.inr true : (Fin n × Bool) ⊕ Bool) = Sum.inr true then 1 else 0
      rw [if_pos rfl, polar_smul_right, polar_comm Q v u, smul_eq_mul, inv_mul_cancel₀ hpuv]

omit [FiniteDimensional K N] in
private theorem minus_list_props {m : ℕ} (hm : 5 ≤ m) {Pn : ℕ → HypPair Q}
    (hPo : ∀ a b, a < m - 1 → b < m - 1 → a ≠ b → (Pn a).Orth (Pn b)) {u v : N}
    (huP : ∀ r, r < m - 1 → polar Q (Pn r).e u = 0 ∧ polar Q (Pn r).f u = 0 ∧
      polar Q (Pn r).e v = 0 ∧ polar Q (Pn r).f v = 0)
    (hQu : Q u = 1) (hpuv : polar Q u v ≠ 0) {w : ℕ → N}
    (hwE : ∀ j, j < m - 3 → w j = (Pn (j + 2)).e)
    (hwF : ∀ j, m - 3 ≤ j → j < 2 * m - 6 → w j = (Pn (j - (m - 3) + 2)).f)
    (hwA : w (2 * m - 6) = (Pn 2).e + u + (Pn 2).f)
    (hwB : w (2 * m - 5) = (Pn 2).e + v + Q v • (Pn 2).f) :
    (∀ j, j < 2 * m - 4 → polar Q (Pn 0).e (w j) = 0 ∧ polar Q (Pn 0).f (w j) = 0 ∧
      polar Q (Pn 1).e (w j) = 0 ∧ polar Q (Pn 1).f (w j) = 0) ∧
    (∀ j, j < 2 * m - 4 → Q (w j) = 0) ∧ (∀ j, j < 2 * m - 4 → w j ≠ 0) := by
  have k02 := hPo 0 2 (by omega) (by omega) (by omega)
  have k12 := hPo 1 2 (by omega) (by omega) (by omega)
  have u0 := huP 0 (by omega)
  have u1 := huP 1 (by omega)
  have u2 := huP 2 (by omega)
  have hAB := minus_new_vectors (Pn 2).Q_e (Pn 2).Q_f (Pn 2).polar_ef u2.1 u2.2.1 u2.2.2.1
    u2.2.2.2 hQu hpuv
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases hj1 : j < m - 3
    · rw [hwE j hj1]; exact perp_e_of_pair Pn hPo (by omega) (by omega)
    · by_cases hj2 : j < 2 * m - 6
      · rw [hwF j (by omega) hj2]; exact perp_f_of_pair Pn hPo (by omega) (by omega)
      · by_cases hj3 : j = 2 * m - 6
        · rw [hj3, hwA]
          exact ⟨(perp_new_of k02.ee k02.ef u0.1 u0.2.2.1).1,
            (perp_new_of k02.fe k02.ff u0.2.1 u0.2.2.2).1,
            (perp_new_of k12.ee k12.ef u1.1 u1.2.2.1).1,
            (perp_new_of k12.fe k12.ff u1.2.1 u1.2.2.2).1⟩
        · rw [show j = 2 * m - 5 by omega, hwB]
          exact ⟨(perp_new_of k02.ee k02.ef u0.1 u0.2.2.1).2,
            (perp_new_of k02.fe k02.ff u0.2.1 u0.2.2.2).2,
            (perp_new_of k12.ee k12.ef u1.1 u1.2.2.1).2,
            (perp_new_of k12.fe k12.ff u1.2.1 u1.2.2.2).2⟩
  · intro j hj
    by_cases hj1 : j < m - 3
    · rw [hwE j hj1]; exact (Pn (j + 2)).Q_e
    · by_cases hj2 : j < 2 * m - 6
      · rw [hwF j (by omega) hj2]; exact (Pn (j - (m - 3) + 2)).Q_f
      · by_cases hj3 : j = 2 * m - 6
        · rw [hj3, hwA]; exact hAB.1
        · rw [show j = 2 * m - 5 by omega, hwB]; exact hAB.2.1
  · intro j hj
    by_cases hj1 : j < m - 3
    · rw [hwE j hj1]; exact (Pn (j + 2)).e_ne_zero
    · by_cases hj2 : j < 2 * m - 6
      · rw [hwF j (by omega) hj2]; exact (Pn (j - (m - 3) + 2)).f_ne_zero
      · by_cases hj3 : j = 2 * m - 6
        · rw [hj3, hwA]; exact hAB.2.2.1
        · rw [show j = 2 * m - 5 by omega, hwB]; exact hAB.2.2.2

omit [CharP K 2] [FiniteDimensional K N] in
private theorem minus_basis_mem {m : ℕ} (hm : 5 ≤ m) {Pn : ℕ → HypPair Q} {u v : N}
    {w : ℕ → N} (hwE : ∀ j, j < m - 3 → w j = (Pn (j + 2)).e)
    (hwF : ∀ j, m - 3 ≤ j → j < 2 * m - 6 → w j = (Pn (j - (m - 3) + 2)).f)
    (hwA : w (2 * m - 6) = (Pn 2).e + u + (Pn 2).f)
    (hwB : w (2 * m - 5) = (Pn 2).e + v + Q v • (Pn 2).f) :
    ∀ i : (Fin (m - 1) × Bool) ⊕ Bool,
      Sum.elim (fun k : Fin (m - 1) × Bool => if k.2 then (Pn k.1).e else (Pn k.1).f)
        (fun b : Bool => if b then v else u) i ∈
        Submodule.span K (w '' Set.Iio (2 * m - 4)) ⊔
          Submodule.span K ({(Pn 0).e, (Pn 0).f, (Pn 1).e, (Pn 1).f} : Set N) := by
  have h0 : w 0 = (Pn 2).e := hwE 0 (by omega)
  have hf2 : w (m - 3) = (Pn 2).f := by
    have h := hwF (m - 3) le_rfl (by omega)
    rwa [show m - 3 - (m - 3) + 2 = 2 by omega] at h
  set S := Submodule.span K (w '' Set.Iio (2 * m - 4)) with hSdef
  have hw0S : w 0 ∈ S :=
    Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by omega)))
  have hf2S : w (m - 3) ∈ S :=
    Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by omega)))
  have hAS : w (2 * m - 6) ∈ S :=
    Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by omega)))
  have hBS : w (2 * m - 5) ∈ S :=
    Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by omega)))
  have hu_S : u ∈ S := by
    have h := S.sub_mem (S.sub_mem hAS hw0S) hf2S
    rwa [show w (2 * m - 6) - w 0 - w (m - 3) = u by rw [hwA, h0, hf2]; abel] at h
  have hv_S : v ∈ S := by
    have h := S.sub_mem (S.sub_mem hBS hw0S) (S.smul_mem (Q v) hf2S)
    rwa [show w (2 * m - 5) - w 0 - Q v • w (m - 3) = v by rw [hwB, h0, hf2]; abel] at h
  rintro (i | b)
  · exact chain_basis_mem (n := m - 1) (c := m - 3) (L := 2 * m - 6) (k := 2 * m - 4)
      (by omega) (by omega) (by omega) hwE hwF i
  · cases b
    · exact Submodule.mem_sup_left hu_S
    · exact Submodule.mem_sup_left hv_S

theorem exists_listFrame_minus {m : ℕ} (hdim : finrank K N = 2 * m) (hm : 5 ≤ m)
    (P : Fin (m - 1) → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u v : N}
    (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hQu : Q u = 1) (hpuv : polar Q u v ≠ 0) :
    ∃ e f p p' : N, ∃ w : ℕ → N, ∃ j₁ : ℕ, IsListFrame Q e f p p' w (2 * m - 4) j₁ ∧
      ∀ j, 0 < j → j < 2 * m - 4 → IsCertified Q w j := by
  obtain ⟨Pn, hPn⟩ : ∃ Pn : ℕ → HypPair Q, ∀ r (h : r < m - 1), Pn r = P ⟨r, h⟩ :=
    ⟨fun r => if h : r < m - 1 then P ⟨r, h⟩ else P ⟨0, by omega⟩, fun r h => by simp [h]⟩
  have hPo : ∀ a b, a < m - 1 → b < m - 1 → a ≠ b → (Pn a).Orth (Pn b) := fun a b ha hb hab => by
    rw [hPn a ha, hPn b hb]
    exact hP _ _ (fun h => hab (congrArg Fin.val h))
  have huP : ∀ r, r < m - 1 → polar Q (Pn r).e u = 0 ∧ polar Q (Pn r).f u = 0 ∧
      polar Q (Pn r).e v = 0 ∧ polar Q (Pn r).f v = 0 := by
    intro r hr
    rw [hPn r hr]
    obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp (huv ⟨r, hr⟩).1
    obtain ⟨h3, h4⟩ := HypPair.mem_perp.mp (huv ⟨r, hr⟩).2
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨w, hwE, hwF, hwA, hwB⟩ := exists_minus_list hm Pn u v
  obtain ⟨hwperp, hwQ, hwne⟩ := minus_list_props hm hPo huP hQu hpuv hwE hwF hwA hwB
  have h01 := hPo 0 1 (by omega) (by omega) (by omega)
  have h0 : w 0 = (Pn 2).e := hwE 0 (by omega)
  have h1 : w 1 = (Pn 3).e := hwE 1 (by omega)
  have hf2 : w (m - 3) = (Pn 2).f := by
    have h := hwF (m - 3) le_rfl (by omega)
    rwa [show m - 3 - (m - 3) + 2 = 2 by omega] at h
  have hcard : Fintype.card ((Fin (m - 1) × Bool) ⊕ Bool) = finrank K N := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hdim]
    omega
  have hyp : polar Q (w 0) (w (m - 3)) = 1 := by
    rw [h0, hf2]
    exact (Pn 2).polar_ef
  refine ⟨(Pn 0).e, (Pn 0).f, (Pn 1).e, (Pn 1).f, w, m - 3,
    isListFrame_of_basis (Pn 0).Q_e (Pn 0).Q_f (Pn 1).Q_e (Pn 1).Q_f (Pn 0).polar_ef
      (Pn 1).polar_ef h01.ee h01.ef h01.fe h01.ff hwQ hwne hwperp
      (minus_dual Pn hPo huP hpuv) hcard (minus_basis_mem hm hwE hwF hwA hwB) (by omega)
      (by omega) hyp, ?_⟩
  have k23 := hPo 2 3 (by omega) (by omega) (by omega)
  have k30 := hPo 3 2 (by omega) (by omega) (by omega)
  have u3 := huP 3 (by omega)
  have hu3f : polar Q u (Pn 3).f = 0 := by rw [polar_comm]; exact u3.2.1
  have hv3f : polar Q v (Pn 3).f = 0 := by rw [polar_comm]; exact u3.2.2.2
  intro j hj0 hj
  by_cases hjL : j < 2 * m - 6
  · exact chain_certified hPo (by omega) (by omega) (by omega) hwE hwF j hj0 hjL
  · by_cases hA : j = 2 * m - 6
    · exact cert_of_perp_pair (by omega) h1 (by rw [hA]; exact hwA)
        (perp_new_of k30.ee k30.ef u3.1 u3.2.2.1).1 (Pn 3).polar_ef
        (perp_new_right k23.ef k23.ff hu3f hv3f).1
    · exact cert_of_perp_pair (by omega) h1 (by rw [show j = 2 * m - 5 by omega]; exact hwB)
        (perp_new_of k30.ee k30.ef u3.1 u3.2.2.1).2 (Pn 3).polar_ef
        (perp_new_right k23.ef k23.ff hu3f hv3f).2

theorem exists_listFrame_three (hdim : finrank K N = 2 * 3) (P : Fin 3 → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∃ e f p p' : N, ∃ w : ℕ → N, ∃ j₁ : ℕ, IsListFrame Q e f p p' w 2 j₁ := by
  obtain ⟨Pn, hPn⟩ : ∃ Pn : ℕ → HypPair Q, ∀ r (h : r < 3), Pn r = P ⟨r, h⟩ :=
    ⟨fun r => if h : r < 3 then P ⟨r, h⟩ else P ⟨0, by omega⟩, fun r h => by simp [h]⟩
  have hPo : ∀ a b, a < 3 → b < 3 → a ≠ b → (Pn a).Orth (Pn b) := fun a b ha hb hab => by
    rw [hPn a ha, hPn b hb]
    exact hP _ _ (fun h => hab (congrArg Fin.val h))
  obtain ⟨w, hw0, hw1⟩ : ∃ w : ℕ → N, w 0 = (Pn 2).e ∧ w 1 = (Pn 2).f :=
    ⟨fun j => if j = 0 then (Pn 2).e else (Pn 2).f, by simp, by simp⟩
  have h01 := hPo 0 1 (by omega) (by omega) (by omega)
  have h02 := hPo 0 2 (by omega) (by omega) (by omega)
  have h12 := hPo 1 2 (by omega) (by omega) (by omega)
  have hwperp : ∀ j, j < 2 → polar Q (Pn 0).e (w j) = 0 ∧ polar Q (Pn 0).f (w j) = 0 ∧
      polar Q (Pn 1).e (w j) = 0 ∧ polar Q (Pn 1).f (w j) = 0 := by
    intro j hj
    interval_cases j
    · rw [hw0]; exact ⟨h02.ee, h02.fe, h12.ee, h12.fe⟩
    · rw [hw1]; exact ⟨h02.ef, h02.ff, h12.ef, h12.ff⟩
  have hwQ : ∀ j, j < 2 → Q (w j) = 0 := by
    intro j hj
    interval_cases j
    · rw [hw0]; exact (Pn 2).Q_e
    · rw [hw1]; exact (Pn 2).Q_f
  have hwne : ∀ j, j < 2 → w j ≠ 0 := by
    intro j hj
    interval_cases j
    · rw [hw0]; exact (Pn 2).e_ne_zero
    · rw [hw1]; exact (Pn 2).f_ne_zero
  set S := Submodule.span K (w '' Set.Iio 2) with hSdef
  have hwS0 : (Pn 2).e ∈ S := by
    rw [← hw0]
    exact Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by norm_num)))
  have hwS1 : (Pn 2).f ∈ S := by
    rw [← hw1]
    exact Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr (by norm_num)))
  have hmemT : ∀ i : Fin 3 × Bool,
      (if i.2 then (Pn i.1).e else (Pn i.1).f) ∈
        S ⊔ Submodule.span K ({(Pn 0).e, (Pn 0).f, (Pn 1).e, (Pn 1).f} : Set N) := by
    rintro ⟨⟨a, ha⟩, b⟩
    by_cases ha2 : a < 2
    · obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
      · cases b <;> exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
      · cases b <;> exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    · obtain rfl : a = 2 := by omega
      cases b
      · exact Submodule.mem_sup_left hwS1
      · exact Submodule.mem_sup_left hwS0
  have hcard : Fintype.card (Fin 3 × Bool) = finrank K N := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hdim]
  refine ⟨(Pn 0).e, (Pn 0).f, (Pn 1).e, (Pn 1).f, w, 1, ?_⟩
  exact isListFrame_of_basis (Pn 0).Q_e (Pn 0).Q_f (Pn 1).Q_e (Pn 1).Q_f (Pn 0).polar_ef
    (Pn 1).polar_ef h01.ee h01.ef h01.fe h01.ff hwQ hwne hwperp (dual_pairs Pn hPo) hcard
    hmemT (by norm_num) (by norm_num) (by rw [hw0, hw1]; exact (Pn 2).polar_ef)

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
