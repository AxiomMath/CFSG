module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.QuasithinUnique.A5.Delta5

open CFSG.QuasithinUnique Equiv

@[expose] def pact (σ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 := fun i => x (σ⁻¹ i)

theorem pact_one (x : Fin 5 → ZMod 2) : pact 1 x = x := rfl

theorem pact_mul (σ τ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) :
    pact (σ * τ) x = pact σ (pact τ x) := by
  funext i
  simp [pact, mul_inv_rev]

theorem pact_add (σ : Perm (Fin 5)) (x y : Fin 5 → ZMod 2) :
    pact σ (x + y) = pact σ x + pact σ y := by
  funext i
  simp [pact]

theorem pact_mem (σ : Perm (Fin 5)) {x : Fin 5 → ZMod 2} (hx : x ∈ evenWeight 5) :
    pact σ x ∈ evenWeight 5 := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, x (σ⁻¹ i) = 0
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

@[expose] def vact (σ : Perm (Fin 5)) (w : evenWeight 5) : evenWeight 5 :=
  ⟨pact σ w.1, pact_mem σ w.2⟩

theorem vact_one (w : evenWeight 5) : vact 1 w = w := rfl

theorem vact_mul (σ τ : Perm (Fin 5)) (w : evenWeight 5) :
    vact (σ * τ) w = vact σ (vact τ w) :=
  Subtype.ext (pact_mul σ τ w.1)

theorem vact_add (σ : Perm (Fin 5)) (x y : evenWeight 5) :
    vact σ (x + y) = vact σ x + vact σ y :=
  Subtype.ext (pact_add σ x.1 y.1)

@[expose] def isEven (x : Fin 5 → ZMod 2) : Prop := ∑ i, x i = 0

instance : DecidablePred isEven := fun x => by unfold isEven; infer_instance

theorem mem_evenWeight_iff (x : Fin 5 → ZMod 2) : x ∈ evenWeight 5 ↔ isEven x := Iff.rfl

theorem pact_faithful : ∀ σ : Perm (Fin 5),
    (∀ x : Fin 5 → ZMod 2, isEven x → pact σ x = x) → σ = 1 := by
  intro σ h
  have ev : ∀ i j : Fin 5, isEven (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) := by
    decide +kernel
  have hs : ∀ i j : Fin 5, (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) (σ i) =
      (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) i := by
    intro i j
    have h1 := congrFun (h _ (ev i j)) (σ i)
    have h2 : pact σ (Pi.single i 1 + Pi.single j 1) (σ i) =
        (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) i := by
      show (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) (σ⁻¹ (σ i)) = _
      rw [show σ⁻¹ (σ i) = i from σ.symm_apply_apply i]
    rw [h2] at h1
    exact h1.symm
  have key : ∀ i s : Fin 5,
      (Pi.single i 1 + Pi.single (i + 1) 1 : Fin 5 → ZMod 2) s =
        (Pi.single i 1 + Pi.single (i + 1) 1 : Fin 5 → ZMod 2) i →
      (Pi.single i 1 + Pi.single (i + 2) 1 : Fin 5 → ZMod 2) s =
        (Pi.single i 1 + Pi.single (i + 2) 1 : Fin 5 → ZMod 2) i → s = i := by
    decide +kernel
  exact Perm.ext fun i => key i (σ i) (hs i (i + 1)) (hs i (i + 2))

theorem vact_faithful {σ : Perm (Fin 5)} (h : ∀ w, vact σ w = w) : σ = 1 :=
  pact_faithful σ fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)

theorem cent_alt : ∀ τ : Perm (Fin 5),
    (∀ a : Perm (Fin 5), Perm.sign a = 1 → τ * a = a * τ) → τ = 1 := by
  intro τ h
  have hfix : ∀ a : Perm (Fin 5), Perm.sign a = 1 → ∀ x : Fin 5, a x = x → a (τ x) = τ x := by
    intro a ha x hx
    have := congrArg (fun π : Perm (Fin 5) => π x) (h a ha)
    simp only [Perm.mul_apply, hx] at this
    exact this.symm
  have two : ∀ (x : Fin 5) (a b : Perm (Fin 5)), Perm.sign a = 1 → Perm.sign b = 1 →
      a x = x → b x = x → (∀ z : Fin 5, a z = z → b z = z → z = x) → τ x = x :=
    fun x a b ha hb hax hbx hz => hz _ (hfix a ha x hax) (hfix b hb x hbx)
  refine Perm.ext fun x => ?_
  rw [Perm.one_apply]
  fin_cases x
  · exact two 0 c[1, 2, 3] c[1, 2, 4] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact two 1 c[0, 2, 3] c[0, 2, 4] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact two 2 c[0, 1, 3] c[0, 1, 4] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact two 3 c[0, 1, 2] c[0, 1, 4] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact two 4 c[0, 1, 2] c[0, 1, 3] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

@[expose] def a0 : Perm (Fin 5) := c[0, 1, 2, 3, 4]

@[expose] def b0 : Perm (Fin 5) := c[0, 3, 1]

def candSet : Finset (Perm (Fin 5) × Perm (Fin 5)) :=
  (Finset.univ : Finset (Perm (Fin 5) × Perm (Fin 5))).filter fun p =>
    p.1 ^ 5 = 1 ∧ p.2 ^ 3 = 1 ∧ (p.1 * p.2) ^ 2 = 1 ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 * p.2 ≠ 1

def imgSet : Finset (Perm (Fin 5) × Perm (Fin 5)) :=
  (Finset.univ : Finset (Perm (Fin 5))).image fun σ => (σ * a0 * σ⁻¹, σ * b0 * σ⁻¹)

theorem cand_sub : candSet ⊆ imgSet := by
  have h5 : ∀ x : Perm (Fin 5), x ^ 5 = 1 → x ≠ 1 → ∃ σ : Perm (Fin 5), σ * a0 * σ⁻¹ = x := by
    have c : ∀ k : Fin 5, ∀ x : Perm (Fin 5), x 0 = k → x ^ 5 = 1 → x ≠ 1 →
        ∃ σ : Perm (Fin 5), σ 0 = 0 ∧ σ 1 = k ∧ σ * a0 * σ⁻¹ = x := by
      intro k
      fin_cases k <;> decide +kernel
    intro x h1 h2
    obtain ⟨σ, -, -, h⟩ := c (x 0) x rfl h1 h2
    exact ⟨σ, h⟩
  have h3 : ∀ y : Perm (Fin 5), y ^ 3 = 1 → (a0 * y) ^ 2 = 1 → y ≠ 1 → a0 * y ≠ 1 →
      ∃ τ : Perm (Fin 5), τ * a0 * τ⁻¹ = a0 ∧ τ * b0 * τ⁻¹ = y := by
    have c : ∀ k : Fin 5, ∀ y : Perm (Fin 5), y 0 = k → y ^ 3 = 1 → (a0 * y) ^ 2 = 1 → y ≠ 1 →
        a0 * y ≠ 1 → ∃ m : Fin 5, a0 ^ (m : ℕ) * b0 * (a0 ^ (m : ℕ))⁻¹ = y := by
      intro k
      fin_cases k <;> decide +kernel
    intro y h1 h2 h3 h4
    obtain ⟨m, hm⟩ := c (y 0) y rfl h1 h2 h3 h4
    refine ⟨a0 ^ (m : ℕ), ?_, hm⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Commute.refl a0).pow_left (m : ℕ)).eq
  simp only [candSet, imgSet, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, Prod.forall, Prod.mk.injEq]
  rintro x y ⟨hx5, hy3, hxy, n1, n2, n3⟩
  obtain ⟨σ, hσ⟩ := h5 x hx5 n1
  have hx : a0 = σ⁻¹ * x * σ := by rw [← hσ]; group
  have h' : a0 * (σ⁻¹ * y * σ) = σ⁻¹ * (x * y) * σ := by rw [hx]; group
  have e3 : (σ⁻¹ * y * σ) ^ 3 = 1 := by
    have := conj_pow (a := σ⁻¹) (b := y) (i := 3)
    rw [inv_inv] at this
    rw [this, hy3]; group
  have e2 : (a0 * (σ⁻¹ * y * σ)) ^ 2 = 1 := by
    have := conj_pow (a := σ⁻¹) (b := x * y) (i := 2)
    rw [inv_inv] at this
    rw [h', this, hxy]; group
  have m1 : σ⁻¹ * y * σ ≠ 1 := by
    intro h
    apply n2
    have : y = σ * (σ⁻¹ * y * σ) * σ⁻¹ := by group
    rw [this, h]; group
  have m2 : a0 * (σ⁻¹ * y * σ) ≠ 1 := by
    intro h
    apply n3
    rw [h'] at h
    have : x * y = σ * (σ⁻¹ * (x * y) * σ) * σ⁻¹ := by group
    rw [this, h]; group
  obtain ⟨τ, hτ1, hτ2⟩ := h3 _ e3 e2 m1 m2
  refine ⟨σ * τ, ?_, ?_⟩
  · calc σ * τ * a0 * (σ * τ)⁻¹ = σ * (τ * a0 * τ⁻¹) * σ⁻¹ := by group
      _ = x := by rw [hτ1, hσ]
  · calc σ * τ * b0 * (σ * τ)⁻¹ = σ * (τ * b0 * τ⁻¹) * σ⁻¹ := by group
      _ = y := by rw [hτ2]; group

set_option maxRecDepth 100000 in
theorem aut_fin (x y : Perm (Fin 5)) (h1 : x ^ 5 = 1) (h2 : y ^ 3 = 1) (h3 : (x * y) ^ 2 = 1)
    (n1 : x ≠ 1) (n2 : y ≠ 1) (n3 : x * y ≠ 1) :
    ∃ σ : Perm (Fin 5), σ * a0 * σ⁻¹ = x ∧ σ * b0 * σ⁻¹ = y := by
  have hm : (x, y) ∈ candSet := by
    simp only [candSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, h2, h3, n1, n2, n3⟩
  have := cand_sub hm
  simp only [imgSet, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at this
  exact this

abbrev Alt5 := alternatingGroup (Fin 5)

theorem a0_alt : a0 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

theorem b0_alt : b0 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

@[expose] def a0' : Alt5 := ⟨a0, a0_alt⟩

@[expose] def b0' : Alt5 := ⟨b0, b0_alt⟩

theorem a5_card : Nat.card Alt5 = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide +kernel

theorem closure_a5 : Subgroup.closure ({a0', b0'} : Set Alt5) = ⊤ := by
  set N : Subgroup Alt5 := Subgroup.closure ({a0', b0'} : Set Alt5) with hN
  have ha : a0' ∈ N := Subgroup.subset_closure (by simp)
  have hb : b0' ∈ N := Subgroup.subset_closure (by simp)
  have hab : a0' * b0' ∈ N := N.mul_mem ha hb
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have o5 : orderOf a0' = 5 := by
    apply orderOf_eq_prime
    · apply Subtype.ext; show a0 ^ 5 = 1; decide +kernel
    · intro h; have := congrArg Subtype.val h; revert this; show ¬ (a0 = 1); decide +kernel
  have o3 : orderOf b0' = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext; show b0 ^ 3 = 1; decide +kernel
    · intro h; have := congrArg Subtype.val h; revert this; show ¬ (b0 = 1); decide +kernel
  have o2 : orderOf (a0' * b0') = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext; show (a0 * b0) ^ 2 = 1; decide +kernel
    · intro h; have := congrArg Subtype.val h; revert this; show ¬ (a0 * b0 = 1); decide +kernel
  have d5 : 5 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N ha; rwa [o5] at this
  have d3 : 3 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hb; rwa [o3] at this
  have d2 : 2 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hab; rwa [o2] at this
  have h30 : 30 ∣ Nat.card N := by omega
  have hdvd : Nat.card N ∣ 60 := by
    rw [← a5_card]; exact Subgroup.card_subgroup_dvd_card N
  have hle : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hcases : Nat.card N = 30 ∨ Nat.card N = 60 := by
    obtain ⟨k, hk⟩ := h30
    omega
  have hsimple : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
  rcases hcases with h | h
  · exfalso
    have hidx : N.index = 2 := by
      have := N.card_mul_index
      rw [a5_card, h] at this; omega
    have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · rw [h1] at h; simp at h
    · rw [h1] at hidx; simp at hidx
  · exact (Subgroup.card_eq_iff_eq_top N).mp (by rw [h, a5_card])

@[expose] def conjA5 (σ : Perm (Fin 5)) : Alt5 →* Alt5 where
  toFun a := ⟨σ * a * σ⁻¹, by
    rw [Equiv.Perm.mem_alternatingGroup]
    have := a.2
    rw [Equiv.Perm.mem_alternatingGroup] at this
    simp [Perm.sign_mul, this]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem aut_inner (ψ : Alt5 ≃* Alt5) :
    ∃ σ : Perm (Fin 5), ∀ a : Alt5, ((ψ a : Alt5) : Perm (Fin 5)) = σ * a * σ⁻¹ := by
  have h1 : ((ψ a0' : Alt5) : Perm (Fin 5)) ^ 5 = 1 := by
    have : (ψ a0') ^ 5 = 1 := by
      rw [← map_pow, show a0' ^ 5 = 1 from Subtype.ext (by show a0 ^ 5 = 1; decide +kernel),
        map_one]
    have := congrArg Subtype.val this
    simpa using this
  have h2 : ((ψ b0' : Alt5) : Perm (Fin 5)) ^ 3 = 1 := by
    have : (ψ b0') ^ 3 = 1 := by
      rw [← map_pow, show b0' ^ 3 = 1 from Subtype.ext (by show b0 ^ 3 = 1; decide +kernel),
        map_one]
    have := congrArg Subtype.val this
    simpa using this
  have h3 : (((ψ a0' : Alt5) : Perm (Fin 5)) * ((ψ b0' : Alt5) : Perm (Fin 5))) ^ 2 = 1 := by
    have : (ψ a0' * ψ b0') ^ 2 = 1 := by
      rw [← map_mul, ← map_pow, show (a0' * b0') ^ 2 = 1 from
        Subtype.ext (by show (a0 * b0) ^ 2 = 1; decide +kernel), map_one]
    have := congrArg Subtype.val this
    simpa using this
  have n1 : ((ψ a0' : Alt5) : Perm (Fin 5)) ≠ 1 := by
    intro h
    have h' : ψ a0' = 1 := Subtype.ext (by simpa using h)
    have := congrArg Subtype.val (ψ.injective (h'.trans (map_one ψ).symm))
    revert this; show ¬ (a0 = 1); decide +kernel
  have n2 : ((ψ b0' : Alt5) : Perm (Fin 5)) ≠ 1 := by
    intro h
    have h' : ψ b0' = 1 := Subtype.ext (by simpa using h)
    have := congrArg Subtype.val (ψ.injective (h'.trans (map_one ψ).symm))
    revert this; show ¬ (b0 = 1); decide +kernel
  have n3 : ((ψ a0' : Alt5) : Perm (Fin 5)) * ((ψ b0' : Alt5) : Perm (Fin 5)) ≠ 1 := by
    intro h
    have h' : ψ (a0' * b0') = 1 := by
      rw [map_mul]; exact Subtype.ext (by simpa using h)
    have := congrArg Subtype.val (ψ.injective (h'.trans (map_one ψ).symm))
    revert this; show ¬ (a0 * b0 = 1); decide +kernel
  obtain ⟨σ, hσ1, hσ2⟩ := aut_fin _ _ h1 h2 h3 n1 n2 n3
  refine ⟨σ, ?_⟩
  have heq : ψ.toMonoidHom = conjA5 σ := by
    apply MonoidHom.eq_of_eqOn_top
    rw [← closure_a5]
    apply MonoidHom.eqOn_closure
    intro x hx
    rcases hx with rfl | rfl
    · exact Subtype.ext hσ1.symm
    · exact Subtype.ext hσ2.symm
  intro a
  exact congrArg Subtype.val (DFunLike.congr_fun heq a)

@[expose] def w0 : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

@[expose] def t1 : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def t2 : Perm (Fin 5) := swap 2 3 * swap 3 4

theorem fix_w0 : ∀ v : Fin 5 → ZMod 2, isEven v → pact t1 v = v → pact t2 v = v →
    v = 0 ∨ v = w0 := by
  decide +kernel

theorem t1_alt : Perm.sign t1 = 1 := by decide +kernel

theorem t2_alt : Perm.sign t2 = 1 := by decide +kernel

theorem t1_w0 : pact t1 w0 = w0 := by decide +kernel

theorem t2_w0 : pact t2 w0 = w0 := by decide +kernel

theorem pairs_conj : ∀ i j : Fin 5, i ≠ j → ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧
    pact σ w0 = Pi.single i 1 + Pi.single j 1 := by
  obtain ⟨g, hg⟩ : ∃ g : Fin 5 → Fin 5 → Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
      Perm.sign (g i j) = 1 ∧ pact (g i j) w0 = Pi.single i 1 + Pi.single j 1 :=
    ⟨fun i j => (swap 0 i * swap 1 (swap 0 i j)) *
      (if Perm.sign (swap 0 i * swap 1 (swap 0 i j)) = 1 then 1 else swap 2 3), by decide +kernel⟩
  exact fun i j hij => ⟨g i j, hg i j hij⟩

theorem span_pairs : ∀ v : Fin 5 → ZMod 2, isEven v →
    v = 0 ∨ (∃ i j, v = Pi.single i 1 + Pi.single j 1) ∨
    (∃ i j k l, v = (Pi.single i 1 + Pi.single j 1) + (Pi.single k 1 + Pi.single l 1)) := by
  have h : ∀ v : Fin 5 → ZMod 2, isEven v → v = 0 ∨
      (∃ i j, v = Pi.single i 1 + Pi.single j 1) ∨
      ∃ m : Fin 5, v = (Pi.single (m + 1) 1 + Pi.single (m + 2) 1) +
        (Pi.single (m + 3) 1 + Pi.single (m + 4) 1) := by
    decide +kernel
  intro v hv
  rcases h v hv with h0 | h2 | ⟨m, h4⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨_, _, _, _, h4⟩)

theorem w0_mem : w0 ∈ evenWeight 5 := by
  show ∑ i, w0 i = 0
  decide +kernel

theorem pair_mem (i j : Fin 5) :
    (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) ∈ evenWeight 5 := by
  show ∑ k, (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) k = 0
  revert i j; decide +kernel

theorem rigid (g : evenWeight 5 → evenWeight 5) (hadd : ∀ x y, g (x + y) = g x + g y)
    (hinj : Function.Injective g)
    (hcomm : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ w, g (vact σ w) = vact σ (g w)) :
    ∀ w, g w = w := by
  have g0 : g 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)
  let W0 : evenWeight 5 := ⟨w0, w0_mem⟩
  have hW0 : W0 ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    revert this; decide +kernel
  have gW0 : g W0 = W0 := by
    have h1 : vact t1 (g W0) = g W0 := by
      rw [← hcomm t1 t1_alt]
      congr 1
      apply Subtype.ext; exact t1_w0
    have h2 : vact t2 (g W0) = g W0 := by
      rw [← hcomm t2 t2_alt]
      congr 1
      apply Subtype.ext; exact t2_w0
    have := fix_w0 (g W0).1 (g W0).2 (congrArg Subtype.val h1) (congrArg Subtype.val h2)
    rcases this with h | h
    · exfalso
      apply hW0
      apply hinj
      rw [g0]
      exact Subtype.ext h
    · exact Subtype.ext h
  have gpair : ∀ i j : Fin 5,
      ∀ hm : (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) ∈ evenWeight 5,
      g ⟨_, hm⟩ = ⟨_, hm⟩ := by
    intro i j hm
    by_cases hij : i = j
    · subst hij
      have : (⟨_, hm⟩ : evenWeight 5) = 0 := by
        apply Subtype.ext
        funext x
        simp [← two_mul, show (2 : ZMod 2) = 0 from rfl]
      rw [this, g0]
    · obtain ⟨σ, hs, hσ⟩ := pairs_conj i j hij
      have : (⟨_, hm⟩ : evenWeight 5) = vact σ W0 := Subtype.ext hσ.symm
      rw [this, hcomm σ hs, gW0]
  intro w
  have hw : isEven w.1 := w.2
  rcases span_pairs w.1 hw with h | ⟨i, j, h⟩ | ⟨i, j, k, l, h⟩
  · have : w = 0 := Subtype.ext h
    rw [this, g0]
  · have hw' : w = ⟨_, pair_mem i j⟩ := Subtype.ext h
    rw [hw']; exact gpair i j (pair_mem i j)
  · have hw' : w = ⟨_, pair_mem i j⟩ + ⟨_, pair_mem k l⟩ := Subtype.ext h
    rw [hw', hadd, gpair i j (pair_mem i j), gpair k l (pair_mem k l)]

end CFSG.QuasithinUnique.A5.Delta5
