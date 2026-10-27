module

public import CFSG.CGT.PushingUpLit.BHSSym.PermSylow
public import CFSG.CGT.PushingUpLit.BHSSym.Delta
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.CGT.PushingUpLit.BHSSym

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm

section Helpers

variable {m : ℕ} {T M : Subgroup (Perm (Fin m))}

theorem toAdd_coreAct (σ : Perm (Fin m)) (v : coreMod m) (k : Fin m) :
    Multiplicative.toAdd ((coreAct m σ v : coreMod m) : PermMod m) k =
      Multiplicative.toAdd (v : PermMod m) (σ⁻¹ k) := rfl

theorem toAdd_eq_of_fixed {v : coreMod m} (hv : ∀ t ∈ T, coreAct m t v = v) {a b : Fin m}
    (hab : ∃ t ∈ T, t a = b) :
    Multiplicative.toAdd (v : PermMod m) a = Multiplicative.toAdd (v : PermMod m) b := by
  obtain ⟨t, ht, rfl⟩ := hab
  have := congrArg (fun w : coreMod m => Multiplicative.toAdd (w : PermMod m) (t a)) (hv t ht)
  simpa [toAdd_coreAct] using this

theorem swap_mem_of_orbit
    (hC : ∀ x : Perm (Fin m),
      (∀ v : coreMod m, (∀ t ∈ T, coreAct m t v = v) → coreAct m x v = v) → x ∈ M)
    {a b : Fin m} (hab : ∃ t ∈ T, t a = b) : swap a b ∈ M := by
  refine hC _ fun v hv => coreMod_ext fun k => ?_
  have h := toAdd_eq_of_fixed hv hab
  rw [toAdd_coreAct, swap_inv]
  by_cases hka : k = a
  · rw [hka, swap_apply_left, h]
  · by_cases hkb : k = b
    · rw [hkb, swap_apply_right, h]
    · rw [swap_apply_of_ne_of_ne hka hkb]

theorem swap_mul_swap_mem_of_edges (hT2 : IsPGroup 2 T)
    (hN : ∀ x : Perm (Fin m),
      (∀ i j : Fin m, i ≠ j → (swap i j ∈ T ↔ swap (x i) (x j) ∈ T)) → x ∈ M)
    {p q p' q' : Fin m} (hpq : p ≠ q) (hpp' : p ≠ p') (hpq' : p ≠ q') (hqp' : q ≠ p')
    (hqq' : q ≠ q') (hp'q' : p' ≠ q') (hT₁ : swap p q ∈ T) (hT₂ : swap p' q' ∈ T) :
    swap p p' * swap q q' ∈ M := by
  set x : Perm (Fin m) := swap p p' * swap q q' with hx
  have hxp : x p = p' := by
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne hpq hpq', swap_apply_left]
  have hxq : x q = q' := by
    rw [hx, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpq'.symm hp'q'.symm]
  have hxp' : x p' = p := by
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne hqp'.symm hp'q', swap_apply_right]
  have hxq' : x q' = q := by
    rw [hx, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hpq.symm hqp']
  have hxo : ∀ i, i ≠ p → i ≠ q → i ≠ p' → i ≠ q' → x i = i := fun i h1 h2 h3 h4 => by
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4, swap_apply_of_ne_of_ne h1 h3]
  have hP : ∀ j, j ≠ p → swap p j ∈ T → j = q := fun j hj h =>
    (eq_of_swap_mem hT2 hpq hj.symm hT₁ h).symm
  have hQ : ∀ j, j ≠ q → swap q j ∈ T → j = p := fun j hj h =>
    (eq_of_swap_mem hT2 hpq.symm hj.symm (by rwa [swap_comm]) h).symm
  have hP' : ∀ j, j ≠ p' → swap p' j ∈ T → j = q' := fun j hj h =>
    (eq_of_swap_mem hT2 hp'q' hj.symm hT₂ h).symm
  have hQ' : ∀ j, j ≠ q' → swap q' j ∈ T → j = p' := fun j hj h =>
    (eq_of_swap_mem hT2 hp'q'.symm hj.symm (by rwa [swap_comm]) h).symm
  have key : ∀ i j : Fin m, i ≠ j → swap i j ∈ T → swap (x i) (x j) ∈ T := by
    intro i j hij hs
    by_cases hi1 : i = p
    · subst hi1
      obtain rfl := hP j hij.symm hs
      rw [hxp, hxq]
      exact hT₂
    by_cases hi2 : i = q
    · subst hi2
      obtain rfl := hQ j hij.symm hs
      rw [hxq, hxp, swap_comm]
      exact hT₂
    by_cases hi3 : i = p'
    · subst hi3
      obtain rfl := hP' j hij.symm hs
      rw [hxp', hxq']
      exact hT₁
    by_cases hi4 : i = q'
    · subst hi4
      obtain rfl := hQ' j hij.symm hs
      rw [hxq', hxp', swap_comm]
      exact hT₁
    have hs' : swap j i ∈ T := by rwa [swap_comm]
    by_cases hj1 : j = p
    · subst hj1
      exact absurd (hP i hi1 hs') hi2
    by_cases hj2 : j = q
    · subst hj2
      exact absurd (hQ i hi2 hs') hi1
    by_cases hj3 : j = p'
    · subst hj3
      exact absurd (hP' i hi3 hs') hi4
    by_cases hj4 : j = q'
    · subst hj4
      exact absurd (hQ' i hi4 hs') hi3
    rw [hxo i hi1 hi2 hi3 hi4, hxo j hj1 hj2 hj3 hj4]
    exact hs
  have hxx : ∀ i, x (x i) = i := by
    intro i
    by_cases hi1 : i = p
    · rw [hi1, hxp, hxp']
    by_cases hi2 : i = q
    · rw [hi2, hxq, hxq']
    by_cases hi3 : i = p'
    · rw [hi3, hxp', hxp]
    by_cases hi4 : i = q'
    · rw [hi4, hxq', hxq]
    rw [hxo i hi1 hi2 hi3 hi4, hxo i hi1 hi2 hi3 hi4]
  refine hN x fun i j hij => ⟨key i j hij, fun h => ?_⟩
  have hne : x i ≠ x j := fun e => hij (x.injective e)
  have := key _ _ hne h
  rwa [hxx, hxx] at this

theorem exists_nonadjacent_same_orbit (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    {p q p' q' : Fin m} (hpq : p ≠ q) (hpp' : p ≠ p') (hpq' : p ≠ q') (hqp' : q ≠ p')
    (hqq' : q ≠ q') (hp'q' : p' ≠ q') (hT₁ : swap p q ∈ T) (hT₂ : swap p' q' ∈ T) :
    ∃ u v : Fin m, u ≠ v ∧ (∃ t ∈ T, t u = v) ∧ swap u v ∉ T := by
  by_contra H
  push Not at H
  have hP : ∀ j, j ≠ p → swap p j ∈ T → j = q := fun j hj h =>
    (eq_of_swap_mem hT2 hpq hj.symm hT₁ h).symm
  have hQ : ∀ j, j ≠ q → swap q j ∈ T → j = p := fun j hj h =>
    (eq_of_swap_mem hT2 hpq.symm hj.symm (by rwa [swap_comm]) h).symm
  have hP' : ∀ j, j ≠ p' → swap p' j ∈ T → j = q' := fun j hj h =>
    (eq_of_swap_mem hT2 hp'q' hj.symm hT₂ h).symm
  have hQ' : ∀ j, j ≠ q' → swap q' j ∈ T → j = p' := fun j hj h =>
    (eq_of_swap_mem hT2 hp'q'.symm hj.symm (by rwa [swap_comm]) h).symm
  set A : Set (Fin m) := {p, q, p', q'} with hAdef
  have hmate : ∀ (x : Fin m), ∀ t ∈ T, t x ≠ x → swap x (t x) ∈ T := fun x t ht h =>
    H x (t x) (fun e => h e.symm) ⟨t, ht, rfl⟩
  have hinv : ∀ t ∈ T, ∀ x ∈ A, t x ∈ A := by
    intro t ht x hx
    simp only [hAdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h | h | h
    · rw [h]
      by_cases h' : t p = p
      · exact Or.inl h'
      · exact Or.inr (Or.inl (hP _ h' (hmate p t ht h')))
    · rw [h]
      by_cases h' : t q = q
      · exact Or.inr (Or.inl h')
      · exact Or.inl (hQ _ h' (hmate q t ht h'))
    · rw [h]
      by_cases h' : t p' = p'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (hP' _ h' (hmate p' t ht h'))))
    · rw [h]
      by_cases h' : t q' = q'
      · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inr (Or.inr (Or.inl (hQ' _ h' (hmate q' t ht h'))))
  have hA : ∀ t ∈ T, ∀ x, t x ∈ A ↔ x ∈ A := by
    intro t ht x
    refine ⟨fun hx => ?_, hinv t ht x⟩
    have := hinv t⁻¹ (T.inv_mem ht) _ hx
    simpa using this
  set c : Perm (Fin m) := swap p p' * swap p' q * swap q q' with hc
  have hcp : c p = p' := by
    rw [hc, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hpq hpq',
      swap_apply_of_ne_of_ne hpp' hpq, swap_apply_left]
  have hcp' : c p' = q := by
    rw [hc, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hqp'.symm hp'q',
      swap_apply_left, swap_apply_of_ne_of_ne hpq.symm hqp']
  have hcq : c q = q' := by
    rw [hc, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hp'q'.symm hqq'.symm, swap_apply_of_ne_of_ne hpq'.symm hp'q'.symm]
  have hcq' : c q' = p := by
    rw [hc, Perm.mul_apply, Perm.mul_apply, swap_apply_right, swap_apply_right, swap_apply_right]
  have hco : ∀ x, x ≠ p → x ≠ q → x ≠ p' → x ≠ q' → c x = x := fun x h1 h2 h3 h4 => by
    rw [hc, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4,
      swap_apply_of_ne_of_ne h3 h2, swap_apply_of_ne_of_ne h1 h3]
  have hcA : c ∈ setStab A := by
    intro x
    by_cases hx : x ∈ A
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      simp only [hAdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with h | h | h | h
      · rw [h, hcp]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h, hcq]
        exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h, hcp']
        exact Or.inr (Or.inl rfl)
      · rw [h, hcq']
        exact Or.inl rfl
    · have hx' := hx
      simp only [hAdef, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx'
      rw [hco x hx'.1 hx'.2.1 hx'.2.2.1 hx'.2.2.2]
  have hc4 : c ^ 4 = 1 := by
    refine Equiv.ext fun x => ?_
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
    by_cases h1 : x = p
    · rw [h1, hcp, hcp', hcq, hcq']
    by_cases h2 : x = q
    · rw [h2, hcq, hcq', hcp, hcp']
    by_cases h3 : x = p'
    · rw [h3, hcp', hcq, hcq', hcp]
    by_cases h4 : x = q'
    · rw [h4, hcq', hcp, hcp', hcq]
    rw [hco x h1 h2 h3 h4, hco x h1 h2 h3 h4, hco x h1 h2 h3 h4, hco x h1 h2 h3 h4]
  have hQ : IsPGroup 2 (Subgroup.zpowers c) := by
    have hord : orderOf c ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one hc4
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    have := Nat.card_zpowers c
    rw [hj] at this
    exact IsPGroup.of_card this
  obtain ⟨h, -, hconj⟩ := exists_conj_le_of_isPGroup hT2 hTidx (le_setStab hA) hQ
    (Subgroup.zpowers_le.2 hcA)
  have ht : h * c * h⁻¹ ∈ T := hconj c (Subgroup.mem_zpowers c)
  have hw1 : (h * c * h⁻¹) (h p) = h p' := by simp [Perm.mul_apply, hcp]
  have hw2 : (h * c * h⁻¹) (h p') = h q := by simp [Perm.mul_apply, hcp']
  have H1 : swap (h p) (h p') ∈ T :=
    H (h p) (h p') (h.injective.ne hpp') ⟨_, ht, hw1⟩
  have H2 : swap (h p) (h q) ∈ T :=
    H (h p) (h q) (h.injective.ne hpq) ⟨_, T.mul_mem ht ht, by rw [Perm.mul_apply, hw1, hw2]⟩
  have := eq_of_swap_mem hT2 (h.injective.ne hpp') (h.injective.ne hpq) H1 H2
  exact hqp' (h.injective this).symm

theorem swap_mem_conj {x : Perm (Fin m)} {a b : Fin m} (hx : x ∈ M) (hab : swap a b ∈ M) :
    swap (x a) (x b) ∈ M := by
  rw [swap_apply_apply]
  exact M.mul_mem (M.mul_mem hx hab) (M.inv_mem hx)

theorem swap_mem_trans {x y z : Fin m} (hxy : swap x y ∈ M) (hyz : swap y z ∈ M) (hxz : x ≠ z) :
    swap x z ∈ M := by
  by_cases h1 : x = y
  · rw [h1]
    exact hyz
  by_cases h2 : y = z
  · rw [← h2]
    exact hxy
  have := swap_mem_conj hxy hyz
  rwa [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hxz) (Ne.symm h2)] at this

end Helpers

theorem exists_point_stabilizer_of_overgroup {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    {T M : Subgroup (Perm (Fin m))} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hTM : T ≤ M)
    (hM : M ≠ ⊤)
    (hN : ∀ x : Perm (Fin m),
      (∀ i j : Fin m, i ≠ j → (swap i j ∈ T ↔ swap (x i) (x j) ∈ T)) → x ∈ M)
    (hC : ∀ x : Perm (Fin m),
      (∀ v : coreMod m, (∀ t ∈ T, coreAct m t v = v) → coreAct m x v = v) → x ∈ M) :
    ∃ i₀ : Fin m, ∀ x : Perm (Fin m), x ∈ M ↔ x i₀ = i₀ := by
  obtain ⟨i₀, hi₀⟩ := exists_isFixed hm hT2
  have huniq : ∀ b, (∀ t ∈ T, t b = b) → b = i₀ := fun b hb => eq_of_isFixed hT2 hTidx hb hi₀
  have hmate : ∀ a, a ≠ i₀ → ∃ b, a ≠ b ∧ swap a b ∈ T := fun a ha => exists_edge hT2 hTidx hi₀ ha
  have hall : ∀ a b : Fin m, a ≠ i₀ → b ≠ i₀ → a ≠ b → swap a b ∈ M := by
    intro a b ha hb hab
    by_cases hadj : swap a b ∈ T
    · exact hTM hadj
    obtain ⟨a', haa', hTa⟩ := hmate a ha
    obtain ⟨b', hbb', hTb⟩ := hmate b hb
    have h1 : a ≠ b' := fun e => hadj (by
      have := hTb
      rw [← e, swap_comm] at this
      exact this)
    have h2 : a' ≠ b := fun e => hadj (by
      have := hTa
      rw [e] at this
      exact this)
    have h3 : a' ≠ b' := fun e => hab (eq_of_swap_mem hT2 (a := a') (b := a) (c := b)
      haa'.symm h2 (by rwa [swap_comm]) (by rw [e, swap_comm]; exact hTb))
    obtain ⟨u, v, huv, ⟨t, ht, htu⟩, hnadj⟩ :=
      exists_nonadjacent_same_orbit hT2 hTidx haa' hab h1 h2 h3 hbb' hTa hTb
    have huM : swap u v ∈ M := swap_mem_of_orbit hC ⟨t, ht, htu⟩
    have hu : u ≠ i₀ := fun e => huv (by rw [← htu, e, hi₀ t ht])
    have hv : v ≠ i₀ := fun e => huv (by
      have h := hi₀ t⁻¹ (T.inv_mem ht)
      calc u = t⁻¹ (t u) := by simp
        _ = t⁻¹ v := by rw [htu]
        _ = t⁻¹ i₀ := by rw [e]
        _ = i₀ := h
        _ = v := e.symm)
    obtain ⟨u', huu', hTu⟩ := hmate u hu
    obtain ⟨v', hvv', hTv⟩ := hmate v hv
    have hu'v : u' ≠ v := fun e => hnadj (by
      have := hTu
      rw [e] at this
      exact this)
    have hcl : ∀ d, d ≠ i₀ → (d = v ∨ swap d v ∈ M) := by
      intro d hd
      by_cases hdv : d = v
      · exact Or.inl hdv
      right
      by_cases hdu : d = u
      · rw [hdu]
        exact huM
      by_cases hdu' : d = u'
      · rw [hdu']
        refine swap_mem_trans (hTM (by rw [swap_comm]; exact hTu)) huM hu'v
      by_cases hdv' : d = v'
      · rw [hdv']
        exact hTM (by rw [swap_comm]; exact hTv)
      obtain ⟨d', hdd', hTd⟩ := hmate d hd
      have e1 : u ≠ d' := fun e => hdu' (eq_of_swap_mem hT2 (a := u) (b := d) (c := u')
        (Ne.symm hdu) huu' (by rw [swap_comm, ← e] at hTd; exact hTd) hTu)
      have e2 : u' ≠ d' := fun e => hdu (eq_of_swap_mem hT2 (a := u') (b := d) (c := u)
        (Ne.symm hdu') huu'.symm (by rw [swap_comm, ← e] at hTd; exact hTd)
        (by rw [swap_comm]; exact hTu))
      have e3 : d' ≠ v := fun e => hdv' (eq_of_swap_mem hT2 (a := v) (b := d) (c := v')
        (Ne.symm hdv) hvv' (by rw [swap_comm, e] at hTd; exact hTd) hTv)
      have hx := swap_mul_swap_mem_of_edges hT2 hN huu' (Ne.symm hdu) e1 (Ne.symm hdu') e2 hdd'
        hTu hTd
      have hxu : (swap u d * swap u' d') u = d := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne huu' e1, swap_apply_left]
      have hxv : (swap u d * swap u' d') v = v := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hu'v) (Ne.symm e3),
          swap_apply_of_ne_of_ne (Ne.symm huv) (Ne.symm hdv)]
      have := swap_mem_conj hx huM
      rwa [hxu, hxv] at this
    rcases hcl a ha with h | h
    · rcases hcl b hb with h' | h'
      · exact absurd (h.trans h'.symm) hab
      · rw [h, swap_comm]
        exact h'
    · rcases hcl b hb with h' | h'
      · rw [h']
        exact h
      · refine swap_mem_trans h ?_ hab
        rw [swap_comm]
        exact h'
  have hstab : ∀ g : Perm (Fin m), g i₀ = i₀ → g ∈ M := by
    intro g hg
    have h1 : ∀ x : Fin m, (g x ≠ i₀) ↔ (x ≠ i₀) := fun x => by
      constructor
      · intro hx e
        exact hx (by rw [e, hg])
      · intro hx e
        exact hx (g.injective (e.trans hg.symm))
    set g' : Perm {x : Fin m // x ≠ i₀} := g.subtypePerm h1 with hg'
    have hgg : Perm.ofSubtype g' = g := by
      refine Perm.ofSubtype_subtypePerm h1 fun x hx hxe => ?_
      exact hx (by rw [hxe, hg])
    rw [← hgg]
    induction g' using Perm.swap_induction_on with
    | one => simp
    | swap_mul f x y hxy ih =>
      rw [map_mul, Perm.ofSubtype_swap_eq]
      exact M.mul_mem (hall _ _ x.2 y.2 (fun e => hxy (Subtype.ext e))) ih
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hle : MulAction.stabilizer (Perm (Fin m)) i₀ ≤ M := fun g hg =>
    hstab g (by simpa using hg)
  have hcoatom : IsCoatom (MulAction.stabilizer (Perm (Fin m)) i₀) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (Perm (Fin m)) i₀
  refine ⟨i₀, fun x => ⟨fun hx => ?_, hstab x⟩⟩
  rcases hcoatom.le_iff.1 hle with h | h
  · exact absurd h hM
  · rw [h] at hx
    simpa using hx

end CFSG.CGT.PushingUpLit.BHSSym
