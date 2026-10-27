module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryWeyl

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {r : ℕ}

section Defs

variable (r)

@[expose] def weylGroupB : Subgroup ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) where
  carrier := {w | ∃ (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ), w = signedPermAut r σ δ}
  mul_mem' := by
    rintro _ _ ⟨σ, δ, rfl⟩ ⟨τ, ε, rfl⟩
    exact ⟨σ * τ, fun i => ε i * δ (τ i), signedPermAut_mul σ τ δ ε⟩
  one_mem' := ⟨1, 1, signedPermAut_one.symm⟩
  inv_mem' := by
    rintro _ ⟨σ, δ, rfl⟩
    exact ⟨σ⁻¹, fun i => δ (σ⁻¹ i), signedPermAut_inv σ δ⟩

@[expose] def shortRootsB : Set (Fin r → ℤ) :=
  {α | ∃ i : Fin r, α = eps r i ∨ α = -eps r i}

@[expose] def rootsB : Set (Fin r → ℤ) :=
  shortRootsB r ∪ roots r

@[expose] def posRootsB : Set (Fin r → ℤ) :=
  Set.range (eps r) ∪ posRoots r

@[expose] def simpleRootB (i : Fin r) : Fin r → ℤ :=
  if h : i.val + 1 < r then eps r i - eps r ⟨i.val + 1, h⟩ else eps r i

@[expose] def signAt (i : Fin r) : Fin r → ℤˣ :=
  fun j => if j = i then -1 else 1

@[expose] def simpleReflB (i : Fin r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) :=
  if h : i.val + 1 < r then signedPermAut r (Equiv.swap i ⟨i.val + 1, h⟩) 1
  else signedPermAut r 1 (signAt r i)

@[expose] def inversionSetB (w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) : Set (Fin r → ℤ) :=
  {β | β ∈ posRootsB r ∧ -(w β) ∈ posRootsB r}

@[expose] noncomputable def weylLengthB (w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) : ℕ :=
  (inversionSetB r w).ncard

end Defs

theorem mem_weylGroupB {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} :
    w ∈ weylGroupB r ↔ ∃ (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ), w = signedPermAut r σ δ :=
  Iff.rfl

theorem signedPermAut_mem_weylGroupB (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) :
    signedPermAut r σ δ ∈ weylGroupB r :=
  ⟨σ, δ, rfl⟩

theorem posRootsB_subset_rootsB : posRootsB r ⊆ rootsB r := by
  rintro α (⟨i, rfl⟩ | hα)
  · exact Or.inl ⟨i, Or.inl rfl⟩
  · exact Or.inr (posRoots_subset_roots hα)

section Forms

theorem sign_eps_ne_sign_vec {a b c : Fin r} (hab : a ≠ b) {s t u : ℤ} (hs : IsSign s)
    (ht : IsSign t) : u • eps r c ≠ s • eps r a + t • eps r b := by
  intro h
  have ha := congrFun h a
  have hb := congrFun h b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eps_apply, ↓reduceIte,
    ite_eq_right hab.symm, ite_eq_right hab, mul_one, mul_zero, add_zero, zero_add] at ha hb
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  by_cases hac : a = c
  · subst hac
    rw [ite_eq_right hab.symm, mul_zero] at hb
    exact ht0 hb.symm
  · rw [ite_eq_right hac, mul_zero] at ha
    exact hs0 ha.symm

theorem mem_shortRootsB_iff_sign {α : Fin r → ℤ} :
    α ∈ shortRootsB r ↔ ∃ (a : Fin r) (s : ℤ), IsSign s ∧ α = s • eps r a := by
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨i, 1, isSign_one, by rw [one_smul]⟩
    · exact ⟨i, -1, isSign_neg_one, by rw [neg_one_smul]⟩
  · rintro ⟨a, s, hs, rfl⟩
    rcases hs with rfl | rfl
    · exact ⟨a, Or.inl (one_smul _ _)⟩
    · exact ⟨a, Or.inr (neg_one_smul _ _)⟩

theorem mem_rootsB_iff_sign {α : Fin r → ℤ} :
    α ∈ rootsB r ↔ (∃ (a : Fin r) (s : ℤ), IsSign s ∧ α = s • eps r a) ∨
      ∃ a b : Fin r, a ≠ b ∧ ∃ s t : ℤ, IsSign s ∧ IsSign t ∧
        α = s • eps r a + t • eps r b := by
  rw [rootsB, Set.mem_union, mem_shortRootsB_iff_sign, mem_roots_iff_sign]

theorem sign_eps_mem_rootsB (a : Fin r) {s : ℤ} (hs : IsSign s) : s • eps r a ∈ rootsB r :=
  mem_rootsB_iff_sign.2 (Or.inl ⟨a, s, hs, rfl⟩)

theorem sign_vec_mem_rootsB {a b : Fin r} (hab : a ≠ b) {s t : ℤ} (hs : IsSign s)
    (ht : IsSign t) : s • eps r a + t • eps r b ∈ rootsB r :=
  Or.inr (sign_vec_mem_roots hab hs ht)

theorem eps_mem_posRootsB (a : Fin r) : eps r a ∈ posRootsB r :=
  Or.inl ⟨a, rfl⟩

theorem sign_eps_mem_posRootsB_iff (a : Fin r) {s : ℤ} (hs : IsSign s) :
    s • eps r a ∈ posRootsB r ↔ s = 1 := by
  constructor
  · rintro (⟨c, hc⟩ | hpos)
    · have h := congrFun hc a
      simp only [Pi.smul_apply, smul_eq_mul, eps_apply] at h
      rcases hs with rfl | rfl
      · rfl
      · split_ifs at h <;> norm_num at h
    · obtain ⟨c, d, hcd, u, hu, h⟩ := mem_posRoots_iff_sign.1 hpos
      exact absurd (h.trans (by rw [one_smul])) (sign_eps_ne_sign_vec hcd.ne isSign_one hu)
  · rintro rfl
    rw [one_smul]
    exact eps_mem_posRootsB a

theorem sign_vec_mem_posRootsB_iff {a b : Fin r} (hab : a ≠ b) {s t : ℤ} (hs : IsSign s)
    (ht : IsSign t) :
    s • eps r a + t • eps r b ∈ posRootsB r ↔ (a < b ∧ s = 1) ∨ (b < a ∧ t = 1) := by
  rw [← sign_vec_mem_posRoots_iff hab hs ht]
  constructor
  · rintro (⟨c, hc⟩ | hpos)
    · exact absurd (by rw [one_smul]; exact hc) (sign_eps_ne_sign_vec hab hs ht (c := c) (u := 1))
    · exact hpos
  · exact Or.inr

theorem neg_mem_rootsB {α : Fin r → ℤ} (hα : α ∈ rootsB r) : -α ∈ rootsB r := by
  rcases hα with ⟨i, rfl | rfl⟩ | hα
  · exact Or.inl ⟨i, Or.inr rfl⟩
  · exact Or.inl ⟨i, Or.inl (neg_neg _)⟩
  · exact Or.inr (neg_mem_roots hα)

theorem ne_zero_of_mem_rootsB {α : Fin r → ℤ} (hα : α ∈ rootsB r) : α ≠ 0 := by
  rcases hα with ⟨i, rfl | rfl⟩ | hα
  · intro h
    have := congrFun h i
    simp [eps_apply] at this
  · intro h
    have := congrFun h i
    simp [eps_apply] at this
  · exact ne_zero_of_mem_roots hα

end Forms

section Height

theorem rootHeight_sign_eps (s : ℤ) (a : Fin r) :
    rootHeight r (s • eps r a) = s * (r - a) := by
  rw [map_zsmul, rootHeight_eps, smul_eq_mul]

theorem mem_posRootsB_iff_rootHeight_pos {α : Fin r → ℤ} (hα : α ∈ rootsB r) :
    α ∈ posRootsB r ↔ 0 < rootHeight r α := by
  rcases mem_rootsB_iff_sign.1 hα with ⟨a, s, hs, rfl⟩ | ⟨a, b, hab, s, t, hs, ht, rfl⟩
  · rw [sign_eps_mem_posRootsB_iff a hs, rootHeight_sign_eps]
    have ha := a.isLt
    rcases hs with rfl | rfl
    · simp only [true_iff, one_mul, sub_pos]
      exact_mod_cast ha
    · simp only [neg_one_mul, Left.neg_pos_iff, sub_neg]
      norm_num
  · rw [sign_vec_mem_posRootsB_iff hab hs ht, ← sign_vec_mem_posRoots_iff hab hs ht]
    exact mem_posRoots_iff_rootHeight_pos (sign_vec_mem_roots hab hs ht)

theorem rootHeight_pos_of_mem_posRootsB {β : Fin r → ℤ} (hβ : β ∈ posRootsB r) :
    0 < rootHeight r β :=
  (mem_posRootsB_iff_rootHeight_pos (posRootsB_subset_rootsB hβ)).1 hβ

theorem mem_posRootsB_or_neg_mem_posRootsB {α : Fin r → ℤ} (hα : α ∈ rootsB r) :
    (α ∈ posRootsB r ∨ -α ∈ posRootsB r) ∧ ¬(α ∈ posRootsB r ∧ -α ∈ posRootsB r) := by
  rw [mem_posRootsB_iff_rootHeight_pos hα, mem_posRootsB_iff_rootHeight_pos (neg_mem_rootsB hα),
    map_neg, Left.neg_pos_iff]
  have h0 : rootHeight r α ≠ 0 := by
    rcases mem_rootsB_iff_sign.1 hα with ⟨a, s, hs, rfl⟩ | ⟨a, b, hab, s, t, hs, ht, rfl⟩
    · rw [rootHeight_sign_eps]
      have ha := a.isLt
      have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
      refine mul_ne_zero hs0 ?_
      rw [sub_ne_zero]
      intro h
      have : (r : ℤ) = (a : ℕ) := h
      omega
    · have h := (mem_posRoots_or_neg_mem_posRoots (sign_vec_mem_roots hab hs ht)).1
      rcases h with h | h
      · exact (rootHeight_pos_of_mem_posRoots h).ne'
      · have := rootHeight_pos_of_mem_posRoots h
        rw [map_neg] at this
        exact (neg_pos.1 this).ne
  constructor
  · rcases lt_or_gt_of_ne h0 with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro ⟨h1, h2⟩
    exact absurd (h1.trans h2) (lt_irrefl _)

theorem posRootsB_finite : (posRootsB r).Finite :=
  (Set.finite_range _).union posRoots_finite

end Height

section Action

theorem signedPermAut_sign_eps (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) (s : ℤ) (a : Fin r) :
    signedPermAut r σ δ (s • eps r a) = (s * δ a) • eps r (σ a) := by
  rw [map_smul, signedPermAut_eps, smul_smul]

theorem signedPermAut_mem_roots (σ : Equiv.Perm (Fin r)) (δ : Fin r → ℤˣ) {α : Fin r → ℤ}
    (hα : α ∈ roots r) : signedPermAut r σ δ α ∈ roots r := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  rw [signedPermAut_sign_vec]
  exact sign_vec_mem_roots (σ.injective.ne hab) (hs.mul (isSign_unit _)) (ht.mul (isSign_unit _))

theorem apply_mem_rootsB {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroupB r)
    {α : Fin r → ℤ} (hα : α ∈ rootsB r) : w α ∈ rootsB r := by
  obtain ⟨σ, δ, rfl⟩ := hw
  rcases mem_rootsB_iff_sign.1 hα with ⟨a, s, hs, rfl⟩ | ⟨a, b, hab, s, t, hs, ht, rfl⟩
  · rw [signedPermAut_sign_eps]
    exact sign_eps_mem_rootsB _ (hs.mul (isSign_unit _))
  · exact Or.inr (signedPermAut_mem_roots σ δ (sign_vec_mem_roots hab hs ht))

theorem exists_unit_of_isSign {s : ℤ} (hs : IsSign s) : ∃ u : ℤˣ, (u : ℤ) = s := by
  rcases hs with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨-1, rfl⟩

theorem exists_weylB_apply_eq_short {α β : Fin r → ℤ} (hα : α ∈ shortRootsB r)
    (hβ : β ∈ shortRootsB r) : ∃ w ∈ weylGroupB r, w α = β := by
  obtain ⟨a, s, hs, rfl⟩ := mem_shortRootsB_iff_sign.1 hα
  obtain ⟨c, t, ht, rfl⟩ := mem_shortRootsB_iff_sign.1 hβ
  obtain ⟨u, hu⟩ := exists_unit_of_isSign hs
  obtain ⟨v, hv⟩ := exists_unit_of_isSign ht
  refine ⟨signedPermAut r (Equiv.swap a c) fun _ => u * v, signedPermAut_mem_weylGroupB _ _, ?_⟩
  rw [signedPermAut_sign_eps, Equiv.swap_apply_left, Units.val_mul, hu, hv, ← mul_assoc]
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [hss, one_mul]

theorem exists_weylB_apply_eq_long {α β : Fin r → ℤ} (hα : α ∈ roots r) (hβ : β ∈ roots r) :
    ∃ w ∈ weylGroupB r, w α = β := by
  obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_roots_iff_sign.mp hα
  obtain ⟨c, d, hcd, s', t', hs', ht', rfl⟩ := mem_roots_iff_sign.mp hβ
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_apply_zero_one hcd a b hab
  obtain ⟨u, hu⟩ := exists_unit_of_isSign hs
  obtain ⟨v, hv⟩ := exists_unit_of_isSign ht
  obtain ⟨u', hu'⟩ := exists_unit_of_isSign hs'
  obtain ⟨v', hv'⟩ := exists_unit_of_isSign ht'
  set δ : Fin r → ℤˣ := fun j => if j = a then u * u' else if j = b then v * v' else 1 with hδ
  refine ⟨signedPermAut r σ δ, signedPermAut_mem_weylGroupB _ _, ?_⟩
  rw [signedPermAut_sign_vec, hσa, hσb]
  have hδa : ((δ a : ℤˣ) : ℤ) = s * s' := by simp [hδ, hu, hu']
  have hδb : ((δ b : ℤˣ) : ℤ) = t * t' := by simp [hδ, hab.symm, hv, hv']
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have htt : t * t = 1 := by rcases ht with rfl | rfl <;> norm_num
  rw [hδa, hδb, ← mul_assoc, ← mul_assoc, hss, htt, one_mul, one_mul]

end Action

section Simple

theorem simpleRootB_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleRootB r i = eps r i - eps r ⟨i.val + 1, h⟩ := by
  rw [simpleRootB, dite_eq_left h]

theorem simpleRootB_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) : simpleRootB r i = eps r i := by
  rw [simpleRootB, dite_eq_right h]

theorem simpleRootB_eq_simpleRoot {i : Fin r} (h : i.val + 1 < r) :
    simpleRootB r i = simpleRoot r i := by
  rw [simpleRootB_of_lt h, simpleRoot, dite_eq_left h]

theorem simpleReflB_of_lt {i : Fin r} (h : i.val + 1 < r) :
    simpleReflB r i = signedPermAut r (Equiv.swap i ⟨i.val + 1, h⟩) 1 := by
  rw [simpleReflB, dite_eq_left h]

theorem simpleReflB_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    simpleReflB r i = signedPermAut r 1 (signAt r i) := by
  rw [simpleReflB, dite_eq_right h]

theorem simpleReflB_eq_simpleRefl {i : Fin r} (h : i.val + 1 < r) :
    simpleReflB r i = simpleRefl r i := by
  rw [simpleReflB_of_lt h, simpleRefl_of_lt h]

theorem simpleReflB_mem (i : Fin r) : simpleReflB r i ∈ weylGroupB r := by
  by_cases h : i.val + 1 < r
  · rw [simpleReflB_of_lt h]
    exact signedPermAut_mem_weylGroupB _ _
  · rw [simpleReflB_of_not_lt h]
    exact signedPermAut_mem_weylGroupB _ _

theorem signAt_self (i : Fin r) : ((signAt r i i : ℤˣ) : ℤ) = -1 := by
  simp [signAt]

theorem signAt_of_ne {i j : Fin r} (h : j ≠ i) : ((signAt r i j : ℤˣ) : ℤ) = 1 := by
  simp [signAt, h]

theorem simpleRootB_mem_posRootsB (i : Fin r) : simpleRootB r i ∈ posRootsB r := by
  by_cases h : i.val + 1 < r
  · rw [simpleRootB_of_lt h]
    exact Or.inr ⟨i, ⟨i.val + 1, h⟩, by rw [Fin.lt_def]; simp, Or.inl rfl⟩
  · rw [simpleRootB_of_not_lt h]
    exact eps_mem_posRootsB i

theorem simpleReflB_simpleRootB (i : Fin r) :
    simpleReflB r i (simpleRootB r i) = -simpleRootB r i := by
  by_cases h : i.val + 1 < r
  · rw [simpleReflB_of_lt h, simpleRootB_of_lt h, map_sub, signedPermAut_eps, signedPermAut_eps,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp only [Pi.one_apply, Units.val_one, one_smul, neg_sub]
  · rw [simpleReflB_of_not_lt h, simpleRootB_of_not_lt h, signedPermAut_eps, signAt_self,
      Equiv.Perm.coe_one, id_eq, neg_one_smul]

theorem simpleReflB_mem_posRootsB {i : Fin r} {β : Fin r → ℤ} (hβ : β ∈ posRootsB r)
    (hne : β ≠ simpleRootB r i) : simpleReflB r i β ∈ posRootsB r := by
  by_cases h : i.val + 1 < r
  · rw [simpleReflB_of_lt h]
    rcases hβ with ⟨a, rfl⟩ | hβ
    · rw [signedPermAut_eps]
      simp only [Pi.one_apply, Units.val_one, one_smul]
      exact eps_mem_posRootsB _
    · rw [← simpleRefl_of_lt h]
      refine Or.inr (simpleRefl_mem_posRoots (by omega) hβ ?_)
      rwa [← simpleRootB_eq_simpleRoot h]
  · rw [simpleReflB_of_not_lt h]
    rcases hβ with ⟨a, rfl⟩ | hβ
    · have hai : a ≠ i := by
        rintro rfl
        exact hne (simpleRootB_of_not_lt h).symm
      rw [signedPermAut_eps, signAt_of_ne hai, one_smul, Equiv.Perm.coe_one, id_eq]
      exact eps_mem_posRootsB a
    · obtain ⟨a, b, hab, t, ht, rfl⟩ := mem_posRoots_iff_sign.mp hβ
      have hai : a ≠ i := by
        rintro rfl
        have := b.isLt
        rw [Fin.lt_def] at hab
        omega
      rw [show eps r a + t • eps r b = (1 : ℤ) • eps r a + t • eps r b by rw [one_smul],
        signedPermAut_sign_vec, signAt_of_ne hai, Equiv.Perm.coe_one, id_eq, id_eq, mul_one,
        sign_vec_mem_posRootsB_iff hab.ne isSign_one (ht.mul (isSign_unit _))]
      exact Or.inl ⟨hab, rfl⟩

theorem simpleReflB_mul_self (i : Fin r) : simpleReflB r i * simpleReflB r i = 1 := by
  by_cases h : i.val + 1 < r
  · rw [simpleReflB_eq_simpleRefl h]
    exact simpleRefl_mul_self (by omega) i
  · rw [simpleReflB_of_not_lt h, signedPermAut_mul, mul_one]
    have : (fun j => signAt r i j * signAt r i ((1 : Equiv.Perm (Fin r)) j)) = 1 := by
      funext j
      by_cases hj : j = i <;> simp [signAt, hj]
    rw [this]
    exact signedPermAut_one

end Simple

section Combination

theorem eps_sub_eps_mem_closureB {i j : Fin r} (hij : i < j) :
    eps r i - eps r j ∈ AddSubmonoid.closure (Set.range (simpleRootB r)) := by
  obtain ⟨n, hn⟩ : ∃ n, j.val = i.val + n + 1 :=
    ⟨j.val - i.val - 1, by rw [Fin.lt_def] at hij; omega⟩
  induction n generalizing j with
  | zero =>
    have h : i.val + 1 < r := by have := j.isLt; omega
    have hj : j = ⟨i.val + 1, h⟩ := Fin.ext (by simp [hn])
    refine AddSubmonoid.subset_closure ⟨i, ?_⟩
    rw [simpleRootB_of_lt h, hj]
  | succ n ih =>
    set k : Fin r := ⟨i.val + n + 1, by have := j.isLt; omega⟩
    have hik : i < k := by rw [Fin.lt_def]; simp [k]
    have hkj : k.val + 1 < r := by have := j.isLt; simp [k]; omega
    have hj : j = ⟨k.val + 1, hkj⟩ := Fin.ext (by simp [k, hn]; omega)
    have h1 := ih hik (by simp [k])
    have h2 : eps r k - eps r j ∈ AddSubmonoid.closure (Set.range (simpleRootB r)) := by
      refine AddSubmonoid.subset_closure ⟨k, ?_⟩
      rw [simpleRootB_of_lt hkj, hj]
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

theorem eps_mem_closureB (i : Fin r) :
    eps r i ∈ AddSubmonoid.closure (Set.range (simpleRootB r)) := by
  set q : Fin r := ⟨r - 1, by have := i.isLt; omega⟩ with hq
  have hlast : eps r q ∈ AddSubmonoid.closure (Set.range (simpleRootB r)) :=
    AddSubmonoid.subset_closure ⟨q, simpleRootB_of_not_lt (by simp [q]; omega)⟩
  by_cases hiq : i = q
  · rw [hiq]
    exact hlast
  · have hlt : i < q := by
      rw [Fin.lt_def]
      have := i.isLt
      rw [Fin.ext_iff] at hiq
      simp only [hq] at hiq ⊢
      omega
    have := add_mem (eps_sub_eps_mem_closureB hlt) hlast
    rwa [sub_add_cancel] at this

theorem exists_nonneg_combB {β : Fin r → ℤ} (hβ : β ∈ posRootsB r) :
    ∃ c : Fin r → ℕ, β = ∑ i, c i • simpleRootB r i := by
  rw [← AddSubmonoid.mem_closure_range_iff_of_fintype]
  rcases hβ with ⟨i, rfl⟩ | ⟨i, j, hij, h | h⟩
  · exact eps_mem_closureB i
  · rw [h]
    exact eps_sub_eps_mem_closureB hij
  · rw [h]
    exact add_mem (eps_mem_closureB i) (eps_mem_closureB j)

end Combination

section Descent

theorem eq_one_of_forall_posRootsB {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroupB r)
    (h : ∀ β ∈ posRootsB r, w β ∈ posRootsB r) : w = 1 := by
  obtain ⟨σ, δ, rfl⟩ := hw
  have hδ : ∀ a, (δ a : ℤ) = 1 := by
    intro a
    have h1 := h _ (eps_mem_posRootsB a)
    rw [show eps r a = (1 : ℤ) • eps r a by rw [one_smul], signedPermAut_sign_eps,
      sign_eps_mem_posRootsB_iff _ (isSign_one.mul (isSign_unit _)), one_mul] at h1
    exact h1
  have hmono : StrictMono σ := by
    intro a b hab
    have h2 := h ((1 : ℤ) • eps r a + (-1 : ℤ) • eps r b)
      (by rw [sign_vec_mem_posRootsB_iff hab.ne isSign_one isSign_neg_one]
          exact Or.inl ⟨hab, rfl⟩)
    rw [signedPermAut_sign_vec, hδ, hδ, sign_vec_mem_posRootsB_iff (σ.injective.ne hab.ne)
      (isSign_one.mul isSign_one) (isSign_neg_one.mul isSign_one)] at h2
    rcases h2 with ⟨h2, -⟩ | ⟨-, h2⟩
    · exact h2
    · norm_num at h2
  have hσ : σ = 1 := Equiv.ext fun a => hmono.apply_eq
  have hδ1 : δ = 1 := funext fun a => Units.ext (hδ a)
  rw [hσ, hδ1, signedPermAut_one]

theorem exists_simpleRootB_neg {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroupB r)
    (hne : w ≠ 1) : ∃ i, -(w⁻¹ (simpleRootB r i)) ∈ posRootsB r := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hpos : ∀ i, w⁻¹ (simpleRootB r i) ∈ posRootsB r := fun i =>
    ((mem_posRootsB_or_neg_mem_posRootsB (apply_mem_rootsB (inv_mem hw)
      (posRootsB_subset_rootsB (simpleRootB_mem_posRootsB i)))).1).resolve_right (hcon i)
  have hall : ∀ β ∈ posRootsB r, w⁻¹ β ∈ posRootsB r := by
    intro β hβ
    obtain ⟨c, hc⟩ := exists_nonneg_combB hβ
    have hroot := apply_mem_rootsB (inv_mem hw) (posRootsB_subset_rootsB hβ)
    rw [mem_posRootsB_iff_rootHeight_pos hroot, hc, map_sum, map_sum]
    simp only [map_nsmul]
    have hne0 : ∃ i, c i ≠ 0 := by
      by_contra h0
      simp only [not_exists, not_not] at h0
      apply ne_zero_of_mem_rootsB (posRootsB_subset_rootsB hβ)
      rw [hc]
      simp [h0]
    obtain ⟨i, hi⟩ := hne0
    have hterm : 0 < c i • rootHeight r (w⁻¹ (simpleRootB r i)) :=
      nsmul_pos (rootHeight_pos_of_mem_posRootsB (hpos i)) hi
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (fun j _ => nsmul_nonneg (rootHeight_pos_of_mem_posRootsB (hpos j)).le _)
      (Finset.mem_univ i))
  exact hne (inv_eq_one.mp (eq_one_of_forall_posRootsB (inv_mem hw) hall))

theorem inversionSetB_simpleReflB_mul {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroupB r) {i : Fin r} (hi : -(w⁻¹ (simpleRootB r i)) ∈ posRootsB r) :
    inversionSetB r (simpleReflB r i * w) = inversionSetB r w \ {-(w⁻¹ (simpleRootB r i))} ∧
      -(w⁻¹ (simpleRootB r i)) ∈ inversionSetB r w := by
  have hαpos := simpleRootB_mem_posRootsB i
  have hwβ₀ : w (-(w⁻¹ (simpleRootB r i))) = -simpleRootB r i := by
    rw [map_neg, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  have hexcl : ∀ γ ∈ rootsB r, ¬(γ ∈ posRootsB r ∧ -γ ∈ posRootsB r) := fun γ hγ =>
    (mem_posRootsB_or_neg_mem_posRootsB hγ).2
  have hnegα : -simpleRootB r i ∉ posRootsB r := fun h =>
    hexcl _ (posRootsB_subset_rootsB hαpos) ⟨hαpos, h⟩
  have hsneg : simpleReflB r i (-simpleRootB r i) = simpleRootB r i := by
    rw [map_neg, simpleReflB_simpleRootB i, neg_neg]
  have hinv : ∀ β, w⁻¹ (w β) = β := fun β => by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  refine ⟨Set.ext fun β => ?_, hi, by rw [hwβ₀, neg_neg]; exact hαpos⟩
  simp only [inversionSetB, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨hβ, hs⟩
    have hγ : w β ∈ rootsB r := apply_mem_rootsB hw (posRootsB_subset_rootsB hβ)
    have hβ₀ : β ≠ -(w⁻¹ (simpleRootB r i)) := by
      rintro rfl
      rw [hwβ₀, hsneg] at hs
      exact hnegα hs
    refine ⟨⟨hβ, ?_⟩, hβ₀⟩
    rcases (mem_posRootsB_or_neg_mem_posRootsB hγ).1 with hpos | hneg
    · exfalso
      by_cases heq : w β = simpleRootB r i
      · have hβeq : β = w⁻¹ (simpleRootB r i) := by rw [← heq, hinv]
        rw [hβeq] at hβ
        exact hexcl _ (apply_mem_rootsB (inv_mem hw) (posRootsB_subset_rootsB hαpos)) ⟨hβ, hi⟩
      · have := simpleReflB_mem_posRootsB hpos heq
        exact hexcl _ (posRootsB_subset_rootsB this) ⟨this, hs⟩
    · exact hneg
  · rintro ⟨⟨hβ, hγ⟩, hne⟩
    refine ⟨hβ, ?_⟩
    have hne' : -(w β) ≠ simpleRootB r i := by
      intro h
      apply hne
      rw [← hinv β, show w β = -simpleRootB r i by rw [← h, neg_neg], map_neg]
    have := simpleReflB_mem_posRootsB hγ hne'
    rwa [map_neg] at this

theorem weylLengthB_simpleReflB_mul {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)}
    (hw : w ∈ weylGroupB r) {i : Fin r} (hi : -(w⁻¹ (simpleRootB r i)) ∈ posRootsB r) :
    weylLengthB r (simpleReflB r i * w) = weylLengthB r w - 1 := by
  obtain ⟨hset, hmem⟩ := inversionSetB_simpleReflB_mul hw hi
  rw [weylLengthB, hset, Set.ncard_sdiff_singleton_of_mem hmem, ← weylLengthB]

theorem weylLengthB_pos {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroupB r) {i : Fin r}
    (hi : -(w⁻¹ (simpleRootB r i)) ∈ posRootsB r) : 0 < weylLengthB r w := by
  have hfin : (inversionSetB r w).Finite := posRootsB_finite.subset fun β hβ => hβ.1
  exact (Set.ncard_pos hfin).mpr ⟨_, (inversionSetB_simpleReflB_mul hw hi).2⟩

theorem closure_simpleReflB : Subgroup.closure (Set.range (simpleReflB r)) = weylGroupB r := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun w hw => ?_
  · rintro _ ⟨i, rfl⟩
    exact simpleReflB_mem i
  · have key : ∀ n, ∀ w ∈ weylGroupB r, weylLengthB r w = n →
        w ∈ Subgroup.closure (Set.range (simpleReflB r)) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro w hw hn
        by_cases h1 : w = 1
        · rw [h1]
          exact one_mem _
        · obtain ⟨i, hi⟩ := exists_simpleRootB_neg hw h1
          have hpos := weylLengthB_pos hw hi
          have hlen := weylLengthB_simpleReflB_mul hw hi
          have hmem := ih (n - 1) (by omega) _ (mul_mem (simpleReflB_mem i) hw)
            (by rw [hlen, hn])
          have hw' : w = simpleReflB r i * (simpleReflB r i * w) := by
            rw [← mul_assoc, simpleReflB_mul_self, one_mul]
          rw [hw']
          exact mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) hmem
    exact key _ w hw rfl

theorem bijOn_simpleReflB (i : Fin r) :
    Set.BijOn (simpleReflB r i) (posRootsB r \ {simpleRootB r i})
      (posRootsB r \ {simpleRootB r i}) := by
  have hαpos := simpleRootB_mem_posRootsB i
  have hinvol : ∀ x, simpleReflB r i (simpleReflB r i x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, simpleReflB_mul_self]
    rfl
  have hmaps : Set.MapsTo (simpleReflB r i) (posRootsB r \ {simpleRootB r i})
      (posRootsB r \ {simpleRootB r i}) := by
    rintro β ⟨hβ, hne⟩
    refine ⟨simpleReflB_mem_posRootsB hβ hne, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h
    have : β = -simpleRootB r i := by rw [← hinvol β, h, simpleReflB_simpleRootB]
    rw [this] at hβ
    exact (mem_posRootsB_or_neg_mem_posRootsB (posRootsB_subset_rootsB hαpos)).2 ⟨hαpos, hβ⟩
  refine ⟨hmaps, (simpleReflB r i).injective.injOn, fun γ hγ => ⟨simpleReflB r i γ, hmaps hγ,
    hinvol γ⟩⟩

end Descent

theorem orthogonal_geometry_tail_B_signed_descent (r : ℕ) :
    (∀ i, simpleReflB r i ∈ weylGroupB r) ∧
      Subgroup.closure (Set.range (simpleReflB r)) = weylGroupB r ∧
      (∀ α ∈ shortRootsB r, ∀ β ∈ shortRootsB r, ∃ w ∈ weylGroupB r, w α = β) ∧
      (∀ α ∈ roots r, ∀ β ∈ roots r, ∃ w ∈ weylGroupB r, w α = β) ∧
      (∀ i, simpleReflB r i (simpleRootB r i) = -simpleRootB r i ∧
        Set.BijOn (simpleReflB r i) (posRootsB r \ {simpleRootB r i})
          (posRootsB r \ {simpleRootB r i})) ∧
      (∀ β ∈ posRootsB r, ∃ c : Fin r → ℕ, β = ∑ i, c i • simpleRootB r i) ∧
      (∀ w ∈ weylGroupB r, w ≠ 1 → ∃ i, -(w⁻¹ (simpleRootB r i)) ∈ posRootsB r) ∧
      (∀ w ∈ weylGroupB r, ∀ i, -(w⁻¹ (simpleRootB r i)) ∈ posRootsB r →
        weylLengthB r (simpleReflB r i * w) = weylLengthB r w - 1) :=
  ⟨simpleReflB_mem, closure_simpleReflB,
    fun _ hα _ hβ => exists_weylB_apply_eq_short hα hβ,
    fun _ hα _ hβ => exists_weylB_apply_eq_long hα hβ,
    fun i => ⟨simpleReflB_simpleRootB i, bijOn_simpleReflB i⟩,
    fun _ hβ => exists_nonneg_combB hβ,
    fun _ hw hne => exists_simpleRootB_neg hw hne,
    fun _ hw _ hi => weylLengthB_simpleReflB_mul hw hi⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
