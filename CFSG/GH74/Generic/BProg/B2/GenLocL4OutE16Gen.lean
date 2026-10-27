module

public import CFSG.GH74.Generic.BProg.B2.GenLocL5Gen

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG CFSG.GH74 Subgroup



theorem not_sectional_of_E16 {J : Type} [Group J] [Finite J] {A : Type} [Group A] [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut J) (a : A)
    (hu : α a ∉ (MulAut.conj : J →* MulAut J).range) (V : Subgroup (MulAut J))
    (hVinn : V ≤ (MulAut.conj : J →* MulAut J).range) (hVea : CFSG.IsElementaryAbelian 2 ↥V)
    (hVcard : 16 ≤ Nat.card ↥V) (hcomm : ∀ φ ∈ V, α a * φ = φ * α a) :
    ¬ SectionalTwoRankLE ↥(innJoin α) 4 := by
  intro hsec
  have hu2 : α a * α a = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  set W : Subgroup (MulAut J) := GenLocL5Gen.adjoinInvolution V (α a) hu2 hcomm with hWdef
  have hWea : CFSG.IsElementaryAbelian 2 ↥W := GenLocL5Gen.isEA_adjoin hVea
  have hWinn : W ≤ innJoin α := by
    intro x hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Subgroup.mem_sup_left (hVinn hx)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hVinn hy))
        (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hEW : V < W := by
    refine lt_of_le_of_ne (fun x hx => GenLocL5Gen.mem_adjoin_of_mem hx) fun hEq => ?_
    have : α a ∈ V := by rw [hEq]; exact GenLocL5Gen.u_mem_adjoin
    exact hu (hVinn this)
  have hcardW : 32 ≤ Nat.card ↥W := by
    have h1 := Subgroup.card_lt_of_lt hEW
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEW.le
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> simp at hk <;> omega
    calc 32 = 16 * 2 := by norm_num
      _ ≤ Nat.card ↥V * k := Nat.mul_le_mul hVcard hk2
      _ = Nat.card ↥W := hk.symm
  let W' : Subgroup ↥(innJoin α) := W.subgroupOf (innJoin α)
  have hW'card : Nat.card ↥W' = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWinn).toEquiv
  have hW'ea : CFSG.IsElementaryAbelian 2 ↥W' := by
    refine WeakSigGen.isElementaryAbelian_of_forall (G := ↥(innJoin α)) (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : MulAut J)) (mul_comm' (⟨x.1, hx⟩ : W) ⟨y.1, hy⟩)
    · apply Subtype.ext
      exact congrArg (fun z : ↥W => (z : MulAut J))
        (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hWea (⟨x.1, hx⟩ : W))
  have hbound := hsec.card_le_of_elementary W'
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 W').1 hW'ea)
  omega



section E16

variable {J : Type} [Group J]

theorem conj_eq_one_of_mem_center {z : J} (hz : z ∈ Subgroup.center J) : (MulAut.conj z : MulAut J) = 1 := by
  ext x
  have h := Subgroup.mem_center_iff.1 hz x
  rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  rfl

theorem conj_comm_of_mul_eq {z g h : J} (hz : z ∈ Subgroup.center J) (hgh : g * h = z * (h * g)) :
    (MulAut.conj g : MulAut J) * MulAut.conj h = MulAut.conj h * MulAut.conj g := by
  rw [← map_mul, ← map_mul, hgh, map_mul, conj_eq_one_of_mem_center hz, one_mul]

theorem conj_mul_self_of_sq {z g : J} (hz : z ∈ Subgroup.center J) (hg : g * g = 1 ∨ g * g = z) :
    (MulAut.conj g : MulAut J) * MulAut.conj g = 1 := by
  rw [← map_mul]
  rcases hg with h | h
  · rw [h, map_one]
  · rw [h, conj_eq_one_of_mem_center hz]

end E16


section E16b

variable {J : Type} [Group J] {z : J}

@[expose] def tau (g : Fin 4 → J) (i : Fin 4) : MulAut J := MulAut.conj (g i)

@[expose] def VE (g : Fin 4 → J) : Subgroup (MulAut J) := Subgroup.closure (Set.range (tau g))

theorem tau_mem (g : Fin 4 → J) (i : Fin 4) : tau g i ∈ VE g := Subgroup.subset_closure ⟨i, rfl⟩

theorem rel_of (hz2 : z * z = 1) (g : Fin 4 → J)
    (h01 : g 0 * g 1 = z * (g 1 * g 0)) (h23 : g 2 * g 3 = z * (g 3 * g 2))
    (h02 : g 0 * g 2 = g 2 * g 0) (h03 : g 0 * g 3 = g 3 * g 0) (h12 : g 1 * g 2 = g 2 * g 1)
    (h13 : g 1 * g 3 = g 3 * g 1) (i j : Fin 4) :
    g i * g j = g j * g i ∨ g i * g j = z * (g j * g i) := by
  have sym : ∀ a b : J, a * b = z * (b * a) → b * a = z * (a * b) := fun a b h => by
    rw [h, ← mul_assoc, hz2, one_mul]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | exact Or.inl trivial
    | exact Or.inr h01 | exact Or.inr (sym _ _ h01) | exact Or.inr h23 | exact Or.inr (sym _ _ h23)
    | exact Or.inl h02 | exact Or.inl h02.symm | exact Or.inl h03 | exact Or.inl h03.symm
    | exact Or.inl h12 | exact Or.inl h12.symm | exact Or.inl h13 | exact Or.inl h13.symm

theorem tau_comm (hz : z ∈ Subgroup.center J) (g : Fin 4 → J)
    (hrel : ∀ i j, g i * g j = g j * g i ∨ g i * g j = z * (g j * g i)) (i j : Fin 4) :
    tau g i * tau g j = tau g j * tau g i := by
  unfold tau
  rcases hrel i j with h | h
  · rw [← map_mul, ← map_mul, h]
  · exact conj_comm_of_mul_eq hz h

end E16b

section E16c

variable {J : Type} [Group J] {z : J}

theorem tau_apply_self (g : Fin 4 → J) (i : Fin 4) : tau g i (g i) = g i := by
  simp [tau, MulAut.conj_apply]

theorem tau_apply (hz2 : z * z = 1) (g : Fin 4 → J)
    (h01 : g 0 * g 1 = z * (g 1 * g 0)) (h23 : g 2 * g 3 = z * (g 3 * g 2))
    (h02 : g 0 * g 2 = g 2 * g 0) (h03 : g 0 * g 3 = g 3 * g 0) (h12 : g 1 * g 2 = g 2 * g 1)
    (h13 : g 1 * g 3 = g 3 * g 1) (i j : Fin 4) :
    tau g i (g j) = (if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then z else 1) * g j := by
  have sym : ∀ a b : J, a * b = z * (b * a) → b * a = z * (a * b) := fun a b h => by
    rw [h, ← mul_assoc, hz2, one_mul]
  have c : ∀ a b : J, a * b = b * a → a * b * a⁻¹ = b := fun a b h => by rw [h, mul_inv_cancel_right]
  have d : ∀ a b : J, a * b = z * (b * a) → a * b * a⁻¹ = z * b := fun a b h => by
    rw [h, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  unfold tau
  simp only [MulAut.conj_apply]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> simp <;>
    first
    | exact c _ _ rfl
    | exact c _ _ h02 | exact c _ _ h02.symm | exact c _ _ h03 | exact c _ _ h03.symm
    | exact c _ _ h12 | exact c _ _ h12.symm | exact c _ _ h13 | exact c _ _ h13.symm
    | exact d _ _ h01 | exact d _ _ (sym _ _ h01) | exact d _ _ h23 | exact d _ _ (sym _ _ h23)

end E16c

section E16d

variable {J : Type} [Group J] {z : J}

theorem VE_comm (hz : z ∈ Subgroup.center J) (g : Fin 4 → J)
    (hrel : ∀ i j, g i * g j = g j * g i ∨ g i * g j = z * (g j * g i)) :
    ∀ a ∈ VE g, ∀ b ∈ VE g, a * b = b * a := by
  have h1 : ∀ i : Fin 4, ∀ b ∈ VE g, tau g i * b = b * tau g i := by
    intro i b hb
    have : VE g ≤ Subgroup.centralizer {tau g i} := by
      refine Subgroup.closure_le _ |>.2 ?_
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact tau_comm hz g hrel i j
    exact (Subgroup.mem_centralizer_iff.1 (this hb)) (tau g i) rfl
  intro a ha b hb
  have : VE g ≤ Subgroup.centralizer {a} := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (h1 j a ha).symm
  exact (Subgroup.mem_centralizer_iff.1 (this hb)) a rfl

theorem VE_sq (hz : z ∈ Subgroup.center J) (g : Fin 4 → J)
    (hrel : ∀ i j, g i * g j = g j * g i ∨ g i * g j = z * (g j * g i))
    (hsq : ∀ i, g i * g i = 1 ∨ g i * g i = z) : ∀ a ∈ VE g, a * a = 1 := by
  intro a ha
  refine Subgroup.closure_induction (p := fun a _ => a * a = 1) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    exact conj_mul_self_of_sq hz (hsq i)
  · simp
  · intro x y hx hy hxx hyy
    have hc := VE_comm hz g hrel x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  · intro x hx hxx
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hxx, inv_one]

theorem VE_le_range (g : Fin 4 → J) : VE g ≤ (MulAut.conj : J →* MulAut J).range := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨g i, rfl⟩

theorem VE_commute (hz : z ∈ Subgroup.center J) (g : Fin 4 → J) (u : MulAut J)
    (hu : ∀ i, u (g i) = g i ∨ u (g i) = z * g i) : ∀ φ ∈ VE g, u * φ = φ * u := by
  have key : ∀ i, u * tau g i = tau g i * u := by
    intro i
    ext x
    have hzx : ∀ y : J, z * y * z⁻¹ = y := fun y => by
      have h := Subgroup.mem_center_iff.1 hz y
      rw [← h, mul_inv_cancel_right]
    rcases hu i with h | h
    · simp [tau, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, h]
    · simp only [tau, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, h]
      have h2 : z * g i * u x * (z * g i)⁻¹ = z * (g i * u x * (g i)⁻¹) * z⁻¹ := by group
      rw [h2]
      exact hzx _
  intro φ hφ
  refine Subgroup.closure_induction (p := fun φ _ => u * φ = φ * u) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨i, rfl⟩
    exact key i
  · simp
  · intro x y _ _ hx hy
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  · intro x _ hx
    exact (Commute.inv_right (show Commute u x from hx)).eq

end E16d

section E16e

variable {J : Type} [Group J] [Finite J] {z : J}

theorem two_mul_card_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H < K) :
    2 * Nat.card ↥H ≤ Nat.card ↥K := by
  have h1 := Subgroup.card_lt_of_lt h
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h.le
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp at hk <;> omega
  calc 2 * Nat.card ↥H ≤ k * Nat.card ↥H := Nat.mul_le_mul_right _ hk2
    _ = Nat.card ↥K := by rw [hk, mul_comm]

theorem VE_card (hz2 : z * z = 1) (hz1 : z ≠ 1) (g : Fin 4 → J)
    (h01 : g 0 * g 1 = z * (g 1 * g 0)) (h23 : g 2 * g 3 = z * (g 3 * g 2))
    (h02 : g 0 * g 2 = g 2 * g 0) (h03 : g 0 * g 3 = g 3 * g 0) (h12 : g 1 * g 2 = g 2 * g 1)
    (h13 : g 1 * g 3 = g 3 * g 1) : 16 ≤ Nat.card ↥(VE g) := by
  have ta := tau_apply hz2 g h01 h23 h02 h03 h12 h13
  have hne : ∀ x : J, z * x ≠ x := fun x h => hz1 (by simpa using h)
  have hmem : ∀ (φ : MulAut J) (x : J), φ ∈ MulAction.stabilizer (MulAut J) x ↔ φ x = x := fun φ x => Iff.rfl
  let V1 : Subgroup (MulAut J) := Subgroup.closure {tau g 0}
  let V2 : Subgroup (MulAut J) := Subgroup.closure {tau g 0, tau g 1}
  let V3 : Subgroup (MulAut J) := Subgroup.closure {tau g 0, tau g 1, tau g 2}
  have hV12 : V1 ≤ V2 := Subgroup.closure_mono (by intro x hx; simp at hx ⊢; exact Or.inl hx)
  have hV23 : V2 ≤ V3 := Subgroup.closure_mono (by intro x hx; simp at hx ⊢; tauto)
  have hV34 : V3 ≤ VE g := Subgroup.closure_le _ |>.2 (by
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact tau_mem g 0
    · exact tau_mem g 1
    · exact tau_mem g 2)
  have s1 : (⊥ : Subgroup (MulAut J)) < V1 := by
    refine lt_of_le_of_ne bot_le fun h => ?_
    have : tau g 0 ∈ (⊥ : Subgroup (MulAut J)) := by
      rw [h]; exact Subgroup.subset_closure rfl
    rw [Subgroup.mem_bot] at this
    have h1 := ta 0 1
    rw [this] at h1
    simp at h1
    exact hz1 h1
  have s2 : V1 < V2 := by
    refine lt_of_le_of_ne hV12 fun h => ?_
    have hmem2 : tau g 1 ∈ V1 := by rw [h]; exact Subgroup.subset_closure (by simp)
    have hst : V1 ≤ MulAction.stabilizer (MulAut J) (g 0) := by
      refine Subgroup.closure_le _ |>.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, SetLike.mem_coe, hmem]
      exact tau_apply_self g 0
    have := (hmem _ _).1 (hst hmem2)
    have h1 := ta 1 0
    rw [this] at h1
    simp at h1
    exact hz1 h1
  have s3 : V2 < V3 := by
    refine lt_of_le_of_ne hV23 fun h => ?_
    have hmem2 : tau g 2 ∈ V2 := by rw [h]; exact Subgroup.subset_closure (by simp)
    have hst : V2 ≤ MulAction.stabilizer (MulAut J) (g 3) := by
      refine Subgroup.closure_le _ |>.2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, hmem]
      rcases hx with rfl | rfl
      · have := ta 0 3; simpa using this
      · have := ta 1 3; simpa using this
    have := (hmem _ _).1 (hst hmem2)
    have h1 := ta 2 3
    rw [this] at h1
    simp at h1
    exact hz1 h1
  have s4 : V3 < VE g := by
    refine lt_of_le_of_ne hV34 fun h => ?_
    have hmem2 : tau g 3 ∈ V3 := by rw [h]; exact tau_mem g 3
    have hst : V3 ≤ MulAction.stabilizer (MulAut J) (g 2) := by
      refine Subgroup.closure_le _ |>.2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, hmem]
      rcases hx with rfl | rfl | rfl
      · have := ta 0 2; simpa using this
      · have := ta 1 2; simpa using this
      · exact tau_apply_self g 2
    have := (hmem _ _).1 (hst hmem2)
    have h1 := ta 3 2
    rw [this] at h1
    simp at h1
    exact hz1 h1
  have c1 := two_mul_card_le s1
  have c2 := two_mul_card_le s2
  have c3 := two_mul_card_le s3
  have c4 := two_mul_card_le s4
  rw [Subgroup.card_bot] at c1
  omega

end E16e



section Pack

theorem exists_E16 {J : Type} [Group J] [Finite J] {z : J} (hz : z ∈ Subgroup.center J) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (g : Fin 4 → J) (hsq : ∀ i, g i * g i = 1 ∨ g i * g i = z)
    (h01 : g 0 * g 1 = z * (g 1 * g 0)) (h23 : g 2 * g 3 = z * (g 3 * g 2))
    (h02 : g 0 * g 2 = g 2 * g 0) (h03 : g 0 * g 3 = g 3 * g 0) (h12 : g 1 * g 2 = g 2 * g 1)
    (h13 : g 1 * g 3 = g 3 * g 1) :
    ∃ V : Subgroup (MulAut J), V ≤ (MulAut.conj : J →* MulAut J).range ∧ CFSG.IsElementaryAbelian 2 ↥V ∧
      16 ≤ Nat.card ↥V ∧
      ∀ u : MulAut J, (∀ i, u (g i) = g i ∨ u (g i) = z * g i) → ∀ φ ∈ V, u * φ = φ * u := by
  have hrel := rel_of hz2 g h01 h23 h02 h03 h12 h13
  refine ⟨VE g, VE_le_range g, ?_, VE_card hz2 hz1 g h01 h23 h02 h03 h12 h13, fun u hu => VE_commute hz g u hu⟩
  have hc := VE_comm hz g hrel
  have hs := VE_sq hz g hrel hsq
  exact WeakSigGen.isElementaryAbelian_of_forall hc hs

end Pack


end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
