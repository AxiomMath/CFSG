module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open

variable {G : Type*} [Group G]

structure ExactTriple (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G) : Prop where
  mem₁ : z₁ ∈ K₁
  mem₂ : z₂ ∈ K₂
  mem₃ : z₃ ∈ K₃
  central₁ : ∀ k ∈ K₁, k * z₁ = z₁ * k
  central₂ : ∀ k ∈ K₂, k * z₂ = z₂ * k
  central₃ : ∀ k ∈ K₃, k * z₃ = z₃ * k
  sq₁ : z₁ * z₁ = 1
  sq₂ : z₂ * z₂ = 1
  sq₃ : z₃ * z₃ = 1
  ne_one₁ : z₁ ≠ 1
  ne_one₂ : z₂ ≠ 1
  ne_one₃ : z₃ ≠ 1
  comm₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  comm₁₃ : ∀ a ∈ K₁, ∀ b ∈ K₃, a * b = b * a
  comm₂₃ : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a
  ne₁₂ : z₁ ≠ z₂
  ne₁₃ : z₁ ≠ z₃
  ne₂₃ : z₂ ≠ z₃

namespace ExactTriple

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

@[expose] def group (_ : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) : Subgroup G :=
  Subgroup.closure {z₁, z₂, z₃}

theorem comm₁₂' (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) : z₁ * z₂ = z₂ * z₁ :=
  h.comm₁₂ z₁ h.mem₁ z₂ h.mem₂

theorem comm₁₃' (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) : z₁ * z₃ = z₃ * z₁ :=
  h.comm₁₃ z₁ h.mem₁ z₃ h.mem₃

theorem comm₂₃' (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) : z₂ * z₃ = z₃ * z₂ :=
  h.comm₂₃ z₂ h.mem₂ z₃ h.mem₃

theorem group_le_centralizer_of_comm (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) {k : G}
    (h₁ : k * z₁ = z₁ * k) (h₂ : k * z₂ = z₂ * k) (h₃ : k * z₃ = z₃ * k) :
    h.group ≤ Subgroup.centralizer {k} := by
  rw [group, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact h₁.symm
  · exact h₂.symm
  · exact h₃.symm

theorem le_centralizer₁ (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) :
    K₁ ≤ Subgroup.centralizer (h.group : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (h.group_le_centralizer_of_comm (h.central₁ k hk) (h.comm₁₂ k hk z₂ h.mem₂)
      (h.comm₁₃ k hk z₃ h.mem₃) ha)

theorem le_centralizer₂ (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) :
    K₂ ≤ Subgroup.centralizer (h.group : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (h.group_le_centralizer_of_comm ((h.comm₁₂ z₁ h.mem₁ k hk).symm) (h.central₂ k hk)
      (h.comm₂₃ k hk z₃ h.mem₃) ha)

theorem le_centralizer₃ (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) :
    K₃ ≤ Subgroup.centralizer (h.group : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (h.group_le_centralizer_of_comm ((h.comm₁₃ z₁ h.mem₁ k hk).symm)
      ((h.comm₂₃ z₂ h.mem₂ k hk).symm) (h.central₃ k hk) ha)

theorem comm_of_mem (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) {x y : G} (hx : x ∈ h.group)
    (hy : y ∈ h.group) : x * y = y * x := by
  have h1 : y * z₁ = z₁ * y := Subgroup.mem_centralizer_singleton_iff.mp
    (h.group_le_centralizer_of_comm rfl h.comm₁₂' h.comm₁₃' hy)
  have h2 : y * z₂ = z₂ * y := Subgroup.mem_centralizer_singleton_iff.mp
    (h.group_le_centralizer_of_comm h.comm₁₂'.symm rfl h.comm₂₃' hy)
  have h3 : y * z₃ = z₃ * y := Subgroup.mem_centralizer_singleton_iff.mp
    (h.group_le_centralizer_of_comm h.comm₁₃'.symm h.comm₂₃'.symm rfl hy)
  exact Subgroup.mem_centralizer_singleton_iff.mp (h.group_le_centralizer_of_comm h1 h2 h3 hx)

theorem isElemAbelian (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) : IsElemAbelian 2 h.group := by
  refine ⟨⟨⟨fun a b => Subtype.ext (h.comm_of_mem a.2 b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  have key : ∀ x (hx : x ∈ Subgroup.closure ({z₁, z₂, z₃} : Set G)), x * x = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x * x = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      exacts [h.sq₁, h.sq₂, h.sq₃]
    · exact mul_one 1
    · intro a b ha hb haa hbb
      have hab : a * b = b * a := h.comm_of_mem ha hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    · intro a _ haa
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [haa, inv_one]
  exact key x hx

theorem not_mem_closure_single (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) :
    z₂ ∉ Subgroup.closure ({z₁} : Set G) := by
  intro hz
  have key : ∀ x (hx : x ∈ Subgroup.closure ({z₁} : Set G)), x = 1 ∨ x = z₁ := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = z₁) ?_ ?_ ?_ ?_ hx
    · intro y hy
      right
      simpa using hy
    · left
      rfl
    · rintro a b - - (ha | ha) (hb | hb) <;> subst ha <;> subst hb
      · left; simp
      · right; simp
      · right; simp
      · left; exact h.sq₁
    · rintro a - (ha | ha) <;> subst ha
      · left; simp
      · right; exact inv_eq_of_mul_eq_one_right h.sq₁
  rcases key _ hz with h1 | h1
  · exact h.ne_one₂ h1
  · exact h.ne₁₂ h1.symm

theorem not_mem_closure_pair (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) :
    z₃ ∉ Subgroup.closure ({z₁, z₂} : Set G) := by
  intro hz
  have c : z₂ * z₁ = z₁ * z₂ := h.comm₁₂'.symm
  have s1 := h.sq₁
  have s2 := h.sq₂
  have s1' : ∀ b, z₁ * (z₁ * b) = b := fun b => by rw [← mul_assoc, s1, one_mul]
  have c' : ∀ b, z₂ * (z₁ * b) = z₁ * (z₂ * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right s1
  have i2 : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right s2
  have key : ∀ x (hx : x ∈ Subgroup.closure ({z₁, z₂} : Set G)),
      x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₁ * z₂ := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₁ * z₂) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> subst hy <;> simp
    · simp
    · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
        simp [mul_assoc, s1, s2, s1', c, c']
    · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]
  rcases key _ hz with h1 | h1 | h1 | h1
  · exact h.ne_one₃ h1
  · exact h.ne₁₃ h1.symm
  · exact h.ne₂₃ h1.symm
  · exact hind h1.symm

theorem two_mul_card_le_of_lt' [Finite G] {A B : Subgroup G} (h : A < B) :
    2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h.le
  have hA : 0 < Nat.card A := Nat.card_pos
  have hB : 0 < Nat.card B := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le (by omega))
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  nlinarith

theorem eight_le_card [Finite G] (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) :
    8 ≤ Nat.card h.group := by
  set A₁ : Subgroup G := Subgroup.closure ({z₁} : Set G) with hA₁
  set A₂ : Subgroup G := Subgroup.closure ({z₁, z₂} : Set G) with hA₂
  have h1 : (⊥ : Subgroup G) < A₁ := by
    refine lt_of_le_of_ne bot_le fun hh => h.ne_one₁ ?_
    have : z₁ ∈ A₁ := Subgroup.subset_closure rfl
    rwa [← hh, Subgroup.mem_bot] at this
  have h2 : A₁ < A₂ := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun hh => ?_
    have : z₂ ∈ A₂ := Subgroup.subset_closure (by simp)
    rw [← hh] at this
    exact h.not_mem_closure_single this
  have h3 : A₂ < h.group := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by intro x hx; simp at hx ⊢; tauto)) fun hh => ?_
    have : z₃ ∈ h.group := Subgroup.subset_closure (by simp)
    rw [← hh] at this
    exact h.not_mem_closure_pair hind this
  have c1 := two_mul_card_le_of_lt' h1
  have c2 := two_mul_card_le_of_lt' h2
  have c3 := two_mul_card_le_of_lt' h3
  have hbot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
  omega

theorem group_eq_closure_pair (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hd : z₁ * z₂ = z₃) :
    h.group = Subgroup.closure ({z₁, z₂} : Set G) := by
  apply le_antisymm
  · rw [group, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact Subgroup.subset_closure (by simp)
    · rw [hx]; exact Subgroup.subset_closure (by simp)
    · rw [hx, ← hd]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact Subgroup.closure_mono (by intro x hx; simp at hx ⊢; tauto)

theorem mem_group_eight (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) {x : G} (hx : x ∈ h.group) :
    x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₃ ∨ x = z₁ * z₂ ∨ x = z₁ * z₃ ∨ x = z₂ * z₃ ∨
      x = z₁ * (z₂ * z₃) := by
  have c12 : z₂ * z₁ = z₁ * z₂ := h.comm₁₂'.symm
  have c13 : z₃ * z₁ = z₁ * z₃ := h.comm₁₃'.symm
  have c23 : z₃ * z₂ = z₂ * z₃ := h.comm₂₃'.symm
  have s1 := h.sq₁
  have s2 := h.sq₂
  have s3 := h.sq₃
  have s1' : ∀ b, z₁ * (z₁ * b) = b := fun b => by rw [← mul_assoc, s1, one_mul]
  have s2' : ∀ b, z₂ * (z₂ * b) = b := fun b => by rw [← mul_assoc, s2, one_mul]
  have c12' : ∀ b, z₂ * (z₁ * b) = z₁ * (z₂ * b) := fun b => by rw [← mul_assoc, c12, mul_assoc]
  have c13' : ∀ b, z₃ * (z₁ * b) = z₁ * (z₃ * b) := fun b => by rw [← mul_assoc, c13, mul_assoc]
  have c23' : ∀ b, z₃ * (z₂ * b) = z₂ * (z₃ * b) := fun b => by rw [← mul_assoc, c23, mul_assoc]
  have i1 : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right s1
  have i2 : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right s2
  have i3 : z₃⁻¹ = z₃ := inv_eq_of_mul_eq_one_right s3
  refine Subgroup.closure_induction
    (p := fun x _ => x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₃ ∨ x = z₁ * z₂ ∨ x = z₁ * z₃ ∨
      x = z₂ * z₃ ∨ x = z₁ * (z₂ * z₃)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> subst hy <;> simp
  · simp
  · rintro a b - - (ha | ha | ha | ha | ha | ha | ha | ha)
      (hb | hb | hb | hb | hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
      simp [mul_assoc, s1, s2, s3, s1', s2', c12, c13, c23, c12', c13', c23']
  · rintro a - (ha | ha | ha | ha | ha | ha | ha | ha) <;> subst ha <;>
      simp [mul_assoc, mul_inv_rev, i1, i2, i3, c12, c13, c23, c12']

theorem card_le_eight [Finite G] (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) : Nat.card h.group ≤ 8 := by
  classical
  have hsub : (h.group : Set G) ⊆ ({1, z₁, z₂, z₃, z₁ * z₂, z₁ * z₃, z₂ * z₃,
      z₁ * (z₂ * z₃)} : Finset G) := by
    intro x hx
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using h.mem_group_eight hx
  calc Nat.card h.group = Nat.card (h.group : Set G) := rfl
    _ ≤ Nat.card (({1, z₁, z₂, z₃, z₁ * z₂, z₁ * z₃, z₂ * z₃, z₁ * (z₂ * z₃)} : Finset G) :
        Set G) := Nat.card_mono (Set.toFinite _) hsub
    _ = Finset.card ({1, z₁, z₂, z₃, z₁ * z₂, z₁ * z₃, z₂ * z₃, z₁ * (z₂ * z₃)} : Finset G) :=
      Nat.card_eq_finsetCard _
    _ ≤ 8 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp

theorem card_eq_eight [Finite G] (h : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) :
    Nat.card h.group = 8 :=
  le_antisymm h.card_le_eight (h.eight_le_card hind)

end ExactTriple

end CFSG.ClassicalInvolution.Balance.Bootstrap
