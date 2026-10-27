module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCoordinates
public import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

variable {Y : Type*} [Group Y]

section Elementary

variable {U : Subgroup Y} [IsElementaryAbelian 2 U]

theorem mul_self_eq_one_of_mem {x : Y} (hx : x ∈ U) : x * x = 1 := by
  have h := congrArg Subtype.val (show (⟨x, hx⟩ : U) * ⟨x, hx⟩ = 1 by
    rw [← pow_two]; exact sq_eq_one_of_isElementaryAbelian _)
  simpa using h

theorem inv_eq_self_of_mem {x : Y} (hx : x ∈ U) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem hx)

theorem mul_comm_of_mem {x y : Y} (hx : x ∈ U) (hy : y ∈ U) : x * y = y * x :=
  congrArg Subtype.val (mul_comm_of_isElementaryAbelian (⟨x, hx⟩ : U) ⟨y, hy⟩)

end Elementary

theorem card_sup_of_normal_of_inf_eq_bot [Finite Y] (N K : Subgroup Y) [N.Normal]
    (h : N ⊓ K = ⊥) : Nat.card (N ⊔ K : Subgroup Y) = Nat.card N * Nat.card K := by
  set H := N ⊔ K with hH
  have hNH : N ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hcompl : (N.subgroupOf H).IsComplement' (K.subgroupOf H) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxN hxK
      have : (x : Y) ∈ N ⊓ K := ⟨hxN, hxK⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · ext x
      simp only [Set.mem_univ, iff_true]
      obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp x.2
      refine Set.mem_mul.mpr ⟨⟨n, hNH hn⟩, hn, ⟨k, hKH hk⟩, hk, Subtype.ext ?_⟩
      simpa using hnk
  rw [← hcompl.card_mul_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]

structure PlaneHyp (U B : Subgroup Y) (b₁ b₂ u₀ : Y) : Prop where
  card_U : Nat.card U = 8
  centralizer_U : Subgroup.centralizer (U : Set Y) = U
  full : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹
  le : B ≤ U
  card_B : Nat.card B = 4
  b₁_mem : b₁ ∈ B
  b₂_mem : b₂ ∈ B
  b₁_ne_one : b₁ ≠ 1
  b₂_ne_one : b₂ ≠ 1
  b₂_ne_b₁ : b₂ ≠ b₁
  u₀_mem : u₀ ∈ U
  u₀_not_mem : u₀ ∉ B

@[expose] def planeTau (u₀ y : Y) : Y := u₀ * (y * u₀ * y⁻¹)

namespace PlaneHyp

variable {U B : Subgroup Y} {b₁ b₂ u₀ : Y} [U.Normal] [IsElementaryAbelian 2 U]
  (h : PlaneHyp U B b₁ b₂ u₀)
include h

omit [U.Normal] [IsElementaryAbelian 2 U] in
theorem b₁_mem_U : b₁ ∈ U := h.le h.b₁_mem

omit [U.Normal] [IsElementaryAbelian 2 U] in
theorem b₂_mem_U : b₂ ∈ U := h.le h.b₂_mem

@[expose] def basis : Fin 3 → U :=
  ![⟨b₁, h.b₁_mem_U⟩, ⟨b₂, h.b₂_mem_U⟩, ⟨u₀, h.u₀_mem⟩]

omit [U.Normal] h in
theorem independent_of_plane {x : Fin 3 → U} (hx0 : (x 0 : Y) ∈ B) (hx1 : (x 1 : Y) ∈ B)
    (h0 : x 0 ≠ 1) (h1 : x 1 ≠ 1) (h10 : x 1 ≠ x 0) (hx2 : (x 2 : Y) ∉ B) : Independent x := by
  refine independent_of_ne h0 h1 h10 ?_ ?_ ?_ ?_
  · intro h2; apply hx2; rw [h2]; exact B.one_mem
  · intro h2; apply hx2; rw [h2]; exact hx0
  · intro h2; apply hx2; rw [h2]; exact hx1
  · intro h2; apply hx2; rw [h2, Subgroup.coe_mul]; exact B.mul_mem hx0 hx1

omit [U.Normal] in
theorem basis_independent : Independent h.basis := by
  refine independent_of_plane h.b₁_mem h.b₂_mem ?_ ?_ ?_ h.u₀_not_mem
  · intro h1; exact h.b₁_ne_one (congrArg Subtype.val h1)
  · intro h1; exact h.b₂_ne_one (congrArg Subtype.val h1)
  · intro h1; exact h.b₂_ne_b₁ (congrArg Subtype.val h1)

omit [U.Normal] in
theorem exists_coords_U {x : Y} (hx : x ∈ U) :
    ∃ a b c : ZMod 2, b₁ ^ a.val * b₂ ^ b.val * u₀ ^ c.val = x := by
  obtain ⟨a, b, c, habc⟩ := exists_coords h.basis_independent h.card_U ⟨x, hx⟩
  exact ⟨a, b, c, by simpa [basis] using congrArg Subtype.val habc⟩

omit [U.Normal] in
theorem mem_B_cases {b : Y} (hb : b ∈ B) : b = 1 ∨ b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂ := by
  obtain ⟨a, b', c, habc⟩ := h.exists_coords_U (h.le hb)
  rcases zmod_two_cases c with rfl | rfl
  · rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b' with rfl | rfl <;>
      simp at habc <;> subst habc <;> simp
  · exfalso
    apply h.u₀_not_mem
    have hp : b₁ ^ a.val * b₂ ^ b'.val ∈ B :=
      B.mul_mem (B.pow_mem h.b₁_mem _) (B.pow_mem h.b₂_mem _)
    have : u₀ = (b₁ ^ a.val * b₂ ^ b'.val)⁻¹ * b := by
      rw [← habc]; simp only [zmod_two_val_one, pow_one]; group
    rw [this]
    exact B.mul_mem (B.inv_mem hp) hb

omit [U.Normal] in
theorem mem_U_cases {x : Y} (hx : x ∈ U) : x ∈ B ∨ u₀ * x ∈ B := by
  obtain ⟨a, b, c, habc⟩ := h.exists_coords_U hx
  have hp : b₁ ^ a.val * b₂ ^ b.val ∈ B :=
    B.mul_mem (B.pow_mem h.b₁_mem _) (B.pow_mem h.b₂_mem _)
  rcases zmod_two_cases c with rfl | rfl
  · left
    rw [← habc]
    simpa using hp
  · right
    rw [← habc]
    simp only [ZMod.val_one, pow_one]
    rw [← mul_assoc, mul_comm_of_mem h.u₀_mem (U.mul_mem (U.pow_mem h.b₁_mem_U _)
      (U.pow_mem h.b₂_mem_U _)), mul_assoc, mul_self_eq_one_of_mem h.u₀_mem, mul_one]
    exact hp

omit [U.Normal] in
theorem not_mem_iff {x : Y} (hx : x ∈ U) : x ∉ B ↔ u₀ * x ∈ B := by
  constructor
  · intro hxB
    exact (h.mem_U_cases hx).resolve_left hxB
  · intro hux hxB
    apply h.u₀_not_mem
    have : u₀ = u₀ * x * x⁻¹ := by group
    rw [this]
    exact B.mul_mem hux (B.inv_mem hxB)

omit [U.Normal] in
theorem U_le_centralizer : U ≤ Subgroup.centralizer (B : Set Y) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact mul_comm_of_mem (h.le hb) hx

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem centralizer_le_normalizer :
    Subgroup.centralizer (B : Set Y) ≤ Subgroup.normalizer (B : Set Y) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have hcomm : ∀ b ∈ B, b * y = y * b := fun b hb => Subgroup.mem_centralizer_iff.mp hy b hb
  constructor
  · intro hb
    rw [← hcomm b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have h1 := hcomm _ hb
    have : b = y * b * y⁻¹ := by
      calc b = y⁻¹ * (y * b * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * b * y⁻¹)) := by rw [h1]
        _ = y * b * y⁻¹ := by group
    rw [this]
    exact hb

omit [IsElementaryAbelian 2 U] h in
theorem conj_mem_U {x y : Y} (hx : x ∈ U) : y * x * y⁻¹ ∈ U :=
  (inferInstance : U.Normal).conj_mem x hx y

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem conj_eq_of_mem_centralizer {b y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y))
    (hb : b ∈ B) : y * b * y⁻¹ = b := by
  rw [← (Subgroup.mem_centralizer_iff.mp hy) b hb, mul_inv_cancel_right]

theorem planeTau_mem {y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y)) :
    planeTau u₀ y ∈ B := by
  have hconjU : y * u₀ * y⁻¹ ∈ U := conj_mem_U h.u₀_mem
  have hnot : y * u₀ * y⁻¹ ∉ B := by
    intro hB
    apply h.u₀_not_mem
    have : u₀ = y⁻¹ * (y * u₀ * y⁻¹) * y := by group
    rw [this]
    have hyinv : y⁻¹ ∈ Subgroup.centralizer (B : Set Y) := Subgroup.inv_mem _ hy
    have := conj_eq_of_mem_centralizer hyinv hB
    rw [inv_inv] at this
    rw [this]
    exact hB
  exact (h.not_mem_iff hconjU).mp hnot

omit [U.Normal] in
theorem conj_u₀ (y : Y) : y * u₀ * y⁻¹ = u₀ * planeTau u₀ y := by
  rw [planeTau, ← mul_assoc, mul_self_eq_one_of_mem h.u₀_mem, one_mul]

theorem conj_of_not_mem {x y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y)) (hx : x ∈ U)
    (hxB : x ∉ B) : y * x * y⁻¹ = x * planeTau u₀ y := by
  have hb := (h.not_mem_iff hx).mp hxB
  have hx' : x = u₀ * (u₀ * x) := by
    rw [← mul_assoc, mul_self_eq_one_of_mem h.u₀_mem, one_mul]
  have hyb := conj_eq_of_mem_centralizer hy hb
  have hτU : planeTau u₀ y ∈ U := h.le (h.planeTau_mem hy)
  calc y * x * y⁻¹ = (y * u₀ * y⁻¹) * (y * (u₀ * x) * y⁻¹) := by
        conv_lhs => rw [hx']
        group
    _ = u₀ * planeTau u₀ y * (u₀ * x) := by rw [h.conj_u₀ y, hyb]
    _ = x * planeTau u₀ y := by
        rw [mul_assoc, mul_comm_of_mem hτU (h.le hb), ← mul_assoc, ← hx']

theorem planeTau_mul {y y' : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y))
    (hy' : y' ∈ Subgroup.centralizer (B : Set Y)) :
    planeTau u₀ (y * y') = planeTau u₀ y * planeTau u₀ y' := by
  have hτ' : planeTau u₀ y' ∈ B := h.planeTau_mem hy'
  calc planeTau u₀ (y * y') = u₀ * (y * (y' * u₀ * y'⁻¹) * y⁻¹) := by
        rw [planeTau]; group
    _ = u₀ * (y * (u₀ * planeTau u₀ y') * y⁻¹) := by rw [h.conj_u₀ y']
    _ = u₀ * ((y * u₀ * y⁻¹) * (y * planeTau u₀ y' * y⁻¹)) := by group
    _ = planeTau u₀ y * planeTau u₀ y' := by
        rw [conj_eq_of_mem_centralizer hy hτ', ← mul_assoc]
        rfl

omit [U.Normal] in
theorem planeTau_eq_one_iff {y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y)) :
    planeTau u₀ y = 1 ↔ y ∈ U := by
  constructor
  · intro h1
    have hyu : y * u₀ * y⁻¹ = u₀ := by
      have := h.conj_u₀ y
      rw [h1, mul_one] at this
      exact this
    rw [← h.centralizer_U, Subgroup.mem_centralizer_iff]
    intro x hx
    rcases h.mem_U_cases hx with hxB | hxB
    · exact (Subgroup.mem_centralizer_iff.mp hy) x hxB
    · have hx' : x = u₀ * (u₀ * x) := by
        rw [← mul_assoc, mul_self_eq_one_of_mem h.u₀_mem, one_mul]
      have hcx := conj_eq_of_mem_centralizer hy hxB
      have hconj : y * x * y⁻¹ = x := by
        calc y * x * y⁻¹ = (y * u₀ * y⁻¹) * (y * (u₀ * x) * y⁻¹) := by
              conv_lhs => rw [hx']
              group
          _ = x := by rw [hyu, hcx, ← hx']
      calc x * y = y * x * y⁻¹ * y := by rw [hconj]
        _ = y * x := by group
  · intro hyU
    rw [planeTau, mul_comm_of_mem hyU h.u₀_mem, mul_inv_cancel_right,
      mul_self_eq_one_of_mem h.u₀_mem]

omit [U.Normal] in
theorem planeTau_of_mem_U {x : Y} (hx : x ∈ U) : planeTau u₀ x = 1 :=
  (h.planeTau_eq_one_iff (h.U_le_centralizer hx)).mpr hx

omit [U.Normal] in
theorem exists_translation {b : Y} (hb : b ∈ B) :
    ∃ y ∈ Subgroup.centralizer (B : Set Y), planeTau u₀ y = b := by
  have hub : u₀ * b ∈ U := U.mul_mem h.u₀_mem (h.le hb)
  let x' : Fin 3 → U := ![⟨b₁, h.b₁_mem_U⟩, ⟨b₂, h.b₂_mem_U⟩, ⟨u₀ * b, hub⟩]
  have hx' : Independent x' := by
    refine independent_of_plane (x := x') h.b₁_mem h.b₂_mem ?_ ?_ ?_ ?_
    · intro h1; exact h.b₁_ne_one (congrArg Subtype.val h1)
    · intro h1; exact h.b₂_ne_one (congrArg Subtype.val h1)
    · intro h1; exact h.b₂_ne_b₁ (congrArg Subtype.val h1)
    · intro hB
      apply h.u₀_not_mem
      have : u₀ = u₀ * b * b⁻¹ := by group
      rw [this]
      exact B.mul_mem hB (B.inv_mem hb)
  let σ := basisAut h.basis_independent hx' h.card_U
  obtain ⟨y, hy⟩ := h.full σ
  have hσ : ∀ i, ((σ (h.basis i) : U) : Y) = (x' i : Y) := fun i => by
    rw [basisAut_apply]
  have hyb₁ : y * b₁ * y⁻¹ = b₁ := by
    have := (hy (h.basis 0)).symm.trans (hσ 0)
    simpa [basis, x'] using this
  have hyb₂ : y * b₂ * y⁻¹ = b₂ := by
    have := (hy (h.basis 1)).symm.trans (hσ 1)
    simpa [basis, x'] using this
  have hyu : y * u₀ * y⁻¹ = u₀ * b := by
    have := (hy (h.basis 2)).symm.trans (hσ 2)
    simpa [basis, x'] using this
  have hyC : y ∈ Subgroup.centralizer (B : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hfix : y * c * y⁻¹ = c := by
      rcases h.mem_B_cases hc with rfl | rfl | rfl | rfl
      · group
      · exact hyb₁
      · exact hyb₂
      · calc y * (b₁ * b₂) * y⁻¹ = (y * b₁ * y⁻¹) * (y * b₂ * y⁻¹) := by group
          _ = b₁ * b₂ := by rw [hyb₁, hyb₂]
    calc c * y = y * c * y⁻¹ * y := by rw [hfix]
      _ = y * c := by group
  refine ⟨y, hyC, ?_⟩
  rw [planeTau, hyu, ← mul_assoc, mul_self_eq_one_of_mem h.u₀_mem, one_mul]

theorem planeTau_conj {n y : Y} (hn : n ∈ Subgroup.normalizer (B : Set Y))
    (hy : y ∈ Subgroup.centralizer (B : Set Y)) :
    planeTau u₀ (n * y * n⁻¹) = n * planeTau u₀ y * n⁻¹ := by
  set u₁ := n⁻¹ * u₀ * n with hu₁
  have hu₁U : u₁ ∈ U := by
    have := conj_mem_U (y := n⁻¹) h.u₀_mem
    rwa [inv_inv] at this
  have hu₁B : u₁ ∉ B := by
    intro hB
    apply h.u₀_not_mem
    have hmem := (Subgroup.mem_normalizer_iff.mp hn u₁).mp hB
    rwa [hu₁, show n * (n⁻¹ * u₀ * n) * n⁻¹ = u₀ by group] at hmem
  have hc := h.conj_of_not_mem hy hu₁U hu₁B
  calc planeTau u₀ (n * y * n⁻¹) = u₀ * (n * (y * u₁ * y⁻¹) * n⁻¹) := by
        rw [planeTau, hu₁]; group
    _ = u₀ * (n * (u₁ * planeTau u₀ y) * n⁻¹) := by rw [hc]
    _ = u₀ * (n * u₁ * n⁻¹) * (n * planeTau u₀ y * n⁻¹) := by group
    _ = n * planeTau u₀ y * n⁻¹ := by
        rw [hu₁, show n * (n⁻¹ * u₀ * n) * n⁻¹ = u₀ by group, mul_self_eq_one_of_mem h.u₀_mem,
          one_mul]

theorem mul_self_mem_B {y : Y} (hy : y ∈ Subgroup.centralizer (B : Set Y)) : y * y ∈ B := by
  have hyy : y * y ∈ Subgroup.centralizer (B : Set Y) := Subgroup.mul_mem _ hy hy
  have hτB : planeTau u₀ y ∈ B := h.planeTau_mem hy
  have hτ : planeTau u₀ (y * y) = 1 := by
    rw [h.planeTau_mul hy hy]
    exact mul_self_eq_one_of_mem (h.le hτB)
  have hyyU : y * y ∈ U := (h.planeTau_eq_one_iff hyy).mp hτ
  by_contra hB
  have hc := h.conj_of_not_mem hy hyyU hB
  rw [show y * (y * y) * y⁻¹ = y * y by group] at hc
  have hτ1 : planeTau u₀ y = 1 := left_eq_mul.mp hc
  have hyU : y ∈ U := (h.planeTau_eq_one_iff hy).mp hτ1
  exact hB (by rw [mul_self_eq_one_of_mem hyU]; exact B.one_mem)

omit [U.Normal] in
theorem isElementaryAbelian_B : IsElementaryAbelian 2 B where
  is_comm := ⟨fun a b => Subtype.ext (mul_comm_of_mem (h.le a.2) (h.le b.2))⟩
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun b => Subtype.ext ?_
    rw [Subgroup.coe_pow, pow_two, OneMemClass.coe_one]
    exact mul_self_eq_one_of_mem (h.le b.2)

omit [U.Normal] in
theorem isKleinFour_B : IsKleinFour B where
  card_four := h.card_B
  exponent_two := by
    have := h.isElementaryAbelian_B
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite B := Nat.finite_of_card_ne_zero (by rw [h.card_B]; omega)
    have : Nontrivial B := by
      rw [← Finite.one_lt_card_iff_nontrivial, h.card_B]; omega
    exact IsElementaryAbelian.exponent_eq_prime

omit [U.Normal] in
theorem exists_normalizer_of_mulAut (α : MulAut B) :
    ∃ n ∈ Subgroup.normalizer (B : Set Y), ∀ b : B, ((α b : B) : Y) = n * b * n⁻¹ := by
  let a₁ : B := α ⟨b₁, h.b₁_mem⟩
  let a₂ : B := α ⟨b₂, h.b₂_mem⟩
  let x' : Fin 3 → U := ![⟨a₁, h.le a₁.2⟩, ⟨a₂, h.le a₂.2⟩, ⟨u₀, h.u₀_mem⟩]
  have ha₁ : (a₁ : Y) ≠ 1 := by
    intro h1
    apply h.b₁_ne_one
    have : α ⟨b₁, h.b₁_mem⟩ = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ α.injective] at this
    exact congrArg Subtype.val this
  have ha₂ : (a₂ : Y) ≠ 1 := by
    intro h1
    apply h.b₂_ne_one
    have : α ⟨b₂, h.b₂_mem⟩ = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ α.injective] at this
    exact congrArg Subtype.val this
  have ha₂₁ : (a₂ : Y) ≠ a₁ := by
    intro h1
    apply h.b₂_ne_b₁
    have := α.injective (Subtype.ext h1 : a₂ = a₁)
    exact congrArg Subtype.val this
  have hx' : Independent x' := by
    refine independent_of_plane (x := x') a₁.2 a₂.2 ?_ ?_ ?_ h.u₀_not_mem
    · intro h1; exact ha₁ (congrArg (fun z : U => (z : Y)) h1)
    · intro h1; exact ha₂ (congrArg (fun z : U => (z : Y)) h1)
    · intro h1; exact ha₂₁ (congrArg (fun z : U => (z : Y)) h1)
  let σ := basisAut h.basis_independent hx' h.card_U
  obtain ⟨y, hy⟩ := h.full σ
  have hσ : ∀ i, ((σ (h.basis i) : U) : Y) = (x' i : Y) := fun i => by
    rw [basisAut_apply]
  have hyb₁ : y * b₁ * y⁻¹ = a₁ := by
    have := (hy (h.basis 0)).symm.trans (hσ 0)
    simpa [basis, x'] using this
  have hyb₂ : y * b₂ * y⁻¹ = a₂ := by
    have := (hy (h.basis 1)).symm.trans (hσ 1)
    simpa [basis, x'] using this
  have hyconj : ∀ b : B, ((α b : B) : Y) = y * b * y⁻¹ := by
    intro b
    rcases h.mem_B_cases b.2 with hb | hb | hb | hb
    · have : b = 1 := Subtype.ext hb
      rw [this, map_one]
      simp
    · have : b = ⟨b₁, h.b₁_mem⟩ := Subtype.ext hb
      rw [this]
      exact hyb₁.symm
    · have : b = ⟨b₂, h.b₂_mem⟩ := Subtype.ext hb
      rw [this]
      exact hyb₂.symm
    · have : b = ⟨b₁, h.b₁_mem⟩ * ⟨b₂, h.b₂_mem⟩ := Subtype.ext hb
      rw [this, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      change (a₁ : Y) * a₂ = y * (b₁ * b₂) * y⁻¹
      rw [← hyb₁, ← hyb₂]
      group
  refine ⟨y, ?_, hyconj⟩
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [← hyconj ⟨c, hc⟩]
    exact (α ⟨c, hc⟩).2
  · intro hc
    obtain ⟨b, hb⟩ := α.surjective ⟨y * c * y⁻¹, hc⟩
    have h1 := hyconj b
    rw [hb] at h1
    have h2 : c = b := by
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
    rw [h2]
    exact b.2

section Cardinality

theorem card_Y : Nat.card Y = 1344 := by
  let ρ : Y →* MulAut U := MulAut.conjNormal
  have hρ : ∀ (g : Y) (z : U), ((ρ g z : U) : Y) = g * z * g⁻¹ := fun g z =>
    MulAut.conjNormal_apply g z
  have hsurj : Function.Surjective ρ := by
    intro σ
    obtain ⟨y, hy⟩ := h.full σ
    exact ⟨y, MulEquiv.ext fun z => Subtype.ext ((hρ y z).trans (hy z).symm)⟩
  have hker : ρ.ker = U := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      rw [← h.centralizer_U, Subgroup.mem_centralizer_iff]
      intro z hz
      have h2 := congrArg (fun σ : MulAut U => ((σ ⟨z, hz⟩ : U) : Y)) h1
      simp only [hρ, MulAut.one_apply] at h2
      calc z * g = g * z * g⁻¹ * g := by rw [h2]
        _ = g * z := by group
    · intro hg
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hρ, MulAut.one_apply, mul_comm_of_mem hg z.2, mul_inv_cancel_right]
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [h.card_U]; omega)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).toEquiv,
    card_mulAut_eq_168 h.card_U, hker, h.card_U]

@[expose] noncomputable def tauHom : Subgroup.centralizer (B : Set Y) →* B where
  toFun y := ⟨planeTau u₀ y, h.planeTau_mem y.2⟩
  map_one' := by
    apply Subtype.ext
    simp [planeTau, mul_self_eq_one_of_mem h.u₀_mem]
  map_mul' y y' := Subtype.ext (h.planeTau_mul y.2 y'.2)

theorem card_C : Nat.card (Subgroup.centralizer (B : Set Y)) = 32 := by
  have hsurj : Function.Surjective h.tauHom := by
    intro b
    obtain ⟨y, hy, hτ⟩ := h.exists_translation b.2
    exact ⟨⟨y, hy⟩, Subtype.ext hτ⟩
  have hker : h.tauHom.ker = U.subgroupOf (Subgroup.centralizer (B : Set Y)) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← h.planeTau_eq_one_iff y.2]
    constructor
    · intro h1; exact congrArg Subtype.val h1
    · intro h1; exact Subtype.ext h1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup h.tauHom.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective h.tauHom hsurj).toEquiv,
    h.card_B, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U_le_centralizer).toEquiv,
    h.card_U]

omit [U.Normal] [IsElementaryAbelian 2 U] h in
theorem restriction_ker :
    (B.normalizerMonoidHom).ker =
      (Subgroup.centralizer (B : Set Y)).subgroupOf (Subgroup.normalizer (B : Set Y)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h2 := congrArg (fun σ : MulAut B => ((σ ⟨b, hb⟩ : B) : Y)) h1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    calc b * (n : Y) = (n : Y) * b * (n : Y)⁻¹ * n := by rw [h2]
      _ = (n : Y) * b := by group
  · intro hn
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
    exact conj_eq_of_mem_centralizer hn b.2

omit [U.Normal] in
theorem restriction_surjective : Function.Surjective (B.normalizerMonoidHom) := by
  intro α
  obtain ⟨n, hn, hα⟩ := h.exists_normalizer_of_mulAut α
  refine ⟨⟨n, hn⟩, MulEquiv.ext fun b => Subtype.ext ?_⟩
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hα]

noncomputable def normalizerQuotientEquiv :
    Subgroup.normalizer (B : Set Y) ⧸
        (Subgroup.centralizer (B : Set Y)).subgroupOf (Subgroup.normalizer (B : Set Y)) ≃*
      MulAut B :=
  (QuotientGroup.quotientMulEquivOfEq (restriction_ker (B := B))).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ h.restriction_surjective)

theorem card_N : Nat.card (Subgroup.normalizer (B : Set Y)) = 192 := by
  have := h.isKleinFour_B
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.centralizer (B : Set Y)).subgroupOf (Subgroup.normalizer (B : Set Y))),
    Nat.card_congr h.normalizerQuotientEquiv.toEquiv,
    CFSG.GorensteinWalter.kleinFourAut_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralizer_le_normalizer (B := B))).toEquiv,
    h.card_C]

end Cardinality

end PlaneHyp

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
