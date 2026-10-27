module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.Uniqueness.SU.KI7

variable {X G : Type*} [Group X] [Group G]

structure CentralKernel (π : X →* G) (z : X) : Prop where
  ne_one : z ≠ 1
  comm : ∀ g : X, g * z = z * g
  map_eq_one : π z = 1
  eq_of_map_eq_one : ∀ x, π x = 1 → x = 1 ∨ x = z

variable {π : X →* G} {z : X}

theorem exists_centralKernel (π : X →* G) (hc : π.ker ≤ Subgroup.center X)
    (h2 : Nat.card π.ker = 2) : ∃ z : X, CentralKernel π z := by
  obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp h2
  refine ⟨z, ⟨fun h => hz1 (Subtype.ext h), fun g => Subgroup.mem_center_iff.mp (hc z.2) g,
    MonoidHom.mem_ker.mp z.2, fun x hx => ?_⟩⟩
  by_cases h : (⟨x, MonoidHom.mem_ker.mpr hx⟩ : π.ker) = 1
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val (hzu _ h))

theorem CentralKernel.mul_self (hK : CentralKernel π z) : z * z = 1 := by
  rcases hK.eq_of_map_eq_one (z * z) (by rw [map_mul, hK.map_eq_one, one_mul]) with h | h
  · exact h
  · exact absurd (mul_left_cancel (a := z) (by rw [mul_one]; exact h)) hK.ne_one

theorem CentralKernel.sq_cases (hK : CentralKernel π z) {y : X} (hy : π y * π y = 1) :
    y * y = 1 ∨ y * y = z :=
  hK.eq_of_map_eq_one _ (by rw [map_mul, hy])

theorem CentralKernel.comm_cases (hK : CentralKernel π z) {y y' : X}
    (h : π y * π y' = π y' * π y) : y * y' = y' * y ∨ y * y' = y' * y * z := by
  have h1 : π (y * y' * (y' * y)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h, mul_inv_cancel]
  rcases hK.eq_of_map_eq_one _ h1 with h2 | h2
  · exact Or.inl (mul_inv_eq_one.mp h2)
  · refine Or.inr ?_
    have h3 : y * y' = z * (y' * y) := mul_inv_eq_iff_eq_mul.mp h2
    rw [h3, ← hK.comm (y' * y)]

theorem CentralKernel.sq_eq_of_conj (hK : CentralKernel π z) {y y' : X} (g : X)
    (hyy : y * y = 1 ∨ y * y = z) (hg : π g * π y * (π g)⁻¹ = π y') : y' * y' = y * y := by
  have hw : π (g * y * g⁻¹ * y'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hg, mul_inv_cancel]
  have hww : (g * y * g⁻¹) * (g * y * g⁻¹) = y * y := by
    have e : (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    rw [e]
    rcases hyy with h | h
    · rw [h]; group
    · rw [h, hK.comm g, mul_inv_cancel_right]
  rcases hK.eq_of_map_eq_one _ hw with h | h
  · have e : g * y * g⁻¹ = y' := mul_inv_eq_one.mp h
    rw [← hww, e]
  · have e : g * y * g⁻¹ = z * y' := mul_inv_eq_iff_eq_mul.mp h
    rw [e] at hww
    rw [← hww]
    calc y' * y' = (z * z) * y' * y' := by rw [hK.mul_self, one_mul]
      _ = z * (z * y') * y' := by group
      _ = z * (y' * z) * y' := by rw [hK.comm y']
      _ = z * y' * (z * y') := by group

theorem sq_eq_one_of_transitive (hK : CentralKernel π z) (S : Subgroup G)
    (hS2 : ∀ s ∈ S, s * s = 1) (s₀ : G)
    (htrans : ∀ s ∈ S, s ≠ 1 → ∃ g : X, π g * s₀ * (π g)⁻¹ = s)
    {y₁ y₂ y₃ : X} (h₁ : π y₁ ∈ S) (h₂ : π y₂ ∈ S) (h₃ : π y₃ ∈ S)
    (n₁ : π y₁ ≠ 1) (n₂ : π y₂ ≠ 1) (n₃ : π y₃ ≠ 1) (n₁₂ : π (y₁ * y₂) ≠ 1)
    (n₁₃ : π (y₁ * y₃) ≠ 1) (n₂₃ : π (y₂ * y₃) ≠ 1) (n₁₂₃ : π (y₁ * (y₂ * y₃)) ≠ 1) :
    ∀ y, π y ∈ S → y * y = 1 := by
  have hinv : ∀ s ∈ S, s⁻¹ = s := fun s hs => inv_eq_of_mul_eq_one_right (hS2 s hs)
  have hSc : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
    intro s hs s' hs'
    calc s * s' = (s * s')⁻¹ := (hinv _ (S.mul_mem hs hs')).symm
      _ = s'⁻¹ * s⁻¹ := mul_inv_rev _ _
      _ = s' * s := by rw [hinv s hs, hinv s' hs']
  have hsq : ∀ y, π y ∈ S → y * y = 1 ∨ y * y = z := fun y hy => hK.sq_cases (hS2 _ hy)
  have hcomm : ∀ y y', π y ∈ S → π y' ∈ S → y * y' = y' * y ∨ y * y' = y' * y * z :=
    fun y y' hy hy' => hK.comm_cases (hSc _ hy _ hy')
  have hconst : ∀ y y', π y ∈ S → π y' ∈ S → π y ≠ 1 → π y' ≠ 1 → y' * y' = y * y := by
    intro y y' hy hy' ny ny'
    obtain ⟨g₁, hg₁⟩ := htrans _ hy ny
    obtain ⟨g₂, hg₂⟩ := htrans _ hy' ny'
    refine hK.sq_eq_of_conj (g₂ * g₁⁻¹) (hsq y hy) ?_
    rw [← hg₁, ← hg₂]
    simp only [map_mul, map_inv]
    group
  have h₁₂ : π (y₁ * y₂) ∈ S := by rw [map_mul]; exact S.mul_mem h₁ h₂
  have h₁₃ : π (y₁ * y₃) ∈ S := by rw [map_mul]; exact S.mul_mem h₁ h₃
  have h₂₃ : π (y₂ * y₃) ∈ S := by rw [map_mul]; exact S.mul_mem h₂ h₃
  have h₁₂₃ : π (y₁ * (y₂ * y₃)) ∈ S := by
    rw [map_mul]; exact S.mul_mem h₁ h₂₃
  rcases hsq y₁ h₁ with hq | hq
  · intro y hy
    by_cases hy1 : π y = 1
    · rcases hK.eq_of_map_eq_one y hy1 with h | h
      · rw [h, one_mul]
      · rw [h, hK.mul_self]
    · rw [hconst y₁ y h₁ hy n₁ hy1, hq]
  · exfalso
    have e₂ : y₂ * y₂ = z := by rw [hconst y₁ y₂ h₁ h₂ n₁ n₂, hq]
    have e₃ : y₃ * y₃ = z := by rw [hconst y₁ y₃ h₁ h₃ n₁ n₃, hq]
    have e₁₂ : y₁ * y₂ * (y₁ * y₂) = z := by rw [hconst y₁ _ h₁ h₁₂ n₁ n₁₂, hq]
    have e₁₃ : y₁ * y₃ * (y₁ * y₃) = z := by rw [hconst y₁ _ h₁ h₁₃ n₁ n₁₃, hq]
    have e₂₃ : y₂ * y₃ * (y₂ * y₃) = z := by rw [hconst y₁ _ h₁ h₂₃ n₁ n₂₃, hq]
    have e₁₂₃ : y₁ * (y₂ * y₃) * (y₁ * (y₂ * y₃)) = z := by
      rw [hconst y₁ _ h₁ h₁₂₃ n₁ n₁₂₃, hq]
    have key : ∀ u v : X, π u ∈ S → π v ∈ S → u * u = z → v * v = z → u * v * (u * v) = z →
        u * v = v * u * z := by
      intro u v hu hv huu hvv huv
      rcases hcomm u v hu hv with h | h
      · exfalso
        have : u * v * (u * v) = u * u * (v * v) := by
          calc u * v * (u * v) = u * (v * u) * v := by group
            _ = u * (u * v) * v := by rw [h]
            _ = u * u * (v * v) := by group
        rw [this, huu, hvv, hK.mul_self] at huv
        exact hK.ne_one huv.symm
      · exact h
    have k₁₂ := key y₁ y₂ h₁ h₂ hq e₂ e₁₂
    have k₁₃ := key y₁ y₃ h₁ h₃ hq e₃ e₁₃
    have k₁₂₃ := key y₁ (y₂ * y₃) h₁ h₂₃ hq e₂₃ e₁₂₃
    have hfin : (y₂ * y₃ * y₁) * z = (y₂ * y₃ * y₁) * 1 := by
      calc (y₂ * y₃) * y₁ * z = y₁ * (y₂ * y₃) := k₁₂₃.symm
        _ = (y₁ * y₂) * y₃ := by group
        _ = (y₂ * y₁ * z) * y₃ := by rw [k₁₂]
        _ = y₂ * y₁ * (z * y₃) := by group
        _ = y₂ * y₁ * (y₃ * z) := by rw [hK.comm y₃]
        _ = y₂ * (y₁ * y₃) * z := by group
        _ = y₂ * (y₃ * y₁ * z) * z := by rw [k₁₃]
        _ = y₂ * y₃ * y₁ * (z * z) := by group
        _ = (y₂ * y₃ * y₁) * 1 := by rw [hK.mul_self]
    exact hK.ne_one (mul_left_cancel hfin)

theorem comm_of_sq_eq_one (S : Subgroup G) (hsq : ∀ y : X, π y ∈ S → y * y = 1) {y y' : X}
    (hy : π y ∈ S) (hy' : π y' ∈ S) : y * y' = y' * y := by
  have hyy' : π (y * y') ∈ S := by rw [map_mul]; exact S.mul_mem hy hy'
  have hinv : ∀ w : X, π w ∈ S → w⁻¹ = w := fun w hw => inv_eq_of_mul_eq_one_right (hsq w hw)
  calc y * y' = (y * y')⁻¹ := (hinv _ hyy').symm
    _ = y'⁻¹ * y⁻¹ := mul_inv_rev _ _
    _ = y' * y := by rw [hinv y hy, hinv y' hy']

theorem conj_step {ĉ g : X} {t s₀ s s' : G} (hĉ : π ĉ = t) (hg : π g * s₀ * (π g)⁻¹ = s)
    (hs : t * s * t⁻¹ = s') : π (ĉ * g) * s₀ * (π (ĉ * g))⁻¹ = s' := by
  rw [map_mul, hĉ, ← hs, ← hg]
  group

theorem card_comap_of_surjective [Finite X] {Y : Type*} [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (K : Subgroup Y) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  have := Finite.of_surjective f hf
  have h1 : (K.comap f).index = K.index := Subgroup.index_comap_of_surjective K hf
  have h2 : Nat.card (K.comap f) * (K.comap f).index = Nat.card X := Subgroup.card_mul_index _
  have h3 : Nat.card K * K.index = Nat.card Y := Subgroup.card_mul_index _
  have h4 : Nat.card f.ker * Nat.card Y = Nat.card X := Subgroup.card_ker_mul_card_of_surjective hf
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (K.comap f) * K.index = Nat.card X := by rw [← h1]; exact h2
    _ = Nat.card f.ker * (Nat.card K * K.index) := by rw [h3, h4]
    _ = Nat.card f.ker * Nat.card K * K.index := by ring

end CFSG.GH74.Uniqueness.SU.KI7
