module

public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.M11Model

open CFSG.Sporadic.Mathieu CFSG.Blueprint Equiv Subgroup

private def uP : Perm (Fin 11) :=
  List.formPerm [2, 6, 8] * List.formPerm [3, 9, 10] * List.formPerm [4, 7, 5]

private def vP : Perm (Fin 11) :=
  List.formPerm [2, 10, 7] * List.formPerm [3, 5, 6] * List.formPerm [4, 8, 9]

private def tP : Perm (Fin 11) := List.formPerm [0, 1] * List.formPerm [2, 7, 5, 9, 6, 3, 10, 4]

private def sP : Perm (Fin 11) :=
  List.formPerm [0, 1] * List.formPerm [3, 4] * List.formPerm [5, 10] * List.formPerm [7, 9]

private def uM : NativeSporadic.M11 :=
  m11b⁻¹ * m11a * m11b * m11b * m11a * m11b⁻¹ * m11a * m11b * m11b

private def vM : NativeSporadic.M11 :=
  m11b * m11b * m11a * m11b⁻¹ * m11a * m11b * m11a * m11b⁻¹ * m11a * m11b⁻¹

private def tM : NativeSporadic.M11 := m11b⁻¹ * m11a * m11b⁻¹ * m11a * m11b * m11b * m11a * m11b⁻¹

private def sM : NativeSporadic.M11 :=
  m11b⁻¹ * m11a * m11b * m11a * m11b * m11b * m11a * m11b⁻¹ * m11b⁻¹ * m11a⁻¹ * m11b *
    m11a⁻¹ * m11b

private theorem uM_val : (uM : Perm (Fin 11)) = uP := by decide +kernel
private theorem vM_val : (vM : Perm (Fin 11)) = vP := by decide +kernel
private theorem tM_val : (tM : Perm (Fin 11)) = tP := by decide +kernel
private theorem sM_val : (sM : Perm (Fin 11)) = sP := by decide +kernel

private def rHomP : Multiplicative (ZMod 3 × ZMod 3) →* Perm (Fin 11) where
  toFun x := uP ^ (Multiplicative.toAdd x).1.val * vP ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' := by decide +kernel

private theorem rHomP_injective : Function.Injective rHomP := by decide +kernel

private theorem tP_conj :
    ∀ x : Multiplicative (ZMod 3 × ZMod 3), ∃ y, tP * rHomP x * tP⁻¹ = rHomP y := by
  decide +kernel

private theorem sP_conj :
    ∀ x : Multiplicative (ZMod 3 × ZMod 3), ∃ y, sP * rHomP x * sP⁻¹ = rHomP y := by
  decide +kernel

private theorem tP_orbit :
    ∀ x : Multiplicative (ZMod 3 × ZMod 3), x ≠ 1 →
      ∃ s : Fin 8, tP ^ (s : ℕ) * uP * (tP ^ (s : ℕ))⁻¹ = rHomP x := by
  decide +kernel

private theorem rHomP_mem (x : Multiplicative (ZMod 3 × ZMod 3)) :
    rHomP x ∈ NativeSporadic.M11 := by
  have h := (uM ^ (Multiplicative.toAdd x).1.val * vM ^ (Multiplicative.toAdd x).2.val).2
  simpa [Subgroup.coe_mul, Subgroup.coe_pow, uM_val, vM_val, rHomP] using h

private def rHom : Multiplicative (ZMod 3 × ZMod 3) →* NativeSporadic.M11 :=
  rHomP.codRestrict NativeSporadic.M11 rHomP_mem

private theorem rHom_val (x : Multiplicative (ZMod 3 × ZMod 3)) :
    ((rHom x : NativeSporadic.M11) : Perm (Fin 11)) = rHomP x := rfl

private theorem rHom_injective : Function.Injective rHom := fun x y h =>
  rHomP_injective (by simpa [rHom_val] using congrArg Subtype.val h)

private def R : Subgroup NativeSporadic.M11 := rHom.range

private theorem R_card : Nat.card R = 3 ^ 2 := by
  rw [R, ← Nat.card_congr (MonoidHom.ofInjective rHom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide

private theorem R_comm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

private theorem R_cube : ∀ a ∈ R, a ^ 3 = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [← map_pow]
  have : x ^ 3 = 1 := by revert x; decide
  rw [this, map_one]

private theorem mem_normalizer_of_conj {g : NativeSporadic.M11} {gP : Perm (Fin 11)}
    (hg : (g : Perm (Fin 11)) = gP)
    (h : ∀ x : Multiplicative (ZMod 3 × ZMod 3), ∃ y, gP * rHomP x * gP⁻¹ = rHomP y) :
    g ∈ normalizer (R : Set NativeSporadic.M11) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨x, rfl⟩ := hn
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, Subtype.ext ?_⟩
  simpa [rHom_val, hg] using hy.symm

private theorem tM_mem : tM ∈ normalizer (R : Set NativeSporadic.M11) :=
  mem_normalizer_of_conj tM_val tP_conj

private theorem sM_mem : sM ∈ normalizer (R : Set NativeSporadic.M11) :=
  mem_normalizer_of_conj sM_val sP_conj

private theorem R_transitive : ∀ a ∈ R, a ≠ 1 → ∀ b ∈ R, b ≠ 1 →
    ∃ n ∈ normalizer (R : Set NativeSporadic.M11), n * a * n⁻¹ = b := by
  have key : ∀ {z : NativeSporadic.M11}, z ∈ R → z ≠ 1 →
      ∃ k : ℕ, tM ^ k * uM * (tM ^ k)⁻¹ = z := by
    intro z hz hz1
    obtain ⟨x, rfl⟩ := hz
    have hx : x ≠ 1 := fun h => hz1 (by rw [h, map_one])
    obtain ⟨k, hk⟩ := tP_orbit x hx
    refine ⟨k, Subtype.ext ?_⟩
    simpa [rHom_val, tM_val, uM_val] using hk
  intro a ha ha1 b hb hb1
  obtain ⟨s, hs⟩ := key ha ha1
  obtain ⟨r, hr⟩ := key hb hb1
  refine ⟨tM ^ r * (tM ^ s)⁻¹, Subgroup.mul_mem _ (Subgroup.pow_mem _ tM_mem r)
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ tM_mem s)), ?_⟩
  rw [← hs, ← hr]
  group

private theorem sP_sq : sP * sP = 1 := by decide +kernel
private theorem sP_conj_t : sP * tP * sP⁻¹ = tP ^ 3 := by decide +kernel
private theorem tP_pow8 : tP ^ 8 = 1 := by decide +kernel
private theorem tP_pow4 : tP ^ 4 ≠ 1 := by decide +kernel

private def zP (x : Fin 8 × Fin 2) : Perm (Fin 11) := tP ^ (x.1 : ℕ) * sP ^ (x.2 : ℕ)

private theorem zP_injective : Function.Injective zP := by decide +kernel

private theorem zP_mul : ∀ x y : Fin 8 × Fin 2, ∃ z, zP x * zP y = zP z := by decide +kernel

private theorem zP_inv : ∀ x : Fin 8 × Fin 2, ∃ z, (zP x)⁻¹ = zP z := by decide +kernel

private def zM (x : Fin 8 × Fin 2) : NativeSporadic.M11 := tM ^ (x.1 : ℕ) * sM ^ (x.2 : ℕ)

private theorem zM_val (x : Fin 8 × Fin 2) : (zM x : Perm (Fin 11)) = zP x := by
  simp [zM, zP, tM_val, sM_val]

private theorem zM_injective : Function.Injective zM := fun x y h =>
  zP_injective (by rw [← zM_val, ← zM_val, h])

private def S : Subgroup NativeSporadic.M11 where
  carrier := Set.range zM
  one_mem' := ⟨(0, 0), by apply Subtype.ext; simp [zM_val, zP]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := zP_mul x y
    exact ⟨z, Subtype.ext (by simp [zM_val, hz])⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := zP_inv x
    exact ⟨z, Subtype.ext (by simp [zM_val, hz])⟩

private theorem S_card : Nat.card S = 16 := by
  have : Nat.card S = Nat.card (Set.range zM) := rfl
  rw [this, Nat.card_range_of_injective zM_injective]
  simp

private theorem tM_mem_S : tM ∈ S := ⟨(1, 0), by apply Subtype.ext; simp [zM_val, zP, tM_val]⟩
private theorem sM_mem_S : sM ∈ S := ⟨(0, 1), by apply Subtype.ext; simp [zM_val, zP, sM_val]⟩

private theorem S_eq_closure : S = Subgroup.closure {tM, sM} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact tM_mem_S
    · exact sM_mem_S

private theorem S_le_normalizer : S ≤ normalizer (R : Set NativeSporadic.M11) := by
  rw [S_eq_closure, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact tM_mem
  · exact sM_mem

private theorem tM_order : orderOf tM = 8 := by
  have h8 : tM ^ 8 = 1 := Subtype.ext (by simpa [tM_val] using tP_pow8)
  have h4 : ¬ tM ^ 4 = 1 := fun h => tP_pow4 (by simpa [tM_val] using congrArg Subtype.val h)
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := tM) (by simpa using h4) (by simpa using h8)
  simpa using this

private theorem sM_order : orderOf sM = 2 := by
  have h2 : sM ^ 2 = 1 := Subtype.ext (by simpa [sM_val, pow_two] using sP_sq)
  have h1 : sM ≠ 1 := fun h => by
    have : sP = 1 := by simpa [sM_val] using congrArg Subtype.val h
    revert this; decide +kernel
  exact orderOf_eq_prime h2 h1

private theorem sM_conj_t : sM * tM * sM⁻¹ = tM ^ 3 :=
  Subtype.ext (by simpa [sM_val, tM_val] using sP_conj_t)

theorem exists_m11_local_data :
    ∃ R₀ S₀ : Subgroup NativeSporadic.M11, Nat.card R₀ = 3 ^ 2 ∧
      (∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a) ∧ (∀ a ∈ R₀, a ^ 3 = 1) ∧ Nat.card S₀ = 16 ∧
      S₀ ≤ normalizer (R₀ : Set NativeSporadic.M11) ∧
      (∃ a ∈ S₀, ∃ b ∈ S₀, orderOf a = 8 ∧ orderOf b = 2 ∧ b * a * b⁻¹ = a ^ 3 ∧
        S₀ = Subgroup.closure {a, b}) ∧
      (∀ a ∈ R₀, a ≠ 1 → ∀ b ∈ R₀, b ≠ 1 →
        ∃ n ∈ normalizer (R₀ : Set NativeSporadic.M11), n * a * n⁻¹ = b) :=
  ⟨R, S, R_card, R_comm, R_cube, S_card, S_le_normalizer,
    ⟨tM, tM_mem_S, sM, sM_mem_S, tM_order, sM_order, sM_conj_t, S_eq_closure⟩, R_transitive⟩

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.M11Model
