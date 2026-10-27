module

public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.M11Model

open CFSG.Sporadic.Mathieu CFSG.Blueprint Equiv Subgroup

private def uP : Perm (Fin 11) :=
  List.formPerm [2, 6, 8] * List.formPerm [3, 9, 10] * List.formPerm [4, 7, 5]

private def vP : Perm (Fin 11) :=
  List.formPerm [2, 10, 7] * List.formPerm [3, 5, 6] * List.formPerm [4, 8, 9]

private def tP : Perm (Fin 11) := List.formPerm [0, 1] * List.formPerm [2, 7, 5, 9, 6, 3, 10, 4]

private def uM : NativeSporadic.M11 :=
  m11b⁻¹ * m11a * m11b * m11b * m11a * m11b⁻¹ * m11a * m11b * m11b

private def vM : NativeSporadic.M11 :=
  m11b * m11b * m11a * m11b⁻¹ * m11a * m11b * m11a * m11b⁻¹ * m11a * m11b⁻¹

private def tM : NativeSporadic.M11 := m11b⁻¹ * m11a * m11b⁻¹ * m11a * m11b * m11b * m11a * m11b⁻¹

private theorem uM_val : (uM : Perm (Fin 11)) = uP := by decide +kernel

private theorem vM_val : (vM : Perm (Fin 11)) = vP := by decide +kernel

private theorem tM_val : (tM : Perm (Fin 11)) = tP := by decide +kernel

private def rHomP : Multiplicative (ZMod 3 × ZMod 3) →* Perm (Fin 11) where
  toFun x := uP ^ (Multiplicative.toAdd x).1.val * vP ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' := by decide +kernel

private theorem rHomP_injective : Function.Injective rHomP := by decide +kernel

private theorem tP_conj :
    ∀ x : Multiplicative (ZMod 3 × ZMod 3), ∃ y, tP * rHomP x * tP⁻¹ = rHomP y := by
  decide +kernel

private theorem tP_orbit :
    ∀ x : Multiplicative (ZMod 3 × ZMod 3), x ≠ 1 →
      ∃ s : Fin 8, tP ^ (s : ℕ) * uP * (tP ^ (s : ℕ))⁻¹ = rHomP x := by
  decide +kernel

private theorem klein_a : m11gA * m11gA = 1 ∧
    (uP * m11gA * uP⁻¹) * (uP * m11gA * uP⁻¹) = 1 ∧
    m11gA * (uP * m11gA * uP⁻¹) = (uP * m11gA * uP⁻¹) * m11gA ∧
    uP * (uP * m11gA * uP⁻¹) * uP⁻¹ = m11gA * (uP * m11gA * uP⁻¹) ∧
    ∀ w : Multiplicative (ZMod 3 × ZMod 3), m11gA * uP * m11gA⁻¹ ≠ rHomP w := by
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

def sylowR : Subgroup NativeSporadic.M11 := rHom.range

theorem sylowR_card : Nat.card sylowR = 3 ^ 2 := by
  rw [sylowR, ← Nat.card_congr (MonoidHom.ofInjective rHom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide

theorem sylowR_comm : ∀ a ∈ sylowR, ∀ b ∈ sylowR, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem sylowR_cube : ∀ a ∈ sylowR, a ^ 3 = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [← map_pow]
  have : x ^ 3 = 1 := by revert x; decide
  rw [this, map_one]

private theorem tM_mem_normalizer : tM ∈ normalizer (sylowR : Set NativeSporadic.M11) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨x, rfl⟩ := hn
  obtain ⟨y, hy⟩ := tP_conj x
  refine ⟨y, Subtype.ext ?_⟩
  simpa [rHom_val, tM_val] using hy.symm

private theorem exists_conj_u {z : NativeSporadic.M11} (hz : z ∈ sylowR) (hz1 : z ≠ 1) :
    ∃ s : ℕ, tM ^ s * uM * (tM ^ s)⁻¹ = z := by
  obtain ⟨x, rfl⟩ := hz
  have hx : x ≠ 1 := fun h => hz1 (by rw [h, map_one])
  obtain ⟨s, hs⟩ := tP_orbit x hx
  refine ⟨s, Subtype.ext ?_⟩
  simpa [rHom_val, tM_val, uM_val] using hs

theorem sylowR_transitive : ∀ a ∈ sylowR, a ≠ 1 → ∀ b ∈ sylowR, b ≠ 1 →
    ∃ n ∈ normalizer (sylowR : Set NativeSporadic.M11), n * a * n⁻¹ = b := by
  intro a ha ha1 b hb hb1
  obtain ⟨s, hs⟩ := exists_conj_u ha ha1
  obtain ⟨r, hr⟩ := exists_conj_u hb hb1
  refine ⟨tM ^ r * (tM ^ s)⁻¹, Subgroup.mul_mem _ (Subgroup.pow_mem _ tM_mem_normalizer r)
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ tM_mem_normalizer s)), ?_⟩
  rw [← hs, ← hr]
  group

theorem sylowR_klein : ∀ z ∈ sylowR, z ≠ 1 → ∃ x y : NativeSporadic.M11, x * x = 1 ∧ y * y = 1 ∧
    x * y = y * x ∧ z * x * z⁻¹ = y ∧ z * y * z⁻¹ = x * y ∧
    x ∉ normalizer (sylowR : Set NativeSporadic.M11) := by
  intro z hz hz1
  obtain ⟨s, hs⟩ := exists_conj_u hz hz1
  obtain ⟨h1, h2, h3, h4, h5⟩ := klein_a
  set n : NativeSporadic.M11 := tM ^ s with hn
  have hnN : n ∈ normalizer (sylowR : Set NativeSporadic.M11) :=
    Subgroup.pow_mem _ tM_mem_normalizer s
  have ha2 : m11a * m11a = 1 := Subtype.ext (by simpa using h1)
  have hy2 : (uM * m11a * uM⁻¹) * (uM * m11a * uM⁻¹) = 1 :=
    Subtype.ext (by simpa [uM_val] using h2)
  have hay : m11a * (uM * m11a * uM⁻¹) = (uM * m11a * uM⁻¹) * m11a :=
    Subtype.ext (by simpa [uM_val] using h3)
  have huy : uM * (uM * m11a * uM⁻¹) * uM⁻¹ = m11a * (uM * m11a * uM⁻¹) :=
    Subtype.ext (by simpa [uM_val] using h4)
  have hnot : m11a ∉ normalizer (sylowR : Set NativeSporadic.M11) := by
    intro hN
    have huR : uM ∈ sylowR := by
      refine ⟨Multiplicative.ofAdd (1, 0), Subtype.ext ?_⟩
      simp [rHom_val, rHomP, uM_val, show ZMod.val (1 : ZMod 3) = 1 from rfl]
    obtain ⟨w, hw⟩ := (mem_normalizer_iff.mp hN uM).mp huR
    exact h5 w (by simpa [rHom_val, uM_val] using congrArg Subtype.val hw.symm)
  refine ⟨n * m11a * n⁻¹, n * (uM * m11a * uM⁻¹) * n⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc n * m11a * n⁻¹ * (n * m11a * n⁻¹) = n * (m11a * m11a) * n⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  · calc n * (uM * m11a * uM⁻¹) * n⁻¹ * (n * (uM * m11a * uM⁻¹) * n⁻¹)
        = n * ((uM * m11a * uM⁻¹) * (uM * m11a * uM⁻¹)) * n⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  · calc n * m11a * n⁻¹ * (n * (uM * m11a * uM⁻¹) * n⁻¹)
        = n * (m11a * (uM * m11a * uM⁻¹)) * n⁻¹ := by group
      _ = n * ((uM * m11a * uM⁻¹) * m11a) * n⁻¹ := by rw [hay]
      _ = n * (uM * m11a * uM⁻¹) * n⁻¹ * (n * m11a * n⁻¹) := by group
  · rw [← hs]
    calc n * uM * n⁻¹ * (n * m11a * n⁻¹) * (n * uM * n⁻¹)⁻¹
        = n * (uM * m11a * uM⁻¹) * n⁻¹ := by group
      _ = n * (uM * m11a * uM⁻¹) * n⁻¹ := rfl
  · rw [← hs]
    calc n * uM * n⁻¹ * (n * (uM * m11a * uM⁻¹) * n⁻¹) * (n * uM * n⁻¹)⁻¹
        = n * (uM * (uM * m11a * uM⁻¹) * uM⁻¹) * n⁻¹ := by group
      _ = n * (m11a * (uM * m11a * uM⁻¹)) * n⁻¹ := by rw [huy]
      _ = n * m11a * n⁻¹ * (n * (uM * m11a * uM⁻¹) * n⁻¹) := by group
  · intro hN
    apply hnot
    have h6 : n⁻¹ * (n * m11a * n⁻¹) * n ∈ normalizer (sylowR : Set NativeSporadic.M11) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hnN) hN) hnN
    simpa [mul_assoc] using h6

theorem sylowR_index : ¬ 3 ∣ sylowR.index := by
  have h := sylowR.index_mul_card
  rw [sylowR_card, card_M11] at h
  have : sylowR.index = 880 := by omega
  rw [this]
  norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.M11Model
