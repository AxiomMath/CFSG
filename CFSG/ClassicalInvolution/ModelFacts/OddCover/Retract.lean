module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open scoped commutatorElement

section Retraction

variable {Y : Type*} [CommGroup Y]

theorem exists_retraction_of_norm (C : Subgroup Y) [Finite C] (φ : MulAut Y) (m : ℕ)
    (hfix : ∀ c ∈ C, φ c = c) (hNC : ∀ y : Y, ∏ i ∈ Finset.range m, (φ ^ i) y ∈ C)
    (hmC : Nat.Coprime m (Nat.card C)) :
    ∃ κ : Y →* C, (∀ c : C, κ c = c) ∧
      ∀ ψ : Y →* Y, (∀ y, ψ (φ y) = φ (ψ y)) → (∀ c ∈ C, ψ c = c) →
        ∀ y, ((κ (ψ y) : C) : Y) = κ y := by
  let N : Y →* Y :=
    { toFun := fun y => ∏ i ∈ Finset.range m, (φ ^ i) y
      map_one' := by simp
      map_mul' := fun y y' => by simp [Finset.prod_mul_distrib] }
  have hNC' : ∀ y, N y ∈ C := hNC
  have hφi : ∀ (i : ℕ), ∀ c ∈ C, (φ ^ i) c = c := by
    intro i
    induction i with
    | zero => intro c _; simp
    | succ i ih =>
      intro c hc
      rw [pow_succ, MulAut.mul_apply, hfix c hc]
      exact ih c hc
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * Nat.card C = 1 := by
    have h := Nat.isCoprime_iff_coprime.2 hmC
    obtain ⟨a, b, hab⟩ := h
    exact ⟨a, b, hab⟩
  have hcpow : ∀ c ∈ C, c ^ (Nat.card C) = 1 := fun c hc => by
    have := pow_card_eq_one' (G := C) (x := ⟨c, hc⟩)
    exact congrArg Subtype.val this
  let κ : Y →* C :=
    { toFun := fun y => ⟨(N y) ^ a, C.zpow_mem (hNC' y) a⟩
      map_one' := by simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        simp [mul_zpow] }
  have hκC : ∀ c : C, κ c = c := by
    intro c
    apply Subtype.ext
    have hNc : N (c : Y) = (c : Y) ^ m := by
      change ∏ i ∈ Finset.range m, (φ ^ i) (c : Y) = _
      rw [Finset.prod_congr rfl (fun i _ => hφi i c c.2)]
      simp
    change (N (c : Y)) ^ a = c
    rw [hNc, ← zpow_natCast, ← zpow_mul]
    have : (m : ℤ) * a = 1 - b * Nat.card C := by linarith
    rw [this, zpow_sub, zpow_one, mul_comm b, zpow_mul, zpow_natCast, hcpow c c.2,
      one_zpow, inv_one, mul_one]
  refine ⟨κ, hκC, fun ψ hψφ hψC y => ?_⟩
  have hψi : ∀ (i : ℕ) (y : Y), ψ ((φ ^ i) y) = (φ ^ i) (ψ y) := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, hψφ]
  have hNψ : N (ψ y) = N y := by
    have h1 : N (ψ y) = ψ (N y) := by
      change ∏ i ∈ Finset.range m, (φ ^ i) (ψ y) = ψ (∏ i ∈ Finset.range m, (φ ^ i) y)
      rw [map_prod]
      exact Finset.prod_congr rfl fun i _ => (hψi i y).symm
    rw [h1]
    exact hψC _ (hNC' y)
  apply congrArg (· ^ a) at hNψ
  exact hNψ

end Retraction

section Subgroups

variable {E : Type*} [Group E]

@[expose] def normSum (z y : E) : ℕ → E
  | 0 => 1
  | m + 1 => normSum z y m * (z ^ m * y * (z ^ m)⁻¹)

@[simp] theorem normSum_zero (z y : E) : normSum z y 0 = 1 := rfl

theorem normSum_succ (z y : E) (m : ℕ) :
    normSum z y (m + 1) = normSum z y m * (z ^ m * y * (z ^ m)⁻¹) := rfl

theorem exists_retraction_fun {Y K : Subgroup E} [Finite K] (hKY : K ≤ Y)
    (hKc : K ≤ Subgroup.center E) (hY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) {z : E}
    (hz : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y) (hz' : ∀ y ∈ Y, z⁻¹ * y * z ∈ Y) {m : ℕ}
    (hmK : Nat.Coprime m (Nat.card K)) (hN : ∀ y ∈ Y, normSum z y m ∈ K) :
    ∃ κ : E → E, (∀ y ∈ Y, κ y ∈ K) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, κ (y * y') = κ y * κ y') ∧
      (∀ c ∈ K, κ c = c) ∧
      ∀ g : E, (∀ y ∈ Y, g * y * g⁻¹ ∈ Y) →
        (∀ y ∈ Y, g * (z * y * z⁻¹) * g⁻¹ = z * (g * y * g⁻¹) * z⁻¹) →
        ∀ y ∈ Y, κ (g * y * g⁻¹) = κ y := by
  classical
  let _ : CommGroup Y :=
    { (inferInstance : Group Y) with mul_comm := fun a b => Subtype.ext (hY a a.2 b b.2) }
  let φ : MulAut Y :=
    { toFun := fun y => ⟨z * y * z⁻¹, hz y y.2⟩
      invFun := fun y => ⟨z⁻¹ * y * z, hz' y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y y' => Subtype.ext (by simp [mul_assoc]) }
  have hφpow : ∀ (i : ℕ) (y : Y), (((φ ^ i) y : Y) : E) = z ^ i * y * (z ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, ih]
      change z ^ i * (z * (y : E) * z⁻¹) * (z ^ i)⁻¹ = _
      group
  have hφnorm : ∀ (m : ℕ) (y : Y), (((∏ i ∈ Finset.range m, (φ ^ i) y : Y)) : E) =
      normSum z y m := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [Finset.prod_range_succ, Subgroup.coe_mul, ih, normSum_succ, hφpow]
  set C : Subgroup Y := K.subgroupOf Y with hCdef
  have hCfin : Finite C := Finite.of_equiv K (Subgroup.subgroupOfEquivOfLe hKY).symm.toEquiv
  have hCcard : Nat.card C = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
  obtain ⟨κ', hκ'C, hκ'inv⟩ := exists_retraction_of_norm C φ m
    (fun c hc => Subtype.ext (by
      have hc' : (c : E) ∈ K := hc
      have := Subgroup.mem_center_iff.1 (hKc hc') z
      change z * (c : E) * z⁻¹ = c
      rw [this, mul_inv_cancel_right]))
    (fun y => by
      change (((∏ i ∈ Finset.range m, (φ ^ i) y : Y)) : E) ∈ K
      rw [hφnorm]
      exact hN y y.2)
    (by rw [hCcard]; exact hmK)
  refine ⟨fun y => if h : y ∈ Y then (((κ' ⟨y, h⟩ : C) : Y) : E) else 1, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [hy, ↓reduceDIte]
    exact (κ' ⟨y, hy⟩).2
  · intro y hy y' hy'
    simp only [hy, hy', Y.mul_mem hy hy', ↓reduceDIte]
    have : κ' (⟨y, hy⟩ * ⟨y', hy'⟩) = κ' ⟨y, hy⟩ * κ' ⟨y', hy'⟩ := map_mul _ _ _
    exact congrArg (fun c : C => ((c : Y) : E)) this
  · intro c hc
    simp only [hKY hc, ↓reduceDIte]
    have := hκ'C ⟨⟨c, hKY hc⟩, hc⟩
    exact congrArg (fun c : C => ((c : Y) : E)) this
  · intro g hg hgz y hy
    simp only [hy, hg y hy, ↓reduceDIte]
    let ψ : Y →* Y :=
      { toFun := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y y' => Subtype.ext (by simp [mul_assoc]) }
    have := hκ'inv ψ (fun y => Subtype.ext (hgz y y.2)) (fun c hc => Subtype.ext (by
      have hc' : (c : E) ∈ K := hc
      have := Subgroup.mem_center_iff.1 (hKc hc') g
      change g * (c : E) * g⁻¹ = c
      rw [this, mul_inv_cancel_right])) ⟨y, hy⟩
    exact congrArg Subtype.val this

theorem commutator_inf_eq_bot_of_fun {K Y G : Subgroup E}
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, ⁅g, h⁆ ∈ Y) {κ : E → E}
    (hmul : ∀ y ∈ Y, ∀ y' ∈ Y, κ (y * y') = κ y * κ y') (hκK : ∀ c ∈ K, κ c = c)
    (hκ0 : ∀ g ∈ G, ∀ h ∈ G, κ ⁅g, h⁆ = 1) : ⁅G, G⁆ ⊓ K = ⊥ := by
  have h1 : κ 1 = 1 := by simpa using hκK 1 K.one_mem
  let M : Subgroup E :=
    { carrier := {y | y ∈ Y ∧ κ y = 1}
      mul_mem' := fun {a b} ha hb => ⟨Y.mul_mem ha.1 hb.1, by rw [hmul a ha.1 b hb.1, ha.2, hb.2,
        one_mul]⟩
      one_mem' := ⟨Y.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨Y.inv_mem ha.1, by
        have := hmul a ha.1 a⁻¹ (Y.inv_mem ha.1)
        rw [mul_inv_cancel, h1, ha.2, one_mul] at this
        exact this.symm⟩ }
  have hle : ⁅G, G⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact ⟨hcomm g hg h hh, hκ0 g hg h hh⟩
  rw [eq_bot_iff]
  rintro c ⟨hcG, hcK⟩
  have := (hle hcG).2
  rw [hκK c hcK] at this
  exact this

end Subgroups

end CFSG.ClassicalInvolution.ModelFacts.OddCover
