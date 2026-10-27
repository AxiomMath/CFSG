module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinPair
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowE6

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

section Conj

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem endo_mul_apply' (g h : hV.minGroup k) (v : Fin D.d →₀ k) :
    hV.endo k (g * h) v = hV.endo k g (hV.endo k h v) := by
  rw [MinData.Valid.endo_mul, Module.End.mul_apply]

theorem endo_inv_apply' (g : hV.minGroup k) (v : Fin D.d →₀ k) :
    hV.endo k g⁻¹ (hV.endo k g v) = v := by
  rw [← Module.End.mul_apply, MinData.Valid.endo_inv_mul, Module.End.one_apply]

theorem endo_apply_inv' (g : hV.minGroup k) (v : Fin D.d →₀ k) :
    hV.endo k g (hV.endo k g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, MinData.Valid.endo_mul_inv, Module.End.one_apply]

theorem fixedSub_map_conj (A : Subgroup (hV.minGroup k)) (g : hV.minGroup k) :
    fixedSub (hV := hV) (k := k) (A.map (MulAut.conj g).toMonoidHom) =
      (fixedSub (hV := hV) (k := k) A).map (hV.endo k g) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨hV.endo k g⁻¹ v, fun a ha => ?_, endo_apply_inv' hV k g v⟩
    have h := hv (g * a * g⁻¹) ⟨a, ha, by simp [MulAut.conj_apply]⟩
    calc hV.endo k a (hV.endo k g⁻¹ v)
        = hV.endo k (a * g⁻¹) v := (endo_mul_apply' hV k a g⁻¹ v).symm
      _ = hV.endo k (g⁻¹ * (g * a * g⁻¹)) v := by rw [show a * g⁻¹ = g⁻¹ * (g * a * g⁻¹) by group]
      _ = hV.endo k g⁻¹ (hV.endo k (g * a * g⁻¹) v) := endo_mul_apply' hV k _ _ _
      _ = hV.endo k g⁻¹ v := by rw [h]
  · rintro ⟨w, hw, rfl⟩ a' ⟨a, ha, rfl⟩
    have h := hw a ha
    calc hV.endo k ((MulAut.conj g).toMonoidHom a) (hV.endo k g w)
        = hV.endo k (g * a) w := by
          rw [← endo_mul_apply']; congr 1; simp [MulAut.conj_apply]
      _ = hV.endo k g (hV.endo k a w) := endo_mul_apply' hV k _ _ _
      _ = hV.endo k g w := by rw [h]

theorem natCard_fixedSub_map_conj (A : Subgroup (hV.minGroup k)) (g : hV.minGroup k) :
    Nat.card (fixedSub (hV := hV) (k := k) (A.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (fixedSub (hV := hV) (k := k) A) := by
  rw [fixedSub_map_conj]
  have hinj : Function.Injective (hV.endo k g) :=
    Function.LeftInverse.injective (endo_inv_apply' hV k g)
  exact (Nat.card_congr (Submodule.equivMapOfInjective (hV.endo k g) hinj _).toEquiv).symm

theorem natCard_map_conj' (A : Subgroup (hV.minGroup k)) (g : hV.minGroup k) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  (Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

theorem comm_of_exp_two {G : Type*} [Group G] {A : Subgroup G} (hel : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h1 := hel (a * b) (mul_mem ha hb)
  have h2 := hel a ha
  have h3 := hel b hb
  have : a * b = (a * b)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← sq]; exact h1
  rw [mul_inv_rev] at this
  have ha' : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact h2
  have hb' : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact h3
  rw [ha', hb'] at this
  exact this

theorem bound_of_conj [Finite k] (U : Subgroup (hV.minGroup k))
    (hconj : ∀ A : Subgroup (hV.minGroup k), (∀ a ∈ A, a ^ 2 = 1) →
      ∃ g : hV.minGroup k, A.map (MulAut.conj g).toMonoidHom ≤ U)
    (N1 N2 : ℕ)
    (H : ∀ A : Subgroup (hV.minGroup k), A ≤ U → A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ N1 ∧
        Nat.card A ^ 2 * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ N2)
    (A : Subgroup (hV.minGroup k)) (hne : A ≠ ⊥) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ N1 ∧
      Nat.card A ^ 2 * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ N2 := by
  obtain ⟨g, hg⟩ := hconj A hel
  have hne' : A.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun h => hne (by
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at h)
  have hel' : ∀ b ∈ A.map (MulAut.conj g).toMonoidHom, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hel a ha, map_one]
  have := H _ hg hne' hel'
  rwa [natCard_map_conj' hV k, natCard_fixedSub_map_conj hV k] at this

theorem lt_of_bounds {q a c N1 N2 : ℕ} (hq : 2 ≤ q) (h1 : a * c ≤ q ^ N1)
    (h2 : a ^ 2 * c ≤ q ^ N2) {M1 M2 : ℕ} (hM1 : N1 < M1) (hM2 : N2 + 2 < M2) :
    a * c < q ^ M1 ∧ 4 * (a ^ 2 * c) < q ^ M2 := by
  refine ⟨h1.trans_lt (Nat.pow_lt_pow_right hq hM1), ?_⟩
  have h4 : 4 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq 2
  calc 4 * (a ^ 2 * c) ≤ q ^ 2 * q ^ N2 := Nat.mul_le_mul h4 h2
    _ = q ^ (N2 + 2) := by ring
    _ < q ^ M2 := Nat.pow_lt_pow_right hq hM2

end Conj

section E6

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem posU6_eq : posU6 K = posUnip e6Data_valid K := by
  unfold posU6 posUnip
  simp only [one_mul]

theorem e6_27_pair_bound_all (A : Subgroup (e6Data_valid.minGroup K)) (hA : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fixedSub (hV := e6Data_valid) (k := K) A) ≤ Nat.card K ^ 26 ∧
      Nat.card A ^ 2 * Nat.card (fixedSub (hV := e6Data_valid) (k := K) A) ≤ Nat.card K ^ 42 := by
  have := finite_minGroup6 K
  exact bound_of_conj e6Data_valid K (posU6 K)
    (fun B hB => e6_conj_into_posU6 K B (isPGroup_of_sq B hB)) 26 42
    (fun B hBU hBne hBel => e6_27_pair_bound K (A := B) (by rwa [← posU6_eq K])
      (comm_of_exp_two hBel) hBne) A hA hel

theorem e6_27_no_offender (A : Subgroup (e6Data_valid.minGroup K)) (hA : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fixedSub (hV := e6Data_valid) (k := K) A) < Nat.card K ^ 27 ∧
      4 * (Nat.card A ^ 2 * Nat.card (fixedSub (hV := e6Data_valid) (k := K) A)) <
        Nat.card K ^ 54 := by
  obtain ⟨h1, h2⟩ := e6_27_pair_bound_all K A hA hel
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  exact lt_of_bounds hq h1 h2 (by norm_num) (by norm_num)

end E6

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
