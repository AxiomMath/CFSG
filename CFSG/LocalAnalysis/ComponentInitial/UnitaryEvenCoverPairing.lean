module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverRadical

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 1 K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 0}

theorem conj_central {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) (g : G) :
    g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]

omit [CharP K 2] in
theorem card_eq_four (h : UnitaryFieldData 2 1 K) : Nat.card K = 4 := by
  rw [h.card]
  norm_num

omit [CharP K 2] in
theorem bar_eq_sq (c : K) : h.bar c = c ^ 2 := by
  rw [h.bar_apply, pow_one]

omit [CharP K 2] in
theorem map_bar_transpose (A : Matrix (Fin r) (Fin r) K) : (A.map h.bar)ᵀ = hconj A := by
  ext i j
  rw [transpose_apply, map_apply, bar_eq_sq, hconj_apply]

theorem isHerm_iff {B : Matrix (Fin r) (Fin r) K} : IsHerm h B ↔ hconj B = B := by
  rw [IsHerm, map_bar_transpose]
  constructor
  · intro hB
    rw [eq_neg_of_add_eq_zero_right hB]
    ext i j
    exact CharTwo.neg_eq _
  · intro hB
    rw [hB]
    ext i j
    exact CharTwo.add_self_eq_zero _

omit [CharP K 2] in
theorem offH_eq_hermO (i j : Fin r) (a : K) : offH h i j a = hermO i j a := by
  rw [offH, hermO, bar_eq_sq]

@[expose] def torusSL (e : Fin r → Kˣ) (he : ∏ i, (e i : K) = 1) :
    SpecialLinearGroup (Fin r) K :=
  ⟨diagonal fun i => (e i : K), by rw [det_diagonal, he]⟩

omit [CharP K 2] in
theorem IsN.conj_SL {B : Matrix (Fin r) (Fin r) K} {m g : E} (hm : IsN θ B m)
    (A : SpecialLinearGroup (Fin r) K) (hg : θ g = leviHom h r A) :
    IsN θ (A * B * hconj (A : Matrix (Fin r) (Fin r) K)) (g * m * g⁻¹) := by
  have := hm.conj (slHom h r A) hg
  rwa [map_bar_transpose] at this

omit [CharP K 2] in
theorem exists_unit_ne_one (hK : Nat.card K = 4) :
    ∃ w : Kˣ, (w : K) ≠ 1 ∧ (w : K) ^ 2 ≠ 1 ∧ (w : K) ^ 3 = 1 := by
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  refine ⟨Units.mk0 ω hω0, hω1, fun h2 => hω1 ?_, four_pow_three hK hω0⟩
  have h3 := four_pow_three hK hω0
  rw [Units.val_mk0] at h2
  calc ω = ω ^ 3 / ω ^ 2 := by field_simp
    _ = 1 := by rw [h3, h2, div_one]

omit [CharP K 2] in
theorem prod_mulSingle_mul (a b : Fin r) (c c' : Kˣ) :
    ∏ i, (((Pi.mulSingle a c * Pi.mulSingle b c' : Fin r → Kˣ) i : Kˣ) : K) = c * c' := by
  rw [← Units.coe_prod]
  simp only [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
    Finset.mem_univ, ite_true, Units.val_mul]

omit [CharP K 2] in
theorem mulSingle_mul_apply (a b k : Fin r) (c c' : Kˣ) :
    (((Pi.mulSingle a c * Pi.mulSingle b c' : Fin r → Kˣ) k : Kˣ) : K) =
      (if k = a then (c : K) else 1) * (if k = b then (c' : K) else 1) := by
  rw [Pi.mul_apply, Units.val_mul, Pi.mulSingle_apply, Pi.mulSingle_apply]
  split_ifs <;> simp

theorem isHerm_hermD (k : Fin r) : IsHerm h (hermD k) :=
  isHerm_iff.mpr (hconj_hermD k)

theorem isHerm_hermO (i j : Fin r) (u : K) : IsHerm h (hermO i j u) :=
  isHerm_iff.mpr (hconj_hermO (card_eq_four h) i j u)

omit [CharP K 2] in
theorem map_conj_nElt (A : SpecialLinearGroup (Fin r) K) {g : E} (hg : θ g = leviHom h r A)
    {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) {B' : Matrix (Fin r) (Fin r) K}
    (hB' : IsHerm h B') (he : A * B * hconj (A : Matrix (Fin r) (Fin r) K) = B') :
    θ g * hypProj h r 0 (nElt hB) * (θ g)⁻¹ = hypProj h r 0 (nElt hB') := by
  rw [hg, leviHom, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul,
    lHom_mul_nElt]
  refine congrArg _ (nElt_ext _ _ ?_)
  rw [← he, map_bar_transpose]
  rfl

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem commutatorElement_eq_one_hermO {i j : Fin r} {u : K} {x y : E}
    (hy : IsN θ (hermO i j u) y) (hx : x ∈ preN θ) {A : SpecialLinearGroup (Fin r) K} {g : E}
    (hg : θ g = leviHom h r A) {ζ : K} (hζ : ζ ≠ 1)
    (hAO : ∀ v, A * hermO i j v * hconj (A : Matrix (Fin r) (Fin r) K) = hermO i j (ζ * v))
    (hgx : θ g * θ x * (θ g)⁻¹ = θ x) : ⁅y, x⁆ = 1 := by
  obtain ⟨hB, hyB⟩ := hy
  refine SymplecticCoverFour.commutatorElement_eq_one_of_weight hθ hC
    (ψ := fun v => hypProj h r 0 (nElt (isHerm_hermO i j v)))
    (fun v v' => by
      rw [← map_mul, nElt_mul]
      exact congrArg _ (nElt_ext _ _ (hermO_add i j v v')))
    hζ (fun e v he => commutatorElement_mem_center hC
      (show e ∈ preN θ from ⟨_, nElt_mem_radN _, he.symm⟩) hx)
    (fun v => map_conj_nElt A hg _ _ (hAO v)) hgx (s := u) ?_
  rw [hyB]

theorem torusSL_congr_hermO (hK : Nat.card K = 4) (e : Fin r → Kˣ) (he : ∏ i, (e i : K) = 1)
    (i j : Fin r) (v : K) :
    (torusSL e he : Matrix (Fin r) (Fin r) K) * hermO i j v *
      hconj (torusSL e he : Matrix (Fin r) (Fin r) K) =
        hermO i j ((e i : K) * (e j : K) ^ 2 * v) :=
  diagonal_congr_hermO hK _ i j v

theorem torusSL_congr_hermD (hK : Nat.card K = 4) (e : Fin r → Kˣ) (he : ∏ i, (e i : K) = 1)
    (k : Fin r) :
    (torusSL e he : Matrix (Fin r) (Fin r) K) * hermD k *
      hconj (torusSL e he : Matrix (Fin r) (Fin r) K) = hermD k :=
  diagonal_congr_hermD _ k (four_pow_three hK (e k).ne_zero)

omit [CharP K 2] in
theorem map_conj_eq_of_isN {B : Matrix (Fin r) (Fin r) K} {x g : E} (hx : IsN θ B x)
    (A : SpecialLinearGroup (Fin r) K) (hg : θ g = leviHom h r A)
    (hfix : A * B * hconj (A : Matrix (Fin r) (Fin r) K) = B) : θ g * θ x * (θ g)⁻¹ = θ x := by
  obtain ⟨hB, hxB⟩ := hx
  rw [hxB]
  exact map_conj_nElt A hg hB hB hfix

include hθ hC in
theorem commutatorElement_eq_one_hermO_hermD {i j k : Fin r} (hij : i ≠ j) {u : K} {x y : E}
    (hy : IsN θ (hermO i j u) y) (hx : IsN θ (hermD k) x) : ⁅y, x⁆ = 1 := by
  have hK := card_eq_four h
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_unit_ne_one hK
  set e : Fin r → Kˣ := Pi.mulSingle i w * Pi.mulSingle j w⁻¹ with he_def
  have he : ∏ l, (e l : K) = 1 := by
    rw [he_def, prod_mulSingle_mul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ w.ne_zero]
  obtain ⟨g, hg⟩ := hθ (leviHom h r (torusSL e he))
  have hei : (e i : K) = w := by
    rw [he_def, mulSingle_mul_apply, ite_eq_left rfl, ite_eq_right hij, mul_one]
  have hej : (e j : K) = (w : K)⁻¹ := by
    rw [he_def, mulSingle_mul_apply, ite_eq_right (Ne.symm hij), ite_eq_left rfl,
      one_mul, Units.val_inv_eq_inv_val]
  refine commutatorElement_eq_one_hermO hθ hC hy hx.mem hg (ζ := (w : K)⁻¹)
    (inv_ne_one.mpr hw1) (fun v => ?_)
    (map_conj_eq_of_isN hx _ hg (torusSL_congr_hermD hK e he k))
  rw [torusSL_congr_hermO hK, hei, hej]
  congr 1
  field_simp

include hθ hC in
theorem commutatorElement_eq_one_hermO_hermO (hr : 4 ≤ r) {i j k l : Fin r} (hij : i ≠ j)
    (h₁ : ¬(i = k ∧ j = l)) (h₂ : ¬(i = l ∧ j = k)) {u u' : K} {x y : E}
    (hy : IsN θ (hermO i j u) y) (hx : IsN θ (hermO k l u') x) : ⁅y, x⁆ = 1 := by
  have hK := card_eq_four h
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  obtain ⟨e, he, hekl, heij⟩ := exists_sep_units_prod hK hr hω0 hω1 hij h₁ h₂
  obtain ⟨g, hg⟩ := hθ (leviHom h r (torusSL e he))
  have hcube : ∀ a : Kˣ, (a : K) ^ 3 = 1 := fun a => four_pow_three hK a.ne_zero
  have hζ : (e i : K) * (e j : K) ^ 2 ≠ 1 := by
    intro h1
    apply heij
    refine Units.ext ?_
    have := congrArg (· * (e j : K)) h1
    simp only [one_mul] at this
    rw [mul_assoc, ← pow_succ, hcube, mul_one] at this
    exact this
  refine commutatorElement_eq_one_hermO hθ hC hy hx.mem hg hζ
    (fun v => by rw [torusSL_congr_hermO hK, mul_assoc])
    (map_conj_eq_of_isN hx _ hg ?_)
  rw [torusSL_congr_hermO hK, hekl, ← pow_succ', hcube, one_mul]

include hθ hC in
theorem commutatorElement_eq_one_hermD_hermD (hr : 3 ≤ r) {i j : Fin r} {x y : E}
    (hx : IsN θ (hermD i) x) (hy : IsN θ (hermD j) y) : ⁅x, y⁆ = 1 := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hik : i ≠ k := Ne.symm hki
  set A : SpecialLinearGroup (Fin r) K := SpecialLinearGroup.transvection hik 1 with hA
  have hAm : (A : Matrix (Fin r) (Fin r) K) = hElem i k 1 := rfl
  obtain ⟨g, hg⟩ := hθ (leviHom h r A)
  obtain ⟨xk, hxk⟩ := exists_isN hθ (isHerm_hermD (h := h) k)
  obtain ⟨o, ho⟩ := exists_isN hθ (isHerm_hermO (h := h) i k 1)
  have h1 : IsN θ (hermD k + hermO i k 1 + hermD i) (g * xk * g⁻¹) := by
    refine (hxk.conj_SL A hg).congr ?_
    rw [hAm, hElem_congr_hermD, ite_eq_left rfl, one_pow, ← hermD, add_assoc]
  have h2 : IsN θ (hermD j) (g * y * g⁻¹) := by
    refine (hy.conj_SL A hg).congr ?_
    rw [hAm, hElem_congr_hermD, ite_eq_right (Ne.symm hkj), add_zero]
  have hcen := commutatorElement_mem_center hC hxk.mem hy.mem
  have e1 : ⁅xk, y⁆ = ⁅xk * o * x, y⁆ := by
    rw [← conj_central hcen g, conjugate_commutatorElement]
    exact commutatorElement_eq_of_map_eq' hC (h1.map_eq ((hxk.mul ho).mul hx)) (h2.map_eq hy)
  rw [commutatorElement_mul_preN hC hx.mem hy.mem, commutatorElement_mul_preN hC ho.mem hy.mem,
    commutatorElement_eq_one_hermO_hermD hθ hC hik ho hy, mul_one] at e1
  exact (mul_eq_left.mp e1.symm)

include hθ hC in
theorem commutatorElement_eq_one_of_gen {x : E} (hx : x ∈ preN θ)
    (hD : ∀ (k : Fin r) (y : E), IsN θ (hermD k) y → ⁅y, x⁆ = 1)
    (hO : ∀ (i j : Fin r), i < j → ∀ (u : K) (y : E), IsN θ (hermO i j u) y → ⁅y, x⁆ = 1)
    {y : E} (hy : y ∈ preN θ) : ⁅y, x⁆ = 1 := by
  have hK := card_eq_four h
  let S : AddSubgroup (Matrix (Fin r) (Fin r) K) :=
    { carrier := {B | hconj B = B ∧ ∀ y, IsN θ B y → ⁅y, x⁆ = 1}
      zero_mem' := ⟨by simp [hconj], fun y hy => commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hC (isN_zero_iff.mp hy)) x).symm⟩
      add_mem' := by
        rintro B B' ⟨hB, h1⟩ ⟨hB', h2⟩
        refine ⟨by rw [hconj_add, hB, hB'], fun y hy => ?_⟩
        obtain ⟨y₁, hy₁⟩ := exists_isN hθ (isHerm_iff.mpr hB)
        have hy₂ : IsN θ B' (y₁⁻¹ * y) := (hy₁.inv.mul hy).congr (by abel)
        rw [show y = y₁ * (y₁⁻¹ * y) by group, commutatorElement_mul_preN hC hy₂.mem hx,
          h1 _ hy₁, h2 _ hy₂, one_mul]
      neg_mem' := by
        rintro B ⟨hB, h1⟩
        refine ⟨?_, fun y hy => ?_⟩
        · ext a b
          rw [hconj_apply, Matrix.neg_apply, Matrix.neg_apply, neg_sq, CharTwo.neg_eq,
            ← hconj_apply, hB]
        · have hy' : IsN θ B y⁻¹ := hy.inv.congr (neg_neg B)
          have h2 := commutatorElement_mul_preN hC hy'.mem hx (m₁ := y)
          rw [mul_inv_cancel, commutatorElement_one_left, h1 _ hy', mul_one] at h2
          exact h2.symm }
  obtain ⟨B, hB⟩ := mem_preN.mp hy
  have hBS : B ∈ S := herm_mem (S := S) (fun k => ⟨hconj_hermD k, hD k⟩)
    (fun i j hij u => ⟨hconj_hermO hK i j u, hO i j hij u⟩) (isHerm_iff.mp hB.1)
  exact hBS.2 y hB

include hθ hC in
theorem mul_comm_of_mem_preN [Finite E] (hr : 4 ≤ r) (h2 : IsPGroup 2 θ.ker) {x y : E}
    (hx : x ∈ preN θ) (hy : y ∈ preN θ) : x * y = y * x := by
  have hK := card_eq_four h
  have := h.finite
  have hDD : ∀ (k l : Fin r) (x₀ y₀ : E), IsN θ (hermD k) x₀ → IsN θ (hermD l) y₀ →
      ⁅y₀, x₀⁆ = 1 := fun k l x₀ y₀ hx₀ hy₀ =>
    commutatorElement_eq_one_hermD_hermD hθ hC (by omega) hy₀ hx₀
  have hOD : ∀ (i j : Fin r), i < j → ∀ (u : K) (k : Fin r) (x₀ y₀ : E),
      IsN θ (hermO i j u) y₀ → IsN θ (hermD k) x₀ → ⁅y₀, x₀⁆ = 1 :=
    fun i j hij u k x₀ y₀ hy₀ hx₀ => commutatorElement_eq_one_hermO_hermD hθ hC hij.ne hy₀ hx₀
  have hOO : ∀ (i j : Fin r), i < j → ∀ (u : K) (k l : Fin r), k < l → ∀ (u' : K) (x₀ y₀ : E),
      IsN θ (hermO i j u) y₀ → IsN θ (hermO k l u') x₀ → ⁅y₀, x₀⁆ = 1 := by
    intro i j hij u k l hkl u' x₀ y₀ hy₀ hx₀
    by_cases he : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := he
      rw [← offH_eq_hermO (h := h)] at hy₀ hx₀
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (commute_of_isN_offH (by omega) hr hθ hC h2 hij.ne hy₀ hx₀)
    · exact commutatorElement_eq_one_hermO_hermO hθ hC hr hij.ne he
        (fun h' => absurd (h'.1 ▸ h'.2 ▸ hij) (not_lt.mpr hkl.le)) hy₀ hx₀
  have hgenD : ∀ (k : Fin r) (x₀ : E), IsN θ (hermD k) x₀ → ∀ y ∈ preN θ, ⁅y, x₀⁆ = 1 :=
    fun k x₀ hx₀ y hy => commutatorElement_eq_one_of_gen hθ hC hx₀.mem
      (fun l y₀ hy₀ => hDD k l x₀ y₀ hx₀ hy₀)
      (fun i j hij u y₀ hy₀ => hOD i j hij u k x₀ y₀ hy₀ hx₀) hy
  have hgenO : ∀ (k l : Fin r), k < l → ∀ (u' : K) (x₀ : E), IsN θ (hermO k l u') x₀ →
      ∀ y ∈ preN θ, ⁅y, x₀⁆ = 1 :=
    fun k l hkl u' x₀ hx₀ y hy => commutatorElement_eq_one_of_gen hθ hC hx₀.mem
      (fun m y₀ hy₀ => by
        rw [← commutatorElement_inv, hOD k l hkl u' m y₀ x₀ hx₀ hy₀, inv_one])
      (fun i j hij u y₀ hy₀ => hOO i j hij u k l hkl u' x₀ y₀ hy₀ hx₀) hy
  refine commutatorElement_eq_one_iff_mul_comm.mp ?_
  rw [← commutatorElement_inv, commutatorElement_eq_one_of_gen hθ hC hx
    (fun k y₀ hy₀ => by rw [← commutatorElement_inv, hgenD k y₀ hy₀ x hx, inv_one])
    (fun i j hij u y₀ hy₀ => by rw [← commutatorElement_inv, hgenO i j hij u y₀ hy₀ x hx, inv_one])
    hy, inv_one]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
