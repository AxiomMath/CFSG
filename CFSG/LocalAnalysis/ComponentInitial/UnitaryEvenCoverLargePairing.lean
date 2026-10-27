module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverHerm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverLevi

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 0}

omit [CharP K 2] in
theorem map_conj_nElt' (A : detFixed h r) {g : E} (hg : θ g = hypProj h r 0 (lHom h r A))
    {B : Matrix (Fin r) (Fin r) K} (hB : IsHerm h B) {B' : Matrix (Fin r) (Fin r) K}
    (hB' : IsHerm h B')
    (he : (A : GL (Fin r) K) * B * (((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ =
      B') :
    θ g * hypProj h r 0 (nElt hB) * (θ g)⁻¹ = hypProj h r 0 (nElt hB') := by
  rw [hg, ← map_inv, ← map_mul, ← map_mul, lHom_mul_nElt]
  exact congrArg _ (nElt_ext _ _ he)

omit [CharP K 2] in
theorem map_conj_eq_of_isN' {B : Matrix (Fin r) (Fin r) K} {x g : E} (hx : IsN θ B x)
    (A : detFixed h r) (hg : θ g = hypProj h r 0 (lHom h r A))
    (hfix : (A : GL (Fin r) K) * B *
      (((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = B) :
    θ g * θ x * (θ g)⁻¹ = θ x := by
  obtain ⟨hB, hxB⟩ := hx
  rw [hxB]
  exact map_conj_nElt' A hg hB hB hfix

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem commutatorElement_eq_one_offH {i j : Fin r} {a : K} {x y : E}
    (hy : IsN θ (offH h i j a) y) (hx : x ∈ preN θ) {A : detFixed h r} {g : E}
    (hg : θ g = hypProj h r 0 (lHom h r A)) {ζ : K} (hζ : ζ ≠ 1)
    (hAO : ∀ v, (A : GL (Fin r) K) * offH h i j v *
      (((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = offH h i j (ζ * v))
    (hgx : θ g * θ x * (θ g)⁻¹ = θ x) : ⁅y, x⁆ = 1 := by
  obtain ⟨hB, hyB⟩ := hy
  refine SymplecticCoverFour.commutatorElement_eq_one_of_weight hθ hC
    (ψ := fun v => hypProj h r 0 (nElt (isHerm_offH (h := h) i j v)))
    (fun v v' => by
      rw [← map_mul, nElt_mul]
      exact congrArg _ (nElt_ext _ _ (by simp only [offH, map_add, single_add]; abel)))
    hζ (fun e v he => commutatorElement_mem_center hC
      (show e ∈ preN θ from ⟨_, nElt_mem_radN _, he.symm⟩) hx)
    (fun v => map_conj_nElt' A hg _ _ (hAO v)) hgx (s := a) ?_
  rw [hyB]

include hθ hC in
theorem commutatorElement_eq_one_single {k : Fin r} {a : K} (ha : h.bar a = a) {x y : E}
    (hy : IsN θ (single k k a) y) (hx : x ∈ preN θ) {A : detFixed h r} {g : E}
    (hg : θ g = hypProj h r 0 (lHom h r A)) {ζ : K} (hζF : h.bar ζ = ζ) (hζ : ζ ≠ 1)
    (hAD : ∀ v, (A : GL (Fin r) K) * single k k v *
      (((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = single k k (ζ * v))
    (hgx : θ g * θ x * (θ g)⁻¹ = θ x) : ⁅y, x⁆ = 1 := by
  obtain ⟨hB, hyB⟩ := hy
  have hζ' : (⟨ζ, hζF⟩ : h.fixedField) ≠ 1 := fun h1 => hζ (congrArg Subtype.val h1)
  refine SymplecticCoverFour.commutatorElement_eq_one_of_weight hθ hC
    (ψ := fun v : h.fixedField => hypProj h r 0 (nElt (isHerm_single (k := k) v.2)))
    (fun v v' => by
      rw [← map_mul, nElt_mul]
      exact congrArg _ (nElt_ext _ _ (by rw [Subfield.coe_add, single_add])))
    hζ' (fun e v he => commutatorElement_mem_center hC
      (show e ∈ preN θ from ⟨_, nElt_mem_radN _, he.symm⟩) hx)
    (fun v => map_conj_nElt' A hg _ _ (hAD v)) hgx (s := ⟨a, ha⟩) ?_
  rw [hyB]

omit [CharP K 2] in
theorem exists_fixed_unit (hf : 2 ≤ f) : ∃ s : Kˣ, h.bar (s : K) = s ∧ (s : K) ≠ 1 := by
  have := h.finite
  have hF : 4 ≤ Nat.card h.fixedField := by
    rw [h.card_fixedField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite h.fixedField := Subtype.finite
  obtain ⟨c, hc0, hc1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le (K := h.fixedField)
    (by omega)
  refine ⟨Units.mk0 (c : K) (fun h0 => hc0 (Subtype.ext h0)), c.2, fun h1 => hc1 ?_⟩
  exact Subtype.ext h1

omit [CharP K 2] in
theorem mulSingle_fixed {s : Kˣ} (hs : h.bar (s : K) = s) (m : Fin r) :
    ∀ k, h.bar ((Pi.mulSingle m s : Fin r → Kˣ) k : K) = (Pi.mulSingle m s : Fin r → Kˣ) k := by
  intro k
  rw [Pi.mulSingle_apply]
  split_ifs
  · exact hs
  · rw [Units.val_one, map_one]

omit [CharP K 2] in
theorem mulSingle_val (m k : Fin r) (s : Kˣ) :
    (((Pi.mulSingle m s : Fin r → Kˣ) k : Kˣ) : K) = if k = m then (s : K) else 1 := by
  rw [Pi.mulSingle_apply]
  split_ifs <;> simp

theorem sq_ne_one_of_ne_one' {s : K} (hs : s ≠ 1) : s ^ 2 ≠ 1 := by
  intro h2
  apply hs
  have : (s + 1) ^ 2 = 0 := by
    rw [add_sq, h2, one_pow, mul_one, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul,
      add_zero, CharTwo.add_self_eq_zero]
  have h1 := pow_eq_zero_iff two_ne_zero |>.mp this
  rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
  exact h1

omit [CharP K 2] in
include hθ hC in
theorem commute_of_isN_offH' [Group.IsPerfect (leviHom h r).range]
    (hinj : ∀ y ∈ ⁅(leviHom h r).range.comap θ, (leviHom h r).range.comap θ⁆, θ y = 1 → y = 1)
    {i j : Fin r} (hij : i ≠ j) {a a' : K} {x x' : E} (hx : IsN θ (offH h i j a) x)
    (hx' : IsN θ (offH h i j a') x') : x * x' = x' * x := by
  have : CharP K 2 := h.charP
  obtain ⟨w, hw⟩ := hθ (hypProj h r 0 (swapElt h j))
  have hroot : ∀ (c : K) (y : E), IsN θ (offH h i j c) y →
      θ (w⁻¹ * y * w) = leviHom h r (SpecialLinearGroup.transvection hij c) := by
    intro c y hy
    obtain ⟨hB, he⟩ := hy
    have hsw := swapElt_mul_lHom (h := h) hij (A := SpecialLinearGroup.transvection hij c)
      (a := c) rfl
    rw [map_mul, map_mul, map_inv, hw, he, nElt_ext _ (isHerm_offH i j c) rfl, ← hsw]
    simp only [map_mul, map_inv, leviHom, MonoidHom.comp_apply]
    group
  have hy := hroot a x hx
  have hy' := hroot a' x' hx'
  have hcomm := SymplecticSixCover.mul_comm_of_derivedComap hθ hC (leviHom h r).range hinj
    (x := w⁻¹ * x * w) (y := w⁻¹ * x' * w) (by rw [hy]; exact ⟨_, rfl⟩)
    (by rw [hy']; exact ⟨_, rfl⟩)
    (by
      rw [hy, hy', ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      change Matrix.transvection i j a * Matrix.transvection i j a' =
        Matrix.transvection i j a' * Matrix.transvection i j a
      rw [Matrix.transvection_mul_transvection_same i j hij,
        Matrix.transvection_mul_transvection_same i j hij, add_comm])
  have := congrArg (fun z => w * z * w⁻¹) hcomm
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
  exact this

include hθ hC in
theorem commutatorElement_eq_one_offH_of_out (hf : 2 ≤ f) {i j m : Fin r} (hij : i ≠ j)
    (hm : m = i ∨ m = j) {a : K} {x y : E} (hy : IsN θ (offH h i j a) y)
    {B : Matrix (Fin r) (Fin r) K} (hx : IsN θ B x)
    (hfix : ∀ s : Kˣ, h.bar (s : K) = s → (diagonal fun k =>
      ((Pi.mulSingle m s : Fin r → Kˣ) k : K)) * B *
        ((diagonal fun k => ((Pi.mulSingle m s : Fin r → Kˣ) k : K)).map h.bar)ᵀ = B) :
    ⁅y, x⁆ = 1 := by
  obtain ⟨s, hs, hs1⟩ := exists_fixed_unit (h := h) hf
  set d : Fin r → Kˣ := Pi.mulSingle m s with hd
  have hdF := mulSingle_fixed hs m
  obtain ⟨g, hg⟩ := hθ (hypProj h r 0 (lHom h r (torusF d hdF)))
  have hζ : ((d i : Kˣ) : K) * (d j : K) = s := by
    rw [hd, mulSingle_val, mulSingle_val]
    rcases hm with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij), mul_one]
    · rw [ite_eq_right hij, ite_eq_left rfl, one_mul]
  refine commutatorElement_eq_one_offH hθ hC hy hx.mem hg (ζ := s) hs1 (fun v => ?_)
    (map_conj_eq_of_isN' hx _ hg (hfix s hs))
  rw [coe_torusF, torusF_congr_offH d hdF, hζ]

include hθ hC in
theorem commutatorElement_eq_one_offH_single (hf : 2 ≤ f) {i j k : Fin r} (hij : i ≠ j)
    {a b : K} {x y : E} (hy : IsN θ (offH h i j a) y)
    (hx : IsN θ (single k k b) x) : ⁅y, x⁆ = 1 := by
  set m := if k = i then j else i with hm
  have hmij : m = i ∨ m = j := by
    rw [hm]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hmk : k ≠ m := by
    rw [hm]
    split_ifs with hki
    · rw [hki]
      exact hij
    · exact hki
  refine commutatorElement_eq_one_offH_of_out hθ hC hf hij hmij hy hx fun s hs => ?_
  rw [torusF_congr_single _ (mulSingle_fixed hs m), mulSingle_val, ite_eq_right hmk, one_pow,
    one_mul]

include hθ hC in
theorem commutatorElement_eq_one_offH_offH (hf : 2 ≤ f) {i j k l : Fin r} (hij : i ≠ j)
    (h₁ : ¬(i = k ∧ j = l)) (h₂ : ¬(i = l ∧ j = k)) {a b : K} {x y : E}
    (hy : IsN θ (offH h i j a) y) (hx : IsN θ (offH h k l b) x) : ⁅y, x⁆ = 1 := by
  obtain ⟨m, hmij, hmk, hml⟩ : ∃ m, (m = i ∨ m = j) ∧ m ≠ k ∧ m ≠ l := by
    by_cases hi : i ≠ k ∧ i ≠ l
    · exact ⟨i, Or.inl rfl, hi.1, hi.2⟩
    · refine ⟨j, Or.inr rfl, ?_, ?_⟩
      · intro hjk
        rcases not_and_or.mp hi with h' | h'
        · exact hij ((not_not.mp h').trans hjk.symm)
        · exact h₂ ⟨not_not.mp h', hjk⟩
      · intro hjl
        rcases not_and_or.mp hi with h' | h'
        · exact h₁ ⟨not_not.mp h', hjl⟩
        · exact hij ((not_not.mp h').trans hjl.symm)
  refine commutatorElement_eq_one_offH_of_out hθ hC hf hij hmij hy hx fun s hs => ?_
  rw [torusF_congr_offH _ (mulSingle_fixed hs m), mulSingle_val, mulSingle_val,
    ite_eq_right (Ne.symm hmk), ite_eq_right (Ne.symm hml), one_mul, one_mul]

include hθ hC in
theorem commutatorElement_eq_one_single_single (hf : 2 ≤ f) {i j : Fin r} (hij : i ≠ j)
    {a b : K} (ha : h.bar a = a) {x y : E} (hy : IsN θ (single i i a) y)
    (hx : IsN θ (single j j b) x) : ⁅y, x⁆ = 1 := by
  obtain ⟨s, hs, hs1⟩ := exists_fixed_unit (h := h) hf
  set d : Fin r → Kˣ := Pi.mulSingle i s with hd
  have hdF := mulSingle_fixed hs i
  obtain ⟨g, hg⟩ := hθ (hypProj h r 0 (lHom h r (torusF d hdF)))
  refine commutatorElement_eq_one_single hθ hC ha hy hx.mem hg (ζ := (s : K) ^ 2)
    (by rw [map_pow, hs]) (sq_ne_one_of_ne_one' hs1) (fun v => ?_)
    (map_conj_eq_of_isN' hx _ hg ?_)
  · rw [coe_torusF, torusF_congr_single d hdF, hd, mulSingle_val, ite_eq_left rfl]
  · rw [coe_torusF, torusF_congr_single d hdF, hd, mulSingle_val, ite_eq_right (Ne.symm hij),
      one_pow, one_mul]

omit [CharP K 2] in
include hC in
theorem commutatorElement_preN_mul' {m m₁ m₂ : E} (hm : m ∈ preN θ) (hm₂ : m₂ ∈ preN θ) :
    ⁅m, m₁ * m₂⁆ = ⁅m, m₁⁆ * ⁅m, m₂⁆ := by
  have hc := commutatorElement_mem_center hC hm hm₂
  rw [show ⁅m, m₁ * m₂⁆ = ⁅m, m₁⁆ * (m₁ * ⁅m, m₂⁆ * m₁⁻¹) by
      simp only [commutatorElement_def]; group,
    Subgroup.mem_center_iff.mp hc m₁, mul_inv_cancel_right]

theorem conj_eq_of_mem_center' {z : E} (hz : z ∈ Subgroup.center E) (g : E) :
    g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]

theorem commutatorElement_eq_one_symm {a b : E} (hab : ⁅a, b⁆ = 1) : ⁅b, a⁆ = 1 := by
  rw [← commutatorElement_inv, hab, inv_one]

include hθ hC in
theorem commutatorElement_eq_one_single_same (hf : 2 ≤ f) (hr : 2 ≤ r)
    [Group.IsPerfect (leviHom h r).range]
    (hinj : ∀ y ∈ ⁅(leviHom h r).range.comap θ, (leviHom h r).range.comap θ⁆, θ y = 1 → y = 1)
    {k : Fin r} {a b : K} (ha : h.bar a = a) (hb : h.bar b = b) {x y : E}
    (hx : IsN θ (single k k a) x) (hy : IsN θ (single k k b) y) : ⁅x, y⁆ = 1 := by
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨i, hik⟩ := exists_ne k
  have hki : k ≠ i := Ne.symm hik
  set A : SpecialLinearGroup (Fin r) K := SpecialLinearGroup.transvection hki 1 with hA
  obtain ⟨g, hg⟩ := hθ (leviHom h r A)
  obtain ⟨xi, hxi⟩ := exists_isN hθ (isHerm_single (k := i) ha)
  obtain ⟨yi, hyi⟩ := exists_isN hθ (isHerm_single (k := i) hb)
  obtain ⟨o, ho⟩ := exists_isN hθ (isHerm_offH (h := h) k i a)
  obtain ⟨o', ho'⟩ := exists_isN hθ (isHerm_offH (h := h) k i b)
  have hconj : ∀ {c : K}, h.bar c = c → ∀ {z : E}, IsN θ (single i i c) z →
      IsN θ (single i i c + offH h k i c + single k k c) (g * z * g⁻¹) := fun hc z hz => by
    refine (hz.conj (slHom h r A) hg).congr ?_
    exact transvection_congr_single i k hc
  have e1 : ⁅xi, yi⁆ = ⁅xi * o * x, yi * o' * y⁆ := by
    rw [← conj_eq_of_mem_center' (commutatorElement_mem_center hC hxi.mem hyi.mem) g,
      conjugate_commutatorElement]
    exact commutatorElement_eq_of_map_eq' hC ((hconj ha hxi).map_eq ((hxi.mul ho).mul hx))
      ((hconj hb hyi).map_eq ((hyi.mul ho').mul hy))
  have hL := ((hxi.mul ho).mul hx).mem
  have e2 : ∀ Z ∈ preN θ, ⁅xi * o * x, Z⁆ = ⁅xi, Z⁆ * ⁅o, Z⁆ * ⁅x, Z⁆ := fun Z hZ => by
    rw [commutatorElement_mul_preN hC hx.mem hZ, commutatorElement_mul_preN hC ho.mem hZ]
  rw [commutatorElement_preN_mul' hC hL hy.mem, commutatorElement_preN_mul' hC hL ho'.mem,
    e2 _ hyi.mem, e2 _ ho'.mem, e2 _ hy.mem] at e1
  have hP1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (commute_of_isN_offH' hθ hC hinj hki ho ho')
  have hxio' := commutatorElement_eq_one_symm
    (commutatorElement_eq_one_offH_single hθ hC hf hki ho' hxi)
  have hoyi := commutatorElement_eq_one_offH_single hθ hC hf hki ho hyi
  have hoy := commutatorElement_eq_one_offH_single hθ hC hf hki ho hy
  have hxo' := commutatorElement_eq_one_symm
    (commutatorElement_eq_one_offH_single hθ hC hf hki ho' hx)
  have hxiy := commutatorElement_eq_one_single_single hθ hC hf hik ha hxi hy
  have hxyi := commutatorElement_eq_one_single_single hθ hC hf hki ha hx hyi
  rw [hP1, hxio', hoyi, hoy, hxo', hxiy, hxyi] at e1
  simp only [mul_one, one_mul] at e1
  exact mul_eq_left.mp e1.symm

include hθ hC in
theorem commutatorElement_eq_one_of_gen' {x : E} (hx : x ∈ preN θ)
    (hD : ∀ (k : Fin r) (a : K), h.bar a = a → ∀ y : E, IsN θ (single k k a) y → ⁅y, x⁆ = 1)
    (hO : ∀ (i j : Fin r), i < j → ∀ (a : K) (y : E), IsN θ (offH h i j a) y → ⁅y, x⁆ = 1)
    {y : E} (hy : y ∈ preN θ) : ⁅y, x⁆ = 1 := by
  let S : AddSubgroup (Matrix (Fin r) (Fin r) K) :=
    { carrier := {B | IsHerm h B ∧ ∀ y, IsN θ B y → ⁅y, x⁆ = 1}
      zero_mem' := ⟨isHerm_zero h, fun y hy => commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hC (isN_zero_iff.mp hy)) x).symm⟩
      add_mem' := by
        rintro B B' ⟨hB, h1⟩ ⟨hB', h2⟩
        refine ⟨isHerm_add hB hB', fun y hy => ?_⟩
        obtain ⟨y₁, hy₁⟩ := exists_isN hθ hB
        have hy₂ : IsN θ B' (y₁⁻¹ * y) := (hy₁.inv.mul hy).congr (by abel)
        rw [show y = y₁ * (y₁⁻¹ * y) by group, commutatorElement_mul_preN hC hy₂.mem hx,
          h1 _ hy₁, h2 _ hy₂, one_mul]
      neg_mem' := by
        rintro B ⟨hB, h1⟩
        refine ⟨isHerm_neg hB, fun y hy => ?_⟩
        have hy' : IsN θ B y⁻¹ := hy.inv.congr (neg_neg B)
        have h2 := commutatorElement_mul_preN hC hy'.mem hx (m₁ := y)
        rw [mul_inv_cancel, commutatorElement_one_left, h1 _ hy', mul_one] at h2
        exact h2.symm }
  obtain ⟨B, hB⟩ := mem_preN.mp hy
  have hBS : B ∈ S := herm_mem' (S := S)
    (fun k a ha => ⟨isHerm_single ha, hD k a ha⟩)
    (fun i j hij a => ⟨isHerm_offH i j a, hO i j hij a⟩) hB.1
  exact hBS.2 y hB

include hθ hC in
theorem mul_comm_of_mem_preN_large [Finite E] (hf : 2 ≤ f) (hr : 2 ≤ r)
    (h2 : IsPGroup 2 θ.ker) {x y : E} (hx : x ∈ preN θ) (hy : y ∈ preN θ) : x * y = y * x := by
  obtain ⟨hperf, hinj⟩ := exists_levi_split_large hf hr hθ hC h2
  have hDD : ∀ (k l : Fin r) (a b : K), h.bar a = a → h.bar b = b → ∀ (x₀ y₀ : E),
      IsN θ (single k k a) x₀ → IsN θ (single l l b) y₀ → ⁅y₀, x₀⁆ = 1 := by
    intro k l a b ha hb x₀ y₀ hx₀ hy₀
    by_cases hkl : l = k
    · subst hkl
      exact commutatorElement_eq_one_single_same hθ hC hf hr hinj hb ha hy₀ hx₀
    · exact commutatorElement_eq_one_single_single hθ hC hf hkl hb hy₀ hx₀
  have hOD : ∀ (i j : Fin r), i < j → ∀ (a : K) (k : Fin r) (b : K) (x₀ y₀ : E),
      IsN θ (offH h i j a) y₀ → IsN θ (single k k b) x₀ → ⁅y₀, x₀⁆ = 1 :=
    fun i j hij a k b x₀ y₀ hy₀ hx₀ => commutatorElement_eq_one_offH_single hθ hC hf hij.ne hy₀ hx₀
  have hOO : ∀ (i j : Fin r), i < j → ∀ (a : K) (k l : Fin r), k < l → ∀ (b : K) (x₀ y₀ : E),
      IsN θ (offH h i j a) y₀ → IsN θ (offH h k l b) x₀ → ⁅y₀, x₀⁆ = 1 := by
    intro i j hij a k l hkl b x₀ y₀ hy₀ hx₀
    by_cases he : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := he
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (commute_of_isN_offH' hθ hC hinj hij.ne hy₀ hx₀)
    · exact commutatorElement_eq_one_offH_offH hθ hC hf hij.ne he
        (fun h' => absurd (h'.1 ▸ h'.2 ▸ hij) (not_lt.mpr hkl.le)) hy₀ hx₀
  have hgenD : ∀ (k : Fin r) (b : K), h.bar b = b → ∀ (x₀ : E), IsN θ (single k k b) x₀ →
      ∀ y ∈ preN θ, ⁅y, x₀⁆ = 1 :=
    fun k b hb x₀ hx₀ y hy => commutatorElement_eq_one_of_gen' hθ hC hx₀.mem
      (fun l a ha y₀ hy₀ => hDD k l b a hb ha x₀ y₀ hx₀ hy₀)
      (fun i j hij a y₀ hy₀ => hOD i j hij a k b x₀ y₀ hy₀ hx₀) hy
  have hgenO : ∀ (k l : Fin r), k < l → ∀ (b : K) (x₀ : E), IsN θ (offH h k l b) x₀ →
      ∀ y ∈ preN θ, ⁅y, x₀⁆ = 1 :=
    fun k l hkl b x₀ hx₀ y hy => commutatorElement_eq_one_of_gen' hθ hC hx₀.mem
      (fun m a ha y₀ hy₀ => commutatorElement_eq_one_symm (hOD k l hkl b m a y₀ x₀ hx₀ hy₀))
      (fun i j hij a y₀ hy₀ => hOO i j hij a k l hkl b x₀ y₀ hy₀ hx₀) hy
  refine commutatorElement_eq_one_iff_mul_comm.mp (commutatorElement_eq_one_symm ?_)
  exact commutatorElement_eq_one_of_gen' hθ hC hx
    (fun k b hb y₀ hy₀ => commutatorElement_eq_one_symm (hgenD k b hb y₀ hy₀ x hx))
    (fun i j hij a y₀ hy₀ => commutatorElement_eq_one_symm (hgenO i j hij a y₀ hy₀ x hx)) hy

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
