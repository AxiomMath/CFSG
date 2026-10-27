module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Equiv Equiv.Perm Subgroup

section Config

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_quaternion_config_perm (p : Fin 8 → α) (hp : Function.Injective p) :
    ∃ a b c t₁ t₂ : Perm α, Perm.sign a = 1 ∧ Perm.sign b = 1 ∧ Perm.sign c = 1 ∧
      a.cycleType = {2, 2} ∧ b.cycleType = {2, 2} ∧ (a * b).cycleType = {2, 2} ∧
      c.cycleType = {2, 2} ∧ (a * c).cycleType = {2, 2, 2, 2} ∧ t₁.IsThreeCycle ∧
      t₂.IsThreeCycle ∧ t₁ * t₂ = c ∧ Commute b t₁ ∧ Commute b t₂ := by
  have hne : ∀ i j : Fin 8, i ≠ j → p i ≠ p j := fun i j h => hp.ne h
  have hd : ∀ i j k l : Fin 8, [i, j, k, l].Nodup →
      Disjoint (swap (p i) (p j)) (swap (p k) (p l)) := fun i j k l h =>
    disjoint_swap_swap (h.map hp)
  have hct : ∀ i j k l : Fin 8, [i, j, k, l].Nodup →
      (swap (p i) (p j) * swap (p k) (p l)).cycleType = {2, 2} := fun i j k l h =>
    cycleType_swap_mul_swap_of_nodup (h.map hp)
  have hsg : ∀ i j k l : Fin 8, i ≠ j → k ≠ l →
      Perm.sign (swap (p i) (p j) * swap (p k) (p l)) = 1 := fun i j k l hij hkl => by
    rw [map_mul, sign_swap (hne i j hij), sign_swap (hne k l hkl)]
    decide
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h03 := hne 0 3 (by decide)
  have h12 := hne 1 2 (by decide)
  have h13 := hne 1 3 (by decide)
  have h23 := hne 2 3 (by decide)
  have hab : swap (p 0) (p 1) * swap (p 2) (p 3) * (swap (p 0) (p 2) * swap (p 1) (p 3)) =
      swap (p 0) (p 3) * swap (p 1) (p 2) := by
    ext x
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
    split_ifs <;> grind
  refine ⟨swap (p 0) (p 1) * swap (p 2) (p 3), swap (p 0) (p 2) * swap (p 1) (p 3),
    swap (p 4) (p 5) * swap (p 6) (p 7), swap (p 4) (p 5) * swap (p 4) (p 6),
    swap (p 4) (p 6) * swap (p 6) (p 7), hsg 0 1 2 3 (by decide) (by decide),
    hsg 0 2 1 3 (by decide) (by decide), hsg 4 5 6 7 (by decide) (by decide),
    hct 0 1 2 3 (by decide), hct 0 2 1 3 (by decide), ?_, hct 4 5 6 7 (by decide), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hab]
    exact hct 0 3 1 2 (by decide)
  · have hdisj : Disjoint (swap (p 0) (p 1) * swap (p 2) (p 3))
        (swap (p 4) (p 5) * swap (p 6) (p 7)) :=
      ((hd 0 1 4 5 (by decide)).mul_right (hd 0 1 6 7 (by decide))).mul_left
        ((hd 2 3 4 5 (by decide)).mul_right (hd 2 3 6 7 (by decide)))
    rw [hdisj.cycleType_mul, hct 0 1 2 3 (by decide), hct 4 5 6 7 (by decide)]
    rfl
  · exact isThreeCycle_swap_mul_swap_same (hne 4 5 (by decide)) (hne 4 6 (by decide))
      (hne 5 6 (by decide))
  · rw [show swap (p 4) (p 6) * swap (p 6) (p 7) = swap (p 6) (p 4) * swap (p 6) (p 7) by
      rw [swap_comm (p 4) (p 6)]]
    exact isThreeCycle_swap_mul_swap_same (hne 6 4 (by decide)) (hne 6 7 (by decide))
      (hne 4 7 (by decide))
  · simp [mul_assoc]
  · exact (((hd 0 2 4 5 (by decide)).mul_right (hd 0 2 4 6 (by decide))).mul_left
        ((hd 1 3 4 5 (by decide)).mul_right (hd 1 3 4 6 (by decide)))).commute
  · exact (((hd 0 2 4 6 (by decide)).mul_right (hd 0 2 6 7 (by decide))).mul_left
        ((hd 1 3 4 6 (by decide)).mul_right (hd 1 3 6 7 (by decide)))).commute

end Config

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem exists_quaternion_config (hn : 8 ≤ n) :
    ∃ a b c t₁ t₂ : alternatingGroup (Fin n),
      (a : Perm (Fin n)).cycleType = {2, 2} ∧ (b : Perm (Fin n)).cycleType = {2, 2} ∧
      ((a * b : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2} ∧
      (c : Perm (Fin n)).cycleType = {2, 2} ∧
      ((a * c : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} ∧
      t₁ ^ 3 = 1 ∧ t₂ ^ 3 = 1 ∧ t₁ * t₂ = c ∧ Commute b t₁ ∧ Commute b t₂ := by
  obtain ⟨a, b, c, t₁, t₂, ha, hb, hc, hca, hcb, hcab, hcc, hcac, ht₁, ht₂, ht, hbt₁, hbt₂⟩ :=
    exists_quaternion_config_perm (Fin.castLE hn) (Fin.castLE_injective hn)
  have h3 : ∀ {g : Perm (Fin n)}, g.IsThreeCycle → ∀ hg : g ∈ alternatingGroup (Fin n),
      (⟨g, hg⟩ : alternatingGroup (Fin n)) ^ 3 = 1 := fun {g} hg _ =>
    Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hg.orderOf, pow_orderOf_eq_one])
  exact ⟨⟨a, Perm.mem_alternatingGroup.mpr ha⟩, ⟨b, Perm.mem_alternatingGroup.mpr hb⟩,
    ⟨c, Perm.mem_alternatingGroup.mpr hc⟩, ⟨t₁, Perm.mem_alternatingGroup.mpr ht₁.sign⟩,
    ⟨t₂, Perm.mem_alternatingGroup.mpr ht₂.sign⟩, hca, hcb, hcab, hcc, hcac, h3 ht₁ _, h3 ht₂ _,
    Subtype.ext ht, Subtype.ext hbt₁.eq, Subtype.ext hbt₂.eq⟩

namespace TwoCover

theorem eq_of_mem_ker_ne_one' (hπ : TwoCover π) {k₁ k₂ : H} (h₁ : k₁ ∈ π.ker) (h₂ : k₂ ∈ π.ker)
    (h₁1 : k₁ ≠ 1) (h₂1 : k₂ ≠ 1) : k₁ = k₂ := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp hπ.card_ker
  have e₁ : (⟨k₁, h₁⟩ : π.ker) = y := hy _ fun h => h₁1 (congrArg Subtype.val h)
  have e₂ : (⟨k₂, h₂⟩ : π.ker) = y := hy _ fun h => h₂1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (e₁.trans e₂.symm)

theorem isConj_of_pow_three_of_isConj (hπ : TwoCover π) {x y : H} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (h : IsConj (π x) (π y)) : IsConj x y := by
  obtain ⟨g, k, hk, hg⟩ := hπ.exists_conj_mul_ker_of_isConj h
  have hkc : Commute y k := Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) y
  have h3 : (y * k) ^ 3 = 1 := by rw [← hg, conj_pow, hx, mul_one, mul_inv_cancel]
  have hk3 : k ^ 3 = 1 := by
    rw [hkc.mul_pow, hy, one_mul] at h3
    exact h3
  have hk1 : k = 1 := by
    calc k = k ^ 3 * (k ^ 2)⁻¹ := by group
      _ = 1 := by rw [hk3, hπ.sq_eq_one_of_mem_ker' hk, inv_one, one_mul]
  exact isConj_iff.mpr ⟨g, by rw [hg, hk1, mul_one]⟩

theorem exists_lift_conj_mul_ker (hπ : TwoCover π) (hn : 8 ≤ n) :
    ∃ x u : H, ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} ∧
      ∃ s ∈ π.ker, s ≠ 1 ∧ u * x * u⁻¹ = x * s := by
  obtain ⟨a, b, c, t₁, t₂, ha, hb, hab, hc, hac, ht₁, ht₂, ht, hbt₁, hbt₂⟩ :=
    exists_quaternion_config hn
  have hn5 : 5 ≤ n := by omega
  obtain ⟨â, hâ⟩ := hπ.surj a
  obtain ⟨û, hû⟩ := hπ.surj b
  obtain ⟨ĉ, hĉ⟩ := hπ.surj c
  obtain ⟨x₁, ⟨hx₁, hx₁3⟩, -⟩ := hπ.existsUnique_lift_pow_three t₁ ht₁
  obtain ⟨x₂, ⟨hx₂, hx₂3⟩, -⟩ := hπ.existsUnique_lift_pow_three t₂ ht₂
  have h1 : Commute û x₁ := hπ.commute_of_pow_three hx₁3 (by rw [hû, hx₁]; exact hbt₁)
  have h2 : Commute û x₂ := hπ.commute_of_pow_three hx₂3 (by rw [hû, hx₂]; exact hbt₂)
  have hk : (x₁ * x₂)⁻¹ * ĉ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hx₁, hx₂, ht, hĉ, inv_mul_cancel]
  have hûk : Commute û ((x₁ * x₂)⁻¹ * ĉ) :=
    Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) û
  have hûĉ : Commute û ĉ := by
    have hĉk : ĉ = x₁ * x₂ * ((x₁ * x₂)⁻¹ * ĉ) := by group
    rw [hĉk]
    exact (h1.mul_right h2).mul_right hûk
  have hâ2 : â ^ 2 ∈ π.ker ∧ â ^ 2 ≠ 1 :=
    hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn5 (by rw [hâ]; exact ha)
  have hu2 : û ^ 2 = â ^ 2 := hπ.sq_eq_of_isConj
    (isConj_alternatingGroup_of_cycleType_eq_two_two (by rw [hû]; exact hb)
      (by rw [hâ]; exact ha)) hâ2.1
  have hxu2 : (â * û) ^ 2 = â ^ 2 := hπ.sq_eq_of_isConj
    (isConj_alternatingGroup_of_cycleType_eq_two_two (by rw [map_mul, hâ, hû]; exact hab)
      (by rw [hâ]; exact ha)) hâ2.1
  have hscomm : ∀ g : H, g * â ^ 2 = â ^ 2 * g :=
    Subgroup.mem_center_iff.mp (hπ.ker_le_center hâ2.1)
  have hs2 : â ^ 2 * â ^ 2 = 1 := by
    rw [← sq]
    exact hπ.sq_eq_one_of_mem_ker' hâ2.1
  have hu2' : û * û = â ^ 2 := by rw [← sq]; exact hu2
  have hx2' : â * â = â ^ 2 := by rw [← sq]
  have hxu2' : â * û * (â * û) = â ^ 2 := by rw [← sq]; exact hxu2
  have hûinv : û⁻¹ = û * â ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hu2', hs2])
  have hâinv : â⁻¹ = â * â ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx2', hs2])
  have hqa : û * â * û⁻¹ = â * â ^ 2 := by
    calc û * â * û⁻¹ = â⁻¹ * (â * û * (â * û)) * â ^ 2 := by rw [hûinv]; group
      _ = â⁻¹ * â ^ 2 * â ^ 2 := by rw [hxu2']
      _ = â⁻¹ := by rw [mul_assoc, hs2, mul_one]
      _ = â * â ^ 2 := hâinv
  refine ⟨â * ĉ, û, ?_, â ^ 2, hâ2.1, hâ2.2, ?_⟩
  · rw [map_mul, hâ, hĉ]
    exact hac
  · calc û * (â * ĉ) * û⁻¹ = (û * â * û⁻¹) * (û * ĉ * û⁻¹) := by group
      _ = (â * â ^ 2) * ĉ := by rw [hqa, hûĉ.eq, mul_inv_cancel_right]
      _ = â * ĉ * â ^ 2 := by rw [mul_assoc, ← hscomm ĉ, ← mul_assoc]

theorem isConj_mul_of_cycleType_two_two_two_two (hπ : TwoCover π) (hn : 8 ≤ n) {x z : H}
    (hx : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2})
    (hz : z ∈ π.ker) : IsConj x (x * z) := by
  by_cases hz1 : z = 1
  · rw [hz1, mul_one]
  obtain ⟨x', u, hx', s, hs, hs1, hu⟩ := hπ.exists_lift_conj_mul_ker hn
  rw [hπ.eq_of_mem_ker_ne_one' hz hs hz1 hs1]
  obtain ⟨g, k, hk, hg⟩ := hπ.exists_conj_mul_ker_of_cycleType_eq (by omega) (c := {2, 2, 2, 2})
    (by simp) hx' hx
  have hkc : ∀ w : H, w * k = k * w := Subgroup.mem_center_iff.mp (hπ.ker_le_center hk)
  have hsc : ∀ w : H, w * s = s * w := Subgroup.mem_center_iff.mp (hπ.ker_le_center hs)
  have e1 : g * u * g⁻¹ * (x * k) * (g * u * g⁻¹)⁻¹ = x * k * s := by
    rw [← hg]
    calc g * u * g⁻¹ * (g * x' * g⁻¹) * (g * u * g⁻¹)⁻¹ = g * (u * x' * u⁻¹) * g⁻¹ := by group
      _ = g * (x' * s) * g⁻¹ := by rw [hu]
      _ = g * x' * g⁻¹ * s := by
        calc g * (x' * s) * g⁻¹ = g * x' * (s * g⁻¹) := by group
          _ = g * x' * (g⁻¹ * s) := by rw [hsc g⁻¹]
          _ = g * x' * g⁻¹ * s := by group
  have e2 : g * u * g⁻¹ * x * (g * u * g⁻¹)⁻¹ * k = x * s * k := by
    calc g * u * g⁻¹ * x * (g * u * g⁻¹)⁻¹ * k
        = g * u * g⁻¹ * x * ((g * u * g⁻¹)⁻¹ * k) := by rw [mul_assoc (g * u * g⁻¹ * x)]
      _ = g * u * g⁻¹ * x * (k * (g * u * g⁻¹)⁻¹) := by rw [hkc (g * u * g⁻¹)⁻¹]
      _ = g * u * g⁻¹ * (x * k) * (g * u * g⁻¹)⁻¹ := by group
      _ = x * k * s := e1
      _ = x * s * k := by rw [mul_assoc, ← hkc s, ← mul_assoc]
  exact isConj_iff.mpr ⟨g * u * g⁻¹, mul_right_cancel e2⟩

theorem isConj_of_orderOf_eq_two (hπ : TwoCover π) (hn : 8 ≤ n) (hn' : n ≤ 11) {x y : H}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxk : x ∉ π.ker) (hyk : y ∉ π.ker) :
    IsConj x y := by
  have hxt := hπ.cycleType_of_orderOf_eq_two hn hn' hx hxk
  have hyt := hπ.cycleType_of_orderOf_eq_two hn hn' hy hyk
  obtain ⟨g, k, hk, hg⟩ := hπ.exists_conj_mul_ker_of_cycleType_eq (by omega) (c := {2, 2, 2, 2})
    (by simp) hxt hyt
  exact (isConj_iff.mpr ⟨g, hg⟩).trans
    (hπ.isConj_mul_of_cycleType_two_two_two_two hn hyt hk).symm

end TwoCover

end CFSG.GH74.Uniqueness.SU.SU13.TA
