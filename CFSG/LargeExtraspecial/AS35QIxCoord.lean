module

public import CFSG.LargeExtraspecial.AS35QThCoordB
public import CFSG.LargeExtraspecial.AS35QThXa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

section Heis

variable {H : Type*} [Group H] [Finite H]

theorem exists_heisenberg_basis_inv {X : Subgroup H} (hcard : Nat.card X = 27)
    (hnc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) {t : H} (ht : t * t = 1)
    (htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hC : Nat.card (X ⊓ Subgroup.centralizer {t} : Subgroup H) = 3)
    (hZt : ∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c * t = t * c) :
    ∃ a b ζ : H, a ∈ X ∧ b ∈ X ∧ ζ ∈ X ∧ (∀ x ∈ X, ζ * x = x * ζ) ∧ ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧
      a * b = ζ * (b * a) ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ t * a * t⁻¹ = a⁻¹ ∧ t * b * t⁻¹ = b⁻¹ ∧
      (∀ x ∈ X, x * t = t * x → x ∈ Subgroup.zpowers ζ) ∧
      (∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c ∈ Subgroup.zpowers ζ) := by
  classical
  have hodd : Odd (Nat.card X) := by rw [hcard]; decide
  have hncX : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  set Z : Subgroup H := (Subgroup.center X).map X.subtype with hZ
  have hZcard : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective X.subtype_injective]
    exact AS35QTh.card_center_eq_three hcard hncX
  have hmemZ : ∀ c : H, c ∈ Z ↔ c ∈ X ∧ ∀ x ∈ X, c * x = x * c := by
    intro c
    constructor
    · rintro ⟨c', hc', rfl⟩
      refine ⟨c'.2, fun x hx => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨x, hx⟩).symm
    · rintro ⟨hcX, hc⟩
      refine ⟨⟨c, hcX⟩, Subgroup.mem_center_iff.mpr fun x => ?_, rfl⟩
      exact Subtype.ext (hc x x.2).symm
  set C : Subgroup H := X ⊓ Subgroup.centralizer {t} with hCdef
  have hZC : Z ≤ C := by
    intro c hc
    obtain ⟨hcX, hcc⟩ := (hmemZ c).mp hc
    exact ⟨hcX, Subgroup.mem_centralizer_singleton_iff.mpr (hZt c hcX hcc)⟩
  have hZeqC : Z = C := Subgroup.eq_of_le_of_card_ge hZC (by rw [hZcard, hC])
  have hCcent : ∀ c ∈ C, c ∈ X ∧ ∀ x ∈ X, c * x = x * c := fun c hc =>
    (hmemZ c).mp (hZeqC ▸ hc)
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hnc
  have hdec : ∀ x ∈ X, ∃ c w : H, c ∈ C ∧ w ∈ X ∧ t * w * t⁻¹ = w⁻¹ ∧ x = c * w := by
    intro x hx
    obtain ⟨c, w, hcX, hwz, hc, hw, hxcw⟩ := AS35QTh.exists_fixed_mul_inverted hodd ht htX hx
    have hwX : w ∈ X := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwz
      exact X.zpow_mem (X.mul_mem (X.inv_mem hx) (htX x hx)) k
    refine ⟨c, w, ⟨hcX, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hwX, hw, hxcw⟩
    calc c * t = t * c * t⁻¹ * t := by rw [hc]
      _ = t * c := by group
  obtain ⟨c₁, w₁, hc₁, hw₁, hσ₁, rfl⟩ := hdec a₀ ha₀
  obtain ⟨c₂, w₂, hc₂, hw₂, hσ₂, rfl⟩ := hdec b₀ hb₀
  obtain ⟨-, hc₁c⟩ := hCcent c₁ hc₁
  obtain ⟨hc₂X, hc₂c⟩ := hCcent c₂ hc₂
  have hw : w₁ * w₂ ≠ w₂ * w₁ := by
    intro h
    apply hab₀
    calc c₁ * w₁ * (c₂ * w₂) = c₁ * (w₁ * c₂) * w₂ := by group
      _ = c₁ * (c₂ * w₁) * w₂ := by rw [← hc₂c w₁ hw₁]
      _ = (c₁ * c₂) * (w₁ * w₂) := by group
      _ = (c₂ * c₁) * (w₂ * w₁) := by rw [hc₁c c₂ hc₂X, h]
      _ = c₂ * (c₁ * w₂) * w₁ := by group
      _ = c₂ * (w₂ * c₁) * w₁ := by rw [hc₁c w₂ hw₂]
      _ = c₂ * w₂ * (c₁ * w₁) := by group
  have hZ3 : ∀ c ∈ Z, c ^ 3 = 1 := by
    intro c hc
    have h := pow_card_eq_one' (G := Z) (x := ⟨c, hc⟩)
    rw [hZcard] at h
    exact congrArg Subtype.val h
  have hcube : ∀ w ∈ X, t * w * t⁻¹ = w⁻¹ → w ^ 3 = 1 := by
    intro w hwX hσ
    have h3 : w ^ 3 ∈ Z := by
      have := AS35QTh.pow_three_mem_center hcard hncX ⟨w, hwX⟩
      exact ⟨_, this, rfl⟩
    have hfix : t * w ^ 3 * t⁻¹ = w ^ 3 := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hZC h3).2
      rw [← hc]
      group
    have hinv : t * w ^ 3 * t⁻¹ = (w ^ 3)⁻¹ := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hσ, inv_pow]
    have h6 : w ^ 6 = 1 := by
      rw [show w ^ 6 = w ^ 3 * w ^ 3 by group]
      calc w ^ 3 * w ^ 3 = w ^ 3 * (w ^ 3)⁻¹ := by rw [← hinv, hfix]
        _ = 1 := mul_inv_cancel _
    have h9 : w ^ 9 = 1 := by rw [show w ^ 9 = (w ^ 3) ^ 3 by group, hZ3 _ h3]
    calc w ^ 3 = w ^ 9 * (w ^ 6)⁻¹ := by group
      _ = 1 := by rw [h9, h6, inv_one, one_mul]
  set ζ := w₁ * w₂ * w₁⁻¹ * w₂⁻¹ with hζ
  have hζZ : ζ ∈ Z := by
    have := AS35QTh.commutator_mem_center hcard hncX ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
    exact ⟨_, this, rfl⟩
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hw
    calc w₁ * w₂ = ζ * (w₂ * w₁) := by rw [hζ]; group
      _ = w₂ * w₁ := by rw [h, one_mul]
  have hζ3 : ζ ^ 3 = 1 := hZ3 ζ hζZ
  have hZeq : Z = Subgroup.zpowers ζ := by
    have hle : Subgroup.zpowers ζ ≤ Z := (Subgroup.zpowers_le).mpr hζZ
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZcard, Nat.card_zpowers]
    have : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one hζ3
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hζ1
    · rw [h]
  obtain ⟨hζX, hζc⟩ := (hmemZ ζ).mp hζZ
  refine ⟨w₁, w₂, ζ, hw₁, hw₂, hζX, hζc, hζ1, hζ3, by rw [hζ]; group, hcube w₁ hw₁ hσ₁,
    hcube w₂ hw₂ hσ₂, hσ₁, hσ₂, fun x hx hxt => ?_, fun c hcX hc => ?_⟩
  · rw [← hZeq, hZeqC]
    exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  · rw [← hZeq]
    exact (hmemZ c).mpr ⟨hcX, hc⟩


end Heis

section Coords

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

open AS35QTh AS35QTh.CoordHyp in
theorem exists_coords_mono {q : QuadraticForm (ZMod 2) V} {a b ζ : V →ₗ[ZMod 2] V}
    (h : AS35QTh.CoordHyp q a b ζ) [Finite V] (hcard : Nat.card V = 64) :
    ∃ l : (Fin 3 → K) → V, (∀ x y, l (x + y) = l x + l y) ∧ Function.Bijective l ∧
      (∀ x, l (ω • x) = ζ (l x)) ∧ (∀ x y, polar q (l x) (l y) = tr2 (herm frob x y)) ∧
      (∀ x, a (l x) = l ![x 0, ω * x 1, frob ω * x 2]) ∧ (∀ x, b (l x) = l ![x 2, x 0, x 1]) := by
  classical
  have hV : ∃ w : V, w ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nat.card V = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨0⟩⟩
    omega
  obtain ⟨w, hw⟩ := hV
  have hv₁ : ∃ v₁ : V, v₁ ≠ 0 ∧ a v₁ = v₁ := by
    set p₀ := w + a w + a (a w)
    set p₁ := w + ζ (ζ (a w)) + ζ (a (a w))
    set p₂ := w + ζ (a w) + ζ (ζ (a (a w)))
    have h0 : a p₀ = p₀ := by
      simp only [p₀, map_add, h.a3]
      abel
    have h1 : a p₁ = ζ p₁ := by
      simp only [p₁, map_add, ← h.ζa, h.a3, zeta_cube h.ζ2]
      abel
    have h2 : a p₂ = ζ (ζ p₂) := by
      simp only [p₂, map_add, ← h.ζa, h.a3, zeta_cube h.ζ2]
      abel
    have hsum : p₀ + p₁ + p₂ = w := by
      have e1 := h.ζ2 (a w)
      have e2 := h.ζ2 (a (a w))
      calc p₀ + p₁ + p₂ = (w + w) + w + (ζ (ζ (a w)) + ζ (a w) + a w) +
          (ζ (ζ (a (a w))) + ζ (a (a w)) + a (a w)) := by simp only [p₀, p₁, p₂]; abel
        _ = w := by rw [e1, e2, add_self_V]; abel
    by_cases hp₀ : p₀ = 0
    · by_cases hp₂ : p₂ = 0
      · have hp₁ : p₁ ≠ 0 := by
          intro hp₁
          apply hw
          rw [← hsum, hp₀, hp₁, hp₂, add_zero, add_zero]
        refine ⟨b (b p₁), fun h' => hp₁ (h.b_injective (h.b_injective (by rw [h', map_zero,
          map_zero]))), h.b_E2 (h.b_E1 h1)⟩
      · exact ⟨b p₂, fun h' => hp₂ (h.b_injective (by rw [h', map_zero])), h.b_E2 h2⟩
    · exact ⟨p₀, hp₀, h0⟩
  obtain ⟨v₁, hv₁0, hv₁a⟩ := hv₁
  set v₂ := b v₁ with hv₂def
  set v₃ := b v₂ with hv₃def
  have hv₂a : a v₂ = ζ v₂ := h.b_E0 hv₁a
  have hv₃a : a v₃ = ζ (ζ v₃) := h.b_E1 hv₂a
  have hv₂0 : v₂ ≠ 0 := fun h' => hv₁0 (h.b_injective (by rw [← hv₂def, h', map_zero]))
  have hv₃0 : v₃ ≠ 0 := fun h' => hv₂0 (h.b_injective (by rw [← hv₃def, h', map_zero]))
  set l := lam ζ v₁ v₂ v₃ with hl
  have hinj : Function.Injective l := by
    intro x y hxy
    have h0 : l (x + y) = 0 := by rw [hl, lam_add, ← hl, hxy, add_self_V]
    obtain ⟨z0, z1, z2⟩ := h.eq_zero_of_E (h.act_E0 ((x + y) 0) hv₁a)
      (h.act_E1 ((x + y) 1) hv₂a) (h.act_E2 ((x + y) 2) hv₃a) h0
    have hxy0 : x + y = 0 := by
      funext i
      fin_cases i
      · exact (act_eq_zero h.ζ2 z0).resolve_right hv₁0
      · exact (act_eq_zero h.ζ2 z1).resolve_right hv₂0
      · exact (act_eq_zero h.ζ2 z2).resolve_right hv₃0
    exact eq_of_add_eq_zero_V hxy0
  have hbij : Function.Bijective l := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_fun, card_K, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have o12 : ∀ c c' : K, polar q (act ζ c v₁) (act ζ c' v₂) = 0 := fun c c' =>
    polar_act_act_of_orth (h.polar_E0_E1 hv₁a hv₂a) (h.polar_E0_E1 hv₁a (h.zeta_E1 hv₂a))
      (h.polar_E0_E1 (h.zeta_E0 hv₁a) hv₂a)
      (h.polar_E0_E1 (h.zeta_E0 hv₁a) (h.zeta_E1 hv₂a)) c c'
  have o13 : ∀ c c' : K, polar q (act ζ c v₁) (act ζ c' v₃) = 0 := fun c c' =>
    polar_act_act_of_orth (h.polar_E0_E2 hv₁a hv₃a) (h.polar_E0_E2 hv₁a (h.zeta_E2 hv₃a))
      (h.polar_E0_E2 (h.zeta_E0 hv₁a) hv₃a)
      (h.polar_E0_E2 (h.zeta_E0 hv₁a) (h.zeta_E2 hv₃a)) c c'
  have o23 : ∀ c c' : K, polar q (act ζ c v₂) (act ζ c' v₃) = 0 := fun c c' =>
    polar_act_act_of_orth (h.polar_E1_E2 hv₂a hv₃a) (h.polar_E1_E2 hv₂a (h.zeta_E2 hv₃a))
      (h.polar_E1_E2 (h.zeta_E1 hv₂a) hv₃a)
      (h.polar_E1_E2 (h.zeta_E1 hv₂a) (h.zeta_E2 hv₃a)) c c'
  have polar_self_act : ∀ (v : V), polar q v (ζ v) = 0 → ∀ c : K, polar q v (act ζ c v) = 0 := by
    intro v hv c
    simp only [act, polar_add_right, polar_smul_right, polar_self_zmod, hv, smul_zero, add_zero]
  have hlx : ∀ x : Fin 3 → K, l x = act ζ (x 0) v₁ + act ζ (x 1) v₂ + act ζ (x 2) v₃ :=
    fun x => rfl
  have p1 : polar q v₁ (ζ v₁) = 1 := by
    rcases zmod2_cases (polar q v₁ (ζ v₁)) with h0 | h1
    · exfalso
      refine hv₁0 (h.nd v₁ fun w => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 w
      have e2 := o12 1 (x 1)
      have e3 := o13 1 (x 2)
      rw [act_one] at e2 e3
      rw [hlx, polar_add_right, polar_add_right, polar_self_act v₁ h0, e2, e3, add_zero,
        add_zero]
    · exact h1
  have p2 : polar q v₂ (ζ v₂) = 1 := by
    rcases zmod2_cases (polar q v₂ (ζ v₂)) with h0 | h1
    · exfalso
      refine hv₂0 (h.nd v₂ fun w => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 w
      have e1 := o12 (x 0) 1
      have e3 := o23 1 (x 2)
      rw [act_one] at e1 e3
      rw [hlx, polar_add_right, polar_add_right, polar_comm, e1, polar_self_act v₂ h0, e3,
        add_zero, add_zero]
    · exact h1
  have p3 : polar q v₃ (ζ v₃) = 1 := by
    rcases zmod2_cases (polar q v₃ (ζ v₃)) with h0 | h1
    · exfalso
      refine hv₃0 (h.nd v₃ fun w => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 w
      have e1 := o13 (x 0) 1
      have e2 := o23 (x 1) 1
      rw [act_one] at e1 e2
      rw [hlx, polar_add_right, polar_add_right, polar_comm, e1, polar_comm, e2,
        polar_self_act v₃ h0, add_zero, zero_add]
    · exact h1
  have hactζ : ∀ (c : K) (v : V), act ζ c (ζ v) = act ζ (ω * c) v := fun c v => by
    rw [act_omega_mul h.ζ2, act_comm (f := ζ) (fun _ => rfl)]
  have hav₃ : a v₃ = ζ (ζ v₃) := hv₃a
  have hbv₃ : b v₃ = v₁ := by rw [hv₃def, hv₂def, h.b3]
  refine ⟨l, lam_add v₁ v₂ v₃, hbij, h.lam_omega v₁ v₂ v₃, fun x y => ?_, fun x => ?_,
    fun x => ?_⟩
  rotate_left
  · rw [hlx, hlx, map_add, map_add, act_comm (f := a) (fun v => h.ζa v),
      act_comm (f := a) (fun v => h.ζa v), act_comm (f := a) (fun v => h.ζa v), hv₁a, hv₂a, hav₃,
      hactζ, hactζ, hactζ, ← mul_assoc, omega_mul_omega]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
  · rw [hlx, hlx, map_add, map_add, act_comm (f := b) (fun v => h.ζb v),
      act_comm (f := b) (fun v => h.ζb v), act_comm (f := b) (fun v => h.ζb v), ← hv₂def,
      ← hv₃def, hbv₃]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    abel
  rw [hlx, hlx, herm_def, Fin.sum_univ_three, tr2_add, tr2_add]
  simp only [polar_add_left, polar_add_right]
  rw [polar_act_act_self p1, polar_act_act_self p2, polar_act_act_self p3, o12, o13, o23,
    polar_comm q (act ζ (x 1) v₂) (act ζ (y 0) v₁), o12, polar_comm q (act ζ (x 2) v₃),
    o13, polar_comm q (act ζ (x 2) v₃) (act ζ (y 1) v₂), o23]
  ring

end Coords

end CFSG.LargeExtraspecial.AS35QIx
