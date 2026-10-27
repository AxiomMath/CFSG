module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalQ8
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns

section Quat

variable {G : Type*} [Group G] {x y : G}

theorem l3b_pow_mul_eq (hyx : y⁻¹ * x * y = x⁻¹) (k : ℕ) :
    x ^ k * y = y * x ^ (-(k : ℤ)) := by
  have h : y⁻¹ * x ^ k * y = (x ^ k)⁻¹ := by
    have := map_pow (MulAut.conj y⁻¹) x k
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hyx, inv_pow]
  calc x ^ k * y = y * (y⁻¹ * x ^ k * y) := by group
    _ = y * x ^ (-(k : ℤ)) := by rw [h, zpow_neg, zpow_natCast]

theorem l3b_pow_val_eq (h4 : x ^ 4 = 1) (i : ZMod 4) (m : ℤ) (hm : (m : ZMod 4) = i) :
    x ^ i.val = x ^ m := by
  have h4' : x ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, h4]
  rw [zpow_eq_zpow_emod m h4', ← hm, ← zpow_natCast]
  congr 1
  exact ZMod.val_intCast m

@[expose] def l3bQuatHom (h4 : x ^ 4 = 1) (hyy : y * y = x * x) (hyx : y⁻¹ * x * y = x⁻¹) :
    QuaternionGroup 2 →* G where
  toFun g := match g with
    | .a i => x ^ i.val
    | .xa i => y * x ^ i.val
  map_one' := by
    show x ^ (0 : ZMod (2 * 2)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · show x ^ (i + j).val = x ^ i.val * x ^ j.val
      rw [l3b_pow_val_eq h4 (i + j) ((i.val : ℤ) + j.val)
        (by push_cast [ZMod.natCast_zmod_val]; rfl), zpow_add, zpow_natCast, zpow_natCast]
    · show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      rw [l3b_pow_val_eq h4 (j - i) (-(i.val : ℤ) + j.val)
        (by push_cast [ZMod.natCast_zmod_val]; ring), ← mul_assoc, l3b_pow_mul_eq hyx]
      group
    · show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [l3b_pow_val_eq h4 (i + j) ((i.val : ℤ) + j.val)
        (by push_cast [ZMod.natCast_zmod_val]; rfl)]
      group
    · show x ^ ((2 : ℕ) + j - i : ZMod (2 * 2)).val = y * x ^ i.val * (y * x ^ j.val)
      rw [l3b_pow_val_eq h4 _ (2 + (j.val : ℤ) - i.val)
        (by push_cast [ZMod.natCast_zmod_val]; ring)]
      calc x ^ (2 + (j.val : ℤ) - i.val) = (x * x) * x ^ (-(i.val : ℤ)) * x ^ j.val := by
            group
        _ = (y * y) * x ^ (-(i.val : ℤ)) * x ^ j.val := by rw [hyy]
        _ = y * (y * x ^ (-(i.val : ℤ))) * x ^ j.val := by group
        _ = y * (x ^ i.val * y) * x ^ j.val := by rw [l3b_pow_mul_eq hyx]
        _ = y * x ^ i.val * (y * x ^ j.val) := by group

theorem l3bQuatHom_injective (h4 : x ^ 4 = 1) (hyy : y * y = x * x) (hyx : y⁻¹ * x * y = x⁻¹)
    (hx2 : x * x ≠ 1) : Function.Injective (l3bQuatHom h4 hyy hyx) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · change x ^ i.val = 1 at h
    have hlt := ZMod.val_lt i
    have hv : i.val = 0 := by
      rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3) with hv | hv | hv | hv
      · exact hv
      · exfalso
        rw [hv, pow_one] at h
        exact hx2 (by rw [h, one_mul])
      · exfalso
        rw [hv, pow_two] at h
        exact hx2 h
      · exfalso
        rw [hv] at h
        have hx1 : x = 1 := by
          calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
            _ = 1 := by rw [h4, h, inv_one, one_mul]
        exact hx2 (by rw [hx1, one_mul])
    rw [(ZMod.val_eq_zero i).mp hv]
    rfl
  · change y * x ^ i.val = 1 at h
    exfalso
    have hy : y = (x ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hc : y⁻¹ * x * y = x := by
      rw [hy, inv_inv]
      group
    rw [hyx] at hc
    apply hx2
    calc x * x = x * x⁻¹ := by rw [hc]
      _ = 1 := mul_inv_cancel x

end Quat

section Heis

variable {G : Type} [Group G]

theorem l3b_conj_eq_on_sup {x₁ x₂ g h : G} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1 : g * x₁ * g⁻¹ = h * x₁ * h⁻¹) (h2 : g * x₂ * g⁻¹ = h * x₂ * h⁻¹)
    {e : G} (he : e ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    g * e * g⁻¹ = h * e * h⁻¹ := by
  obtain ⟨i, j, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.exists_zpow_mul_of_mem_sup h12 he
  have e1 : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = (g * x₁ * g⁻¹) ^ i * (g * x₂ * g⁻¹) ^ j := by
    rw [conj_zpow, conj_zpow]
    group
  have e2 : h * (x₁ ^ i * x₂ ^ j) * h⁻¹ = (h * x₁ * h⁻¹) ^ i * (h * x₂ * h⁻¹) ^ j := by
    rw [conj_zpow, conj_zpow]
    group
  rw [e1, e2, h1, h2]

theorem l3b_isElemAbelian_sup {x₁ x₂ : G} (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) : IsElemAbelian 3 (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
  have hc : ∀ a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
      ∀ b ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, j, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.exists_zpow_mul_of_mem_sup h12 ha
    obtain ⟨k, l, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.exists_zpow_mul_of_mem_sup h12 hb
    have c12 : Commute x₁ x₂ := h12
    have e1 : x₂ ^ j * x₁ ^ k = x₁ ^ k * x₂ ^ j := (Commute.zpow_zpow c12.symm j k).eq
    calc x₁ ^ i * x₂ ^ j * (x₁ ^ k * x₂ ^ l) = x₁ ^ i * (x₂ ^ j * x₁ ^ k) * x₂ ^ l := by group
      _ = x₁ ^ i * (x₁ ^ k * x₂ ^ j) * x₂ ^ l := by rw [e1]
      _ = x₁ ^ (i + k) * x₂ ^ (j + l) := by
        rw [_root_.zpow_add, _root_.zpow_add]; group
      _ = x₁ ^ (k + i) * x₂ ^ (l + j) := by rw [add_comm i k, add_comm j l]
      _ = x₁ ^ k * x₂ ^ l * (x₁ ^ i * x₂ ^ j) := by
        have e2 : x₂ ^ l * x₁ ^ i = x₁ ^ i * x₂ ^ l := (Commute.zpow_zpow c12.symm l i).eq
        calc x₁ ^ (k + i) * x₂ ^ (l + j) = x₁ ^ k * (x₁ ^ i * x₂ ^ l) * x₂ ^ j := by
              rw [_root_.zpow_add, _root_.zpow_add]; group
          _ = x₁ ^ k * (x₂ ^ l * x₁ ^ i) * x₂ ^ j := by rw [e2]
          _ = _ := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨i, j, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.exists_zpow_mul_of_mem_sup h12 hx
  have c12 : Commute x₁ x₂ := h12
  have : (x₁ ^ i * x₂ ^ j) ^ 3 = x₁ ^ (i * 3) * x₂ ^ (j * 3) := by
    have := ((Commute.zpow_zpow c12 i j).mul_pow 3)
    rw [this, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    norm_cast
  rw [this, mul_comm i 3, mul_comm j 3, _root_.zpow_mul, _root_.zpow_mul, zpow_ofNat, zpow_ofNat,
    h1, h2, one_zpow, one_zpow, one_mul]

theorem l3b_mem_normalizer_of_gens [Finite G] {x₁ x₂ n : G} (h12 : x₁ * x₂ = x₂ * x₁)
    (h₁ : n * x₁ * n⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (h₂ : n * x₂ * n⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    n ∈ Subgroup.normalizer ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G) := by
  apply l3b_mem_normalizer
  intro x hx
  obtain ⟨i, j, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.exists_zpow_mul_of_mem_sup h12 hx
  have e1 : n * (x₁ ^ i * x₂ ^ j) * n⁻¹ = (n * x₁ * n⁻¹) ^ i * (n * x₂ * n⁻¹) ^ j := by
    rw [conj_zpow, conj_zpow]
    group
  rw [e1]
  exact mul_mem (zpow_mem h₁ i) (zpow_mem h₂ j)

theorem l3b_card_sup_zpowers [Finite G] {x₁ x₂ : G} (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) (hx1 : x₁ ≠ 1) (hx2 : x₂ ∉ Subgroup.zpowers x₁) :
    Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = 9 := by
  have hx2' : x₂ ≠ 1 := fun h => hx2 (by rw [h]; exact Subgroup.one_mem _)
  have o1 : Nat.card (Subgroup.zpowers x₁) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h1 hx1]
  have o2 : Nat.card (Subgroup.zpowers x₂) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h2 hx2']
  have hdisj : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
    set W := Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ with hW
    have hle : W ≤ Subgroup.zpowers x₂ := inf_le_right
    have hd : Nat.card W ∣ 3 := o2 ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact Subgroup.eq_bot_of_card_eq W h
    · exfalso
      have heq : W = Subgroup.zpowers x₂ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h, o2])
      apply hx2
      have : x₂ ∈ W := by rw [heq]; exact Subgroup.mem_zpowers x₂
      exact this.1
  have hcomm : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute x₁ x₂ from h12) k l).eq
  rw [card_sup_of_commute_disjoint hcomm hdisj, o1, o2]

theorem l3b_heis_q8_data [Finite G] {J E : Subgroup G} {x₁ x₂ n₁ n₂ : G}
    (hE : E = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) (hx1 : x₁ ≠ 1)
    (hx2 : x₂ ∉ Subgroup.zpowers x₁)
    (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (hN1 : n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹) (hN2 : n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁)
    (hn₁ : n₁ ∈ J) (hn₂ : n₂ ∈ J) :
    IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      (∃ f : QuaternionGroup 2 →* autizer J E, Function.Injective f) ∧
      ∀ u ∈ E, ∀ v ∈ E, u ≠ 1 → v ≠ 1 →
        ∃ g ∈ J ⊓ Subgroup.normalizer (E : Set G), g * u * g⁻¹ = v := by
  subst hE
  set E := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hEdef
  have hx₁E : x₁ ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂E : x₂ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hF1' : n₁ * x₁⁻¹ * n₁⁻¹ = x₂ := by
    rw [show n₁ * x₁⁻¹ * n₁⁻¹ = (n₁ * x₁ * n₁⁻¹)⁻¹ by group, hF1, inv_inv]
  have hF2' : n₁ * x₂⁻¹ * n₁⁻¹ = x₁⁻¹ := by
    rw [show n₁ * x₂⁻¹ * n₁⁻¹ = (n₁ * x₂ * n₁⁻¹)⁻¹ by group, hF2]
  have hN1' : n₂ * x₁⁻¹ * n₂⁻¹ = x₁ * x₂ := by
    rw [show n₂ * x₁⁻¹ * n₂⁻¹ = (n₂ * x₁ * n₂⁻¹)⁻¹ by group, hN1, _root_.mul_inv_rev, inv_inv,
      inv_inv]
  have hN2' : n₂ * x₂⁻¹ * n₂⁻¹ = x₁⁻¹ * x₂⁻¹ * x₁⁻¹ := by
    rw [show n₂ * x₂⁻¹ * n₂⁻¹ = (n₂ * x₂ * n₂⁻¹)⁻¹ by group, hN2]
    group
  have hF1i : n₁⁻¹ * x₂ * n₁ = x₁⁻¹ := by
    have : n₁⁻¹ * x₂⁻¹ * n₁ = x₁ := by rw [← hF1]; group
    rw [show n₁⁻¹ * x₂ * n₁ = (n₁⁻¹ * x₂⁻¹ * n₁)⁻¹ by group, this]
  have hF2i : n₁⁻¹ * x₁ * n₁ = x₂ := by rw [← hF2]; group
  have hsq1 : x₁ * x₁ = x₁⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc x₁ * x₁ * x₁ = x₁ ^ 3 := (pow_three' x₁).symm
      _ = 1 := h1
  have hsq2 : x₂ * x₂ = x₂⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc x₂ * x₂ * x₂ = x₂ ^ 3 := (pow_three' x₂).symm
      _ = 1 := h2
  have hc' : x₁ * x₂⁻¹ * x₁⁻¹ = x₂⁻¹ := by
    have : Commute x₁ x₂⁻¹ := (show Commute x₁ x₂ from h12).inv_right
    rw [this.eq]; group
  have hn₁N : n₁ ∈ Subgroup.normalizer (E : Set G) :=
    l3b_mem_normalizer_of_gens h12 (by rw [hF1]; exact inv_mem hx₂E) (by rw [hF2]; exact hx₁E)
  have hn₂N : n₂ ∈ Subgroup.normalizer (E : Set G) :=
    l3b_mem_normalizer_of_gens h12 (by rw [hN1]; exact mul_mem (inv_mem hx₂E) (inv_mem hx₁E))
      (by rw [hN2]; exact mul_mem (mul_mem hx₁E hx₂E) hx₁E)
  have htr := CFSG.RankThree.PartTwo.Sec4.transitive_of_q8 (M := J) h12 h1 h2 hF1 hF2 hN1 hN2
    hn₁ hn₂
  refine ⟨l3b_isElemAbelian_sup h12 h1 h2, l3b_card_sup_zpowers h12 h1 h2 hx1 hx2, ?_,
    fun u hu v hv hu1 hv1 => htr u hu hu1 v hv hv1⟩
  let g₁ : ↥(J ⊓ Subgroup.normalizer (E : Set G)) := ⟨n₁, hn₁, hn₁N⟩
  let g₂ : ↥(J ⊓ Subgroup.normalizer (E : Set G)) := ⟨n₂, hn₂, hn₂N⟩
  let a : autizer J E := QuotientGroup.mk g₁
  let b : autizer J E := QuotientGroup.mk g₂
  have key : ∀ g h : ↥(J ⊓ Subgroup.normalizer (E : Set G)),
      (g : G) * x₁ * (g : G)⁻¹ = (h : G) * x₁ * (h : G)⁻¹ →
      (g : G) * x₂ * (g : G)⁻¹ = (h : G) * x₂ * (h : G)⁻¹ →
      (QuotientGroup.mk g : autizer J E) = QuotientGroup.mk h := fun g h e1 e2 =>
    (l3b_autizer_mk_eq_iff g h).2 fun e he => l3b_conj_eq_on_sup h12 e1 e2 he
  have pow4 : n₁ ^ 4 = n₁ * n₁ * n₁ * n₁ := by simp [pow_succ]
  have R1 : a ^ 4 = 1 := by
    have : (QuotientGroup.mk (g₁ ^ 4) : autizer J E) = QuotientGroup.mk 1 := by
      refine key _ _ ?_ ?_
      · show n₁ ^ 4 * x₁ * (n₁ ^ 4)⁻¹ = 1 * x₁ * (1 : G)⁻¹
        rw [pow4]
        calc n₁ * n₁ * n₁ * n₁ * x₁ * (n₁ * n₁ * n₁ * n₁)⁻¹ =
            n₁ * (n₁ * (n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹) * n₁⁻¹) * n₁⁻¹ := by group
          _ = 1 * x₁ * (1 : G)⁻¹ := by rw [hF1, hF2', hF1', hF2]; group
      · show n₁ ^ 4 * x₂ * (n₁ ^ 4)⁻¹ = 1 * x₂ * (1 : G)⁻¹
        rw [pow4]
        calc n₁ * n₁ * n₁ * n₁ * x₂ * (n₁ * n₁ * n₁ * n₁)⁻¹ =
            n₁ * (n₁ * (n₁ * (n₁ * x₂ * n₁⁻¹) * n₁⁻¹) * n₁⁻¹) * n₁⁻¹ := by group
          _ = 1 * x₂ * (1 : G)⁻¹ := by rw [hF2, hF1, hF2', hF1']; group
    rw [QuotientGroup.mk_pow] at this
    simpa using this
  have R2 : b * b = a * a := by
    have : (QuotientGroup.mk (g₂ * g₂) : autizer J E) = QuotientGroup.mk (g₁ * g₁) := by
      refine key _ _ ?_ ?_
      · show n₂ * n₂ * x₁ * (n₂ * n₂)⁻¹ = n₁ * n₁ * x₁ * (n₁ * n₁)⁻¹
        calc n₂ * n₂ * x₁ * (n₂ * n₂)⁻¹ = n₂ * (n₂ * x₁ * n₂⁻¹) * n₂⁻¹ := by group
          _ = (n₂ * x₂⁻¹ * n₂⁻¹) * (n₂ * x₁⁻¹ * n₂⁻¹) := by rw [hN1]; group
          _ = x₁⁻¹ := by rw [hN2', hN1']; group
          _ = n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹ := by rw [hF1, hF2']
          _ = n₁ * n₁ * x₁ * (n₁ * n₁)⁻¹ := by group
      · show n₂ * n₂ * x₂ * (n₂ * n₂)⁻¹ = n₁ * n₁ * x₂ * (n₁ * n₁)⁻¹
        calc n₂ * n₂ * x₂ * (n₂ * n₂)⁻¹ = n₂ * (n₂ * x₂ * n₂⁻¹) * n₂⁻¹ := by group
          _ = (n₂ * x₁ * n₂⁻¹) * (n₂ * x₂ * n₂⁻¹) * (n₂ * x₁ * n₂⁻¹) := by
            conv_lhs => rw [hN2]
            group
          _ = x₁ * x₂⁻¹ * x₁⁻¹ := by rw [hN1, hN2]; group
          _ = x₂⁻¹ := hc'
          _ = n₁ * (n₁ * x₂ * n₁⁻¹) * n₁⁻¹ := by rw [hF2, hF1]
          _ = n₁ * n₁ * x₂ * (n₁ * n₁)⁻¹ := by group
    simpa [QuotientGroup.mk_mul] using this
  have R3 : a * b = b * a⁻¹ := by
    have : (QuotientGroup.mk (g₁ * g₂) : autizer J E) = QuotientGroup.mk (g₂ * g₁⁻¹) := by
      refine key _ _ ?_ ?_
      · show n₁ * n₂ * x₁ * (n₁ * n₂)⁻¹ = n₂ * n₁⁻¹ * x₁ * (n₂ * n₁⁻¹)⁻¹
        calc n₁ * n₂ * x₁ * (n₁ * n₂)⁻¹ = n₁ * (n₂ * x₁ * n₂⁻¹) * n₁⁻¹ := by group
          _ = (n₁ * x₂⁻¹ * n₁⁻¹) * (n₁ * x₁⁻¹ * n₁⁻¹) := by rw [hN1]; group
          _ = x₁⁻¹ * x₂ := by rw [hF2', hF1']
          _ = x₁ * x₂ * x₁ := by
            calc x₁⁻¹ * x₂ = (x₁ * x₁) * x₂ := by rw [hsq1]
              _ = x₁ * x₂ * x₁ := by
                calc x₁ * x₁ * x₂ = x₁ * (x₁ * x₂) := mul_assoc _ _ _
                  _ = x₁ * (x₂ * x₁) := by rw [h12]
                  _ = x₁ * x₂ * x₁ := (mul_assoc _ _ _).symm
          _ = n₂ * (n₁⁻¹ * x₁ * n₁) * n₂⁻¹ := by rw [hF2i, hN2]
          _ = n₂ * n₁⁻¹ * x₁ * (n₂ * n₁⁻¹)⁻¹ := by group
      · show n₁ * n₂ * x₂ * (n₁ * n₂)⁻¹ = n₂ * n₁⁻¹ * x₂ * (n₂ * n₁⁻¹)⁻¹
        calc n₁ * n₂ * x₂ * (n₁ * n₂)⁻¹ = n₁ * (n₂ * x₂ * n₂⁻¹) * n₁⁻¹ := by group
          _ = (n₁ * x₁ * n₁⁻¹) * (n₁ * x₂ * n₁⁻¹) * (n₁ * x₁ * n₁⁻¹) := by rw [hN2]; group
          _ = x₂⁻¹ * x₁ * x₂⁻¹ := by rw [hF1, hF2]
          _ = x₁ * x₂ := by
            have : Commute x₁ x₂⁻¹ := (show Commute x₁ x₂ from h12).inv_right
            calc x₂⁻¹ * x₁ * x₂⁻¹ = (x₂⁻¹ * x₁) * x₂⁻¹ := rfl
              _ = (x₁ * x₂⁻¹) * x₂⁻¹ := by rw [← this.eq]
              _ = x₁ * (x₂⁻¹ * x₂⁻¹) := mul_assoc _ _ _
              _ = x₁ * x₂ := by
                rw [show x₂⁻¹ * x₂⁻¹ = x₂ from by rw [← mul_inv_rev, hsq2, inv_inv]]
          _ = n₂ * x₁⁻¹ * n₂⁻¹ := hN1'.symm
          _ = n₂ * (n₁⁻¹ * x₂ * n₁) * n₂⁻¹ := by rw [hF1i]
          _ = n₂ * n₁⁻¹ * x₂ * (n₂ * n₁⁻¹)⁻¹ := by group
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
  have R4 : a * a ≠ 1 := by
    intro h
    have : (QuotientGroup.mk (g₁ * g₁) : autizer J E) = QuotientGroup.mk 1 := by
      simpa [QuotientGroup.mk_mul] using h
    have h' := (l3b_autizer_mk_eq_iff _ _).1 this x₁ hx₁E
    have h'' : n₁ * n₁ * x₁ * (n₁ * n₁)⁻¹ = 1 * x₁ * (1 : G)⁻¹ := h'
    have : n₁ * n₁ * x₁ * (n₁ * n₁)⁻¹ = x₁⁻¹ := by
      calc n₁ * n₁ * x₁ * (n₁ * n₁)⁻¹ = n₁ * (n₁ * x₁ * n₁⁻¹) * n₁⁻¹ := by group
        _ = x₁⁻¹ := by rw [hF1, hF2']
    rw [this] at h''
    apply hx1
    have h3 : x₁⁻¹ = x₁ := by simpa using h''
    have h4 : x₁ * x₁ = 1 := by
      calc x₁ * x₁ = x₁ * x₁⁻¹ := by rw [h3]
        _ = 1 := mul_inv_cancel x₁
    have h5 : x₁⁻¹ = 1 := by rw [← hsq1]; exact h4
    exact inv_eq_one.1 h5
  have hyx : b⁻¹ * a * b = a⁻¹ := by
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (b * a⁻¹) := by rw [R3]
      _ = a⁻¹ := by group
  exact ⟨l3bQuatHom R1 R2 hyx, l3bQuatHom_injective R1 R2 hyx R4⟩

end Heis

end CFSG.HardMathSupport.Solomon.Coordinator
