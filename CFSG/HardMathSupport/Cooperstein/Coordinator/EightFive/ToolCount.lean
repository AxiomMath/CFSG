module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFF
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

section Section

variable {X : Type*} [CommGroup X] [Finite X]

theorem card_mul_card_inf_le_of_section {N : Type*} [Group N] {P₀ P₁ Y C : Subgroup X}
    (h01 : P₀ ≤ P₁) (h1Y : P₁ ≤ Y) (π : ↥P₁ →* N) (hπ : Function.Surjective π)
    (hker : π.ker = P₀.subgroupOf P₁) {F : Subgroup N}
    (hCF : ∀ u : ↥P₁, (u : X) ∈ C → π u ∈ F) :
    Nat.card N * Nat.card ↥(Y ⊓ C) ≤ Nat.card Y * Nat.card F := by
  have : Finite N := Finite.of_surjective π hπ
  have hP₀ : Nat.card ↥(P₀.subgroupOf P₁) = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h01).toEquiv
  have h1 : Nat.card P₀ * Nat.card N = Nat.card P₁ := by
    have := Subgroup.card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top, hker, hP₀] at this
    exact this
  have h2 : Nat.card ↥(P₁ ⊓ C) ≤ Nat.card F * Nat.card P₀ := by
    have e := B1More.card_map_mul_card_inf_ker (C.subgroupOf P₁) π
    have hle : (C.subgroupOf P₁).map π ≤ F := by
      rintro _ ⟨u, hu, rfl⟩
      exact hCF u (Subgroup.mem_subgroupOf.1 hu)
    have hC : Nat.card ↥(C.subgroupOf P₁) = Nat.card ↥(P₁ ⊓ C) := by
      have : C.subgroupOf P₁ = (P₁ ⊓ C).subgroupOf P₁ := by
        ext u
        simp [Subgroup.mem_subgroupOf]
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hk : Nat.card ↥(C.subgroupOf P₁ ⊓ π.ker) ≤ Nat.card P₀ := by
      rw [← hP₀, ← hker]
      exact Subgroup.card_le_of_le inf_le_right
    rw [← hC, ← e]
    exact Nat.mul_le_mul (Subgroup.card_le_of_le hle) hk
  have h3 : Nat.card ↥(Y ⊓ C) * Nat.card P₁ ≤ Nat.card Y * Nat.card ↥(P₁ ⊓ C) := by
    have e := card_sup_mul_card_inf (Y ⊓ C) P₁
    have hsup : Y ⊓ C ⊔ P₁ ≤ Y := sup_le inf_le_left h1Y
    have hinf : Y ⊓ C ⊓ P₁ = P₁ ⊓ C := by
      rw [inf_right_comm, inf_eq_right.2 h1Y, inf_comm]
    rw [hinf] at e
    rw [← e]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hsup)
  have hpos : 0 < Nat.card P₀ := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card N * Nat.card ↥(Y ⊓ C) * Nat.card P₀
      = Nat.card ↥(Y ⊓ C) * (Nat.card P₀ * Nat.card N) := by ring
    _ = Nat.card ↥(Y ⊓ C) * Nat.card P₁ := by rw [h1]
    _ ≤ Nat.card Y * Nat.card ↥(P₁ ⊓ C) := h3
    _ ≤ Nat.card Y * (Nat.card F * Nat.card P₀) := Nat.mul_le_mul_left _ h2
    _ = Nat.card Y * Nat.card F * Nat.card P₀ := by ring

theorem card_mul_card_inf_fixV_le {m : ℕ} {P₀ P₁ Y : Subgroup X} (h01 : P₀ ≤ P₁) (h1Y : P₁ ≤ Y)
    (π : ↥P₁ →* Multiplicative (altHeart m)) (hπ : Function.Surjective π)
    (hker : π.ker = P₀.subgroupOf P₁) {A : Subgroup (MulAut X)} {B : Subgroup (Perm (Fin m))}
    (hAB : ∀ b ∈ B, ∃ a ∈ A, ∀ u v : ↥P₁, (v : X) = a u →
      Multiplicative.toAdd (π v) = altAct b (Multiplicative.toAdd (π u))) :
    Nat.card (altHeart m) * Nat.card ↥(Y ⊓ fixV A) ≤ Nat.card Y * Nat.card (altFix m B) := by
  have h := card_mul_card_inf_le_of_section h01 h1Y π hπ hker (C := fixV A)
    (F := AddSubgroup.toSubgroup (altFix m B)) fun u hu => by
      change Multiplicative.toAdd (π u) ∈ altFix m B
      rw [mem_altFix_iff_altAct]
      intro b hb
      obtain ⟨a, ha, hab⟩ := hAB b hb
      exact (hab u u (hu a ha).symm).symm
  have e1 : Nat.card (Multiplicative (altHeart m)) = Nat.card (altHeart m) := rfl
  have e2 : Nat.card ↥(AddSubgroup.toSubgroup (altFix m B)) = Nat.card (altFix m B) := rfl
  rwa [e1, e2] at h

theorem card_fixV_le_card_ker_mul_card_range (φ : X →* X) {A : Subgroup (MulAut X)}
    (hφA : ∀ a ∈ A, ∀ v, φ (a v) = a (φ v)) :
    Nat.card (fixV A) ≤ Nat.card ↥(φ.ker ⊓ fixV A) * Nat.card ↥(φ.range ⊓ fixV A) := by
  have e := B1More.card_map_mul_card_inf_ker (fixV A) φ
  have hle : (fixV A).map φ ≤ φ.range ⊓ fixV A := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨v, rfl⟩, fun a ha => ?_⟩
    rw [← hφA a ha, hv a ha]
  rw [← e, inf_comm (fixV A), mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

end Section

section Num

variable {m : ℕ}

theorem two_pow_le_card_of_isMatchingGroup {B : Subgroup (Perm (Fin m))} (hΔ : IsMatchingGroup B) :
    2 ^ (m / 2) ≤ Nat.card B := by
  obtain ⟨t, ht, ht2, rfl⟩ := hΔ
  have h1 := card_FixP_le_card_matchingGroup ht ht2
  rw [card_FixP_eq] at h1
  have h2 := card_eq_two_mul_card_orb (card_orbit_matchingGroup ht ht2)
  rw [Nat.card_fin] at h2
  have h3 : m / 2 = Nat.card (Orb (matchingGroup t)) := by omega
  rw [h3]
  exact h1

theorem two_mul_card_mul_sq_lt (hm : 8 ≤ m) {B : Subgroup (Perm (Fin m))}
    (hB : ∀ b ∈ B, b * b = 1) (hfix : ∀ i, ∃ b ∈ B, b i ≠ i) :
    2 * Nat.card B * Nat.card (altFix m B) ^ 2 < Nat.card (altHeart m) ^ 2 := by
  have hC : 0 < Nat.card (altFix m B) := Nat.card_pos
  have hN : 0 < Nat.card (altHeart m) := Nat.card_pos
  by_cases hΔ : IsMatchingGroup B
  · have h1 := natFF_matching (by omega) hΔ
    have h16 : 16 ≤ Nat.card B := by
      have h2 := two_pow_le_card_of_isMatchingGroup hΔ
      have h3 : 2 ^ 4 ≤ 2 ^ (m / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 8 * Nat.card (altFix m B) ≤ Nat.card (altHeart m) := by
      have := Nat.mul_le_mul_right (Nat.card (altFix m B)) h16
      omega
    have e : 2 * Nat.card B * Nat.card (altFix m B) ^ 2 =
        4 * Nat.card (altHeart m) * Nat.card (altFix m B) := by
      rw [show 2 * Nat.card B * Nat.card (altFix m B) ^ 2 =
        2 * (Nat.card B * Nat.card (altFix m B)) * Nat.card (altFix m B) by ring, h1]
      ring
    have h5 : Nat.card (altHeart m) * (8 * Nat.card (altFix m B)) ≤
        Nat.card (altHeart m) * Nat.card (altHeart m) := Nat.mul_le_mul_left _ h4
    have h6 : 0 < Nat.card (altHeart m) * Nat.card (altFix m B) := Nat.mul_pos hN hC
    rw [e, pow_two]
    nlinarith
  · have h1 := natFF_le (by omega) hB hΔ
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      obtain ⟨b, hb, hbi⟩ := hfix ⟨0, by omega⟩
      exact ⟨b, hb, fun h => hbi (by rw [h, Perm.one_apply])⟩
    by_cases h2 : Nat.card B = 2
    ·
      have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hB b hbB
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
      have hBz : Subgroup.zpowers b = B :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbB)
          (by rw [h2, Nat.card_zpowers, hord])
      have hbfix : ∀ i, b i ≠ i := by
        intro i
        obtain ⟨c, hc, hci⟩ := hfix i
        rw [← hBz] at hc
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
        intro hbi
        apply hci
        have hfixpow : ∀ j : ℤ, (b ^ j) i = i := fun j => by
          have : b ∈ MulAction.stabilizer (Perm (Fin m)) i := hbi
          exact ((MulAction.stabilizer (Perm (Fin m)) i).zpow_mem this j)
        exact hfixpow k
      have h3 := natFF_fpf hm (hB b hbB) hbfix
      rw [hBz] at h3
      rw [h2]
      have h4 := Nat.pow_le_pow_left h3 2
      have h5 : 0 < Nat.card (altFix m B) ^ 2 := pow_pos hC 2
      rw [mul_pow] at h4
      omega
    · have h3 : 3 ≤ Nat.card B := by
        have h4 : Nat.card B ≠ 1 := fun h => hb1 (by
          have := Subgroup.card_eq_one.1 h
          have hb : b ∈ (⊥ : Subgroup (Perm (Fin m))) := this ▸ hbB
          exact Subgroup.mem_bot.1 hb)
        have h5 : 0 < Nat.card B := Nat.card_pos
        omega
      have h6 : 2 * Nat.card B < Nat.card B * Nat.card B := by nlinarith
      have h7 : 2 * Nat.card B * Nat.card (altFix m B) ^ 2 <
          Nat.card B * Nat.card B * Nat.card (altFix m B) ^ 2 :=
        Nat.mul_lt_mul_of_pos_right h6 (pow_pos hC 2)
      have h8 : Nat.card B * Nat.card B * Nat.card (altFix m B) ^ 2 =
          (Nat.card B * Nat.card (altFix m B)) ^ 2 := by ring
      have h9 := Nat.pow_le_pow_left h1 2
      omega

end Num

section Ord

variable {V : Type*} [CommGroup V] [Finite V]

theorem eq_one_of_pow_seven (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V} (hy : y ^ 7 = 1)
    (hcard : Nat.card V ≤ 4 * Nat.card (fixV (Subgroup.zpowers y))) : y = 1 := by
  set f := commHom y with hf
  set U := f.range with hU
  have hUcard : Nat.card U ≤ 4 := by
    have e := Subgroup.card_ker_mul_card_range f
    rw [ker_commHom] at e
    have hpos : 0 < Nat.card (fixV (Subgroup.zpowers y)) := Nat.card_pos
    nlinarith
  have hfy : ∀ v, f (y v) = y (f v) := fun v => by
    rw [hf, commHom_apply, commHom_apply, map_mul, map_inv]
  have hfyi : ∀ v, f (y⁻¹ v) = y⁻¹ (f v) := fun v => by
    rw [hf, commHom_apply, commHom_apply, map_mul, map_inv, MulAut.inv_apply_self,
      MulAut.apply_inv_self]
  have hinv : ∀ u, y u ∈ U ↔ u ∈ U := fun u => by
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨y⁻¹ v, ?_⟩
      rw [hfyi, hv, MulAut.inv_apply_self]
    · rintro ⟨v, rfl⟩
      exact ⟨y v, hfy v⟩
  have hinv' : ∀ u, (MulAut.toPerm V y) u ∈ U ↔ u ∈ U := hinv
  set σ : Perm U := Perm.subtypePerm (MulAut.toPerm V y) hinv' with hσ
  have hσ7 : σ ^ 7 = 1 := by
    rw [hσ, Perm.subtypePerm_pow]
    have h1 : (MulAut.toPerm V y) ^ 7 = 1 := by rw [← map_pow, hy, map_one]
    refine Equiv.ext fun u => Subtype.ext ?_
    change ((MulAut.toPerm V y) ^ 7) u = u
    rw [h1]
    rfl
  have hσ1 : σ = 1 := by
    have hfin : Finite U := inferInstance
    have h1 : orderOf σ ∣ 7 := orderOf_dvd_of_pow_eq_one hσ7
    have h2 : orderOf σ ∣ (Nat.card U).factorial := by
      rw [← Nat.card_perm]
      exact orderOf_dvd_natCard σ
    have h3 : Nat.Coprime 7 (Nat.card U).factorial := by
      interval_cases (Nat.card U) <;> decide
    have h4 : orderOf σ = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
    exact orderOf_eq_one_iff.1 h4
  have hyU : ∀ v, y (f v) = f v := fun v => by
    have := congrArg (fun τ : Perm U => ((τ ⟨f v, v, rfl⟩ : U) : V)) hσ1
    exact this
  have hy2 : y ^ 2 = 1 := by
    refine MulEquiv.ext fun v => ?_
    have h1 : y v = f v * v := by rw [hf, commHom_apply, inv_mul_cancel_right]
    calc (y ^ 2) v = y (y v) := by rw [pow_two]; rfl
      _ = y (f v) * y v := by rw [h1, map_mul, ← h1]
      _ = f v * (f v * v) := by rw [hyU, h1]
      _ = f v ^ 2 * v := by rw [pow_two, mul_assoc]
      _ = v := by rw [hV, one_mul]
  calc y = y ^ 7 * (y ^ 2)⁻¹ ^ 3 := by group
    _ = 1 := by rw [hy, hy2, inv_one, one_pow, one_mul]

end Ord

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
