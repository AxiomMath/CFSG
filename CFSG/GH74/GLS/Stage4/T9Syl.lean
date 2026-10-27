module

public import CFSG.GH74.GLS.Stage4.T6Basic
public import CFSG.GH74.GLS.Stage4.T6Irr
public import CFSG.GH74.GLS.Stage4.T6SylF

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T9

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6 CFSG.GH74.BNPair
open scoped Pointwise commutatorElement

section SL2

variable {F : Type} [Field F]

theorem t9_sl2U_inv (c : F) : (sl2U c)⁻¹ = sl2U (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← sl2U_add, add_neg_cancel, sl2U_zero]

theorem t9_sl2L_inv (c : F) : (sl2L c)⁻¹ = sl2L (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← sl2L_add, add_neg_cancel, sl2L_zero]

theorem t9_alpha_eq (α : MulAut (SL2 F)) (hU : ∀ c : F, α (sl2U c) = sl2U (-c))
    (hL : ∀ c : F, α (sl2L c) = sl2L (-c)) (g : SL2 F) : α g = slConj (dNeg F) g := by
  have hle : uSub F ⊔ lSub F ≤ MonoidHom.eqLocus (α : SL2 F →* SL2 F) (slConj (dNeg F)) := by
    apply sup_le
    · intro x hx
      obtain ⟨c, rfl⟩ := mem_uSub.1 hx
      show α (sl2U c) = slConj (dNeg F) (sl2U c)
      rw [hU, slConj_dNeg_uSub _ (sl2U_mem_uSub c), t9_sl2U_inv]
    · intro x hx
      obtain ⟨c, rfl⟩ := mem_lSub.1 hx
      show α (sl2L c) = slConj (dNeg F) (sl2L c)
      rw [hL, slConj_dNeg_lSub _ (sl2L_mem_lSub c), t9_sl2L_inv]
  rw [uSub_sup_lSub] at hle
  exact hle (Subgroup.mem_top g)

theorem t9_coe_slConj_dNeg (x : SL2 F) :
    (slConj (dNeg F) x : Matrix (Fin 2) (Fin 2) F) =
      !![(x : Matrix (Fin 2) (Fin 2) F) 0 0, -(x : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(x : Matrix (Fin 2) (Fin 2) F) 1 0, (x : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  rw [dNeg, t2B_slConj_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem t9_check : ∀ y : SL2 (ZMod 3), y ≠ 1 → y ^ 3 = 1 →
    (slConj (dNeg (ZMod 3)) y = y ∨ slConj (dNeg (ZMod 3)) y = y⁻¹) →
      ((y : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 = 1 ∧ (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1 = 1 ∧
        (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0) ∨
      ((y : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 = 1 ∧ (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1 = 1 ∧
        (y : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1 = 0) := by
  decide

theorem t9_sylow3_inv {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) (α : MulAut (SL2 F))
    (hU : ∀ c : F, α (sl2U c) = sl2U (-c)) (hL : ∀ c : F, α (sl2L c) = sl2L (-c))
    (Y : Subgroup (SL2 F)) (hY : Nat.card ↥Y = 3) (hα : ∀ g ∈ Y, α g ∈ Y) :
    Y = uSub F ∨ Y = lSub F := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
  let r : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e : SL2 F ≃* SL2 (ZMod 3) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map r.toRingHom)
      (Matrix.SpecialLinearGroup.map r.symm.toRingHom) (by ext x i j; simp) (by ext x i j; simp)
  have he : ∀ (x : SL2 F) (i j : Fin 2),
      ((e x : SL2 (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j = r ((x : Matrix (Fin 2) (Fin 2) F) i j) := by
    intro x i j; rfl
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Y = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hcon x hx)
    rw [this, Subgroup.card_bot] at hY
    omega
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hyY⟩)
    rw [hY] at this
    simpa using congrArg Subtype.val this
  have hYz : Y = Subgroup.zpowers y := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hyY
    · rw [Nat.card_zpowers, hY]
      have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1
      · rw [h]
  have hαy : α y = y ∨ α y = y⁻¹ := by
    have hmem : α y ∈ Subgroup.zpowers y := hYz ▸ hα y hyY
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk3 : y ^ k = y ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
      have : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
      rw [this, one_zpow, mul_one]
    have hlt : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hα1 : α y ≠ 1 := by
      intro h; apply hy1; apply α.injective; rw [h, map_one]
    rcases hlt with h0 | h1 | h2
    · exfalso; apply hα1; rw [← hk, hk3, h0]; simp
    · left; rw [← hk, hk3, h1]; simp
    · right
      rw [← hk, hk3, h2]
      have : y ^ (2 : ℤ) * y = 1 := by
        rw [← zpow_add_one]; exact_mod_cast hy3
      exact (eq_inv_of_mul_eq_one_left this)
  have hconj : ∀ x : SL2 F, e (slConj (dNeg F) x) = slConj (dNeg (ZMod 3)) (e x) := by
    intro x
    apply Subtype.ext
    ext i j
    have h1 := he (slConj (dNeg F) x) i j
    rw [h1, t9_coe_slConj_dNeg, t9_coe_slConj_dNeg]
    fin_cases i <;> fin_cases j <;> simp [he] <;> exact map_neg r _
  have hαe : α y = slConj (dNeg F) y := t9_alpha_eq α hU hL y
  have hey1 : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hey3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hcase : slConj (dNeg (ZMod 3)) (e y) = e y ∨ slConj (dNeg (ZMod 3)) (e y) = (e y)⁻¹ := by
    rw [← hconj]
    rw [hαe] at hαy
    rcases hαy with h | h
    · left; rw [h]
    · right; rw [h, map_inv]
  have key := t9_check (e y) hey1 hey3 hcase
  rcases key with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
  · left
    have hyU : y ∈ uSub F := by
      refine ⟨?_, ?_, ?_⟩
      · exact r.injective (by rw [← he y 0 0, k1, map_one])
      · exact r.injective (by rw [← he y 1 1, k2, map_one])
      · exact r.injective (by rw [← he y 1 0, k3, map_zero])
    have hle : Subgroup.zpowers y ≤ uSub F := by rw [Subgroup.zpowers_le]; exact hyU
    rw [hYz]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_uSub, h3, Nat.card_zpowers]
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · rw [h]
  · right
    have hyL : y ∈ lSub F := by
      refine ⟨?_, ?_, ?_⟩
      · exact r.injective (by rw [← he y 0 0, k1, map_one])
      · exact r.injective (by rw [← he y 1 1, k2, map_one])
      · exact r.injective (by rw [← he y 0 1, k3, map_zero])
    have hle : Subgroup.zpowers y ≤ lSub F := by rw [Subgroup.zpowers_le]; exact hyL
    rw [hYz]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_lSub, h3, Nat.card_zpowers]
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · rw [h]

end SL2

section Grp

variable {G : Type} [Group G]

theorem t9_exists_aut {F : Type} [Field F] [Finite F] {φ : SL2 F →* G} (hφ : Function.Injective φ)
    {y : G} (hy : ∀ g ∈ φ.range, y * g * y⁻¹ ∈ φ.range) :
    ∃ α : MulAut (SL2 F), ∀ g : SL2 F, φ (α g) = y * φ g * y⁻¹ := by
  have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hyn : y ∈ normalizer (φ.range : Set G) := Subgroup.mem_normalizer_fintype (fun n hn => hy n hn)
  let ρ : MulAut ↥φ.range := Subgroup.normalizerMonoidHom φ.range ⟨y, hyn⟩
  have hρ : ∀ g : ↥φ.range, ((ρ g : ↥φ.range) : G) = y * g * y⁻¹ := fun g => rfl
  let eφ : SL2 F ≃* ↥φ.range := MonoidHom.ofInjective hφ
  have heφ : ∀ g : SL2 F, ((eφ g : ↥φ.range) : G) = φ g := fun g => rfl
  let α : MulAut (SL2 F) := eφ.trans (ρ.trans eφ.symm)
  have hα : ∀ g : SL2 F, φ (α g) = y * φ g * y⁻¹ := by
    intro g
    have h1 : eφ (α g) = ρ (eφ g) := by
      show eφ (eφ.symm (ρ (eφ g))) = ρ (eφ g)
      exact eφ.apply_symm_apply _
    have h2 := congrArg (fun x : ↥φ.range => (x : G)) h1
    simpa [heφ, hρ] using h2
  exact ⟨α, hα⟩

theorem t9_syl₁ [Finite G] {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {B : Subgroup G} (hB : B ≤ N.K₁)
    (hBp : IsPGroup p ↥B) (hBH : ∀ x ∈ N.H, ∀ y ∈ B, x * y * x⁻¹ ∈ B)
    (hBc : Nat.card ↥B = N.q₁) : B = N.X₁ ∨ B = N.X₁' := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₁
  obtain ⟨m, hm⟩ := h.q₁_pow
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.sec5.loc.q₁_odd
  have h5 : 5 ≤ Nat.card F := by rw [hcard]; exact h.sec5.loc.q₁_ge
  have hF : Nat.card F = p ^ m := by rw [hcard, hm]
  have hBr : B ≤ φ.range := by rw [hrange]; exact hB
  have hT : ∀ t ∈ tSub F, ∀ b ∈ B, φ t * b * (φ t)⁻¹ ∈ B := by
    intro t ht b hb
    have : φ t ∈ N.H ⊓ N.K₁ := by rw [hHK]; exact Subgroup.mem_map_of_mem φ ht
    exact hBH _ this.1 b hb
  rcases t6_pSub_inv hinj h.prime hF hodd h5 hBr hBp hT with h1 | h1 | h1
  · exfalso
    rw [h1, Subgroup.card_bot] at hBc
    have := h.sec5.loc.q₁_ge
    omega
  · left; rw [h1, hX]
  · right; rw [h1, hX']

theorem t9_syl₂ [Finite G] {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {B : Subgroup G} (hB : B ≤ N.K₂)
    (hBp : IsPGroup p ↥B) (hBH : ∀ x ∈ N.H, ∀ y ∈ B, x * y * x⁻¹ ∈ B)
    (hBc : Nat.card ↥B = N.q₂) : B = N.X₂ ∨ B = N.X₂' := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₂
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.sec5.loc.q₂_odd
  have hq3 : 3 ≤ N.q₂ := h.sec5.loc.q₂_ge
  have hBr : B ≤ φ.range := by rw [hrange]; exact hB
  by_cases hq : N.q₂ = 3
  ·
    have h3 : Nat.card F = 3 := by rw [hcard, hq]
    have huH : u ∈ N.H := h.sec5.loc.u_mem_H
    have huK : ∀ g ∈ φ.range, u * g * u⁻¹ ∈ φ.range := by
      rw [hrange]
      exact (h.Cnorm u h.sec5.loc.u_comm).2
    obtain ⟨α, hα⟩ := t9_exists_aut hinj huK
    have hU : ∀ c : F, α (sl2U c) = sl2U (-c) := by
      intro c
      apply hinj
      have hmem : φ (sl2U c) ∈ N.X₂ := by rw [hX]; exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub c)
      rw [hα, h.sec5.loc.u_inv_X₂ _ hmem, ← map_inv, t9_sl2U_inv]
    have hL : ∀ c : F, α (sl2L c) = sl2L (-c) := by
      intro c
      apply hinj
      have hmem : φ (sl2L c) ∈ N.X₂' := by rw [hX']; exact Subgroup.mem_map_of_mem φ (sl2L_mem_lSub c)
      rw [hα, h.sec5.loc.u_inv_X₂' _ hmem, ← map_inv, t9_sl2L_inv]
    have hYc : Nat.card ↥(B.comap φ) = 3 := by
      have h1 : Nat.card ↥((B.comap φ).map φ) = Nat.card ↥(B.comap φ) :=
        Subgroup.card_map_of_injective hinj
      rw [t6_map_comap hBr] at h1
      rw [← h1, hBc, hq]
    have hYα : ∀ g ∈ B.comap φ, α g ∈ B.comap φ := by
      intro g hg
      rw [Subgroup.mem_comap] at hg ⊢
      rw [hα]
      exact hBH u huH _ hg
    rcases t9_sylow3_inv h3 α hU hL (B.comap φ) hYc hYα with h1 | h1
    · left
      rw [← t6_map_comap hBr, h1, hX]
    · right
      rw [← t6_map_comap hBr, h1, hX']
  · have h5 : 5 ≤ Nat.card F := by
      rw [hcard]
      have : N.q₂ % 2 = 1 := Nat.odd_iff.1 h.sec5.loc.q₂_odd
      omega
    have hF : Nat.card F = p ^ n := by rw [hcard, hn]
    have hT : ∀ t ∈ tSub F, ∀ b ∈ B, φ t * b * (φ t)⁻¹ ∈ B := by
      intro t ht b hb
      have : φ t ∈ N.H ⊓ N.K₂ := by rw [hHK]; exact Subgroup.mem_map_of_mem φ ht
      exact hBH _ this.1 b hb
    rcases t6_pSub_inv hinj h.prime hF hodd h5 hBr hBp hT with h1 | h1 | h1
    · exfalso
      rw [h1, Subgroup.card_bot] at hBc
      omega
    · left; rw [h1, hX]
    · right; rw [h1, hX']

end Grp

end CFSG.GH74.GLS.Stage4.Rest.T9
