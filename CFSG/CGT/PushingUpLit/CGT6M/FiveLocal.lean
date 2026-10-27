module

public import CFSG.CGT.PushingUpLit.CGT6M.FixSub

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open MulAction

variable {V : Type} [Group V] {K : Type*} [Group K]

theorem not_dvd_burnside : ∀ d ≤ 8, ∀ e₁ < d, ∀ e₂ < d, 5 ∣ 2 ^ d - 2 ^ e₁ → 5 ∣ 2 ^ d - 2 ^ e₂ →
    ¬ 25 ∣ 2 ^ d + 12 * (2 ^ e₁ + 2 ^ e₂) := by
  decide

abbrev C55 : Type := Multiplicative (ZMod 5 × ZMod 5)

@[expose] def phi (A B : K) (hA : A ^ 5 = 1) (hB : B ^ 5 = 1) (hAB : Commute A B) :
    C55 →* K :=
  MonoidHom.mk' (fun u => A ^ (Multiplicative.toAdd u).1.val * B ^ (Multiplicative.toAdd u).2.val)
    (by
      intro u v
      obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
      obtain ⟨⟨i', j'⟩, rfl⟩ : ∃ w, v = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd v, rfl⟩
      simp only [← ofAdd_add, toAdd_ofAdd, Prod.mk_add_mk, ZMod.val_add]
      rw [pow_mod_five hA, pow_mod_five hB, pow_add, pow_add]
      have h := (hAB.pow_pow i'.val j.val).eq
      calc A ^ i.val * A ^ i'.val * (B ^ j.val * B ^ j'.val)
          = A ^ i.val * (A ^ i'.val * B ^ j.val) * B ^ j'.val := by simp only [mul_assoc]
        _ = A ^ i.val * (B ^ j.val * A ^ i'.val) * B ^ j'.val := by rw [h]
        _ = A ^ i.val * B ^ j.val * (A ^ i'.val * B ^ j'.val) := by simp only [mul_assoc])

theorem phi_ofAdd (A B : K) (hA : A ^ 5 = 1) (hB : B ^ 5 = 1) (hAB : Commute A B)
    (i j : ZMod 5) :
    phi A B hA hB hAB (Multiplicative.ofAdd (i, j)) = A ^ i.val * B ^ j.val := rfl

@[expose] def mapM : ZMod 5 × ZMod 5 →+ ZMod 5 × ZMod 5 :=
  AddMonoidHom.mk' (fun w => (-w.2, w.1 - w.2)) (by
    intro a b
    ext <;> simp <;> ring)

theorem c55_hom_ext {K : Type*} [Group K] {f g : C55 →* K}
    (h1 : f (Multiplicative.ofAdd (1, 0)) = g (Multiplicative.ofAdd (1, 0)))
    (h2 : f (Multiplicative.ofAdd (0, 1)) = g (Multiplicative.ofAdd (0, 1))) : f = g := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
  have h : (Multiplicative.ofAdd (i, j) : C55) =
      Multiplicative.ofAdd ((1 : ZMod 5), (0 : ZMod 5)) ^ i.val *
        Multiplicative.ofAdd ((0 : ZMod 5), (1 : ZMod 5)) ^ j.val := by
    rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
    congr 1
    ext <;> simp
  rw [h, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h1, h2]

theorem inv_eq_pow_four {x : K} (h : x ^ 5 = 1) : x⁻¹ = x ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h)

theorem val_one_zmod5 : (1 : ZMod 5).val = 1 := rfl

theorem val_zero_zmod5 : (0 : ZMod 5).val = 0 := rfl

theorem val_two_zmod5 : (2 : ZMod 5).val = 2 := rfl

theorem val_neg_one_zmod5 : (-1 : ZMod 5).val = 4 := rfl

section PhiMap

variable {A B G : K}

theorem phi_mapM (hA5 : A ^ 5 = 1) (hB5 : B ^ 5 = 1) (hAB : Commute A B)
    (hGA : G * A * G⁻¹ = B) (hGB : G * B * G⁻¹ = (A * B)⁻¹) (u : C55) :
    phi A B hA5 hB5 hAB (AddMonoidHom.toMultiplicative mapM u) =
      G * phi A B hA5 hB5 hAB u * G⁻¹ := by
  have key : (phi A B hA5 hB5 hAB).comp (AddMonoidHom.toMultiplicative mapM) =
      (MulAut.conj G).toMonoidHom.comp (phi A B hA5 hB5 hAB) := by
    apply c55_hom_ext
    · simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, mapM,
        AddMonoidHom.mk'_apply, phi_ofAdd]
      simp [val_one_zmod5, hGA]
    · simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, mapM,
        AddMonoidHom.mk'_apply, phi_ofAdd]
      have hinv : (A * B)⁻¹ = A ^ 4 * B ^ 4 := by
        rw [mul_inv_rev, ← hAB.inv_inv.eq, inv_eq_pow_four hA5, inv_eq_pow_four hB5]
      simp [val_one_zmod5, hGB, hinv]
  exact DFunLike.congr_fun key u

end PhiMap

theorem dvd_sum_card_fixSub [Finite V] (Φ : C55 →* MulAut V) :
    25 ∣ ∑ u : C55, Nat.card (fixSub (Φ u)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let _ : MulAction C55 V := MulAction.compHom V Φ
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group C55 V
  have hc : Fintype.card C55 = 25 := by
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod, ZMod.card]
  rw [hc] at h
  have h2 : ∀ u : C55, Fintype.card (fixedBy V u) = Nat.card (fixSub (Φ u)) := fun u => by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.refl _)
  simp only [h2] at h
  exact ⟨_, h.trans (mul_comm _ _)⟩

theorem sum_zmod5_prod (f : ZMod 5 × ZMod 5 → ℕ) :
    ∑ w : ZMod 5 × ZMod 5, f w =
      f (0, 0) + f (0, 1) + f (0, 2) + f (0, 3) + f (0, 4) +
      (f (1, 0) + f (1, 1) + f (1, 2) + f (1, 3) + f (1, 4)) +
      (f (2, 0) + f (2, 1) + f (2, 2) + f (2, 3) + f (2, 4)) +
      (f (3, 0) + f (3, 1) + f (3, 2) + f (3, 3) + f (3, 4)) +
      (f (4, 0) + f (4, 1) + f (4, 2) + f (4, 3) + f (4, 4)) := by
  rw [Fintype.sum_prod_type]
  have h : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  rw [h]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  omega

theorem sum_card_fixSub {Φ : C55 →* MulAut V} {G : MulAut V}
    (hM : ∀ u : C55, Φ (AddMonoidHom.toMultiplicative mapM u) = G * Φ u * G⁻¹) :
    ∑ u : C55, Nat.card (fixSub (Φ u)) =
      Nat.card (fixSub (Φ 1)) + 12 * Nat.card (fixSub (Φ (Multiplicative.ofAdd (1, 0)))) +
        12 * Nat.card (fixSub (Φ (Multiplicative.ofAdd (1, 2)))) := by
  let g : ZMod 5 × ZMod 5 → ℕ := fun w => Nat.card (fixSub (Φ (Multiplicative.ofAdd w)))
  have hscl : ∀ (k : ℕ) (r s : ZMod 5 × ZMod 5), ¬ 5 ∣ k → k • r = s → g s = g r := by
    intro k r s hk hks
    have hX5 : (Φ (Multiplicative.ofAdd r)) ^ 5 = 1 := by
      rw [← map_pow, ← ofAdd_nsmul]
      have h5 : (5 : ℕ) • r = 0 := by
        have h5' : (5 : ZMod 5) = 0 := by decide
        ext <;> simp [h5']
      rw [h5]
      exact map_one Φ
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hk).symm (by norm_num)
    show Nat.card (fixSub (Φ (Multiplicative.ofAdd s))) =
      Nat.card (fixSub (Φ (Multiplicative.ofAdd r)))
    rw [← hks, ofAdd_nsmul, map_pow, fixSub_pow_eq hX5 hm]
  have hMl : ∀ r s : ZMod 5 × ZMod 5, (-r.2, r.1 - r.2) = s → g s = g r := by
    intro r s hrs
    have h := hM (Multiplicative.ofAdd r)
    rw [AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd] at h
    show Nat.card (fixSub (Φ (Multiplicative.ofAdd s))) =
      Nat.card (fixSub (Φ (Multiplicative.ofAdd r)))
    rw [← hrs]
    change Nat.card (fixSub (Φ (Multiplicative.ofAdd (mapM r)))) = _
    rw [h, card_fixSub_conj]
  have hsum : ∑ u : C55, Nat.card (fixSub (Φ u)) = ∑ w : ZMod 5 × ZMod 5, g w :=
    Fintype.sum_equiv Multiplicative.toAdd _ _ (fun u => rfl)
  rw [hsum, sum_zmod5_prod]
  have e1 : g (2, 0) = g (1, 0) := hscl 2 (1, 0) (2, 0) (by decide) (by decide)
  have e2 : g (3, 0) = g (1, 0) := hscl 3 (1, 0) (3, 0) (by decide) (by decide)
  have e3 : g (4, 0) = g (1, 0) := hscl 4 (1, 0) (4, 0) (by decide) (by decide)
  have e4 : g (0, 1) = g (1, 0) := hMl (1, 0) (0, 1) (by decide)
  have e5 : g (0, 2) = g (0, 1) := hscl 2 (0, 1) (0, 2) (by decide) (by decide)
  have e6 : g (0, 3) = g (0, 1) := hscl 3 (0, 1) (0, 3) (by decide) (by decide)
  have e7 : g (0, 4) = g (0, 1) := hscl 4 (0, 1) (0, 4) (by decide) (by decide)
  have e8 : g (4, 4) = g (0, 1) := hMl (0, 1) (4, 4) (by decide)
  have e9 : g (1, 1) = g (4, 4) := hscl 4 (4, 4) (1, 1) (by decide) (by decide)
  have e10 : g (2, 2) = g (4, 4) := hscl 3 (4, 4) (2, 2) (by decide) (by decide)
  have e11 : g (3, 3) = g (4, 4) := hscl 2 (4, 4) (3, 3) (by decide) (by decide)
  have f1 : g (2, 4) = g (1, 2) := hscl 2 (1, 2) (2, 4) (by decide) (by decide)
  have f2 : g (3, 1) = g (1, 2) := hscl 3 (1, 2) (3, 1) (by decide) (by decide)
  have f3 : g (4, 3) = g (1, 2) := hscl 4 (1, 2) (4, 3) (by decide) (by decide)
  have f4 : g (3, 4) = g (1, 2) := hMl (1, 2) (3, 4) (by decide)
  have f5 : g (1, 3) = g (3, 4) := hscl 2 (3, 4) (1, 3) (by decide) (by decide)
  have f6 : g (4, 2) = g (3, 4) := hscl 3 (3, 4) (4, 2) (by decide) (by decide)
  have f7 : g (2, 1) = g (3, 4) := hscl 4 (3, 4) (2, 1) (by decide) (by decide)
  have f8 : g (1, 4) = g (3, 4) := hMl (3, 4) (1, 4) (by decide)
  have f9 : g (2, 3) = g (1, 4) := hscl 2 (1, 4) (2, 3) (by decide) (by decide)
  have f10 : g (3, 2) = g (1, 4) := hscl 3 (1, 4) (3, 2) (by decide) (by decide)
  have f11 : g (4, 1) = g (1, 4) := hscl 4 (1, 4) (4, 1) (by decide) (by decide)
  have h0 : g (0, 0) = Nat.card (fixSub (Φ 1)) := by
    show Nat.card (fixSub (Φ (Multiplicative.ofAdd (0, 0)))) = _
    rfl
  have h10 : Nat.card (fixSub (Φ (Multiplicative.ofAdd (1, 0)))) = g (1, 0) := rfl
  have h12 : Nat.card (fixSub (Φ (Multiplicative.ofAdd (1, 2)))) = g (1, 2) := rfl
  rw [h10, h12]
  omega

variable [Finite V]

theorem false_of_five_local {d : ℕ} (hV : Nat.card V = 2 ^ d) (hd : d ≤ 8)
    {A B G : MulAut V} (hA1 : A ≠ 1) (hA5 : A ^ 5 = 1) (hAB : Commute A B)
    (hGA : G * A * G⁻¹ = B) (hGB : G * B * G⁻¹ = (A * B)⁻¹) : False := by
  have hB5 : B ^ 5 = 1 := by
    rw [← hGA, conj_pow, hA5]
    group
  have hB1 : B ≠ 1 := by
    intro h
    apply hA1
    have h' : G * A * G⁻¹ = 1 := hGA.trans h
    calc A = G⁻¹ * (G * A * G⁻¹) * G := by group
      _ = 1 := by rw [h']; group
  have hAB2 : A * B ^ 2 ≠ 1 := by
    intro h
    have hA' : A = (B ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hAB' : (A * B)⁻¹ = B := by
      rw [hA']
      group
    have h2 : B * ((A * B)⁻¹) ^ 2 = 1 := by
      have e1 : G * (A * B ^ 2) * G⁻¹ = (G * A * G⁻¹) * (G * B ^ 2 * G⁻¹) := by group
      have e2 : G * (A * B ^ 2) * G⁻¹ = B * ((A * B)⁻¹) ^ 2 := by
        rw [e1, ← conj_pow, hGA, hGB]
      rw [← e2, h]
      group
    rw [hAB'] at h2
    have h3 : B ^ 3 = 1 := by
      rw [← h2]
      group
    have h4 : orderOf B ∣ Nat.gcd 5 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hB5) (orderOf_dvd_of_pow_eq_one h3)
    have h5 : orderOf B = 1 := Nat.dvd_one.mp (by simpa using h4)
    exact hB1 (orderOf_eq_one_iff.mp h5)
  have hdvd := dvd_sum_card_fixSub (phi A B hA5 hB5 hAB)
  rw [sum_card_fixSub (G := G) (fun u => phi_mapM hA5 hB5 hAB hGA hGB u)] at hdvd
  have h1 : Nat.card (fixSub (phi A B hA5 hB5 hAB 1)) = 2 ^ d := by
    rw [map_one, fixSub_one, Subgroup.card_top, hV]
  have hA : Nat.card (fixSub (phi A B hA5 hB5 hAB (Multiplicative.ofAdd (1, 0)))) =
      Nat.card (fixSub A) := by
    rw [phi_ofAdd, val_one_zmod5, val_zero_zmod5, pow_one, pow_zero, mul_one]
  have hX : Nat.card (fixSub (phi A B hA5 hB5 hAB (Multiplicative.ofAdd (1, 2)))) =
      Nat.card (fixSub (A * B ^ 2)) := by
    rw [phi_ofAdd, val_one_zmod5, val_two_zmod5, pow_one]
  obtain ⟨e1, he1, hf1, hd1⟩ := exists_card_fixSub_five hV hA5 hA1
  have hX5 : (A * B ^ 2) ^ 5 = 1 := by
    rw [(hAB.pow_right 2).mul_pow, hA5, ← pow_mul, mul_comm 2 5, pow_mul, hB5, one_pow, one_mul]
  obtain ⟨e2, he2, hf2, hd2⟩ := exists_card_fixSub_five hV hX5 hAB2
  rw [h1, hA, hX, hf1, hf2] at hdvd
  refine not_dvd_burnside d hd e1 he1 e2 he2 hd1 hd2 ?_
  have e : 2 ^ d + 12 * 2 ^ e1 + 12 * 2 ^ e2 = 2 ^ d + 12 * (2 ^ e1 + 2 ^ e2) := by ring
  rwa [e] at hdvd

end CFSG.CGT.PushingUpLit.CGT6M
