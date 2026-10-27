module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsAlt

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b

section SL2

variable {K : Type*} [Field K]

theorem natCard_SL2 [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem exists_SL2_mulVec_single (x : Fin 2 → K) (hx : x ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K).mulVec ![1, 0] = x := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i <;> simp_all
    refine ⟨⟨!![0, -(x 1)⁻¹; x 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![x 0, 0; x 1, (x 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_SL2_mulVec_eq (x y : Fin 2 → K) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K).mulVec x = y := by
  obtain ⟨A, hA⟩ := exists_SL2_mulVec_single x hx
  obtain ⟨B, hB⟩ := exists_SL2_mulVec_single y hy
  refine ⟨B * A⁻¹, ?_⟩
  have hAinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec x =
      ![1, 0] := by
    rw [← hA, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hAinv, hB]

end SL2

theorem natCard_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  have h := Polynomial.SplittingField.adjoin_rootSet
    (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2))
  have hpoly : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)) = 0 := by simp
  have hempty : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)).rootSet
      (GaloisField 2 0) = ∅ := by
    ext x
    simp only [Polynomial.mem_rootSet, hpoly, ne_eq, not_true_eq_false, false_and,
      Set.mem_empty_iff_false]
  change Algebra.adjoin (ZMod 2) ((Polynomial.X ^ 2 ^ 0 - Polynomial.X :
    Polynomial (ZMod 2)).rootSet (GaloisField 2 0)) = ⊤ at h
  rw [hempty, Algebra.adjoin_empty] at h
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (GaloisField 2 0)) := by
    intro x
    have : x ∈ (⊥ : Subalgebra (ZMod 2) (GaloisField 2 0)) := by rw [h]; trivial
    exact Algebra.mem_bot.mp this
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap (ZMod 2) (GaloisField 2 0)).injective,
    hsurj⟩), Nat.card_zmod]

theorem eq_two_of_natCard_galoisField {k : ℕ} (h : Nat.card (GaloisField 2 k) = 4) : k = 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [natCard_galoisField_two_zero] at h
    norm_num at h
  · rw [GaloisField.card 2 k hk.ne'] at h
    exact Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num))

variable {n : ℕ}

theorem vcoord_of_mem_fixV_commV {F : Subgroup (Equiv.Perm (Fin n))} {x₀ : Fin n}
    (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a) {v : ↥(coreMod n)}
    (hv : v ∈ fixV (F.map (coreAct n))) (hv' : v ∈ commV (F.map (coreAct n))) (i : Fin n) :
    vcoord v i = if i ∈ movFin F then vcoord v x₀ else 0 := by
  split_ifs with hi
  · obtain ⟨f, hf, rfl⟩ := hsame i (mem_movFin.1 hi)
    exact mem_fixV_map_iff.1 hv f hf x₀
  · refine vcoord_eq_zero_of_mem_commV hv' fun f hf => ?_
    by_contra hne
    exact hi (mem_movFin.2 ⟨f, hf, hne⟩)

theorem card_fixV_inf_commV_le_two {F : Subgroup (Equiv.Perm (Fin n))} {x₀ : Fin n}
    (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a) :
    Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) ≤ 2 := by
  let φ : ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) → ZMod 2 :=
    fun v => vcoord (v : ↥(coreMod n)) x₀
  have hφ : Function.Injective φ := by
    intro v w h
    apply Subtype.ext
    apply vcoord_ext
    intro i
    rw [vcoord_of_mem_fixV_commV hsame v.2.1 v.2.2, vcoord_of_mem_fixV_commV hsame w.2.1 w.2.2]
    simp only [φ] at h
    rw [h]
  exact (Nat.card_le_card_of_injective φ hφ).trans_eq (Nat.card_zmod 2)

theorem pairVec_mem_commV_of_mem (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))} {x₀ : Fin n}
    (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a) {a b : Fin n} (ha : a ∈ movFin F)
    (hb : b ∈ movFin F) : pairVec a b ∈ commV (F.map (coreAct n)) := by
  obtain ⟨f, hf, rfl⟩ := hsame a (mem_movFin.1 ha)
  obtain ⟨g, hg, rfl⟩ := hsame b (mem_movFin.1 hb)
  rw [← pairVec_mul x₀, pairVec_comm x₀]
  exact Subgroup.mul_mem _ (pairVec_mem_commV hn hf x₀)
    (by rw [pairVec_comm]; exact pairVec_mem_commV hn hg x₀)

theorem apply_mem_movFin {F : Subgroup (Equiv.Perm (Fin n))} {f : Equiv.Perm (Fin n)}
    (hf : f ∈ F) {x : Fin n} (hx : x ∈ movFin F) : f x ∈ movFin F := by
  obtain ⟨g, hg, hgx⟩ := mem_movFin.1 hx
  refine mem_movFin.2 ⟨f * g * f⁻¹, F.mul_mem (F.mul_mem hf hg) (F.inv_mem hf), ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self]
  exact fun h => hgx (f.injective h)

theorem exists_mul_pairVec_mem_of_SL (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F) {x₀ : Fin n} (hx₀ : ∃ f ∈ F, f x₀ ≠ x₀) {k : ℕ}
    (hSL : IsSLNatSection (F.map (coreAct n)) (commV (F.map (coreAct n)))
      (fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) k)
    {w : ↥(coreMod n)} (hw : w ∈ commV (F.map (coreAct n)))
    (hw' : w ∉ fixV (F.map (coreAct n))) :
    ∃ c ∈ movFin F, ∃ d ∈ movFin F, c ≠ d ∧
      w * pairVec c d ∈ fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n)) := by
  obtain ⟨hinv, θ, β, -, hβk, hβe⟩ := hSL
  obtain ⟨f, hf, hfx⟩ := hx₀
  obtain ⟨g, hg, hgx, hgf⟩ := exists_third_of_opResidual hF hf hfx
  have hp₀ : pairVec (f x₀) x₀ ∈ commV (F.map (coreAct n)) := pairVec_mem_commV hn hf x₀
  have hp₀' : pairVec (f x₀) x₀ ∉ fixV (F.map (coreAct n)) := by
    intro h
    have h1 := mem_fixV_map_iff.1 h g hg x₀
    rw [vcoord_pairVec, vcoord_pairVec] at h1
    simp [hgx, hgf, hfx.symm] at h1
  have hker : ∀ u : ↥(commV (F.map (coreAct n))), β u = 1 →
      (u : ↥(coreMod n)) ∈ fixV (F.map (coreAct n)) := by
    intro u hu
    have h1 : u ∈ β.ker := hu
    rw [hβk, Subgroup.mem_subgroupOf] at h1
    exact h1.1
  have hne : ∀ u : ↥(commV (F.map (coreAct n))), (u : ↥(coreMod n)) ∉ fixV (F.map (coreAct n)) →
      Multiplicative.toAdd (β u) ≠ 0 := fun u hu h =>
    hu (hker u (by rw [← ofAdd_toAdd (β u), h]; rfl))
  obtain ⟨A, hA⟩ := exists_SL2_mulVec_eq _ _ (hne ⟨_, hp₀⟩ hp₀') (hne ⟨w, hw⟩ hw')
  obtain ⟨x, hxA⟩ : ∃ x, θ x = A := ⟨θ.symm A, θ.apply_symm_apply A⟩
  obtain ⟨σ, hσ, hσx⟩ := Subgroup.mem_map.1 x.2
  have hxp := hinv x x.2 _ hp₀
  have h1 := hβe x ⟨_, hp₀⟩ hxp
  rw [hxA, hA, ofAdd_toAdd] at h1
  have hxv : x.1 (pairVec (f x₀) x₀) = pairVec (σ (f x₀)) (σ x₀) := by
    rw [← hσx]
    exact coreAct_pairVec σ (f x₀) x₀
  have hx₀m : x₀ ∈ movFin F := mem_movFin.2 ⟨f, hf, hfx⟩
  have hfx₀m : f x₀ ∈ movFin F := apply_mem_movFin hf hx₀m
  refine ⟨σ (f x₀), apply_mem_movFin hσ hfx₀m, σ x₀, apply_mem_movFin hσ hx₀m,
    fun h => hfx (σ.injective h), ?_⟩
  have h2 : β (⟨w, hw⟩ * (⟨_, hxp⟩ : ↥(commV (F.map (coreAct n))))⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := hker _ h2
  have e1 : ((⟨w, hw⟩ * (⟨_, hxp⟩ : ↥(commV (F.map (coreAct n))))⁻¹ :
      ↥(commV (F.map (coreAct n)))) : ↥(coreMod n)) = w * pairVec (σ (f x₀)) (σ x₀) := by
    show w * (x.1 (pairVec (f x₀) x₀))⁻¹ = _
    rw [hxv, coreMod_inv_eq]
  rw [← e1]
  exact ⟨h3, (⟨w, hw⟩ * (⟨_, hxp⟩ : ↥(commV (F.map (coreAct n))))⁻¹).2⟩

theorem card_movFin_eq_six_of_SL (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F) {x₀ : Fin n} (hx₀ : ∃ f ∈ F, f x₀ ≠ x₀)
    (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a) {k : ℕ}
    (hSL : IsSLNatSection (F.map (coreAct n)) (commV (F.map (coreAct n)))
      (fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) k)
    (h5 : 5 ≤ (movFin F).card) : (movFin F).card = 6 := by
  classical
  set S := movFin F with hS
  have hx₀m : x₀ ∈ S := mem_movFin.2 hx₀
  obtain ⟨b, hb, hb'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x₀}) (t := S)
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨c, hc, hc'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x₀, b}) (t := S)
    (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x₀, b, c}) (t := S)
    (Finset.card_le_three.trans_lt (by omega))
  obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x₀, b, c, d}) (t := S)
    (Finset.card_le_four.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb' hc' hd' he'
  set w := pairVec x₀ b * pairVec c d with hwdef
  have hw : w ∈ commV (F.map (coreAct n)) := Subgroup.mul_mem _
    (pairVec_mem_commV_of_mem hn hsame hx₀m hb) (pairVec_mem_commV_of_mem hn hsame hc hd)
  have hwc : ∀ i, vcoord w i = ((if i = x₀ then 1 else 0) + (if i = b then 1 else 0)) +
      ((if i = c then 1 else 0) + (if i = d then 1 else 0)) := fun i => by
    rw [hwdef, vcoord_mul, vcoord_pairVec, vcoord_pairVec]
  have hw' : w ∉ fixV (F.map (coreAct n)) := by
    intro h
    have h1 := vcoord_of_mem_fixV_commV hsame h hw x₀
    have h2 := vcoord_of_mem_fixV_commV hsame h hw e
    rw [ite_eq_left hx₀m] at h1
    rw [ite_eq_left he, ← h1, hwc, hwc] at h2
    simp [Ne.symm hb', Ne.symm hc'.1, Ne.symm hd'.1, he'.1, he'.2.1, he'.2.2.1, he'.2.2.2] at h2
  obtain ⟨c', -, d', -, -, hu⟩ := exists_mul_pairVec_mem_of_SL hn hF hx₀ hSL hw hw'
  have huc := vcoord_of_mem_fixV_commV hsame hu.1 hu.2
  have hu' : ∀ i, vcoord (w * pairVec c' d') i =
      vcoord w i + ((if i = c' then 1 else 0) + (if i = d' then 1 else 0)) := fun i => by
    rw [vcoord_mul, vcoord_pairVec]
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key (vcoord (w * pairVec c' d') x₀) with h0 | h0
  · exfalso
    have hpv : ∀ i, vcoord w i = 1 → i = c' ∨ i = d' := by
      intro i hi
      have h1 := huc i
      rw [h0, ite_self, hu', hi] at h1
      by_contra hne
      push Not at hne
      simp [hne.1, hne.2] at h1
    have ka := hpv x₀ (by rw [hwc]; simp [Ne.symm hb', Ne.symm hc'.1, Ne.symm hd'.1])
    have kb := hpv b (by rw [hwc]; simp [hb', Ne.symm hc'.2, Ne.symm hd'.2.1])
    have kc := hpv c (by rw [hwc]; simp [hc'.1, hc'.2, Ne.symm hd'.2.2])
    rcases ka with ha | ha <;> rcases kb with hb2 | hb2 <;> rcases kc with hc2 | hc2
    all_goals first
      | exact hb' (hb2.trans ha.symm)
      | exact hc'.1 (hc2.trans ha.symm)
      | exact hc'.2 (hc2.trans hb2.symm)
  · have hle : (movFin F).card ≤ 6 := by
      by_contra hlt
      push Not at hlt
      obtain ⟨e₂, he₂, he₂'⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {x₀, b, c, d, c', d'}) (t := S) (Finset.card_le_six.trans_lt hlt)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he₂'
      have h1 := huc e₂
      rw [ite_eq_left he₂, h0, hu', hwc] at h1
      simp [he₂'.1, he₂'.2.1, he₂'.2.2.1, he₂'.2.2.2.1, he₂'.2.2.2.2.1, he₂'.2.2.2.2.2] at h1
    have heven : Even (movFin F).card := by
      have h1 := sum_vcoord (w * pairVec c' d')
      rw [Finset.sum_congr rfl fun i _ => huc i, h0, Finset.sum_boole] at h1
      rw [← ZMod.natCast_eq_zero_iff_even, ← h1]
      congr 2
      ext i
      simp
    obtain ⟨j, hj⟩ := heven
    rw [hS] at h5 ⊢
    omega

theorem two_fourteen_c (n : ℕ) (hn : Odd n) {F Y : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F)
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n))))
    (k : ℕ) (hSL : IsSLNatSection (F.map (coreAct n)) (commV (F.map (coreAct n)))
      (fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) k) (hY : IsMaxSwapGroup Y) :
    k = 2 ∧ Nat.card {i : Fin n // ∀ f ∈ F, f i = i} = n - 6 ∧
      ∃ g : Equiv.Perm (Fin n),
        (∀ y ∈ conjSub g Y, ∀ w ∈ commV (F.map (coreAct n)),
          coreAct n y w ∈ commV (F.map (coreAct n))) ∧
        (∀ y ∈ conjSub g Y, ∀ w ∈ fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n)),
          coreAct n y w ∈ fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) := by
  obtain ⟨x₀, hx₀⟩ := exists_moved_of_irr hirr
  have hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a :=
    fun a ha => same_orbit_of_moved hn hF hirr ha hx₀
  have hm3 : 3 ≤ (movFin F).card := three_le_card_movFin hF hx₀
  have h3n : 3 ≤ n := hm3.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hadd := card_movFin_add F
  have hcV : Nat.card (commV (F.map (coreAct n))) * 2 = 2 ^ (movFin F).card := by
    have hcount := card_commV_mul hn hx₀ hsame
    have h2 : 2 ^ n = 2 ^ (movFin F).card * 2 ^ Nat.card {i : Fin n // ∀ f ∈ F, f i = i} := by
      rw [← pow_add, hadd]
    rw [h2, mul_right_comm] at hcount
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hcount
  have hSL₀ := hSL
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hSL₀
  have hβcard : Nat.card (commV (F.map (coreAct n))) =
      Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) *
        Nat.card (GaloisField 2 k) ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.2 hβs, Subgroup.card_top, hβk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
    rw [← h]
    congr 1
    change Nat.card (Fin 2 → GaloisField 2 k) = _
    rw [Nat.card_fun, Nat.card_fin]
  have hC2 := card_fixV_inf_commV_le_two hsame
  have hC1 : 0 < Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) := Nat.card_pos
  have hm6 : (movFin F).card = 6 := by
    by_contra hne
    have hm34 : (movFin F).card = 3 ∨ (movFin F).card = 4 := by
      by_contra h'
      exact hne (card_movFin_eq_six_of_SL hn hF hx₀ hsame hSL (by omega))
    have hq : Nat.card (GaloisField 2 k) = 2 := by
      obtain ⟨q, hq⟩ : ∃ q, Nat.card (GaloisField 2 k) = q := ⟨_, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) = c :=
        ⟨_, rfl⟩
      rw [hq, hc] at hβcard
      rw [hc] at hC1 hC2
      rw [hq]
      have hM : c * q ^ 2 * 2 = 8 ∨ c * q ^ 2 * 2 = 16 := by
        rcases hm34 with h | h <;> rw [h, hβcard] at hcV <;> norm_num at hcV <;> omega
      have hq3 : q ≤ 3 := by rcases hM with h | h <;> nlinarith
      interval_cases c <;> interval_cases q <;> omega
    have hFc : Nat.card F = 6 := by
      refine (Subgroup.card_map_of_injective (coreAct_injective h3n)).symm.trans
        ((Nat.card_congr θ.toEquiv).trans ?_)
      rw [natCard_SL2, hq]
      norm_num
    rcases hm34 with h3 | h4
    · have h1 := Subgroup.card_le_of_le (le_altOn_movFin hF)
      rw [card_altOn (by omega), h3, hFc] at h1
      norm_num at h1
    · have hdvd : (MulAction.orbit F x₀).ncard ∣ Nat.card F := by
        rw [← MulAction.index_stabilizer]
        exact Subgroup.index_dvd_card _
      have horb : MulAction.orbit F x₀ = ↑(movFin F) := by
        ext y
        rw [Finset.mem_coe]
        constructor
        · rintro ⟨⟨f, hf⟩, rfl⟩
          exact apply_mem_movFin hf (mem_movFin.2 hx₀)
        · intro hy
          obtain ⟨f, hf, rfl⟩ := hsame y (mem_movFin.1 hy)
          exact ⟨⟨f, hf⟩, rfl⟩
      rw [horb, Set.ncard_coe_finset, h4, hFc] at hdvd
      norm_num at hdvd
  have hq4 : Nat.card (GaloisField 2 k) = 4 := by
    obtain ⟨q, hq⟩ : ∃ q, Nat.card (GaloisField 2 k) = q := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) = c :=
      ⟨_, rfl⟩
    rw [hq, hc] at hβcard
    rw [hc] at hC1 hC2
    rw [hq]
    rw [hm6, hβcard] at hcV
    norm_num at hcV
    have hq6 : q ≤ 6 := by nlinarith
    interval_cases c <;> interval_cases q <;> omega
  refine ⟨eq_two_of_natCard_galoisField hq4, by omega, ?_⟩
  obtain ⟨g, hg⟩ := exists_conjSub_le_setStab hn hY (movFin F)
  have hst : ∀ y ∈ conjSub g Y, ∀ x, y⁻¹ x ∈ movFin F ↔ x ∈ movFin F := fun y hy x =>
    mem_setStab.1 ((setStab (movFin F)).inv_mem (hg hy)) x
  have hcomm : ∀ y ∈ conjSub g Y, ∀ w ∈ commV (F.map (coreAct n)),
      coreAct n y w ∈ commV (F.map (coreAct n)) := by
    intro y hy w hw
    rw [mem_commV_iff_of_orbit hn hsame] at hw ⊢
    intro i hi
    rw [vcoord_coreAct]
    refine hw _ fun f hf => ?_
    by_contra hne
    have h1 : y⁻¹ i ∈ movFin F := mem_movFin.2 ⟨f, hf, hne⟩
    rw [hst y hy] at h1
    obtain ⟨f', hf', hf'i⟩ := mem_movFin.1 h1
    exact hf'i (hi f' hf')
  refine ⟨g, hcomm, fun y hy w hw => ⟨?_, hcomm y hy w hw.2⟩⟩
  refine mem_fixV_map_iff.2 fun f hf i => ?_
  rw [vcoord_coreAct, vcoord_coreAct, vcoord_of_mem_fixV_commV hsame hw.1 hw.2,
    vcoord_of_mem_fixV_commV hsame hw.1 hw.2 (y⁻¹ i)]
  have hiff : y⁻¹ (f i) ∈ movFin F ↔ y⁻¹ i ∈ movFin F := by
    rw [hst y hy, hst y hy]
    refine ⟨fun h => ?_, apply_mem_movFin hf⟩
    have h1 := apply_mem_movFin (F.inv_mem hf) h
    rwa [perm_inv_apply_self] at h1
  rcases em (y⁻¹ i ∈ movFin F) with h | h
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]

end CFSG.CGT.PushingUpLit.BHS
