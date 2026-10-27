module


public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallU3Psu
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallU3Mat
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Psu

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (coe_glAut)
open Matrix
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs

variable {K : Type} [Field K]

theorem fixed_entries (h : UnitaryFieldData 3 3 K) (h3 : (3 : K) = 0) (σ : K ≃+* K)
    (g : unitarySU 3 3 K 3)
    (hg : psuField h σ (QuotientGroup.mk g : unitaryPSU h 3) = QuotientGroup.mk g) (i j : Fin 3) :
    σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j := by
  rw [psuField_mk] at hg
  have h1 : (suField h σ g)⁻¹ * g = 1 := eq_one_of_mem_unitaryScalars h h3 (QuotientGroup.eq.1 hg)
  have h2 : suField h σ g = g := inv_mul_eq_one.1 h1
  have h4 := congrArg (fun x : unitarySU 3 3 K 3 => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) h2
  simpa [coe_suField, coe_glAut, Matrix.map_apply] using h4

theorem card_fixed (h : UnitaryFieldData 3 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) = 9 := by
  have hK : Nat.card K = 3 ^ 6 := by norm_num [h.card]
  obtain ⟨-, hc⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield (ℓ := 3) (f := 6) (p := 3)
    Nat.prime_three (by norm_num) hK hσ
  rw [hc]
  norm_num

theorem exists_bar_ne_fixed (h : UnitaryFieldData 3 3 K) (F₀ : Subfield K) (hF₀ : Nat.card F₀ = 9) :
    ∃ c ∈ F₀, h.bar c ≠ c := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Finite F₀ := Nat.finite_of_card_ne_zero (by rw [hF₀]; norm_num)
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  have hroot : ∀ c : F₀, (c : K) ^ 3 = (c : K) := by
    intro c
    have h9 : c ^ 9 = c := by
      have := FiniteField.pow_card c
      rwa [Fintype.card_eq_nat_card, hF₀] at this
    have h9K : (c : K) ^ 9 = (c : K) := by
      have := congrArg Subtype.val h9
      simpa using this
    have hb := hcon (c : K) c.2
    rw [h.bar_apply] at hb
    have e1 : (c : K) ^ 27 = (c : K) ^ 3 := by
      rw [show (27 : ℕ) = 9 * 3 from rfl, pow_mul, h9K]
    norm_num at hb
    rw [← e1]
    exact hb
  set p : Polynomial K := Polynomial.X ^ 3 - Polynomial.X with hp
  have hp0 : p ≠ 0 := by
    intro h0
    have hc : p.coeff 3 = 1 := by
      rw [hp, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
      norm_num
    rw [h0, Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  have hnat : p.natDegree ≤ 3 := by
    rw [hp]
    compute_degree
  let Z : Finset K := Finset.univ.image (fun c : F₀ => (c : K))
  have hZcard : Z.card = 9 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      Fintype.card_eq_nat_card, hF₀]
  have hsub : Z.val ⊆ p.roots := by
    intro x hx
    have hx' : x ∈ Z := hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx'
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hp, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    exact hroot c
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hZcard] at hle
  omega

theorem f2_psu (h : UnitaryFieldData 3 3 K) (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0)
    (E : Subgroup (MulAut (unitaryPSU h 3))) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3)
    (hnot : ¬ E ≤ inner (unitaryPSU h 3))
    (hE0 : Nat.card ↥(E ⊓ inner (unitaryPSU h 3)) = 3 ^ 2) :
    SmallF2 (unitaryPSU h 3) E := by
  classical
  haveI : Finite (unitaryPSU h 3) := by
    haveI := h.finite
    infer_instance
  haveI : Finite (MulAut (unitaryPSU h 3)) := MulEquiv.finite_left
  intro W hW hWI hWC
  by_contra hW0
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨b, hbE, hbI⟩ : ∃ b ∈ E, b ∉ inner (unitaryPSU h 3) := by
    obtain ⟨b, hb, hbn⟩ := SetLike.not_le_iff_exists.1 hnot
    exact ⟨b, hb, hbn⟩
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  have hbD : b ∉ (psuConj h).range := fun hm => hbI (range_psuConj_le_inner h hm)
  obtain ⟨σ, hσ3, H, hbH⟩ := unitary_order_three_field_descent (h := h) (by norm_num) b hb3 hbD
  have hF₀ : Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) = 9 :=
    card_fixed h hσ3
  have hbarF := exists_bar_ne_fixed h _ hF₀
  have hW2 : 2 ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := hW.exists_card_eq
    have hne : Nat.card W ≠ 1 := fun h1 => hW0 (Subgroup.eq_bot_of_card_eq W h1)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by rw [hn]; norm_num)
    rw [hn]
    exact dvd_pow_self 2 hn0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 hW2
  have ht2 : (t : MulAut (unitaryPSU h 3)) ^ 2 = 1 := by
    have h' := congrArg (fun x : ↥W => (x : MulAut (unitaryPSU h 3)))
      (show t ^ 2 = 1 by rw [← ht]; exact pow_orderOf_eq_one t)
    simpa using h'
  have ht1 : (t : MulAut (unitaryPSU h 3)) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    norm_num at ht
  have htW : (t : MulAut (unitaryPSU h 3)) ∈ W := t.2
  have htI : (t : MulAut (unitaryPSU h 3)) ∈ inner (unitaryPSU h 3) := hWI htW
  set t₀ : MulAut (unitaryPSU h 3) := (t : MulAut (unitaryPSU h 3)) with ht₀
  set c := psuConj h H with hc_def
  set f := psuField h σ with hf_def
  set V : Subgroup (MulAut (unitaryPSU h 3)) := E ⊓ inner (unitaryPSU h 3) with hVdef
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hE0]; norm_num)
  haveI : Fintype V := Fintype.ofFinite V
  choose L hL using exists_lift h
  let uv : V → MulAut (unitaryPSU h 3) := fun v => c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c
  have hvV : ∀ v : V, (v : MulAut (unitaryPSU h 3)) ∈ E ∧
      (v : MulAut (unitaryPSU h 3)) ∈ inner (unitaryPSU h 3) := fun v => Subgroup.mem_inf.1 v.2
  have huv_in : ∀ v : V, uv v ∈ inner (unitaryPSU h 3) := fun v =>
    conj_mem_inner c (hvV v).2
  have hL' : ∀ v : V, MulAut.conj (QuotientGroup.mk (L (uv v)) : unitaryPSU h 3) = uv v :=
    fun v => hL _ (huv_in v)
  let M : V → Matrix (Fin 3) (Fin 3) K := fun v => ((L (uv v) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hMinj : Function.Injective M := by
    intro v w hvw
    have hLvw : L (uv v) = L (uv w) := subtype_eq_of_mat_eq hvw
    have huv : uv v = uv w := by rw [← hL' v, ← hL' w, hLvw]
    apply Subtype.ext
    have h' : c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c = c⁻¹ * (w : MulAut (unitaryPSU h 3)) * c := huv
    exact mul_left_cancel (mul_right_cancel h')
  set P : Finset (Matrix (Fin 3) (Fin 3) K) := Finset.univ.image M with hPdef
  have hPcard : P.card = 9 := by
    rw [hPdef, Finset.card_image_of_injective _ hMinj, Finset.card_univ,
      Fintype.card_eq_nat_card, hE0]
    norm_num
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
    have hvw : (v : MulAut (unitaryPSU h 3)) * (w : MulAut (unitaryPSU h 3)) =
        (w : MulAut (unitaryPSU h 3)) * (v : MulAut (unitaryPSU h 3)) :=
      isElemAbelian_commute hE (hvV v).1 (hvV w).1
    have hcomm : uv v * uv w = uv w * uv v := by
      show c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c * (c⁻¹ * (w : MulAut (unitaryPSU h 3)) * c) =
        c⁻¹ * (w : MulAut (unitaryPSU h 3)) * c * (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c)
      calc c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c * (c⁻¹ * (w : MulAut (unitaryPSU h 3)) * c)
          = c⁻¹ * ((v : MulAut (unitaryPSU h 3)) * (w : MulAut (unitaryPSU h 3))) * c := by group
        _ = c⁻¹ * ((w : MulAut (unitaryPSU h 3)) * (v : MulAut (unitaryPSU h 3))) * c := by rw [hvw]
        _ = c⁻¹ * (w : MulAut (unitaryPSU h 3)) * c * (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c) := by
          group
    have hc := comm_of_conj_comm h h3 (center_trivial h) (L (uv v)) (L (uv w))
      (by rw [hL' v, hL' w]; exact hcomm)
    exact mat_mul_comm hc
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    have hv3 : (uv v) ^ 3 = 1 := by
      show (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c) ^ 3 = 1
      rw [conj_pow', hE.2 _ (hvV v).1, mul_one, inv_mul_cancel]
    have hL3 : L (uv v) ^ 3 = 1 :=
      pow_eq_one_of_conj_pow h h3 _ 3 (by rw [hL' v]; exact hv3)
    exact mat_pow_eq_one hL3
  have hfu : ∀ v : V, f * uv v = uv v * f := by
    intro v
    have hcomm := isElemAbelian_commute hE hbE (hvV v).1
    rw [hbH] at hcomm
    show f * (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c) = c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c * f
    calc f * (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c)
        = c⁻¹ * (c * f * c⁻¹ * (v : MulAut (unitaryPSU h 3))) * c := by group
      _ = c⁻¹ * ((v : MulAut (unitaryPSU h 3)) * (c * f * c⁻¹)) * c := by rw [hcomm]
      _ = c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c * f := by group
  have hPF : ∀ x ∈ P, ∀ i j, x i j ∈ CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ := by
    intro x hx i j
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    have hfix : psuField h σ (QuotientGroup.mk (L (uv v)) : unitaryPSU h 3) =
        QuotientGroup.mk (L (uv v)) := by
      have e1 : MulAut.conj (f (QuotientGroup.mk (L (uv v)) : unitaryPSU h 3)) =
          MulAut.conj (QuotientGroup.mk (L (uv v)) : unitaryPSU h 3) := by
        rw [← mul_conj_mul_inv' f, hL' v, hfu v, mul_inv_cancel_right]
      exact conj_injective_of_center (center_trivial h) e1
    have hent := fixed_entries h h3 σ (L (uv v)) hfix i j
    exact RingHom.mem_eqLocusField.2 (by simpa using hent)
  have hPU : ∀ x ∈ P, (x.map h.bar)ᵀ * x = 1 := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    exact ((mem_unitarySU_iff h).1 (L (uv v)).2).2
  set t₁ : MulAut (unitaryPSU h 3) := c⁻¹ * t₀ * c with ht₁
  have ht₁I : t₁ ∈ inner (unitaryPSU h 3) := conj_mem_inner c htI
  have ht₁2 : t₁ ^ 2 = 1 := by
    rw [ht₁, conj_pow', ht₀, ht2, mul_one, inv_mul_cancel]
  have ht₁1 : t₁ ≠ 1 := by
    intro e
    apply ht1
    have : t₀ = c * t₁ * c⁻¹ := by rw [ht₁]; group
    rw [this, e]
    group
  set B := L t₁ with hBdef
  have hBconj : MulAut.conj (QuotientGroup.mk B : unitaryPSU h 3) = t₁ := hL _ ht₁I
  have hB2 : B ^ 2 = 1 := pow_eq_one_of_conj_pow h h3 B 2 (by rw [hBconj]; exact ht₁2)
  have hB1 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro e
    apply ht₁1
    have hBeq : B = 1 := subtype_eq_of_mat_eq (by rw [e]; rfl)
    rw [← hBconj, hBeq, QuotientGroup.mk_one, map_one]
  have hBm : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ -1 := by
    intro e
    have hd := ((mem_unitarySU_iff h).1 B.2).1
    rw [e, Matrix.det_neg, Matrix.det_one] at hd
    have : (2 : K) = 0 := by
      norm_num at hd
      linear_combination -hd
    exact h2 this
  have hBP : ∀ x ∈ P, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x =
      x * ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    have ht0v : t₀ * (v : MulAut (unitaryPSU h 3)) = (v : MulAut (unitaryPSU h 3)) * t₀ :=
      Subgroup.mem_centralizer_iff.1 (hWC v.2) t₀ htW
    have hcomm : t₁ * uv v = uv v * t₁ := by
      show c⁻¹ * t₀ * c * (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c) =
        c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c * (c⁻¹ * t₀ * c)
      calc c⁻¹ * t₀ * c * (c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c)
          = c⁻¹ * (t₀ * (v : MulAut (unitaryPSU h 3))) * c := by group
        _ = c⁻¹ * ((v : MulAut (unitaryPSU h 3)) * t₀) * c := by rw [ht0v]
        _ = c⁻¹ * (v : MulAut (unitaryPSU h 3)) * c * (c⁻¹ * t₀ * c) := by group
    have hc := comm_of_conj_comm h h3 (center_trivial h) B (L (uv v))
      (by rw [hBconj, hL' v]; exact hcomm)
    exact mat_mul_comm hc
  exact KDRank3SmallU3Mat.no_involution_of_F9 hK h3 h.bar _ hF₀ hbarF P hPcard hPc hP3 hPF hPU
    (mat_sq_eq_one hB2) hB1 hBm hBP

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Psu

end
