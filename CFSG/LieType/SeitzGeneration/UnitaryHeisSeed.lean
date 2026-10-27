module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisHom

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_homology_su (h : UnitaryFieldData ℓ f K) {ρ lam n : K} (w : Fin 3 → K)
    (hρ : h.bar ρ * ρ = 1) (hlam : h.bar lam * lam = 1) (hdet : ρ ^ 2 * lam = 1) (hn : n ≠ 0)
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = n) :
    ∃ g : unitarySU ℓ f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = homMat h ρ ((lam - ρ) / n) w := by
  have hbn : h.bar n = n := by
    rw [← hw, map_add, map_add, map_mul, map_mul, map_mul, h.bar_bar, h.bar_bar, h.bar_bar]
    ring
  have hcross : h.bar ρ * ((lam - ρ) / n) + h.bar ((lam - ρ) / n) * ρ +
      h.bar ((lam - ρ) / n) * ((lam - ρ) / n) * n = 0 := by
    rw [map_div₀, hbn, map_sub]
    field_simp
    linear_combination hlam - hρ
  have hU := homMat_unitary h w hρ hcross hw
  have hd : (homMat h ρ ((lam - ρ) / n) w).det = 1 := by
    rw [det_homMat h w hw, div_mul_cancel₀ _ hn]
    linear_combination hdet
  have hinv : homMat h ρ ((lam - ρ) / n) w * ((homMat h ρ ((lam - ρ) / n) w).map h.bar)ᵀ = 1 :=
    mul_eq_one_comm.2 hU
  refine ⟨⟨⟨homMat h ρ ((lam - ρ) / n) w, ((homMat h ρ ((lam - ρ) / n) w).map h.bar)ᵀ, hinv, hU⟩,
    (mem_unitarySU_iff h).2 ⟨hd, hU⟩⟩, rfl⟩

theorem mem_heisClosure_of_comm {ω : K} {M : Matrix (Fin 3) (Fin 3) K} (hM : M ∈ heisLines ω)
    {g : unitarySU ℓ f K 3}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : g ∈ heisClosure ℓ f K ω :=
  Subgroup.subset_closure ⟨M, hM, 1, by rw [one_smul]; exact hg⟩

theorem homMat_unit_comm_hD (h : UnitaryFieldData ℓ f K) (ρ κ ω : K) (i : Fin 3) :
    homMat h ρ κ (Pi.single i 1) * hD ω = hD ω * homMat h ρ κ (Pi.single i 1) := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [homMat_apply, hD, Matrix.mul_apply, Fin.sum_univ_three, Pi.single_apply] <;> ring

theorem homMat_ones_comm_hS (h : UnitaryFieldData ℓ f K) (ρ κ : K) :
    homMat h ρ κ ![1, 1, 1] * hS = hS * homMat h ρ κ ![1, 1, 1] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [homMat_apply, hS, Matrix.mul_apply, Fin.sum_univ_three]

theorem homMat_fourier_comm_hS (h : UnitaryFieldData ℓ f K) {ω : K} (hω3 : ω ^ 3 = 1)
    (hbω : h.bar ω = ω ^ 2) (ρ κ : K) :
    homMat h ρ κ ![1, ω, ω ^ 2] * hS = hS * homMat h ρ κ ![1, ω, ω ^ 2] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [homMat_apply, hS, Matrix.mul_apply, Fin.sum_univ_three, hbω] <;> grind

theorem exists_shift_su (h : UnitaryFieldData ℓ f K) :
    ∃ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS := by
  have hU : ((hS : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * hS = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS, Matrix.mul_apply, Fin.sum_univ_three]
  have hd : (hS : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [hS, Matrix.det_fin_three]
  exact ⟨⟨⟨hS, ((hS : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ, mul_eq_one_comm.2 hU, hU⟩,
    (mem_unitarySU_iff h).2 ⟨hd, hU⟩⟩, rfl⟩

theorem exists_orderOf_eq (h : UnitaryFieldData ℓ f K) : ∃ a : K, orderOf a = ℓ ^ f + 1 := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := CFSG.SectionRank.OddCover.normOne K (ℓ ^ f))
  have hord : orderOf g = ℓ ^ f + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, CFSG.SectionRank.OddCover.card_normOne hK]
  refine ⟨(((g : Kˣ)) : K), ?_⟩
  rw [orderOf_units, Subgroup.orderOf_coe, hord]

theorem exists_norm_one_not_root (h : UnitaryFieldData ℓ f K) (P : Polynomial K) (hP : P ≠ 0)
    (hdeg : P.natDegree < ℓ ^ f + 1) : ∃ b : K, h.bar b * b = 1 ∧ P.eval b ≠ 0 := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  by_contra hcon
  push Not at hcon
  have : Fintype (CFSG.SectionRank.OddCover.normOne K (ℓ ^ f)) := Fintype.ofFinite _
  let Z : Finset K := Finset.univ.image
    (fun u : CFSG.SectionRank.OddCover.normOne K (ℓ ^ f) => (((u : Kˣ)) : K))
  have hinj : Function.Injective
      (fun u : CFSG.SectionRank.OddCover.normOne K (ℓ ^ f) => (((u : Kˣ)) : K)) := by
    intro u v huv
    exact Subtype.ext (Units.ext huv)
  have hZcard : Z.card = ℓ ^ f + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CFSG.SectionRank.OddCover.card_normOne hK]
  have hsub : Z.val ⊆ P.roots := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hz
    rw [Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    apply hcon
    have := CFSG.SectionRank.OddCover.mem_normOne.1 u.2
    rw [bar_mul_self_eq_pow, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  omega

theorem generic_column (h : UnitaryFieldData ℓ f K) {ω b : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hbω : h.bar ω = ω ^ 2) (hb0 : b ≠ 0) (h30 : (3 : K) ≠ 0) :
    homMat h b⁻¹ ((b ^ 2 - b⁻¹) / 3) ![1, 1, 1] *ᵥ
      (homMat h b ((b⁻¹ ^ 2 - b) / 3) ![1, ω, ω ^ 2] *ᵥ ![0, 0, 1]) =
    ![((b⁻¹ ^ 3 - 1) * ω + (b ^ 3 - 1)) / 3, ((b⁻¹ ^ 3 - 1) * ω ^ 2 + (b ^ 3 - 1)) / 3,
      (b ^ 3 + b⁻¹ ^ 3 + 1) / 3] := by
  ext i
  fin_cases i <;>
    simp [homMat_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hbω] <;>
    field_simp <;> grind

theorem generic_column_facts (h : UnitaryFieldData ℓ f K) {ω t : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hbω : h.bar ω = ω ^ 2) (ht : h.bar t * t = 1) (ht3 : t ^ 3 ≠ 1)
    (hq : t ^ 2 + 4 * t + 1 ≠ 0) (h30 : (3 : K) ≠ 0) :
    ((t⁻¹ - 1) * ω + (t - 1)) / 3 ≠ 0 ∧ ((t⁻¹ - 1) * ω ^ 2 + (t - 1)) / 3 ≠ 0 ∧
      (t + t⁻¹ + 1) / 3 ≠ 0 ∧
      h.bar (((t⁻¹ - 1) * ω + (t - 1)) / 3) * (((t⁻¹ - 1) * ω + (t - 1)) / 3) +
        h.bar (((t⁻¹ - 1) * ω ^ 2 + (t - 1)) / 3) * (((t⁻¹ - 1) * ω ^ 2 + (t - 1)) / 3) ≠ 0 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hbt : h.bar t = t⁻¹ := by
    have : h.bar t * t = t⁻¹ * t := by rw [ht, inv_mul_cancel₀ ht0]
    exact mul_right_cancel₀ ht0 this
  have ht1 : t - 1 ≠ 0 := by
    intro h1
    apply ht3
    have : t = 1 := by linear_combination h1
    rw [this]
    norm_num
  have htω : t - ω ≠ 0 := by
    intro h1
    apply ht3
    have : t = ω := by linear_combination h1
    rw [this]
    linear_combination (ω - 1) * hω
  have htω2 : t - ω ^ 2 ≠ 0 := by
    intro h1
    apply ht3
    have : t = ω ^ 2 := by linear_combination h1
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    rw [this, ← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have htt : t ^ 2 + t + 1 ≠ 0 := by
    intro h1
    apply ht3
    linear_combination (t - 1) * h1
  have h90 : (9 : K) ≠ 0 := by
    rw [show (9 : K) = 3 * 3 by norm_num]
    exact mul_ne_zero h30 h30
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ((t⁻¹ - 1) * ω + (t - 1)) / 3 = (t - 1) * (t - ω) / (3 * t) := by
      field_simp
      grind
    rw [this]
    exact div_ne_zero (mul_ne_zero ht1 htω) (mul_ne_zero h30 ht0)
  · have : ((t⁻¹ - 1) * ω ^ 2 + (t - 1)) / 3 = (t - 1) * (t - ω ^ 2) / (3 * t) := by
      field_simp
      grind
    rw [this]
    exact div_ne_zero (mul_ne_zero ht1 htω2) (mul_ne_zero h30 ht0)
  · have : (t + t⁻¹ + 1) / 3 = (t ^ 2 + t + 1) / (3 * t) := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero htt (mul_ne_zero h30 ht0)
  · have : h.bar (((t⁻¹ - 1) * ω + (t - 1)) / 3) * (((t⁻¹ - 1) * ω + (t - 1)) / 3) +
        h.bar (((t⁻¹ - 1) * ω ^ 2 + (t - 1)) / 3) * (((t⁻¹ - 1) * ω ^ 2 + (t - 1)) / 3) =
        -((t - 1) ^ 2 * (t ^ 2 + 4 * t + 1)) / (9 * t ^ 2) := by
      simp only [map_div₀, map_add, map_mul, map_sub, map_one, map_inv₀, map_ofNat, map_pow, hbω,
        hbt, inv_inv]
      field_simp
      linear_combination ((9 * ω ^ 2 - 9 * ω + 9) * t ^ 4 +
        (-9 * ω ^ 4 + 9 * ω ^ 3 - 18 * ω ^ 2) * t ^ 3 +
        (18 * ω ^ 4 - 18 * ω ^ 3 + 9 * ω ^ 2 + 27 * ω - 18) * t ^ 2 +
        (-9 * ω ^ 4 + 9 * ω ^ 3 - 18 * ω) * t + 9) * hω
    rw [this]
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (pow_ne_zero 2 ht1) hq))
      (mul_ne_zero h90 (pow_ne_zero 2 ht0))

theorem val_inv_eq_star (h : UnitaryFieldData ℓ f K) (g : unitarySU ℓ f K 3) :
    (((g⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
  have hU := ((mem_unitarySU_iff h).1 g.2).2
  have h1 : ((g⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) * (g : GL (Fin 3) K) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 : (((g⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, h1, Units.val_one]
  have h3 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 := mul_eq_one_comm.2 hU
  calc (((g⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = (((g⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ) := by
        rw [h3, Matrix.mul_one]
    _ = (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
        rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

open Polynomial in
theorem heisB12_le_heisClosure_of_large (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (h17 : 17 ≤ ℓ ^ f) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    heisB12 ℓ f K ≤ heisClosure ℓ f K ω := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h3f : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    omega
  have h30 : (3 : K) ≠ 0 := by
    intro h0
    have : ℓ ∣ 3 := (CharP.cast_eq_zero_iff K ℓ 3).1 (by exact_mod_cast h0)
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 this)
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have := hω.geom_sum_eq_zero (by norm_num)
    simp [Finset.sum_range_succ] at this
    linear_combination this
  have hbω : h.bar ω = ω ^ 2 := bar_eq_sq_of_cube h hq3 hω3
  obtain ⟨a, ha⟩ := exists_orderOf_eq h
  have hPmonic : (((X : K[X]) ^ 9 - 1) * (X ^ 6 + 4 * X ^ 3 + 1)).Monic := by
    have h1 : ((X : K[X]) ^ 9 - 1).Monic := by
      simpa using monic_X_pow_sub_C (1 : K) (by norm_num : 9 ≠ 0)
    have h2 : ((X : K[X]) ^ 6 + 4 * X ^ 3 + 1).Monic := by monicity!
    exact h1.mul h2
  have hPne : ((X : K[X]) ^ 9 - 1) * (X ^ 6 + 4 * X ^ 3 + 1) ≠ 0 := hPmonic.ne_zero
  have hPdeg : (((X : K[X]) ^ 9 - 1) * (X ^ 6 + 4 * X ^ 3 + 1)).natDegree < ℓ ^ f + 1 := by
    have : (((X : K[X]) ^ 9 - 1) * (X ^ 6 + 4 * X ^ 3 + 1)).natDegree ≤ 15 := by
      compute_degree
    omega
  obtain ⟨b, hbN, hbP⟩ := exists_norm_one_not_root h _ hPne hPdeg
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbN
  have hbP' : (b ^ 9 - 1) * (b ^ 6 + 4 * b ^ 3 + 1) ≠ 0 := by simpa using hbP
  have htN : h.bar (b ^ 3) * b ^ 3 = 1 := by
    rw [map_pow, ← mul_pow, hbN, one_pow]
  have ht3 : (b ^ 3) ^ 3 ≠ 1 := by
    intro h1
    apply hbP'
    have : b ^ 9 = 1 := by rw [← h1]; ring
    rw [this]
    ring
  have hq4 : (b ^ 3) ^ 2 + 4 * b ^ 3 + 1 ≠ 0 := by
    intro h1
    apply hbP'
    have : b ^ 6 + 4 * b ^ 3 + 1 = 0 := by linear_combination h1
    rw [this]
    ring
  obtain ⟨hw0, hw1, hw2, hwnz⟩ := generic_column_facts h hω2 hbω htN ht3 hq4 h30
  have hcol := generic_column h hω2 hbω hb0 h30
  rw [show b⁻¹ ^ 3 = (b ^ 3)⁻¹ from inv_pow b 3] at hcol
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hna : h.bar a * a = 1 := by
    rw [bar_mul_self_eq_pow, ← ha]
    exact pow_orderOf_eq_one a
  have hinvN : ∀ x : K, h.bar x * x = 1 → h.bar x⁻¹ * x⁻¹ = 1 := fun x hx => by
    rw [map_inv₀, ← mul_inv, hx, inv_one]
  have hsqN : ∀ x : K, h.bar x * x = 1 → h.bar (x ^ 2) * x ^ 2 = 1 := fun x hx => by
    rw [map_pow, ← mul_pow, hx, one_pow]
  have hnorm3 : ∀ w : Fin 3 → K, w 0 = 1 → h.bar (w 0) * w 0 + h.bar (w 1) * w 1 +
      h.bar (w 2) * w 2 = 1 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 := fun w hw => by
    rw [hw]
    simp
  obtain ⟨g0, hg0⟩ := exists_homology_su h (ρ := b⁻¹) (lam := b ^ 2) (n := 3) ![1, 1, 1]
    (hinvN b hbN) (hsqN b hbN) (by field_simp) h30 (by simp; norm_num)
  obtain ⟨g1, hg1⟩ := exists_homology_su h (ρ := b) (lam := b⁻¹ ^ 2) (n := 3) ![1, ω, ω ^ 2]
    hbN (hsqN _ (hinvN b hbN)) (by field_simp) h30 (by
      simp [hbω]
      linear_combination (ω ^ 3 + 2) * hω3)
  obtain ⟨ge1, hge1⟩ := exists_homology_su h (ρ := a) (lam := a⁻¹ ^ 2) (n := 1) ![1, 0, 0]
    hna (hsqN _ (hinvN a hna)) (by field_simp) one_ne_zero (by simp)
  obtain ⟨ge3, hge3⟩ := exists_homology_su h (ρ := a) (lam := a⁻¹ ^ 2) (n := 1) ![0, 0, 1]
    hna (hsqN _ (hinvN a hna)) (by field_simp) one_ne_zero (by simp)
  have hSm : hS ∈ heisLines ω := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hDm : hD ω ∈ heisLines ω := Set.mem_insert _ _
  have hg0c : g0 ∈ heisClosure ℓ f K ω :=
    mem_heisClosure_of_comm hSm (by rw [hg0]; exact homMat_ones_comm_hS h _ _)
  have hg1c : g1 ∈ heisClosure ℓ f K ω :=
    mem_heisClosure_of_comm hSm (by rw [hg1]; exact homMat_fourier_comm_hS h hω3 hbω _ _)
  have he1 : (![1, 0, 0] : Fin 3 → K) = Pi.single 0 1 := by
    ext j
    fin_cases j <;> simp
  have he3 : (![0, 0, 1] : Fin 3 → K) = Pi.single 2 1 := by
    ext j
    fin_cases j <;> simp
  have hge1c : ge1 ∈ heisClosure ℓ f K ω :=
    mem_heisClosure_of_comm hDm (by rw [hge1, he1]; exact homMat_unit_comm_hD h _ _ ω 0)
  have hge3c : ge3 ∈ heisClosure ℓ f K ω :=
    mem_heisClosure_of_comm hDm (by rw [hge3, he3]; exact homMat_unit_comm_hD h _ _ ω 2)
  set y : unitarySU ℓ f K 3 := g0 * g1 with hy
  have hyc : y ∈ heisClosure ℓ f K ω := Subgroup.mul_mem _ hg0c hg1c
  have hymat : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g0 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl
  have hyU := ((mem_unitarySU_iff h).1 y.2).2
  have hyP : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 := mul_eq_one_comm.2 hyU
  have hwcol : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
      ![(((b ^ 3)⁻¹ - 1) * ω + (b ^ 3 - 1)) / 3, (((b ^ 3)⁻¹ - 1) * ω ^ 2 + (b ^ 3 - 1)) / 3,
        (b ^ 3 + (b ^ 3)⁻¹ + 1) / 3] := by
    rw [hymat, ← Matrix.mulVec_mulVec, hg0, hg1]
    exact hcol
  have hwN : h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 +
      h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 +
      h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 = 1 := by
    have := congrFun (congrFun hyU 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] using this
  have hzc : y * ge3 * y⁻¹ ∈ heisClosure ℓ f K ω :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyc hge3c) (Subgroup.inv_mem _ hyc)
  have hzm : (((y * ge3 * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a)
        (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) := by
    have e : (((y * ge3 * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((ge3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
      rw [← val_inv_eq_star h y]
      rfl
    rw [e, hge3, div_one, conj_homMat h _ hyP]
  have hApp := su2_block_mem_of_generic h hℓ3 h17 hq3 ha
    ((heisClosure ℓ f K ω).map (unitarySU ℓ f K 3).subtype)
    ⟨(ge1 : GL (Fin 3) K), ⟨ge1, hge1c, rfl⟩, by rw [hge1, div_one]⟩
    ⟨(ge3 : GL (Fin 3) K), ⟨ge3, hge3c, rfl⟩, by rw [hge3, div_one]⟩
    (w := ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) hwN
    (by rw [hwcol]; exact hw0) (by rw [hwcol]; exact hw1) (by rw [hwcol]; exact hw2)
    (by rw [hwcol]; exact hwnz)
    ⟨((y * ge3 * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K), ⟨_, hzc, rfl⟩, hzm⟩
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨x, hx, hxA⟩ := hApp A hA
  have : x = g := Subtype.ext (hxA.trans (Units.ext hgA).symm)
  rw [← this]
  exact hx

end CFSG.LieType.SeitzGeneration
