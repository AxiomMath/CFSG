module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldInv
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open CFSG.Glauberman.Dickson (h826_pglMap h826_pglMap_mk h826_pglMap_injective)

variable {F : Type} [Field F] [Finite F]

section Sub

variable (K₀ : Subfield F)

@[expose] def psl2Sub : PSL2 K₀ →* PSL2 F :=
  QuotientGroup.map _ _ (Matrix.SpecialLinearGroup.map K₀.subtype) (by
    intro A hA
    rw [Subgroup.mem_comap]
    obtain ⟨ω, hω, hωA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨K₀.subtype ω, by
      rw [← map_pow, hω, map_one], ?_⟩
    rw [Matrix.SpecialLinearGroup.map_apply_coe, ← hωA]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp)

omit [Finite F] in
theorem toPGL_psl2Sub (x : PSL2 K₀) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2Sub K₀ x) =
      h826_pglMap K₀.subtype (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
    (QuotientGroup.mk (Matrix.SpecialLinearGroup.map K₀.subtype A)) = _
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
    h826_pglMap_mk]
  congr 1
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

omit [Finite F] in
theorem psl2Sub_injective : Function.Injective (psl2Sub K₀) := by
  intro x y h
  have := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  rw [toPGL_psl2Sub, toPGL_psl2Sub] at this
  exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (h826_pglMap_injective _ K₀.subtype_injective this)

end Sub

abbrev fieldCent (σ : F ≃+* F) : Subgroup (PSL2 F) :=
  MonoidHom.eqLocus (psl2FieldAut F σ).toMonoidHom (MonoidHom.id _)

section Field

variable {σ : F ≃+* F} {K₀ : Subfield F}

omit [Finite F] in
theorem psl2Sub_mem_fieldCent (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (x : PSL2 K₀) :
    psl2Sub K₀ x ∈ fieldCent σ := by
  show psl2FieldAut F σ (psl2Sub K₀ x) = psl2Sub K₀ x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [psl2FieldAut_toPGL, toPGL_psl2Sub]
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL x)
  rw [← hA, h826_pglMap_mk, pgl2FieldAut_mk]
  congr 1
  ext i j
  simp only [Matrix.GeneralLinearGroup.map, RingEquiv.toRingHom_eq_coe, Units.coe_map]
  exact (hK₀ _).mp (Subtype.mem _)

omit [Finite F] in
theorem mem_range_of_pgl2FieldAut_fixed (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c) (hσσ : ∀ x, σ (σ x) = x)
    {g : PGL2 F} (hg : pgl2FieldAut F σ g = g) : g ∈ (h826_pglMap K₀.subtype).range := by
  obtain ⟨G, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [pgl2FieldAut_mk] at hg
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hg
  have hent : ∀ i j, σ ((G : Matrix (Fin 2) (Fin 2) F) i j) * (c : F) =
      (G : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F) i j) hc
    simpa [Matrix.GeneralLinearGroup.map, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.mul_apply, Fin.sum_univ_two] using this
  have hcc : (c : F) * σ c = 1 := by
    have hG0 : ∃ i j, (G : Matrix (Fin 2) (Fin 2) F) i j ≠ 0 := by
      by_contra h
      push Not at h
      apply G.det_ne_zero
      simp [Matrix.det_fin_two, h]
    obtain ⟨i, j, hij⟩ := hG0
    have h1 := hent i j
    have h2 : (G : Matrix (Fin 2) (Fin 2) F) i j * σ (c : F) =
        σ ((G : Matrix (Fin 2) (Fin 2) F) i j) := by
      have := congrArg σ h1
      rwa [map_mul, hσσ] at this
    have h3 : (c : F) * σ c * (G : Matrix (Fin 2) (Fin 2) F) i j =
        (G : Matrix (Fin 2) (Fin 2) F) i j := by
      calc (c : F) * σ c * (G : Matrix (Fin 2) (Fin 2) F) i j =
          (G : Matrix (Fin 2) (Fin 2) F) i j * σ (c : F) * c := by ring
        _ = (G : Matrix (Fin 2) (Fin 2) F) i j := by rw [h2, h1]
    exact mul_right_cancel₀ hij (h3.trans (one_mul _).symm)
  obtain ⟨y, hy⟩ := h90 _ hcc
  have hσy : σ (y : F) ≠ 0 := by rw [map_ne_zero]; exact y.ne_zero
  set H : Matrix (Fin 2) (Fin 2) F := σ (y : F) • (G : Matrix (Fin 2) (Fin 2) F)
  have hfix : ∀ i j, σ (H i j) = H i j := by
    intro i j
    simp only [H, Matrix.smul_apply, smul_eq_mul, map_mul, hσσ]
    have h1 := hent i j
    rw [← hy] at h1
    field_simp at h1
    linear_combination h1
  have hHdet : H.det ≠ 0 := by
    simp only [H, Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ hσy) G.det_ne_zero
  let H₀ : Matrix (Fin 2) (Fin 2) K₀ := fun i j => ⟨H i j, (hK₀ _).mpr (hfix i j)⟩
  have hH₀ : (K₀.subtype).mapMatrix H₀ = H := by
    ext i j
    rfl
  have hH₀det : H₀.det ≠ 0 := by
    intro h
    apply hHdet
    rw [← hH₀, ← RingHom.map_det, h, map_zero]
  refine ⟨Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero H₀ hH₀det), ?_⟩
  rw [h826_pglMap_mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨(Units.mk0 _ hσy)⁻¹, ?_⟩
  ext i j
  have e1 : ((Matrix.GeneralLinearGroup.map K₀.subtype
      (Matrix.GeneralLinearGroup.mkOfDetNeZero H₀ hH₀det) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = H := hH₀
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar, e1]
  simp only [H, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  field_simp

omit [Finite F] in
theorem card_fieldCent_le [Finite F] (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c) (hσσ : ∀ x, σ (σ x) = x) :
    Nat.card (fieldCent σ) ≤ Nat.card (PGL2 K₀) := by
  have hle : (fieldCent σ).map Matrix.ProjectiveSpecialLinearGroup.toPGL ≤
      (h826_pglMap K₀.subtype).range := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_range_of_pgl2FieldAut_fixed hK₀ h90 hσσ
    have hx' : psl2FieldAut F σ x = x := hx
    rw [← psl2FieldAut_toPGL, hx']
  calc Nat.card (fieldCent σ) =
      Nat.card ((fieldCent σ).map Matrix.ProjectiveSpecialLinearGroup.toPGL) :=
        (Subgroup.card_map_of_injective
          Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm
    _ ≤ Nat.card (h826_pglMap K₀.subtype).range := Subgroup.card_le_of_le hle
    _ = Nat.card (PGL2 K₀) := (Nat.card_congr (MonoidHom.ofInjective
        (h826_pglMap_injective _ K₀.subtype_injective)).toEquiv).symm

theorem isOddPrimePower_of_odd_card (K : Type) [Field K] [Finite K] (h : Odd (Nat.card K)) :
    IsOddPrimePower (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  refine ⟨ringChar K, n, hp, ?_, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  rcases hp.eq_two_or_odd' with h2 | h2
  · exfalso
    rw [Nat.card_eq_fintype_card, hn, h2] at h
    have : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.ne_zero).mpr even_two
    exact Nat.not_even_iff_odd.mpr h this
  · exact h2

theorem even_psl2_card {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    Even (Nat.card (PSL2 K)) := by
  rw [psl2_card_formula K hK]
  obtain ⟨p, n, -, hpodd, -, hc⟩ := hK
  obtain ⟨k, hk⟩ := (hpodd.pow : Odd (p ^ n))
  rw [hc, hk]
  have e : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) = 2 * (2 * ((2 * k + 1) * (k * k + k))) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
    ring
  rw [e, Nat.mul_div_cancel_left _ two_pos]
  exact even_two_mul _

theorem pgl2_card_eq_two_mul {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    Nat.card (PGL2 K) = 2 * Nat.card (PSL2 K) := by
  rw [pgl2_card_formula, psl2_card_formula K hK]
  obtain ⟨p, n, -, hpodd, -, hc⟩ := hK
  obtain ⟨k, hk⟩ := (hpodd.pow : Odd (p ^ n))
  rw [hc, hk]
  have e : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) = 2 * (2 * ((2 * k + 1) * (k * k + k))) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
    ring
  rw [e, Nat.mul_div_cancel_left _ two_pos]

theorem eq_bot_of_odd_normal_fieldCent (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c) (hσσ : ∀ x, σ (σ x) = x)
    (hcard : Nat.card F = Nat.card K₀ ^ 2) (hodd : IsOddPrimePower (Nat.card F))
    {N : Subgroup (PSL2 F)} (hNC : N ≤ fieldCent σ)
    (hNn : ∀ c ∈ fieldCent σ, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := by
    apply isOddPrimePower_of_odd_card
    have hFodd : Odd (Nat.card F) := by
      obtain ⟨p, n, -, hpodd, -, hc⟩ := hodd
      rw [hc]
      exact hpodd.pow
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  have hMC : ∀ x : PSL2 K₀, psl2Sub K₀ x ∈ fieldCent σ := psl2Sub_mem_fieldCent hK₀
  have hNM : ∀ x : PSL2 K₀, psl2Sub K₀ x ∈ N → x = 1 := by
    let P : Subgroup (PSL2 K₀) := N.comap (psl2Sub K₀)
    have hPn : P.Normal := ⟨fun n hn g => by
      show psl2Sub K₀ (g * n * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNn _ (hMC g) _ hn⟩
    have hPdvd : Nat.card P ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective (psl2Sub_injective K₀)]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    have hPodd : Odd (Nat.card P) := Odd.of_dvd_nat hNodd hPdvd
    have hPbot : P = ⊥ := by
      by_cases h3 : Nat.card K₀ = 3
      · have h12 : Nat.card (PSL2 K₀) = 12 := by
          rw [psl2_card_formula _ hK₀odd, h3]
          norm_num
        have hd : Nat.card P ∣ 3 * 4 := by
          have := Subgroup.card_subgroup_dvd_card P
          rwa [h12] at this
        have hcop : Nat.Coprime (Nat.card P) 4 :=
          (Nat.coprime_two_right.mpr hPodd).pow_right 2
        have hd3 : Nat.card P ∣ 3 := hcop.dvd_of_dvd_mul_right hd
        have hP13 : Nat.card P = 3 ^ 0 ∨ Nat.card P = 3 ^ 1 := by
          rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
          · exact Or.inl (by rw [h, pow_zero])
          · exact Or.inr (by rw [h, pow_one])
        have hP3 : IsPGroup 3 P := by
          rcases hP13 with h | h
          · exact IsPGroup.of_card h
          · exact IsPGroup.of_card h
        exact normal_pSubgroup_eq_bot_of_psl2_odd K₀ hK₀odd 3 Nat.prime_three ⟨1, rfl⟩ P hPn hP3
      · have h4 : 4 ≤ Nat.card K₀ := by
          obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hK₀odd
          have hp3 : 3 ≤ p := by
            have := hp.two_le
            rcases hpodd with ⟨m, hm⟩
            omega
          have : 3 ≤ Nat.card K₀ := by
            rw [hc]
            calc 3 ≤ p := hp3
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
          have hne : Nat.card K₀ ≠ 4 := by
            intro h4
            rw [h4] at hc
            have : 2 ∣ p ^ n := ⟨2, by omega⟩
            have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this)
            rcases hpodd with ⟨m, hm⟩
            omega
          omega
        have hsimple : IsSimpleGroup (PSL2 K₀) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
        have := hPn
        rcases hsimple.eq_bot_or_eq_top_of_normal P with h | h
        · exact h
        · exfalso
          rw [h, Subgroup.card_top] at hPodd
          exact Nat.not_even_iff_odd.mpr hPodd (even_psl2_card hK₀odd)
    intro x hx
    have : x ∈ P := hx
    rw [hPbot, mem_bot] at this
    exact this
  let φ : N × PSL2 K₀ → fieldCent σ := fun nx =>
    ⟨nx.1 * psl2Sub K₀ nx.2, mul_mem (hNC nx.1.2) (hMC nx.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨n, x⟩ ⟨n', x'⟩ h
    have h0 : (n : PSL2 F) * psl2Sub K₀ x = n' * psl2Sub K₀ x' := congrArg Subtype.val h
    have h1 : psl2Sub K₀ (x * x'⁻¹) ∈ N := by
      have : psl2Sub K₀ (x * x'⁻¹) = (n : PSL2 F)⁻¹ * n' := by
        rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, h0, mul_inv_cancel_right]
      rw [this]
      exact mul_mem (inv_mem n.2) n'.2
    have hx : x = x' := mul_inv_eq_one.mp (hNM _ h1)
    subst hx
    have hn : (n : PSL2 F) = n' := mul_right_cancel h0
    exact Prod.ext (Subtype.ext hn) rfl
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod] at hle
  have hC := card_fieldCent_le hK₀ h90 hσσ
  rw [pgl2_card_eq_two_mul hK₀odd] at hC
  have hpos : 0 < Nat.card (PSL2 K₀) := Nat.card_pos
  have hN2 : Nat.card N ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 * Nat.card (PSL2 K₀) ≤ Nat.card N * Nat.card (PSL2 K₀) :=
      Nat.mul_le_mul_right _ h
    omega
  have hN1 : Nat.card N = 1 := by
    obtain ⟨k, hk⟩ := hNodd
    omega
  exact Subgroup.eq_bot_of_card_eq N hN1

theorem not_isSolvable_fieldCent (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (hK₀odd : IsOddPrimePower (Nat.card K₀)) (h3 : 3 < Nat.card K₀) :
    ¬ Group.IsSolvable (fieldCent σ) := by
  intro hsolv
  let φ : PSL2 K₀ →* fieldCent σ :=
    (psl2Sub K₀).codRestrict _ (psl2Sub_mem_fieldCent hK₀)
  have hφ : Function.Injective φ := fun x y h =>
    psl2Sub_injective K₀ (congrArg Subtype.val h)
  have := Group.isSolvable_of_isSolvable_injective hφ
  have := psl2_isPerfect_of_card_gt_three K₀ h3
  have : Nontrivial (PSL2 K₀) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [psl2_card_formula K₀ hK₀odd]
    set r := Nat.card K₀
    have h16 : 16 ≤ r ^ 2 := by nlinarith
    have h1 : 15 ≤ r ^ 2 - 1 := by omega
    have h2 : 60 ≤ r * (r ^ 2 - 1) := by nlinarith
    omega
  exact Group.IsPerfect.not_isSolvable _ ‹_›

end Field

end CFSG.ComponentClassification.AutL2Facts
