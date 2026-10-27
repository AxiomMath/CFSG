module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PT
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZ
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLe

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 DiagL CSL

section Std

variable {F : Type} [Field F] [Fintype F]

theorem exists_det_comm_kG (hq : Odd (Fintype.card F)) (c : Fˣ) :
    ∃ D : GL (Fin 4) F, GeneralLinearGroup.det D = c ∧
      D * kG (neg_one_ne_zero' (F := F)) = kG neg_one_ne_zero' * D := by
  obtain ⟨a, b, hab⟩ : ∃ a b : F, a ^ 2 + b ^ 2 = c := by
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
      (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C (c : F))
      (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) _)
      (Nat.odd_iff.mp hq)
    refine ⟨a, b, ?_⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_C] at hab
    linear_combination hab
  set M : Matrix (Fin 4) (Fin 4) F := !![a, -b, 0, 0; b, a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
    with hM
  have hdet : M.det = c := by
    rw [hM, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
    linear_combination hab
  have hM0 : M.det ≠ 0 := by rw [hdet]; exact Units.ne_zero c
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM0, Units.ext ?_, Units.ext ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_mkOfDetNeZero, hdet]
  · rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.val_mkOfDetNeZero, coe_kG]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, kZero, Matrix.mul_apply, Fin.sum_univ_four]

theorem exists_conj_kSL_of_conjAut (hq : Odd (Fintype.card F)) (P : GL (Fin 4) F) :
    ∃ g : projectiveSL 4 F, conjAut 4 F (P * kG neg_one_ne_zero' * P⁻¹) =
      MulAut.conj (g * proj 4 F kSL * g⁻¹) := by
  obtain ⟨D, hD, hDk⟩ := exists_det_comm_kG hq (GeneralLinearGroup.det P)⁻¹
  have hdet : GeneralLinearGroup.det (P * D) = 1 := by rw [map_mul, hD, mul_inv_cancel]
  set g₀ : SpecialLinearGroup (Fin 4) F := ⟨((P * D : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
    by
      have := congrArg Units.val hdet
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this⟩ with hg₀
  have hg : SpecialLinearGroup.toGL g₀ = P * D := Units.ext rfl
  refine ⟨proj 4 F g₀, ?_⟩
  have e1 : P * kG neg_one_ne_zero' * P⁻¹ =
      (P * D) * kG (neg_one_ne_zero' (F := F)) * (P * D)⁻¹ := by
    calc P * kG neg_one_ne_zero' * P⁻¹ =
        P * (D * kG (neg_one_ne_zero' (F := F)) * D⁻¹) * P⁻¹ := by
          rw [hDk, mul_inv_cancel_right]
      _ = (P * D) * kG (neg_one_ne_zero' (F := F)) * (P * D)⁻¹ := by group
  rw [e1, ← hg, map_mul, map_mul, map_inv, conjAut_toGL, conjAut_kG_eq, map_mul, map_mul,
    map_inv]

end Std

section Transport

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
  {F : Type} [Field F] [Fintype F]

theorem conj_kSL_of_component (hC : centralizer (N : Set H) = ⊥) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hFq : Fintype.card F = p ^ f) (e : ↥N ≃* projectiveSL 4 F)
    {ι : H} (hιN : ι ∈ N) (hι : orderOf ι = 2) {J₁ : Subgroup H}
    (hJC : J₁ ≤ centralizer ({ι} : Set H)) (hJp : ⁅J₁, J₁⁆ = J₁)
    (hJt : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) :
    J₁ ≤ N ∧ ¬ IsSquare (-1 : F) ∧
      ∃ g : projectiveSL 4 F, e ⟨ι, hιN⟩ = g * proj 4 F kSL * g⁻¹ := by
  classical
  have hq : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
  have hJN : J₁ ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv e (fun J hJ => DiagL.le_range_conj_of_perfect hJ)) hJp
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJt
  have := Fact.mk hs
  obtain ⟨⟨y, hyJ⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := ↥J₁) s
    (hsJ.trans (Subgroup.card_quotient_dvd_card _))
  rw [Subgroup.orderOf_mk] at hys
  have hyN := hJN hyJ
  obtain ⟨Yα, hYα⟩ := proj_surjective 4 F (e ⟨ι, hιN⟩)
  set A := SpecialLinearGroup.toGL Yα with hA
  have hαA : actP e ι = conjAut 4 F A := by rw [actP_eq_conj e hιN, ← hYα, hA, conjAut_toGL]
  have hαα : ι * ι = 1 := by rw [← sq, ← hι, pow_orderOf_eq_one]
  have hα1 : ι ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hι
    norm_num at hι
  have hA1 : conjAut 4 F A ≠ 1 := fun h => hα1 (eq_one_of_actP_eq_one hC e (hαA ▸ h))
  have hA2 : conjAut 4 F A ^ 2 = 1 := by rw [← hαA, ← map_pow, sq, hαα, map_one]
  have hyα : y * ι = ι * y := mem_centralizer_singleton_iff.mp (hJC hyJ)
  have hAy : conjAut 4 F A (e ⟨y, hyN⟩) = e ⟨y, hyN⟩ := by
    rw [← hαA]
    have := actP_comm_conj e hyN hyα.symm
    rw [← mul_inv_eq_iff_eq_mul, mul_conj_mul_inv] at this
    exact CSL.conj_injective this
  have hys' : orderOf (e ⟨y, hyN⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, hl2, hns⟩ := exists_nonsquare_of_conjAut hq hs hs2 (by rw [hFq]; exact hsq) A hA1
    hA2 hys' hAy
  obtain ⟨P, hP⟩ := exists_conj_eq_kG hns hl2
  have hll : (l : F) = -1 := by
    have hdet : (A : Matrix (Fin 4) (Fin 4) F).det = 1 := Yα.2
    have h1 := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F).det) hP
    simp only [Units.val_mul, Matrix.det_mul, coe_kG, det_kZero] at h1
    have h3 : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det *
        (P : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h4' : (l : F) ^ 2 = 1 := by
      rw [← h1, hdet, mul_one, h3]
    have h5 : (l : F) * l = 1 := by rw [← sq]; exact h4'
    rcases mul_self_eq_one_iff.mp h5 with h | h
    · exact absurd ⟨1, by rw [h, mul_one]⟩ hns
    · exact h
  have hneg : ¬ IsSquare (-1 : F) := hll ▸ hns
  have hkG : kG (Units.ne_zero l) = kG (neg_one_ne_zero' (F := F)) :=
    Units.ext (by rw [coe_kG, coe_kG, hll])
  have hAP : A = P * kG (neg_one_ne_zero' (F := F)) * P⁻¹ := by
    rw [← hkG, ← hP]
    group
  obtain ⟨g, hg⟩ := exists_conj_kSL_of_conjAut hq P
  refine ⟨hJN, hneg, g, CSL.conj_injective ?_⟩
  rw [← actP_eq_conj e hιN, hαA, hAP, hg]

theorem map_eq_JK {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hFq : Fintype.card F = p ^ f)
    (hneg : ¬ IsSquare (-1 : F)) (e : ↥N ≃* projectiveSL 4 F) {ι : H} (hιN : ι ∈ N)
    (hek : e ⟨ι, hιN⟩ = proj 4 F kSL) {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJp : ⁅J₁, J₁⁆ = J₁) (hJN : J₁ ≤ N) (hJt : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) :
    (J₁.subgroupOf N).map e.toMonoidHom = JK F neg_one_ne_zero' ∧ pPrimeCore 2 ↥J₁ = ⊥ ∧
      2 * Nat.card J₁ = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
  classical
  have hq : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_odd hq
  have hF : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hFq]
  have hα' : actP e ι = conjAut 4 F (kG neg_one_ne_zero') := by
    rw [actP_eq_conj e hιN, hek, conjAut_kG_eq]
  set J' : Subgroup (projectiveSL 4 F) := (J₁.subgroupOf N).map e.toMonoidHom with hJ'
  have hJ'p : ⁅J', J'⁆ = J' := by
    rw [hJ', ← Subgroup.map_commutator, AZ.subgroupOf_perfect hJN hJp]
  have hJ'k : ∀ x ∈ J', conjAut 4 F (kG neg_one_ne_zero') x = x := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hα']
    change actP e ι (e z) = e z
    rw [actP_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have := mem_centralizer_singleton_iff.mp (hJC (mem_subgroupOf.1 hz))
    rw [← this]
    group
  have hcJ : Nat.card J' = Nat.card J₁ := by
    rw [hJ', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
  have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJt
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J₁)
  have hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J' := by
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥J₁))
    rw [hcJ, hF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring, ← h1]
    omega
  have hJK : J' = JK F neg_one_ne_zero' := eq_JK h2 neg_one_ne_zero' hneg hJ'k hJ'p hcard
  have hle := two_mul_card_JK_le h2 neg_one_ne_zero' hneg
  rw [← hJK, hcJ, hF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring] at hle
  have hO1 : Nat.card (pPrimeCore 2 ↥J₁) = 1 := by
    have hpos : 0 < Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) := Nat.card_pos
    have hpos' : 0 < Nat.card (pPrimeCore 2 ↥J₁) := Nat.card_pos
    rw [hQ, ← h1] at hle
    rcases Nat.lt_or_ge (Nat.card (pPrimeCore 2 ↥J₁)) 2 with h | h
    · omega
    · exfalso
      have : 2 * Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) * 2 ≤
          2 * (Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) * Nat.card (pPrimeCore 2 ↥J₁)) := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_left _ h
      omega
  refine ⟨hJK, Subgroup.card_eq_one.mp hO1, ?_⟩
  rw [hQ, hO1, mul_one, h1]

end Transport

theorem exists_std_L4 {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (hL : Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 p f)
    {ι : H} (hιF : ι ∈ generalizedFitting H) (hι : orderOf ι = 2)
    {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))))
    (hJt : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = p ^ f ∧
      ¬ IsSquare (-1 : F) ∧ J₁ ≤ generalizedFitting H ∧ pPrimeCore 2 ↥J₁ = ⊥ ∧
      2 * Nat.card J₁ = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ∧
      ∃ e : ↥(generalizedFitting H) ≃* projectiveSL 4 F,
        e ⟨ι, hιF⟩ = proj 4 F kSL ∧
        (J₁.subgroupOf (generalizedFitting H)).map e.toMonoidHom = JK F neg_one_ne_zero' := by
  classical
  have : (generalizedFitting H).Normal := (LocalCores.generalized_fitting_characteristic (G := H)).2
  obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
  let : Fintype F := Fintype.ofFinite F
  have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
  set e₀ : ↥(generalizedFitting H) ≃* projectiveSL 4 F :=
    eL.trans ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 4 F).symm)) with he₀
  have hJp : ⁅J₁, J₁⁆ = J₁ := P211.commutator_eq_of_isPComp hJC hJ
  obtain ⟨hJN, hneg, g, hg⟩ := conj_kSL_of_component hC hp hp2 hf hFq e₀ hιF hι hJC hJp hJt
  set e : ↥(generalizedFitting H) ≃* projectiveSL 4 F := e₀.trans (MulAut.conj g⁻¹) with he
  have hek : e ⟨ι, hιF⟩ = proj 4 F kSL := by
    rw [he, MulEquiv.trans_apply, hg, MulAut.conj_apply]
    group
  obtain ⟨hJK, hO, hcard⟩ := map_eq_JK hp hp2 hFq hneg e hιF hek hJC hJp hJN hJt
  exact ⟨F, inferInstance, inferInstance, hFq, hneg, hJN, hO, hcard, e, hek, hJK⟩

end CFSG.ComponentClassification.GSThmB.P29
