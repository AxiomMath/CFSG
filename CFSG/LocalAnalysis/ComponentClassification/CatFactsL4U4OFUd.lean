module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFUc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFUb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OFU

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut UnitaryConj HBlocks StabU DiagU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB CSU

theorem X1_mul_X1 {K : Type} [Field K] (l : K) :
    X1 l * X1 l = (l ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem X1_neg {K : Type} [Field K] (l : K) : X1 (-l) = -X1 l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1]

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {p f : ℕ} {α : G}
  {J : Subgroup G}

theorem outer_diag_fusion_U4 (hcfg : OutInv.OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (eU : ↥N ≃* StatedProj (StatedSU 4 (p ^ f) K)) {A : GL (Fin 4) K}
    (hαA : IsCU h A (AZ.actE eU α)) {ζ : G} (hζJ : ζ ∈ J) (hζ2 : orderOf ζ = 2) :
    ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  classical
  obtain ⟨-, hC, -, hα2, hαN, hJα, -, hJ, hstd⟩ := hcfg
  have : Finite K := h.finite
  set Φ := AZ.actE eU with hΦ
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv eU (fun J hJ => DiagU.le_range_conj_of_perfect_U h hp2 hJ)) hJp
  have hJtype : IsSec8JType (↥J ⧸ center ↥J) p f := Or.inl hJ
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have := Fact.mk hs
  obtain ⟨⟨y, hyJ⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) s
    (hsJ.trans (Subgroup.card_quotient_dvd_card _))
  rw [Subgroup.orderOf_mk] at hys
  have hyN := hJN hyJ
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα2
    norm_num at hα2
  have hα1' : Φ α ≠ 1 := fun h1 => hα1 (AZ.eq_one_of_actE_eq_one hC eU h1)
  have hα2' : Φ α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  obtain ⟨hperf, hcJ, hfix⟩ := AZ.image_facts eU hJN
  set J' := (J.subgroupOf N).map eU.toMonoidHom with hJ'
  have hαfix : ∀ j ∈ J, α * j * α⁻¹ = j := by
    intro j hj
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hy' : eU ⟨y, hyN⟩ ∈ J' := ⟨⟨y, hyN⟩, mem_subgroupOf.2 hyJ, rfl⟩
  have hys' : orderOf (eU ⟨y, hyN⟩) = s := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, P, hbl, hP, hAP⟩ := exists_hyp_of_diag h hp2 hαA hα1' hα2' hs hs2 hsq hys'
    (hfix α hαfix _ hy')
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbl
    exact zero_ne_one (neg_eq_zero.1 hbl.symm).symm
  have hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J' := by
    have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥J))
    rw [hcJ, ← h1]
    omega
  have hJeq := eq_map_commutator h hp2 P hP hl0 hαA hAP (hfix α hαfix) (hperf hJp) hcard _ rfl
  have hq3 : p ^ f % 4 = 3 := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h13 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    rcases h13 with h1 | h3
    · exfalso
      obtain ⟨Y, hY⟩ := OCU.exists_conj_of_mod_four h hp2 h1 P hbl hαA hAP
      apply hαN
      set x : G := (eU.symm (thU p f K Y) : G) with hx
      have hxN : x ∈ N := (eU.symm _).2
      have hex : eU ⟨x, hxN⟩ = thU p f K Y := by simp [hx]
      have h2 : Φ (α * x⁻¹) = 1 := by
        rw [map_mul, map_inv, hΦ, actE_eq_conj eU hxN, hex, ← hΦ, hY, mul_inv_cancel]
      rw [mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eU h2)]
      exact hxN
    · exact h3
  have hζN := hJN hζJ
  have hζJ' : eU ⟨ζ, hζN⟩ ∈ J' := ⟨⟨ζ, hζN⟩, mem_subgroupOf.2 hζJ, rfl⟩
  rw [hJeq] at hζJ'
  obtain ⟨Z, hZ, hZe⟩ := hζJ'
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ2
    norm_num at hζ2
  have hζsq : ζ ^ 2 = 1 := by rw [← hζ2, pow_orderOf_eq_one]
  have hZ1 : thU p f K Z ≠ 1 := by
    rw [hZe]
    intro h1
    exact hζ1 (congrArg Subtype.val (eU.map_eq_one_iff.mp h1))
  have hZ2 : thU p f K Z ^ 2 = 1 := by
    have h1 : (⟨ζ, hζN⟩ : ↥N) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact hζsq)
    rw [hZe, ← map_pow, h1, map_one]
  have hZZ := mul_self_eq_neg_one_U h hp2 P hP hl0 hAP hZ hZ1 hZ2
  have hZC : Z ∈ (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype :=
    (Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
      ⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
        (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆ ≤
        (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype) hZ
  have hZA : ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A =
      (A : Matrix (Fin 4) (Fin 4) K) * (Z : GL (Fin 4) K) := by
    have := mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hZC)
    exact congrArg Units.val this
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one h hp2
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hi
    exact one_ne_zero (by linear_combination hi : (1 : K) = 0)
  have hi4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hi]; norm_num
  have hbi : h.bar i * i = 1 := by
    rw [h.bar_apply]
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 3 := ⟨p ^ f / 4, by omega⟩
    rw [hk, ← pow_succ, show 4 * k + 3 + 1 = 4 * (k + 1) by ring, pow_mul, hi4, one_pow]
  set u : Kˣ := Units.mk0 i⁻¹ (inv_ne_zero hi0) with hu
  have hbu : h.bar (u : K) * u = 1 := by
    rw [hu, Units.val_mk0, map_inv₀, ← mul_inv, hbi, inv_one]
  set W : GL (Fin 4) K := GeneralLinearGroup.scalar (Fin 4) u * (A * (Z : GL (Fin 4) K)) with hW
  have hWu : W ∈ uMat h 4 :=
    mul_mem (scalar_mem_uMat h hbu) (mul_mem hαA.1 (mem_uMat_of_mem_SU h Z))
  have hWm : (W : Matrix (Fin 4) (Fin 4) K) =
      (u : K) • ((A * (Z : GL (Fin 4) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hW, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hΦζ : Φ ζ = MulAut.conj (thU p f K Z) := by rw [hΦ, actE_eq_conj eU hζN, ← hZe]
  have hWcu : IsCU h W (Φ (α * ζ)) := by
    rw [map_mul, hΦζ]
    exact (hαA.mul h (isCU_conj h Z)).of_eq_smul h hWu hWm
  have hαζ1 : Φ (α * ζ) ≠ 1 := by
    intro h1
    apply hαN
    rw [mul_eq_one_iff_eq_inv.mp (AZ.eq_one_of_actE_eq_one hC eU h1)]
    exact inv_mem hζN
  have hαζ2 : Φ (α * ζ) ^ 2 = 1 := by
    have hcomm : ζ * α = α * ζ := mem_centralizer_singleton_iff.mp (hJα hζJ)
    have e : (α * ζ) ^ 2 = 1 := by
      calc (α * ζ) ^ 2 = α * (ζ * α) * ζ := by rw [sq]; group
        _ = α * α * (ζ * ζ) := by rw [hcomm]; group
        _ = 1 := by rw [hαα, ← sq, hζsq, one_mul]
    rw [← map_pow, e, map_one]
  have hAm : (A : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hAP, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA2 : (A : Matrix (Fin 4) (Fin 4) K) * A = (l ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [hAm]
    calc (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        (P : Matrix (Fin 4) (Fin 4) K) * (X1 l * X1 l) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K), hPP, Matrix.one_mul]
      _ = (l ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K) := by
          rw [X1_mul_X1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
            mul_inv_cancel, Units.val_one]
  have hWW : (W : Matrix (Fin 4) (Fin 4) K) * W = (l ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K) := by
    have e1 : ((A * (Z : GL (Fin 4) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((A * (Z : GL (Fin 4) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        -((l ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K)) := by
      rw [Units.val_mul]
      calc (A : Matrix (Fin 4) (Fin 4) K) * ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((A : Matrix (Fin 4) (Fin 4) K) * ((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) =
          (A : Matrix (Fin 4) (Fin 4) K) *
            (((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A) * (Z : GL (Fin 4) K) := by
            simp only [Matrix.mul_assoc]
        _ = (A : Matrix (Fin 4) (Fin 4) K) * A *
            (((Z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Z : GL (Fin 4) K)) := by
            rw [hZA]
            simp only [Matrix.mul_assoc]
        _ = -((l ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K)) := by
            rw [hA2, hZZ, Matrix.mul_neg, Matrix.mul_one]
    rw [hWm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, e1, smul_neg, smul_smul, ← neg_smul]
    congr 1
    have hii : (u : K) * u = -1 := by
      rw [hu, Units.val_mk0, ← mul_inv, ← sq, hi, inv_neg, inv_one]
    rw [hii]
    ring
  obtain ⟨l', P', -, hP', hWP'⟩ := exists_hyp_of_sq h hp2 hWcu hαζ1 hαζ2 hbl hWW
  have hcancel : ∀ M M' : Matrix (Fin 4) (Fin 4) K, M * P' = M' * P' → M = M' := by
    intro M M' e
    have := congrArg (· * (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)) e
    simpa [Matrix.mul_assoc] using this
  have hl'2 : l' ^ 2 = l ^ 2 := by
    have e1 : (W : Matrix (Fin 4) (Fin 4) K) * W * P' =
        (l' ^ 2) • (P' : Matrix (Fin 4) (Fin 4) K) := by
      rw [Matrix.mul_assoc, hWP', ← Matrix.mul_assoc, hWP', Matrix.mul_assoc, X1_mul_X1,
        Matrix.mul_smul, Matrix.mul_one]
    rw [hWW, Matrix.smul_mul, Matrix.one_mul] at e1
    have e2 := congrArg (· * (↑P'⁻¹ : Matrix (Fin 4) (Fin 4) K)) e1
    simp only [Matrix.smul_mul, Units.mul_inv] at e2
    have e3 := congrFun (congrFun e2 0) 0
    simpa using e3.symm
  obtain ⟨g, hg⟩ := exists_conj_hyp h P P' hP hP' hAP
  have hsign : ∃ c : K, h.bar c * c = 1 ∧
      (((g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = c • (W : Matrix (Fin 4) (Fin 4) K) := by
    have e : (l' - l) * (l' + l) = 0 := by linear_combination hl'2
    rcases mul_eq_zero.1 e with e1 | e1
    · refine ⟨1, by rw [map_one, one_mul], ?_⟩
      rw [one_smul]
      apply hcancel
      rw [hg, hWP', sub_eq_zero.1 e1]
    · refine ⟨-1, by rw [map_neg, map_one]; ring, ?_⟩
      apply hcancel
      rw [hg, Matrix.smul_mul, hWP', eq_neg_of_add_eq_zero_left e1, X1_neg, Matrix.mul_neg,
        neg_one_smul, neg_neg]
  obtain ⟨c, hc, hcW⟩ := hsign
  set γ : G := (eU.symm (thU p f K g⁻¹) : G) with hγ
  have hγN : γ ∈ N := (eU.symm _).2
  have heγ : eU ⟨γ, hγN⟩ = thU p f K g⁻¹ := by
    rw [show (⟨γ, hγN⟩ : ↥N) = eU.symm (thU p f K g⁻¹) from rfl, MulEquiv.apply_symm_apply]
  refine ⟨γ, hγN, ?_⟩
  have hgA : (g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹ ∈ uMat h 4 :=
    mul_mem (mul_mem (mem_uMat_of_mem_SU h g) hαA.1) (inv_mem (mem_uMat_of_mem_SU h g))
  have hcu1 : IsCU h ((g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹) (Φ (γ⁻¹ * α * γ)) := by
    have hk : Φ (γ⁻¹ * α * γ) = (MulAut.conj (thU p f K g⁻¹))⁻¹ * Φ α *
        MulAut.conj (thU p f K g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hΦ, actE_eq_conj eU hγN, heγ]
    have h1 := isCU_conj h g⁻¹
    have h2 := ((h1.inv h).mul h hαA).mul h h1
    have e : (((g⁻¹ : unitarySU p f K 4) : GL (Fin 4) K))⁻¹ * A *
        ((g⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) =
        (g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹ := by
      rw [InvMemClass.coe_inv, inv_inv]
    rw [hk, ← e]
    exact h2
  have hcu2 : IsCU h ((g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹) (Φ (α * ζ)) :=
    hWcu.of_eq_smul h hgA hcW
  have heq := hcu1.unique h hcu2
  have h1 : Φ (γ⁻¹ * α * γ * (α * ζ)⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eU h1)

end OFU

end CFSG.ComponentClassification.CatFactsL4U4
