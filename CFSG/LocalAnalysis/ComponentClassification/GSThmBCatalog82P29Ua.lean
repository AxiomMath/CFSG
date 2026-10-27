module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PT
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification.CatFactsL4U4
  UnitaryOut UnitaryConj HBlocks StabU DiagU CSU ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

theorem exists_std_U4 {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (hU : Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 p f)
    {ι : H} (hιF : ι ∈ generalizedFitting H) (hι : orderOf ι = 2)
    {J₁ : Subgroup H} (hJC : J₁ ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))))
    (hJt : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K), p ^ f % 4 = 1 ∧
      J₁ ≤ generalizedFitting H ∧ pPrimeCore 2 ↥J₁ = ⊥ ∧
      2 * Nat.card J₁ = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ∧
      ∃ (e : ↥(generalizedFitting H) ≃* StatedProj (StatedSU 4 (p ^ f) K))
        (Y : unitarySU p f K 4) (P : GL (Fin 4) K) (l : K),
        e ⟨ι, hιF⟩ = thU p f K Y ∧ h.bar l * l = -1 ∧
        uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG ∧
        ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l ∧
        (J₁.subgroupOf (generalizedFitting H)).map e.toMonoidHom =
          (⁅(Subgroup.centralizer {(Y : GL (Fin 4) K)}).comap (unitarySU p f K 4).subtype,
            (Subgroup.centralizer {(Y : GL (Fin 4) K)}).comap
              (unitarySU p f K 4).subtype⁆).map (thU p f K) := by
  classical
  set N := generalizedFitting H with hNdef
  have : N.Normal := (LocalCores.generalized_fitting_characteristic (G := H)).2
  obtain ⟨-, K, _, _, hK, ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Finite K := h.finite
  set Φ := AZ.actE eU with hΦ
  have hJp : ⁅J₁, J₁⁆ = J₁ := P211.commutator_eq_of_isPComp hJC hJ
  have hJN : J₁ ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv eU (fun J hJ => DiagU.le_range_conj_of_perfect_U h hp2 hJ)) hJp
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJt
  have := Fact.mk hs
  obtain ⟨⟨y, hyJ⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := ↥J₁) s
    (hsJ.trans (Subgroup.card_quotient_dvd_card _))
  rw [Subgroup.orderOf_mk] at hys
  have hyN := hJN hyJ
  obtain ⟨Yα, hYα⟩ := thU_surjective (eU ⟨ι, hιF⟩)
  have hz : IsCU h (Yα : GL (Fin 4) K) (Φ ι) := by
    rw [hΦ, actE_eq_conj eU hιF, ← hYα]
    exact isCU_conj h Yα
  have hαα : ι * ι = 1 := by rw [← sq, ← hι, pow_orderOf_eq_one]
  have hα1 : ι ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hι
    norm_num at hι
  have hα1' : Φ ι ≠ 1 := fun h1 => hα1 (AZ.eq_one_of_actE_eq_one hC eU h1)
  have hα2' : Φ ι ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  obtain ⟨hperf, hcJ, hfix⟩ := AZ.image_facts eU hJN
  set J' := (J₁.subgroupOf N).map eU.toMonoidHom with hJ'
  have hαfix : ∀ j ∈ J₁, ι * j * ι⁻¹ = j := by
    intro j hj
    have := mem_centralizer_singleton_iff.mp (hJC hj)
    rw [← this]; group
  have hy' : eU ⟨y, hyN⟩ ∈ J' := ⟨⟨y, hyN⟩, mem_subgroupOf.2 hyJ, rfl⟩
  have hys' : orderOf (eU ⟨y, hyN⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, P, hbl, hP, hAP⟩ := exists_hyp_of_diag h hp2 hz hα1' hα2' hs hs2 hsq hys'
    (hfix ι hαfix _ hy')
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbl
    exact zero_ne_one (neg_eq_zero.1 hbl.symm).symm
  have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJt
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J₁)
  have hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J' := by
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥J₁))
    rw [hcJ, ← h1]
    omega
  obtain ⟨-, -, hle⟩ := eq_of_perfect_diag h hp2 P hP hl0 hz hAP (hfix ι hαfix) (hperf hJp) hcard
  have hJeq := eq_map_commutator h hp2 P hP hl0 hz hAP (hfix ι hαfix) (hperf hJp) hcard _ rfl
  have hl4 : l ^ 4 = 1 := by
    have hdet : ((Yα : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 :=
      ((mem_unitarySU_iff h).1 Yα.2).1
    have h1 := congrArg Matrix.det hAP
    rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, CSU.det_X1] at h1
    have hP0 : (P : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
    exact (mul_right_eq_self₀.mp h1.symm).resolve_right hP0
  have hq4 := card_mod_four_of_inner h hp2 hl4 hbl
  rw [hcJ] at hle
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
  refine ⟨K, inferInstance, h, hq4, hJN, Subgroup.card_eq_one.mp hO1, ?_, eU, Yα, P, l,
    hYα.symm, hbl, hP, hAP, hJeq⟩
  rw [hQ, hO1, mul_one, h1]

end CFSG.ComponentClassification.GSThmB.P29
