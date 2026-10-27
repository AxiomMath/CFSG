module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCLb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OFL

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL CSL OCL
  CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {p f : ℕ} {α : G}
  {J : Subgroup G}

theorem diag_setup_L4 (hcfg : OutInv.OuterL2Config G N p f α J) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {F : Type} [Field F] [Fintype F] (hFq : Fintype.card F = p ^ f)
    (e : ↥N ≃* projectiveSL 4 F) {A : GL (Fin 4) F} (hαA : actP e α = conjAut 4 F A) :
    J ≤ N ∧ ∃ (l : F) (hl : l ≠ 0) (e' : ↥N ≃* projectiveSL 4 F), ¬ IsSquare l ∧
      IsSquare (-1 : F) ∧ actP e' α = conjAut 4 F (kG hl) ∧
      (J.subgroupOf N).map e'.toMonoidHom = JK F hl := by
  classical
  obtain ⟨-, hC, -, hα2, hαN, hJα, -, hJ, hstd⟩ := hcfg
  have hq : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_odd hq
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv e (fun J hJ => DiagL.le_range_conj_of_perfect hJ)) hJp
  refine ⟨hJN, ?_⟩
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
  have hA1 : conjAut 4 F A ≠ 1 := fun h => hα1 (eq_one_of_actP_eq_one hC e (hαA ▸ h))
  have hA2 : conjAut 4 F A ^ 2 = 1 := by rw [← hαA, ← map_pow, sq, hαα, map_one]
  have hyα : y * α = α * y := mem_centralizer_singleton_iff.mp (hJα hyJ)
  have hAy : conjAut 4 F A (e ⟨y, hyN⟩) = e ⟨y, hyN⟩ := by
    rw [← hαA]
    have := actP_comm_conj e hyN hyα.symm
    rw [← mul_inv_eq_iff_eq_mul, mul_conj_mul_inv] at this
    exact conj_injective this
  have hys' : orderOf (e ⟨y, hyN⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, hl2, hns⟩ := exists_nonsquare_of_conjAut hq hs hs2 (by rw [hFq]; exact hsq) A hA1
    hA2 hys' hAy
  obtain ⟨P, hP⟩ := exists_conj_eq_kG hns hl2
  have hl : (l : F) ≠ 0 := Units.ne_zero l
  have hneg : IsSquare (-1 : F) := by
    by_contra hneg
    obtain ⟨Y, hY⟩ := conjAut_mem_range_conj hneg hns hP
    apply hαN
    set x : G := (e.symm (proj 4 F Y) : G) with hx
    have hxN : x ∈ N := (e.symm _).2
    have hex : e ⟨x, hxN⟩ = proj 4 F Y := by simp [hx]
    have h1 : actP e (α * x⁻¹) = 1 := by
      rw [map_mul, map_inv, actP_eq_conj e hxN, hex, hαA, hY, mul_inv_cancel]
    rw [mul_inv_eq_one.mp (eq_one_of_actP_eq_one hC e h1)]
    exact hxN
  set e' : ↥N ≃* projectiveSL 4 F := e.trans (conjAut 4 F P⁻¹) with he'
  have hα' : actP e' α = conjAut 4 F (kG hl) := by
    rw [he', actP_trans, hαA, ← map_inv, ← map_mul, ← map_mul, inv_inv, hP]
  set J' : Subgroup (projectiveSL 4 F) := (J.subgroupOf N).map e'.toMonoidHom with hJ'
  have hJ'p : ⁅J', J'⁆ = J' := by
    rw [hJ', ← Subgroup.map_commutator, AZ.subgroupOf_perfect hJN hJp]
  have hJ'k : ∀ x ∈ J', conjAut 4 F (kG hl) x = x := by
    rw [← hα']
    rintro _ ⟨z, hz, rfl⟩
    change actP e' α (e' z) = e' z
    rw [actP_apply]
    congr 1
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    have := mem_centralizer_singleton_iff.mp (hJα (mem_subgroupOf.1 hz))
    rw [← this]
    group
  have hcJ : Nat.card J' = Nat.card J := by
    rw [hJ', Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
  have hF : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hFq]
  have hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J' := by
    have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥J))
    rw [hcJ, hF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring, ← h1]
    omega
  exact ⟨l, hl, e', hns, hneg, hα', eq_JK h2 hl hns hJ'k hJ'p hcard⟩

theorem outer_diag_fusion_L4 (hcfg : OutInv.OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {F : Type} [Field F] [Fintype F] (hFq : Fintype.card F = p ^ f)
    (e : ↥N ≃* projectiveSL 4 F) {A : GL (Fin 4) F} (hαA : actP e α = conjAut 4 F A) {ζ : G}
    (hζJ : ζ ∈ J) (hζ2 : orderOf ζ = 2) : ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  classical
  have hC := hcfg.2.1
  obtain ⟨hJN, l, hl, e', hns, hneg, hα', hJK⟩ := diag_setup_L4 hcfg hp hp2 hf hFq e hαA
  have hq : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
  have hq2 : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hq
  have hζN := hJN hζJ
  have hζJ' : e' ⟨ζ, hζN⟩ ∈ JK F hl := by
    rw [← hJK]
    exact ⟨⟨ζ, hζN⟩, mem_subgroupOf.2 hζJ, rfl⟩
  obtain ⟨Z, hZ, hZe⟩ := hζJ'
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ2
    norm_num at hζ2
  have hZ1 : proj 4 F Z ≠ 1 := by
    rw [hZe]
    intro h
    apply hζ1
    exact congrArg Subtype.val (e'.map_eq_one_iff.mp h)
  have hζsq : ζ ^ 2 = 1 := by rw [← hζ2, pow_orderOf_eq_one]
  have hZ2 : proj 4 F Z ^ 2 = 1 := by
    have h1 : (⟨ζ, hζN⟩ : ↥N) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact hζsq)
    rw [hZe, ← map_pow, h1, map_one]
  have hZZ := mul_self_eq_neg_one hl hns hZ hZ1 hZ2
  have hZZm : (Z : Matrix (Fin 4) (Fin 4) F) * Z = -1 := by
    have := congrArg (fun X : SpecialLinearGroup (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F)) hZZ
    simpa using this
  have hZk : (Z : Matrix (Fin 4) (Fin 4) F) * kZero l = kZero l * Z :=
    (mem_CK_iff hl).1 (mem_CK_of_mem_SK hl hZ)
  obtain ⟨i, hi⟩ := hneg
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hi
    exact one_ne_zero (neg_eq_zero.1 hi)
  set u : Fˣ := Units.mk0 i hi0 with hu
  set W : GL (Fin 4) F :=
    GeneralLinearGroup.scalar (Fin 4) u⁻¹ * (kG hl * SpecialLinearGroup.toGL Z) with hW
  have hWm : (W : Matrix (Fin 4) (Fin 4) F) = i⁻¹ • (kZero l * (Z : Matrix (Fin 4) (Fin 4) F)) := by
    rw [hW, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_kG,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Units.val_inv_eq_inv_val, hu, Units.val_mk0]
    rfl
  have hWW : (W : Matrix (Fin 4) (Fin 4) F) * W = l • (1 : Matrix (Fin 4) (Fin 4) F) := by
    have e1 : kZero l * (Z : Matrix (Fin 4) (Fin 4) F) * (kZero l * Z) = -(l • 1) := by
      calc kZero l * (Z : Matrix (Fin 4) (Fin 4) F) * (kZero l * Z) =
          kZero l * ((Z : Matrix (Fin 4) (Fin 4) F) * kZero l) * Z := by
            simp only [Matrix.mul_assoc]
        _ = kZero l * (kZero l * Z) * Z := by rw [hZk]
        _ = kZero l * kZero l * ((Z : Matrix (Fin 4) (Fin 4) F) * Z) := by
            simp only [Matrix.mul_assoc]
        _ = -(l • 1) := by rw [kZero_mul_kZero, hZZm, Matrix.mul_neg, Matrix.mul_one]
    rw [hWm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, e1, smul_neg, smul_smul, ← neg_smul]
    congr 1
    have hii : i⁻¹ * i⁻¹ = -1 := by
      rw [← mul_inv, ← hi, inv_neg, inv_one]
    rw [hii]
    ring
  obtain ⟨Y, hY⟩ := exists_conj_eq hq2 hl hns hWW
  set γ : G := (e'.symm (proj 4 F Y) : G) with hγ
  have hγN : γ ∈ N := (e'.symm _).2
  have heγ : e' ⟨γ, hγN⟩ = proj 4 F Y := by simp [hγ]
  refine ⟨γ, hγN, ?_⟩
  have hinj : ∀ x y : G, actP e' x = actP e' y → x = y := fun x y h => by
    have h1 : actP e' (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (eq_one_of_actP_eq_one hC e' h1)
  have hL : actP e' (γ⁻¹ * α * γ) = conjAut 4 F W := by
    rw [map_mul, map_mul, map_inv, actP_eq_conj e' hγN, heγ, ← conjAut_toGL, hα', hY]
  have hR : actP e' (α * ζ) = conjAut 4 F W := by
    rw [map_mul, hα', actP_eq_conj e' hζN, ← hZe, ← conjAut_toGL, hW, map_mul, map_mul,
      (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2 ⟨u⁻¹, rfl⟩,
      one_mul]
  exact hinj _ _ (hL.trans hR.symm)

end OFL

end CFSG.ComponentClassification.CatFactsL4U4
