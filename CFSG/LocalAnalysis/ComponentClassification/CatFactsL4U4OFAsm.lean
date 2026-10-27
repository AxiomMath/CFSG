module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCAsm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFLb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFUd

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL CSL DiagU
  CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

theorem fusion_of_act {G X : Type} [Group G] [Group X] {N : Subgroup G} (e : ↥N ≃* X)
    (Φ : G →* MulAut X) (hΦN : ∀ (x : G) (hx : x ∈ N), Φ x = MulAut.conj (e ⟨x, hx⟩))
    (hinj : ∀ g : G, Φ g = 1 → g = 1) {α ζ : G} (hζN : ζ ∈ N) {γ' : X}
    (h : (MulAut.conj γ')⁻¹ * Φ α * MulAut.conj γ' = Φ α * MulAut.conj (e ⟨ζ, hζN⟩)) :
    ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  set γ : G := (e.symm γ' : G) with hγ
  have hγN : γ ∈ N := (e.symm γ').2
  have heγ : e ⟨γ, hγN⟩ = γ' := by
    rw [show (⟨γ, hγN⟩ : ↥N) = e.symm γ' from rfl, MulEquiv.apply_symm_apply]
  refine ⟨γ, hγN, ?_⟩
  have h1 : Φ (γ⁻¹ * α * γ * (α * ζ)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_mul, hΦN γ hγN, heγ, hΦN ζ hζN, h,
      mul_inv_cancel]
  exact mul_inv_eq_one.mp (hinj _ h1)

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} {p f : ℕ} {α : G} {J : Subgroup G}

theorem fusion_L4 (hI : OuterInvCentL4) (hcfg : OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : Blueprint.LieModel ↥N .PSL 4 p f) {ζ : G} (hζJ : ζ ∈ J)
    (hζ2 : orderOf ζ = 2) : ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  classical
  have hcfg' := hcfg
  obtain ⟨hNn, hC, -, hα2, -, hJα, hJc, hJ, hstd⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
  let : Fintype F := Fintype.ofFinite F
  have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
  set e : ↥N ≃* projectiveSL 4 F :=
    eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 4 F).symm)) with he
  by_cases hd : actP e α ∈ (conjAut 4 F).range
  · obtain ⟨A, hA⟩ := hd
    exact OFL.outer_diag_fusion_L4 hcfg' hp hp2 hf hFq e hA.symm hζJ hζ2
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv e (fun J hJ => DiagL.le_range_conj_of_perfect hJ)) hJp
  have hΦ : ∀ (g : G) (x : ↥N), actP e g (e x) = e (MulAut.conjNormal g x) := actP_apply e
  obtain ⟨hle, hcomp⟩ := fixSub_component e (actP e) hΦ hJN hJα hJc
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hφ2 : actP e α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hζN := hJN hζJ
  have hζ' : e ⟨ζ, hζN⟩ ∈ (J.subgroupOf N).map e.toMonoidHom :=
    ⟨⟨ζ, hζN⟩, mem_subgroupOf.2 hζJ, rfl⟩
  have hζ'2 : orderOf (e ⟨ζ, hζN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hζ2]
  obtain ⟨γ', hγ'⟩ := (hI F p f hp hp2 hf hFq (actP e α) hφ2 hd _ hle hcomp
    (lieModel_map e hJN hJ)).2 _ hζ' hζ'2
  exact fusion_of_act e (actP e) (fun x hx => actP_eq_conj e hx)
    (fun g hg => eq_one_of_actP_eq_one hC e hg) hζN hγ'

theorem fusion_U4 (hI : OuterInvCentU4) (hcfg : OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hU : Blueprint.LieModel ↥N .PSU 4 p f) {ζ : G} (hζJ : ζ ∈ J)
    (hζ2 : orderOf ζ = 2) : ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  classical
  have hcfg' := hcfg
  obtain ⟨hNn, hC, -, hα2, -, hJα, hJc, hJ, hstd⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, K, _, _, hK, ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  by_cases hd : AZ.actE eU α ∈ InnU p f K h
  · obtain ⟨A, hA⟩ := hd
    exact OFU.outer_diag_fusion_U4 hcfg' hp hp2 hf h eU hA hζJ hζ2
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv eU (fun J hJ => DiagU.le_range_conj_of_perfect_U h hp2 hJ)) hJp
  have hΦ : ∀ (g : G) (x : ↥N), AZ.actE eU g (eU x) = eU (MulAut.conjNormal g x) :=
    AZ.actE_apply eU
  obtain ⟨hle, hcomp⟩ := fixSub_component eU (AZ.actE eU) hΦ hJN hJα hJc
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hφ2 : AZ.actE eU α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hζN := hJN hζJ
  have hζ' : eU ⟨ζ, hζN⟩ ∈ (J.subgroupOf N).map eU.toMonoidHom :=
    ⟨⟨ζ, hζN⟩, mem_subgroupOf.2 hζJ, rfl⟩
  have hζ'2 : orderOf (eU ⟨ζ, hζN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hζ2]
  obtain ⟨γ', hγ'⟩ := (hI K p f h hp2 (AZ.actE eU α) hφ2 hd _ hle hcomp
    (lieModel_map eU hJN hJ)).2 _ hζ' hζ'2
  exact fusion_of_act eU (AZ.actE eU) (fun x hx => CSU.actE_eq_conj eU hx)
    (fun g hg => AZ.eq_one_of_actE_eq_one hC eU hg) hζN hγ'

omit [Finite G] in
theorem fusion_O8 (hI : OuterInvCentO8) (hcfg : OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hJN : J ≤ N) {e : ℕ} (he : f = 2 * e)
    (hO : Blueprint.LieModel ↥N .POmegaMinus 4 p e) {ζ : G} (hζJ : ζ ∈ J)
    (hζ2 : orderOf ζ = 2) : ∃ γ ∈ N, γ⁻¹ * α * γ = α * ζ := by
  classical
  obtain ⟨hNn, hC, -, hα2, hαN, hJα, hJc, hJ, -⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, K, _, _, hK, b, c, hbc, ⟨eO⟩⟩ :=
    statedClassicalModel_of_lieModel_ne_zero (by norm_num) hO
  let : Fintype K := Fintype.ofFinite K
  have hKq : Fintype.card K = p ^ e := by rw [Fintype.card_eq_nat_card, hK]
  have he1 : 1 ≤ e := by omega
  set Φ := AZ.actE eO with hΦdef
  have hΦ : ∀ (g : G) (x : ↥N), Φ g (eO x) = eO (MulAut.conjNormal g x) := AZ.actE_apply eO
  have hout : Φ α ∉
      (MulAut.conj : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) →* _).range := by
    rintro ⟨y, hy⟩
    apply hαN
    set x : G := (eO.symm y : G) with hx
    have hxN : x ∈ N := (eO.symm y).2
    have hex : eO ⟨x, hxN⟩ = y := by simp [hx]
    have h1 : Φ (α * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hΦdef, CSU.actE_eq_conj eO hxN, hex, ← hΦdef, ← hy, mul_inv_cancel]
    rw [mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eO h1)]
    exact hxN
  obtain ⟨hle, hcomp⟩ := fixSub_component eO Φ hΦ hJN hJα hJc
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hφ2 : Φ α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hJ' := lieModel_map eO hJN hJ
  rw [he] at hJ'
  have hζN := hJN hζJ
  have hζ' : eO ⟨ζ, hζN⟩ ∈ (J.subgroupOf N).map eO.toMonoidHom :=
    ⟨⟨ζ, hζN⟩, mem_subgroupOf.2 hζJ, rfl⟩
  have hζ'2 : orderOf (eO ⟨ζ, hζN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hζ2]
  obtain ⟨γ', hγ'⟩ := (hI K p e hp hp2 he1 hKq b c hbc (Φ α) hφ2 hout _ hle hcomp hJ').2 _ hζ'
    hζ'2
  exact fusion_of_act eO Φ (fun x hx => CSU.actE_eq_conj eO hx)
    (fun g hg => AZ.eq_one_of_actE_eq_one hC eO hg) hζN hγ'

theorem outerL2Fusion_of (hL4 : OuterInvCentL4) (hU4 : OuterInvCentU4)
    (hO8 : OuterInvCentO8) : OuterL2Fusion := by
  intro G _ _ N p f hp hp2 hf α J hcfg hJN ζ hζJ hζ2
  rcases hcfg.2.2.1 with hL | hU | ⟨e, he, hO⟩
  · exact fusion_L4 hL4 hcfg hp hp2 hf hL hζJ hζ2
  · exact fusion_U4 hU4 hcfg hp hp2 hf hU hζJ hζ2
  · exact fusion_O8 hO8 hcfg hp hp2 hf hJN he hO hζJ hζ2

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
