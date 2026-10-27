module

public import CFSG.ClassicalInvolution.Q3.Q3T6DCaseIA
public import CFSG.ClassicalInvolution.Uniform.U7Inv
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreTight

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank


section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem g2Section3_of_violation (hΩ : HypOmegaModU (.sl2 3 1) Ω) {n : ℕ}
    (hn : CITBelowT (.sl2 3 1) n) {H K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω)
    (hHdef : omegaGen (aStar Ω K) = H) (hv : AViol Ω K J zK zJ) (hlt : Nat.card ↥H < n) :
    G2Section H zK := by
  have hΩg : HypOmegaGen Ω := hypGen_of_modU hΩ
  have hMH : ∀ M ∈ aStar Ω K, M ≤ H := fun M hM => hHdef ▸ le_omegaGen hM
  have hKH : K ≤ H := hMH K Relation.ReflTransGen.refl
  have hJS : J ∈ aStar Ω K := Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  have hJH : J ≤ H := hMH J hJS
  have hΛ : HypOmegaModU (.sl2 3 1) (restrictFamily Ω H) := hypOmegaModU_restrict hΩ H
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hΦ : HypOmegaModU (.sl2 3 1) (oddQuotientFamily (restrictFamily Ω H)) :=
    hypOmegaModU_oddQuotientFamily hΛ
  have hO : classicalInvolutionOddCore (↥H ⧸ classicalInvolutionOddCore ↥H) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥H
  have hlt' : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hlt
  obtain ⟨D⟩ := exists_omegaLieU hn hΦ ⟨_, barImg_mem H hK hKH⟩ hO hlt'
  obtain ⟨a, hQ⟩ := quotViol_of_aViol_three hΛ (subgroupOf_mem_restrictFamily hK hKH)
    (aViol_subgroupOf hΩg hKH hJH hv)
  obtain ⟨C, R, S, hR, hS, hKR, hJS'⟩ := exists_g2Comp_of_quotViol hΦ D hQ
  have hKi : barImg H K ∈ C.members := ⟨barImg_mem H hK hKH, R, hR, hKR⟩
  have hsurj : Function.Surjective C.ψ := g2Comp_psi_surjective hΩ hK hHdef C hKi
  have hinj : Function.Injective C.ψ := C.inj
  have hsimple : IsSimpleGroup G2Model :=
    isSimpleGroup_model_of_g2d4 (p := 3) (e := 1) (by norm_num) g2Adm3 (Or.inl rfl)
  let e : G2Model ≃* (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    MulEquiv.ofBijective C.ψ ⟨hinj, hsurj⟩
  have hsimpleX : IsSimpleGroup (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    MulEquiv.isSimpleGroup e.symm
  have hnab : ∃ x y : ↥H ⧸ classicalInvolutionOddCore ↥H, x * y ≠ y * x := by
    obtain ⟨zz, hzz⟩ := hΦ.classical _ (barImg_mem H hK hKH)
    obtain ⟨x, -, y, -, hxy⟩ := hzz.exists_noncomm
    exact ⟨x, y, hxy⟩
  refine ⟨isQuasisimple_of_simple_nonabelian hnab, ?_⟩
  intro x hxH hx2 hx1
  have hz : IsUniqueInvolution K zK := hv.hzK
  have hzH : zK ∈ H := hKH hz.mem
  set z' : ↥H := ⟨zK, hzH⟩ with hz'
  set x' : ↥H := ⟨x, hxH⟩ with hx'
  have hz'2 : z' * z' = 1 := Subtype.ext hz.sq
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hz'1 : oddQuot ↥H z' ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val
    (eq_one_of_mul_self_of_mem_odd hodd ((QuotientGroup.eq_one_iff _).mp h) hz'2))
  have hx'1 : oddQuot ↥H x' ≠ 1 := fun h => hx1 (congrArg Subtype.val
    (eq_one_of_mul_self_of_mem_odd hodd ((QuotientGroup.eq_one_iff _).mp h) hx'2))
  obtain ⟨c₁, hc₁⟩ := hsurj (oddQuot ↥H z')
  obtain ⟨c₂, hc₂⟩ := hsurj (oddQuot ↥H x')
  have hc₁sq : c₁ * c₁ = 1 := hinj (by rw [map_mul, hc₁, ← map_mul, hz'2, map_one, map_one])
  have hc₂sq : c₂ * c₂ = 1 := hinj (by rw [map_mul, hc₂, ← map_mul, hx'2, map_one, map_one])
  have hc₁ne : c₁ ≠ 1 := fun h => hz'1 (by rw [← hc₁, h, map_one])
  have hc₂ne : c₂ ≠ 1 := fun h => hx'1 (by rw [← hc₂, h, map_one])
  obtain ⟨h₀, hh₀⟩ := g2_model_involutions_conj (p := 3) (n := 0) (e := 1) rfl (by norm_num)
    g2Adm3 hc₁sq hc₂sq hc₁ne hc₂ne
  obtain ⟨h₁, hh₁⟩ := QuotientGroup.mk'_surjective _ (C.ψ h₀)
  have hconj : oddQuot ↥H (h₁ * z' * h₁⁻¹) = oddQuot ↥H x' := by
    rw [map_mul, map_mul, map_inv, hh₁, ← hc₁, ← map_inv, ← map_mul, ← map_mul, hh₀, hc₂]
  have hu2 : h₁ * z' * h₁⁻¹ * (h₁ * z' * h₁⁻¹) = 1 := by
    calc h₁ * z' * h₁⁻¹ * (h₁ * z' * h₁⁻¹) = h₁ * (z' * z') * h₁⁻¹ := by group
      _ = 1 := by rw [hz'2]; group
  obtain ⟨m, -, hm⟩ := exists_conj_of_map_eq_of_involutions hodd hu2 hx'2 hconj
  refine ⟨((m * h₁ : ↥H) : G), (m * h₁).2, ?_⟩
  have := congrArg Subtype.val hm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  have hx'v : (x' : G) = x := rfl
  have hz'v : (z' : G) = zK := rfl
  rw [hz'v, hx'v] at this
  rw [← this]
  group

end Sec

end CFSG.ClassicalInvolution.Q3.Q3T6D
