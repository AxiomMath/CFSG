module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTri

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits

section Cert

variable
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem oppositeFixed_graphFixedRootGroup_D4_of_nf (hσ3 : σ ^ 3 = 1)
    (hNF : UniqueNormalFormOn (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    OppositeFixed ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore hne hRQ hC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3' : σ ^ TwistTag.D4.order = 1 := hσ3
  have hfinM : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hQ₀ne : Q.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≠ ⊥ := fun h =>
    hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_fixed TwistTag.D4 σ hσ3'
    (Subgroup.map_subtype_le Q) (hQ2.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)
    hQ₀ne
  obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  have hQ₀C : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom J
  have hQJ2 : IsPGroup 2 (radTri K σ J) := by
    have h2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
      (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
        ((inf_le_left : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
          parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J)).trans
          (parabolicRadical_le_posUnipotent _))
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₀C).symm
  have hPQ₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
  have hPJ : parTri K σ J ≤ Subgroup.normalizer ((radTri K σ J : Subgroup ↥(graphFixedRootGroup
      TwistTag.D4 K σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := hPQ₀ (Subgroup.mem_subgroupOf.1 hx)
    simp only [radTri, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  have hN : ∀ x ∈ Subgroup.normalizer (Q : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ * x * ⟨g, hg⟩ ∈
        parTri K σ J :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype hx))
  have hQ : ∀ q ∈ Q, (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ * q *
      ⟨g, hg⟩ ∈ radTri K σ J :=
    fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    hcore hQJ2 hPJ hN hQ
  set γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ with hγ
  set R' : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hQmap : Q.map γ.toMonoidHom = radTri K σ J := hQ'
  have hQR' : ∀ α' ∈ R', (radTri K σ J).map α'.toMonoidHom = radTri K σ J := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom :=
      MonoidHom.ext fun y => congrArg γ (congrArg α (MulAut.inv_apply_self _ γ y))
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ parTri K σ J := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := (MulAut.inv_apply_self _ γ _).symm
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup ↥(graphFixedRootGroup
        TwistTag.D4 K σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', MulAut.apply_inv_self _ γ x⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have key := autCentralizer_inf_radC_eq_bot σ hσ3 hNF J hp hp2 hR'p hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ radTri K σ J := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      have h := hzC α hα
      change (γ * α * γ⁻¹) (γ z) = γ z
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h]
    · rw [← hQmap]
      exact Subgroup.mem_map_of_mem _ hzQ
  rw [key] at hz1
  exact Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff γ).1 (Subgroup.mem_bot.1 hz1))

end Cert

end CFSG.LieType.ChevTwo.Semi
