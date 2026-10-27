module

public import CFSG.LieType.ChevTwo.OppCl.D4Core

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits

section Cert

variable
    {K : Type} [Field K] [Finite K] [CharP K 2]

theorem oppositeFixed_adjointGroup_D4 : OppositeFixed ↥(adjointGroup Tag.D4 K) := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore hne hRQ hC
  classical
  have hfinM : Finite (ModGL Tag.D4 K) := finite_modGL
  have hQ₀ne : Q.map (adjointGroup Tag.D4 K).subtype ≠ ⊥ := fun h =>
    hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q (adjointGroup Tag.D4 K).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_ordinary (Subgroup.map_subtype_le Q)
    (hQ2.map (adjointGroup Tag.D4 K).subtype) hQ₀ne
  have hQJle : parabolicRadical Tag.D4 K J ≤ adjointGroup Tag.D4 K :=
    fun x hx => rootSpan_le_adjointGroup K _ hx
  have hQJ2 : IsPGroup 2 (radG Tag.D4 K J) := by
    have h2 : IsPGroup 2 (parabolicRadical Tag.D4 K J) :=
      (isPGroup_posUnipotent 2 Tag.D4).to_le (parabolicRadical_le_posUnipotent J)
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hQJle).symm
  have hPJ : parG Tag.D4 K J ≤ Subgroup.normalizer ((radG Tag.D4 K J : Subgroup ↥(adjointGroup
      Tag.D4 K)) : Set ↥(adjointGroup Tag.D4 K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := parabolicSubgroup_le_normalizer_parabolicRadical J (Subgroup.mem_subgroupOf.1 hx)
    simp only [radG, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  have hN : ∀ x ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup Tag.D4 K)),
      (⟨g, hg⟩ : ↥(adjointGroup Tag.D4 K))⁻¹ * x * ⟨g, hg⟩ ∈ parG Tag.D4 K J :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype hx))
  have hQ : ∀ q ∈ Q, (⟨g, hg⟩ : ↥(adjointGroup Tag.D4 K))⁻¹ * q * ⟨g, hg⟩ ∈
      radG Tag.D4 K J := fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(adjointGroup Tag.D4 K)) hcore hQJ2 hPJ hN hQ
  set γ : MulAut ↥(adjointGroup Tag.D4 K) :=
    MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup Tag.D4 K))⁻¹ with hγ
  set R' : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)) := R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hQmap : Q.map γ.toMonoidHom = radG Tag.D4 K J := hQ'
  have hQR' : ∀ α' ∈ R', (radG Tag.D4 K J).map α'.toMonoidHom = radG Tag.D4 K J := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom := by
      ext x; simp [MulAut.conj_apply]
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ parG Tag.D4 K J := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := by simpa [MulAut.conj_apply] using h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := by simp
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup Tag.D4 K)) := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup ↥(adjointGroup
        Tag.D4 K)) : Set ↥(adjointGroup Tag.D4 K)) := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', by simp⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have key := autCentralizer_inf_radG_eq_bot_D4 J hp hp2 hR'p hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ radG Tag.D4 K J := by
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
