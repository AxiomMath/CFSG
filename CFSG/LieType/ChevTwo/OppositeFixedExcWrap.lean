module

public import CFSG.LieType.ChevTwo.OppositeFixedExcBase

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LieType.BorelTits

theorem oppositeFixed_of_family {K' : Type} [Group K'] [Finite K'] {ι : Type*}
    (QJ PJ : ι → Subgroup K') (hQJ2 : ∀ j, IsPGroup 2 (QJ j))
    (hPJ : ∀ j, PJ j ≤ Subgroup.normalizer ((QJ j : Subgroup K') : Set K'))
    (hstd : ∀ Q : Subgroup K', Q ≠ ⊥ → IsPGroup 2 Q → ∃ (g : K') (j : ι),
      (∀ x ∈ Subgroup.normalizer (Q : Set K'), g⁻¹ * x * g ∈ PJ j) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈ QJ j)
    (hcore : ∀ (j : ι) (p : ℕ), p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K'), IsPGroup p R →
      (∀ α ∈ R, (QJ j).map α.toMonoidHom = QJ j) →
        Subgroup.normalizer ((QJ j : Subgroup K') : Set K') = PJ j →
          autCentralizer R ≤ PJ j → autCentralizer R ⊓ QJ j = ⊥) :
    OppositeFixed K' := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore' hne hRQ hC
  obtain ⟨g, j, hN, hQ⟩ := hstd Q hQ0 hQ2
  obtain ⟨hQ', hNQ⟩ := std_position g hcore' (hQJ2 j) (hPJ j) hN hQ
  set γ : MulAut K' := MulAut.conj g⁻¹ with hγ
  set R' : Subgroup (MulAut K') := R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hQmap : Q.map γ.toMonoidHom = QJ j := hQ'
  have hQR' : ∀ α' ∈ R', (QJ j).map α'.toMonoidHom = QJ j := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom := by
      ext x; simp [MulAut.conj_apply]
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ PJ j := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := by simpa [MulAut.conj_apply] using h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := by simp
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set K') := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup K') : Set K') := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', by simp⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have key := hcore j p hp hp2 R' hR'p hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ QJ j := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      have h := hzC α hα
      change (γ * α * γ⁻¹) (γ z) = γ z
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h]
    · rw [← hQmap]
      exact Subgroup.mem_map_of_mem _ hzQ
  rw [key] at hz1
  exact Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff γ).1 (Subgroup.mem_bot.1 hz1))

end CFSG.LieType.ChevTwo
