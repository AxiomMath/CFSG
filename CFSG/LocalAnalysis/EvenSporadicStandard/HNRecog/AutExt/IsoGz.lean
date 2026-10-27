module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Cosets
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Extend
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OuterLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.QzMem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Uniq

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem exists_iso_Gz (h : F5Std a z) (h' : F5Std a' z') {w : G} {w' : G'} (hw : IsConj z w)
    (hw' : IsConj z' w') : ∃ γ : G → G', IsIsoOn (Gx w) (Gx w') γ := by
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw
  have hF' : F5Std a' w' := h'.of_isConj (IsConj.refl a') hw'
  haveI : Finite G := h.finite
  haveI : Finite G' := h'.finite
  obtain ⟨Q, hQn, hAH⟩ := hF.loc.gz9.self.aschbacher
  haveI : Q.Normal := hQn
  obtain ⟨Q', hQ'n, hAH'⟩ := hF'.loc.gz9.self.aschbacher
  haveI : Q'.Normal := hQ'n
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.HNRecog.aschbacherUniq
    ↥(Gx w) ↥(Gx w') Q Q' hAH hAH'
  obtain ⟨f, hf, _⟩ := exists_isIsoOn_of_mulEquiv e
  exact ⟨f, hf⟩

theorem exists_iso_Gz_fix (h : F5Std a z) (h' : F5Std a' z') {w x : G} {w' x' : G'}
    (hw : IsConj z w) (hx : IsConj a x) (hwx : IsConj z (w * x)) (hw' : IsConj z' w')
    (hx' : IsConj a' x') (hwx' : IsConj z' (w' * x')) :
    ∃ γ : G → G', IsIsoOn (Gx w) (Gx w') γ ∧ γ x = x' := by
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw
  have hF' : F5Std a' w' := h'.of_isConj (IsConj.refl a') hw'
  have hxw : x ∈ Gx w := mem_Gx.2 (h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inr hwx))
  have hxw' : x' ∈ Gx w' := mem_Gx.2 (h'.mul_comm (Or.inr hw') (Or.inl hx') (Or.inr hwx'))
  have hxQ : x ∉ Qz w := not_mem_Qz_of_isConj_mul h hw hx hwx
  have hx'Q : x' ∉ Qz w' := not_mem_Qz_of_isConj_mul h' hw' hx' hwx'
  have hxD : x ∉ derivedOf (Gx w) := not_mem_derived_of_outer_2A hF hxw hxQ hx
  have hx'D : x' ∉ derivedOf (Gx w') := not_mem_derived_of_outer_2A hF' hxw' hx'Q hx'
  obtain ⟨γ₀, hγ₀⟩ := exists_iso_Gz h h' hw hw'
  have hy_mem : γ₀ x ∈ Gx w' := hγ₀.mem x hxw
  have hy_ord : orderOf (γ₀ x) = 2 := by
    rw [hγ₀.orderOf_eq hxw, h.orderOf_eq_two (Or.inl hx)]
  have hy2 : (γ₀ x) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (γ₀ x)
    rw [hy_ord] at h
    simpa using h
  have hyD : γ₀ x ∉ derivedOf (Gx w') := by
    intro hyDmem
    obtain ⟨u, hu_mem, hu_eq⟩ := (hγ₀.derived).surjOn (γ₀ x) hyDmem
    have huGx : u ∈ Gx w := derivedOf_le (Gx w) hu_mem
    exact hxD ((hγ₀.injOn u huGx x hxw hu_eq) ▸ hu_mem)
  obtain ⟨k, hk, q, hq, hkq⟩ :=
    exists_conj_mem_coset hF' hxw' hx'Q hx' hy_mem hy2 hyD
  have hy1_mem : k * (γ₀ x) * k⁻¹ ∈ Gx w' :=
    (Gx w').mul_mem ((Gx w').mul_mem hk hy_mem) ((Gx w').inv_mem hk)
  have hy1_ord : orderOf (k * (γ₀ x) * k⁻¹) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj k) (γ₀ x)
    simpa [MulAut.conj_apply, hy_ord] using h
  have hy1_coset : ∃ q ∈ Qz w', k * (γ₀ x) * k⁻¹ = x' * q := ⟨q, hq, hkq⟩
  have hcase := involution_in_coset h' hw' hx' hwx' hy1_coset hy1_ord
  rcases hcase with ⟨m, hm, hmx⟩ | ⟨m, hm, hmx⟩
  · refine exists_isIsoOn_fix hγ₀ ⟨m⁻¹ * k, ?_, ?_⟩
    · exact (Gx w').mul_mem ((Gx w').inv_mem hm) hk
    · have hmx' : k * (γ₀ x) * k⁻¹ = m * x' * m⁻¹ := hmx.symm
      calc (m⁻¹ * k) * (γ₀ x) * (m⁻¹ * k)⁻¹
          = m⁻¹ * (k * (γ₀ x) * k⁻¹) * m := by group
        _ = m⁻¹ * (m * x' * m⁻¹) * m := by rw [hmx']
        _ = x' := by group
  · have hconj : ConjIn (Gx w') (γ₀ x) (x' * w') := by
      refine ⟨m⁻¹ * k, (Gx w').mul_mem ((Gx w').inv_mem hm) hk, ?_⟩
      have hmx' : k * (γ₀ x) * k⁻¹ = m * (x' * w') * m⁻¹ := hmx.symm
      calc (m⁻¹ * k) * (γ₀ x) * (m⁻¹ * k)⁻¹
          = m⁻¹ * (k * (γ₀ x) * k⁻¹) * m := by group
        _ = m⁻¹ * (m * (x' * w') * m⁻¹) * m := by rw [hmx']
        _ = x' * w' := by group
    obtain ⟨γ₁, hγ₁, hγ₁x⟩ := exists_isIsoOn_fix hγ₀ hconj
    have hw'2 : w' * w' = 1 := by
      have h := pow_orderOf_eq_one w'
      rw [hF'.orderOf_eq_two (Or.inr (IsConj.refl w'))] at h
      simpa [pow_two] using h
    have hw'D : w' ∈ derivedOf (Gx w') := (derived_Gx_z hF').1
    have hx'w'_mem : x' * w' ∈ Gx w' := (Gx w').mul_mem hxw' (self_mem_Gx w')
    have hx'w'_notD : x' * w' ∉ derivedOf (Gx w') := by
      intro hmem
      apply hx'D
      have h1 : (x' * w') * w'⁻¹ ∈ derivedOf (Gx w') :=
        (derivedOf (Gx w')).mul_mem hmem ((derivedOf (Gx w')).inv_mem hw'D)
      rwa [mul_inv_cancel_right] at h1
    obtain ⟨τ, hτ, _, hτout⟩ := exists_tau hF' (Or.inr (IsConj.refl w'))
    have hτx' : τ (x' * w') = x' := by
      rw [hτout (x' * w') hx'w'_mem hx'w'_notD, mul_assoc, hw'2, mul_one]
    exact ⟨τ ∘ γ₁, hγ₁.comp hτ, by rw [Function.comp_apply, hγ₁x, hτx']⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
