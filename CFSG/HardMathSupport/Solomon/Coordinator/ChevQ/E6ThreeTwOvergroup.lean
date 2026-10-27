module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Exists
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwClose

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwOvergroup



section Overgroup

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}

theorem mem_twR_of_entries_of_twGens (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) {J₀ : Subgroup ↥(twistedE6RootGroup K σ)}
    (hJ₀ : J₀ ≤ twR σ η) (hgen : TwGens σ η (J₀.map (twIncl σ)))
    (g : ↥(twistedE6RootGroup K σ))
    (hall : ∀ r ∈ J₀, ∀ r' ∈ J₀,
      entry (twIncl σ (r * g * r')) (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield η) :
    g ∈ twR σ η := by
  classical
  set Z := vanishSub (J₀.map (twIncl σ)) (negLabel hθ.1) with hZ
  set gP : ↥(adjointGroup Tag.E6 K) := twIncl σ g with hgP
  set g₂ : ↥(adjointGroup Tag.E6 K) := entrywiseAdjointAut Tag.E6 η gP with hg₂
  have hRfix : ∀ r ∈ J₀, entrywiseAdjointAut Tag.E6 η (twIncl σ r) = twIncl σ r :=
    fun r hr => (mem_twR_iff σ η r).1 (hJ₀ hr)
  have hent : ∀ r ∈ J₀, ∀ r' ∈ J₀,
      entry (twIncl σ r * g₂ * twIncl σ r') (negLabel hθ.1) (rootLabel hθ.1) =
        entry (twIncl σ r * gP * twIncl σ r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : twIncl σ r * g₂ * twIncl σ r' =
        entrywiseAdjointAut Tag.E6 η (twIncl σ r * gP * twIncl σ r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    have := hall r hr r' hr'
    rw [map_mul, map_mul] at this
    exact (mem_fixSubfield η).1 this
  have hDmem : ∀ r' ∈ J₀,
      (endHom K g₂ - endHom K gP) (endHom K (twIncl σ r') (rootVec Tag.E6 K θ)) ∈ Z := by
    intro r' hr'
    rw [hZ, mem_vanishSub]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hx
    have hv : rootVec Tag.E6 K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply,
      ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hspan := twE6_span_orbit_eq_top hS hθ hgen
  have hle : Submodule.span K
      {x | ∃ r ∈ J₀.map (twIncl σ), x = endHom K r (rootVec Tag.E6 K θ)} ≤
      Z.comap (endHom K g₂ - endHom K gP) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    obtain ⟨r'', hr'', rfl⟩ := Subgroup.mem_map.1 hr'
    exact hDmem r'' hr''
  rw [hspan] at hle
  have hDV : ∀ v, (endHom K g₂ - endHom K gP) v ∈ Z := fun v => hle (Submodule.mem_top (x := v))
  have hx : ∀ v : RootModule Tag.E6 K, endHom K (g₂ * gP⁻¹) v - v ∈ Z := by
    intro v
    have h1 := hDV (endHom K gP⁻¹ v)
    have e1 : endHom K gP (endHom K gP⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact h1
  have h1 := eq_one_of_sub_mem_fixed hS.four_le_card hθ Z
    (twE6_vanishSub_fixed hS hθ hgen) (g₂ * gP⁻¹) hx
  have h2 : g₂ = gP := mul_inv_eq_one.1 h1
  rw [mem_twR_iff]
  exact h2

theorem exists_bad_entry_of_twGens (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ) {J₀ : Subgroup ↥(twistedE6RootGroup K σ)}
    (hJ₀ : J₀ ≤ twR σ η) (hgen : TwGens σ η (J₀.map (twIncl σ)))
    (g : ↥(twistedE6RootGroup K σ)) (hg : g ∉ twR σ η) :
    ∃ r ∈ J₀, ∃ r' ∈ J₀,
      entry (twIncl σ (r * g * r')) (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield η := by
  by_contra h
  push Not at h
  exact hg (mem_twR_of_entries_of_twGens hS hθ hJ₀ hgen g h)

private theorem twE6X2_map_u2 (c : ↥(fixSubfield σ)) :
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype (u2 c) = u2 (c : K) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, u2_coe, u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

private theorem twE6X2_map_l2 (c : ↥(fixSubfield σ)) :
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype (l2 c) = l2 (c : K) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, l2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

private theorem twE6X2_aux (hS : TwE6Setup K σ η p) {θ : Fin Tag.E6.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.E6 θ)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)))
    {H : Subgroup ↥(twistedE6RootGroup K σ)}
    (hxR : ∀ c : K, σ c = c → η c = c → xE6 θ c ∈ H.map (twIncl σ))
    {g : ↥(twistedE6RootGroup K σ)} (hgH : g ∈ H)
    (hbad : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield η) :
    ∃ t : K, σ t = t ∧ η t ≠ t ∧ xE6 θ t ∈ H.map (twIncl σ) := by
  have hlamσ : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ :=
    twE6_entry_mem_fixSubfield hθ g
  have hlam0 : entry (twIncl σ g) (negLabel hθ.1) (rootLabel hθ.1) ≠ 0 :=
    fun h => hbad (h ▸ (fixSubfield η).zero_mem)
  obtain ⟨ψ, μ₁, μ₂, hμ₁, hμμ, hbig⟩ :=
    bigCell' (τ := Tag.E6) (Or.inl rfl) hθ (twIncl σ g) hlam0
  have hF : μ₁ * μ₂ ∈ fixSubfield σ := by
    rcases hμμ with hμ | hμ
    · rw [hμ]
      exact hlamσ
    · rw [hμ]
      exact neg_mem hlamσ
  have hlam'' : (1 : ↥(fixSubfield σ)) * (⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ)) ∉
      fixSubfield (fixSubfieldRestrict η σ) := by
    intro h
    rw [mem_fixSubfield, one_mul] at h
    have h' : η (μ₁ * μ₂) = μ₁ * μ₂ := congrArg Subtype.val h
    apply hbad
    rw [mem_fixSubfield]
    rcases hμμ with hμ | hμ
    · rw [hμ] at h'
      exact h'
    · rw [hμ, map_neg] at h'
      exact neg_injective h'
  obtain ⟨ψ', hψ'u, hψ'l⟩ : ∃ ψ' : Matrix.SpecialLinearGroup (Fin 2) ↥(fixSubfield σ) →*
      ↥(adjointGroup Tag.E6 K),
      (∀ c : ↥(fixSubfield σ), ψ' (u2 c) = xE6 θ (c : K)) ∧
      (∀ c : ↥(fixSubfield σ), ψ' (l2 ((⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ)) * c)) =
        twIncl σ g * xE6 θ (c : K) * (twIncl σ g)⁻¹) := by
    refine ⟨(ψ.comp (diagConj μ₁ hμ₁)).comp
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype), ?_, ?_⟩
    · intro c
      simp only [MonoidHom.comp_apply]
      rw [twE6X2_map_u2, diagConj_u2]
      exact (hbig (c : K)).1
    · intro c
      simp only [MonoidHom.comp_apply]
      rw [twE6X2_map_l2]
      show ψ (diagConj μ₁ hμ₁ (l2 (μ₁ * μ₂ * (c : K)))) = _
      rw [diagConj_l2]
      have e : μ₁⁻¹ * (μ₁ * μ₂ * (c : K)) = μ₂ * (c : K) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ₁, one_mul]
      rw [e]
      exact (hbig (c : K)).2
  have hgP : twIncl σ g ∈ H.map (twIncl σ) := Subgroup.mem_map_of_mem _ hgH
  have hconj : ∀ c : K, σ c = c → η c = c →
      twIncl σ g * xE6 θ c * (twIncl σ g)⁻¹ ∈ H.map (twIncl σ) := fun c hc hηc =>
    (H.map (twIncl σ)).mul_mem ((H.map (twIncl σ)).mul_mem hgP (hxR c hc hηc))
      ((H.map (twIncl σ)).inv_mem hgP)
  have hD' : ringChar ↥(fixSubfield σ) ≠ 2 ∨
      4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)) := by
    rw [ringChar_fixSubfield]
    exact hD
  have hσ' : orderOf (fixSubfieldRestrict η σ) = p := hS.orderOf_restrict
  have hu : ∀ c ∈ fixSubfield (fixSubfieldRestrict η σ),
      ψ' (u2 (1 * c)) ∈ H.map (twIncl σ) := by
    intro c hc
    have hc' : η (c : K) = (c : K) := congrArg Subtype.val ((mem_fixSubfield _).1 hc)
    rw [one_mul, hψ'u]
    exact hxR (c : K) ((mem_fixSubfield _).1 c.2) hc'
  have hl : ∀ c ∈ fixSubfield (fixSubfieldRestrict η σ),
      ψ' (l2 ((⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ)) * c)) ∈ H.map (twIncl σ) := by
    intro c hc
    have hc' : η (c : K) = (c : K) := congrArg Subtype.val ((mem_fixSubfield _).1 hc)
    rw [hψ'l c]
    exact hconj (c : K) ((mem_fixSubfield _).1 c.2) hc'
  have hne1 : fixSubfieldRestrict η σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ'
    have := hS.two_lt
    omega
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥(fixSubfield σ), fixSubfieldRestrict η σ c₀ ≠ c₀ := by
    by_contra h
    push Not at h
    exact hne1 (RingEquiv.ext h)
  have key := sl2_hom_mem_of_pair (K := ↥(fixSubfield σ)) (fixSubfieldRestrict η σ) hS.prime
    hS.ne_two hσ' hD' (H := H.map (twIncl σ)) ψ' 1 (⟨μ₁ * μ₂, hF⟩ : ↥(fixSubfield σ))
    one_ne_zero hlam'' hu hl c₀
  rw [one_mul, hψ'u] at key
  exact ⟨(c₀ : K), (mem_fixSubfield _).1 c₀.2, fun h => hc₀ (Subtype.ext h), key⟩

theorem le_twR_or_eq_top_of_twGens (hS : TwE6Setup K σ η p)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)))
    {J₀ : Subgroup ↥(twistedE6RootGroup K σ)} (hJ₀ : J₀ ≤ twR σ η)
    (hgen : TwGens σ η (J₀.map (twIncl σ))) {H : Subgroup ↥(twistedE6RootGroup K σ)}
    (hH : J₀ ≤ H) : H ≤ twR σ η ∨ H = ⊤ := by
  by_cases hle : H ≤ twR σ η
  · exact Or.inl hle
  right
  obtain ⟨g, hgH, hg⟩ := SetLike.not_le_iff_exists.1 hle
  obtain ⟨θ, hθ⟩ := exists_maxHeightRoot Tag.E6
  have hgenH : TwGens σ η (H.map (twIncl σ)) := hgen.mono (Subgroup.map_mono hH)
  have hxR : ∀ c : K, σ c = c → η c = c → xE6 θ c ∈ H.map (twIncl σ) := by
    intro c hc hηc
    obtain ⟨n, hn, ε, hε, hconj⟩ := twE6_theta_conj_of_twGens hgenH hθ
    have hεc : σ ((ε : K) * c) = (ε : K) * c ∧ η ((ε : K) * c) = (ε : K) * c := by
      rcases hε with rfl | rfl <;> simp [hc, hηc]
    have h3 : n * xE6 θ c * n⁻¹ ∈ H.map (twIncl σ) := by
      rw [hconj c]
      exact hgenH.fixedX 3 (by decide) ((ε : K) * c) hεc.1 hεc.2
    have e : xE6 θ c = n⁻¹ * (n * xE6 θ c * n⁻¹) * n := by group
    rw [e]
    exact (H.map (twIncl σ)).mul_mem
      ((H.map (twIncl σ)).mul_mem ((H.map (twIncl σ)).inv_mem hn) h3) hn
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_of_twGens hS hθ hJ₀ hgen g hg
  have hgH' : r * g * r' ∈ H := H.mul_mem (H.mul_mem (hH hr) hgH) (hH hr')
  obtain ⟨t, hσt, hηt, ht⟩ := twE6X2_aux hS hθ hD hxR hgH' hbad
  exact twE6_eq_top_of_twGens hS hθ H hgenH hσt hηt ht

end Overgroup

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwOvergroup
