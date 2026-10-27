module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupInner
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisFusion

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

abbrev fixPSL (W : Subgroup (PGammaL2 F)) : Subgroup (PSL2 F) :=
  (centralizer (W : Set (PGammaL2 F))).comap (incl F)

abbrev fourFixSup (E : Subgroup (PGammaL2 F)) : Subgroup (PSL2 F) :=
  ⨆ (W : Subgroup (PGammaL2 F)) (_ : W ≤ E) (_ : Nat.card W = 4), fixPSL W

theorem mem_fourFixSup_of {E : Subgroup (PGammaL2 F)} {x y : PGammaL2 F} (hx : x ∈ E)
    (hy : y ∈ E) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x * y = y * x)
    (hne : x ≠ y) {s : PSL2 F} (hsx : x * incl F s = incl F s * x)
    (hsy : y * incl F s = incl F s * y) : s ∈ fourFixSup E := by
  obtain ⟨V, hVle, -, hV4⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hx2 hy2 hxy hne
  have hVE : V ≤ E := hVle.trans ((closure_le E).mpr (by
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy))
  have hVC : V ≤ centralizer ({incl F s} : Set (PGammaL2 F)) := hVle.trans ((closure_le _).mpr (by
    rintro _ (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr hsx
    · exact mem_centralizer_singleton_iff.mpr hsy))
  have hsV : s ∈ fixPSL V := by
    change incl F s ∈ centralizer (V : Set (PGammaL2 F))
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hVC hh)
  exact (show fixPSL V ≤ fourFixSup E from le_iSup₂_of_le V hVE (le_iSup_of_le hV4 le_rfl)) hsV

theorem card_linearPart_of_card_eight (hodd : IsOddPrimePower (Nat.card F))
    {E : Subgroup (PGammaL2 F)} (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8) :
    Nat.card (linearPart E) = 4 := by
  have h1 : Nat.card (linearPart E) ≤ 4 :=
    pgl2_card_le_four_of_sq hodd _ fun g hg => SemidirectProduct.inl_injective (by
      rw [map_mul, map_one]; exact hE2 _ hg)
  have h2 : Nat.card (E.map (fieldProj F)) ≤ 2 := card_le_two_of_sq_ringAut _ (by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, hE2 y hy, map_one])
  have h3 := card_eq_linearPart_mul E
  rw [hE8] at h3
  interval_cases h : Nat.card (E.map (fieldProj F)) <;> omega

theorem centralizer_tor_neg_one_le_fourFixSup (hodd : IsOddPrimePower (Nat.card F))
    {E : Subgroup (PGammaL2 F)} (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8)
    (hz : SemidirectProduct.inl (tor F (-1)) ∈ E) {s : PSL2 F}
    (hs : incl F s * SemidirectProduct.inl (tor F (-1)) =
      SemidirectProduct.inl (tor F (-1)) * incl F s) : s ∈ fourFixSup E := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower hodd
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    commute_of_forall_sq E hE2 ha hb
  have hnmE : ∀ x ∈ E, ∃ a ε, x = nm F a ε x.right := fun x hx =>
    (commute_tor_neg_one_iff h2 x).mp (hcommE x hx _ hz)
  have horder : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hE2 x hx) hx1
  have hz1 : SemidirectProduct.inl (tor F (-1)) ≠ (1 : PGammaL2 F) := fun h =>
    tor_neg_one_ne_one h2 (SemidirectProduct.inl_injective (h.trans (map_one _).symm))
  have hz2 := horder _ hz hz1
  obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E hE2 hE8.ge
  have hψ2 : x₀.right * x₀.right = 1 := by
    have := congrArg SemidirectProduct.right (hE2 x₀ hx₀E)
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at this
  have hψo : orderOf x₀.right = 2 := orderOf_eq_prime (by rw [pow_two]; exact hψ2) hx₀r
  obtain ⟨K₀, hK₀, hcard, -⟩ := exists_fixed_subfield x₀.right hψo
  have hsqK : ∀ y : Fˣ, fu F x₀.right y = y → IsSquare (y : F) := fun y hy =>
    isSquare_of_mem_fixed hcard hodd ⟨y, (hK₀ y).mpr (congrArg Units.val hy)⟩
  have hsq : IsSquare (-1 : F) := by
    have := hsqK (-1) (fu_neg_one x₀.right)
    simpa using this
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀r (by rw [h]; rfl)
  obtain ⟨A₁, hA₁, A₂, hA₂, hA₁1, hA₂1, hA₁₂⟩ :=
    exists_two_ne_of_card_four (linearPart E) (card_linearPart_of_card_eight hodd hE2 hE8)
  obtain ⟨A, hAE, hA1, hAz⟩ : ∃ A : PGL2 F, SemidirectProduct.inl A ∈ E ∧ A ≠ 1 ∧
      A ≠ tor F (-1) := by
    by_cases h : A₁ = tor F (-1)
    · exact ⟨A₂, hA₂, hA₂1, fun h' => hA₁₂ (h.trans h'.symm)⟩
    · exact ⟨A₁, hA₁, hA₁1, h⟩
  have hv1 : (SemidirectProduct.inl A : PGammaL2 F) ≠ 1 := fun h =>
    hA1 (SemidirectProduct.inl_injective (h.trans (map_one _).symm))
  obtain ⟨b', ε', hv⟩ := hnmE _ hAE
  rw [SemidirectProduct.right_inl] at hv
  have hε' : ε' = true := by
    by_contra hne
    have hf : ε' = false := by simpa using hne
    rw [hf, ← inl_tor] at hv
    have hAt : A = tor F b' := SemidirectProduct.inl_injective hv
    have hb2 : b' ^ 2 = 1 := by
      apply pGammaL2FullSplitTorus_injective F
      rw [map_pow, map_one, ← hAt, pow_two]
      exact SemidirectProduct.inl_injective (by rw [map_mul, map_one]; exact hE2 _ hAE)
    rcases units_eq_one_or_neg_one hb2 with h | h
    · exact hA1 (by rw [hAt, h, map_one])
    · exact hAz (by rw [hAt, h])
  rw [hε'] at hv
  have hvPSL : SemidirectProduct.inl A ∈ pGammaL2PSLRange F := by
    have hx₀v : x₀ * SemidirectProduct.inl A ∈ E := E.mul_mem hx₀E hAE
    have hr : (x₀ * SemidirectProduct.inl A).right ≠ 1 := by
      rwa [SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one]
    have hs1 := sqLeft_of_involution hodd (horder _ hx₀E hx₀1) hx₀r
    have hs2 := sqLeft_of_involution hodd (horder _ hx₀v (fun h => hr (by rw [h]; rfl))) hr
    rw [mem_pslRange_iff]
    exact ⟨SemidirectProduct.right_inl A, ((sqLeft_mul _ _).mp hs2).mp hs1⟩
  obtain ⟨c₀, ε₀, hx₀⟩ := hnmE x₀ hx₀E
  have hvx₀ : SemidirectProduct.inl A * x₀ = nm F (b' * (c₀)⁻¹) (!ε₀) x₀.right := by
    rw [hv, hx₀, nm_mul]
    simp [fu_one]
  have hpair : ∀ ε : Bool, ∃ c : Fˣ, nm F c ε x₀.right ∈ E := by
    intro ε
    by_cases h : ε = ε₀
    · exact ⟨c₀, by rw [h, ← hx₀]; exact hx₀E⟩
    · refine ⟨b' * (c₀)⁻¹, ?_⟩
      have : ε = !ε₀ := by revert h; cases ε <;> cases ε₀ <;> decide
      rw [this, ← hvx₀]
      exact E.mul_mem hAE hx₀E
  obtain ⟨cf, hcf⟩ := hpair false
  obtain ⟨ct, hct⟩ := hpair true
  have hne_nm : ∀ (c : Fˣ) (ε : Bool), SemidirectProduct.inl (tor F (-1)) ≠ nm F c ε x₀.right :=
    fun c ε h => hx₀r (by
      have := congrArg SemidirectProduct.right h
      rw [SemidirectProduct.right_inl, nm_right] at this
      exact this.symm)
  have hord_nm : ∀ (c : Fˣ) (ε : Bool), nm F c ε x₀.right ∈ E → orderOf (nm F c ε x₀.right) = 2 :=
    fun c ε h => horder _ h (fun h1 => hx₀r (by
      have := congrArg SemidirectProduct.right h1
      rwa [nm_right, SemidirectProduct.one_right] at this))
  have htorus : ∀ (t : PSL2 F) (b : Fˣ), incl F t = nm F b false 1 → t ∈ fourFixSup E := by
    intro t b ht
    have hb : IsSquare (b : F) := by
      have h1 := congrArg SemidirectProduct.left ht
      rw [incl_apply, SemidirectProduct.left_inl, nm_left, swp_false, mul_one] at h1
      exact (tor_mem_range_iff b).mp ⟨t, h1⟩
    obtain ⟨d₀, hd₀⟩ := hb
    have hd₀0 : d₀ ≠ 0 := by
      rintro rfl
      exact b.ne_zero (by rw [hd₀, mul_zero])
    set d : Fˣ := Units.mk0 d₀ hd₀0 with hd
    set ψ := x₀.right with hψ
    set μ₁ : Fˣ := d * fu F ψ d with hμ₁def
    set μ₂ : Fˣ := d * (fu F ψ d)⁻¹ with hμ₂def
    have hμ : μ₁ * μ₂ = b := by
      rw [hμ₁def, hμ₂def, mul_mul_mul_comm, mul_inv_cancel, mul_one]
      exact Units.ext (by rw [Units.val_mul, Units.val_mk0, hd₀])
    have hμ₁ : fu F ψ μ₁ = μ₁ := by
      rw [hμ₁def, map_mul, ← fu_mul, hψ2, fu_one, mul_comm]
    have hμ₂ : fu F ψ μ₂ = μ₂⁻¹ := by
      rw [hμ₂def, map_mul, map_inv, ← fu_mul, hψ2, fu_one, mul_inv_rev, inv_inv]
    have hsq₁ : IsSquare (μ₁ : F) := hsqK μ₁ hμ₁
    have hsq₂ : IsSquare (μ₂ : F) := by
      have hb' : IsSquare ((μ₁ : F) * μ₂) := by
        rw [← Units.val_mul, hμ, hd₀]
        exact ⟨d₀, rfl⟩
      exact ((isSquare_mul_iff μ₁.ne_zero μ₂.ne_zero).mp hb').mp hsq₁
    obtain ⟨t₁, ht₁⟩ := nm_mem_pslRange hsq hsq₁ false
    obtain ⟨t₂, ht₂⟩ := nm_mem_pslRange hsq hsq₂ false
    change incl F t₁ = nm F μ₁ false 1 at ht₁
    change incl F t₂ = nm F μ₂ false 1 at ht₂
    have hteq : t = t₁ * t₂ := by
      apply incl_injective F
      rw [map_mul, ht₁, ht₂, nm_mul, ht]
      simp only [twist_false, fu_one, Bool.xor_false, mul_one, hμ]
    have hzt : ∀ μ : Fˣ, SemidirectProduct.inl (tor F (-1)) * nm F μ false 1 =
        nm F μ false 1 * SemidirectProduct.inl (tor F (-1)) := fun μ => by
      rw [inl_tor, nm_commute_tor_iff]
      rfl
    rw [hteq]
    refine mul_mem (mem_fourFixSup_of hz hcf hz2 (hord_nm _ _ hcf) (hcommE _ hz _ hcf)
      (hne_nm _ _) (by rw [ht₁]; exact hzt μ₁) ?_)
      (mem_fourFixSup_of hz hct hz2 (hord_nm _ _ hct) (hcommE _ hz _ hct)
      (hne_nm _ _) (by rw [ht₂]; exact hzt μ₂) ?_)
    · rw [ht₁, nm_commute_tor_iff]
      exact hμ₁
    · rw [ht₂, nm_commute_tor_iff, hμ₂]
      exact inv_inv μ₂
  have hsr : (incl F s).right = 1 := by rw [incl_apply, SemidirectProduct.right_inl]
  obtain ⟨b, ε, hsb⟩ := (commute_tor_neg_one_iff h2 (incl F s)).mp hs
  rw [hsr] at hsb
  cases ε
  · exact htorus s b hsb
  · obtain ⟨s', hs'⟩ := hvPSL
    change incl F s' = SemidirectProduct.inl A at hs'
    have hsplit : s = (s * s'⁻¹) * s' := by group
    rw [hsplit]
    refine mul_mem (htorus _ (b * (b')⁻¹) ?_) ?_
    · rw [map_mul, map_inv, hs', hsb, hv, nm_inv, nm_mul]
      simp [fu_one]
    · refine mem_fourFixSup_of hz hAE hz2 (horder _ hAE hv1) (hcommE _ hz _ hAE)
        (fun h => hAz (SemidirectProduct.inl_injective h).symm) ?_ ?_
      · rw [hs']
        exact hcommE _ hz _ hAE
      · rw [hs']

end CFSG.ComponentClassification.AutL2Facts
