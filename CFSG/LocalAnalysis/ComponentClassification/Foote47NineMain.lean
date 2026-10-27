module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47NineCent
public import CFSG.LocalAnalysis.ComponentClassification.Foote47NineGrp

public noncomputable section

namespace CFSG.ComponentClassification.Foote47.Nine

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem centralizer_le_fourFixSup
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    {E : Subgroup (PGammaL2 F)} (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8)
    {t : PSL2 F} (htE : incl F t ∈ E) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set (PSL2 F)) ≤ fourFixSup E := by
  obtain ⟨z, hz⟩ := exists_psl2_tor_neg_one hsq
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  have hz2 : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply incl_injective F
      rw [map_pow, hz, ← map_pow, ← map_pow, neg_one_sq, map_one, map_one, map_one]
    · intro h
      apply tor_neg_one_ne_one h2
      have h' : (SemidirectProduct.inl (tor F (-1)) : PGammaL2 F) = SemidirectProduct.inl 1 := by
        rw [← hz, h, map_one, map_one]
      exact SemidirectProduct.inl_injective h'
  have hI : ∀ x : PSL2 F, orderOf x = 2 → BenderSuzuki.PFAppendixIII.IsInvolution x :=
    fun x hx => ⟨fun h => by rw [h, orderOf_one] at hx; omega,
      by have h := pow_orderOf_eq_one x; rwa [hx] at h⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd t z (hI t ht2)
    (hI z hz2)
  set E' := E.map (MulAut.conj (incl F g)).toMonoidHom with hE'
  have hE'2 : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE2 x hx, map_one]
  have hE'8 : Nat.card E' = 8 := by
    rw [hE', card_map_of_injective (MulAut.conj _).injective, hE8]
  have hzE' : SemidirectProduct.inl (tor F (-1)) ∈ E' := by
    refine ⟨incl F t, htE, ?_⟩
    change incl F g * incl F t * (incl F g)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, hg, hz]
  intro s hs
  have hs' : incl F (g * s * g⁻¹) * SemidirectProduct.inl (tor F (-1)) =
      SemidirectProduct.inl (tor F (-1)) * incl F (g * s * g⁻¹) := by
    rw [← hz, ← map_mul, ← map_mul, ← hg]
    congr 1
    have h1 := mem_centralizer_singleton_iff.mp hs
    calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
      _ = g * (t * s) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
  have hmem := centralizer_tor_neg_one_le_fourFixSup hodd hE'2 hE'8 hzE' hs'
  have := map_fourFixSup_conj_le g E ⟨_, hmem, rfl⟩
  change g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ ∈ fourFixSup E at this
  rwa [inv_inv, show g⁻¹ * (g * s * g⁻¹) * g = s by group] at this

theorem card_comap_incl_eq_four
    (hodd : IsOddPrimePower (Nat.card F)) {E : Subgroup (PGammaL2 F)}
    (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8) : Nat.card (E.comap (incl F)) = 4 := by
  obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E hE2 hE8.ge
  have h : (E.comap (incl F)).map (incl F) = (linearPart E).map SemidirectProduct.inl := by
    rw [map_comap_eq]
    ext g
    constructor
    · rintro ⟨⟨s, rfl⟩, hg⟩
      exact ⟨_, hg, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨mem_pslRange_of_right_eq_one hodd hE2 hx₀E hx₀r hA (SemidirectProduct.right_inl A),
        hA⟩
  rw [← card_map_of_injective (incl_injective F), h,
    card_map_of_injective SemidirectProduct.inl_injective,
    card_linearPart_of_card_eight hodd hE2 hE8]

theorem fourFixSup_sup_eq_top_of_nine
    (hF : Nat.card F = 3 ^ 2) {T : Subgroup (PGammaL2 F)} (hT2 : IsPGroup 2 T)
    {E : Subgroup (PGammaL2 F)} (hET : E ≤ T) (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8)
    (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) :
    ∃ E' : Subgroup (PGammaL2 F), E' ≤ T ∧ (∀ x ∈ E', x * x = 1) ∧ Nat.card E' = 8 ∧
      fourFixSup E ⊔ fourFixSup E' = ⊤ := by
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, hF⟩
  have hAut : Nat.card (F ≃+* F) = 2 := card_ringAut F Nat.prime_three hF
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have : Finite (PGammaL2 F) := Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right))
    fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  obtain ⟨E', hE'T, hE'2, hE'8, t, htE, htE', htr, ht1, t₀, ht₀E, ht₀r, u, huE', hur, ht₀u⟩ :=
    exists_e8_pair hodd hAut hT2 hET hE2 hE8 hnab
  refine ⟨E', hE'T, hE'2, hE'8, ?_⟩
  have hsq : IsSquare (-1 : F) :=
    isSquare_neg_one_of_card_sq (f := 1) Nat.prime_three (by norm_num) hF
  have hpre : ∀ {E₀ : Subgroup (PGammaL2 F)}, (∀ x ∈ E₀, x * x = 1) → Nat.card E₀ = 8 →
      ∀ g ∈ E₀, g.right = 1 → ∃ s : PSL2 F, incl F s = g := by
    intro E₀ h2 h8 g hg hgr
    obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E₀ h2 h8.ge
    exact mem_pslRange_of_right_eq_one hodd h2 hx₀E hx₀r hg hgr
  obtain ⟨ts, hts⟩ := hpre hE2 hE8 t htE htr
  obtain ⟨ts₀, hts₀⟩ := hpre hE2 hE8 t₀ ht₀E ht₀r
  obtain ⟨us, hus⟩ := hpre hE'2 hE'8 u huE' hur
  have hord : ∀ {E₀ : Subgroup (PGammaL2 F)}, (∀ x ∈ E₀, x * x = 1) →
      ∀ s : PSL2 F, incl F s ∈ E₀ → s ≠ 1 → orderOf s = 2 := by
    intro E₀ h2 s hs hs1
    refine orderOf_eq_prime ?_ hs1
    apply incl_injective F
    rw [map_pow, pow_two, map_one]
    exact h2 _ hs
  have hts1 : ts ≠ 1 := fun h => ht1 (by rw [← hts, h, map_one])
  have hts₀1 : ts₀ ≠ 1 := fun h => ht₀u (by rw [← hts₀, h, map_one, one_mul, mul_one])
  have hus1 : us ≠ 1 := fun h => ht₀u (by rw [← hus, h, map_one, one_mul, mul_one])
  have htsE : incl F ts ∈ E := by rw [hts]; exact htE
  have htsE' : incl F ts ∈ E' := by rw [hts]; exact htE'
  have hts₀E : incl F ts₀ ∈ E := by rw [hts₀]; exact ht₀E
  have husE' : incl F us ∈ E' := by rw [hus]; exact huE'
  have hc8 : ∀ s : PSL2 F, orderOf s = 2 → Nat.card (centralizer ({s} : Set (PSL2 F))) = 8 := by
    intro s hs
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := ((CFSG.Walter.psl2_centralizer_involution F hF (by decide) (by norm_num) hs).1
      (by norm_num)).1
    rw [h]
    norm_num
  have hcommE : ∀ {E₀ : Subgroup (PGammaL2 F)}, (∀ x ∈ E₀, x * x = 1) →
      ∀ a ∈ E₀.comap (incl F), ∀ b ∈ E₀.comap (incl F), a * b = b * a := by
    intro E₀ h2 a ha b hb
    apply incl_injective F
    rw [map_mul, map_mul]
    exact commute_of_forall_sq E₀ h2 ha hb
  have hsimple : IsSimpleGroup (PSL2 F) :=
    BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hF]; norm_num))
      (Or.inr (by rw [hF]; norm_num))
  have h360 : Nat.card (PSL2 F) = 360 := by
    rw [psl2_card_formula F hodd, hF]
    norm_num
  exact eq_top_of_three_centralizers_le h360 (card_comap_incl_eq_four hodd hE2 hE8)
    (card_comap_incl_eq_four hodd hE'2 hE'8) (hcommE hE2) (hcommE hE'2) htsE htsE' hts1 hts₀E
    husE' (fun h => ht₀u (by rw [← hts₀, ← hus, ← map_mul, h, map_mul]))
    (hc8 ts (hord hE2 ts htsE hts1)) (hc8 ts₀ (hord hE2 ts₀ hts₀E hts₀1))
    (hc8 us (hord hE'2 us husE' hus1))
    ((centralizer_le_fourFixSup hodd hsq hE2 hE8 htsE (hord hE2 ts htsE hts1)).trans le_sup_left)
    ((centralizer_le_fourFixSup hodd hsq hE2 hE8 hts₀E (hord hE2 ts₀ hts₀E hts₀1)).trans
      le_sup_left)
    ((centralizer_le_fourFixSup hodd hsq hE'2 hE'8 husE' (hord hE'2 us husE' hus1)).trans
      le_sup_right)

theorem fourFixSup_map_le {S : Type} [Group S] (e : S ≃* PSL2 F) (E₀ : Subgroup (MulAut S)) :
    fourFixSup (E₀.map (autEquiv e).toMonoidHom) ≤
      (⨆ (W : Subgroup (MulAut S)) (_ : W ≤ E₀) (_ : Nat.card W = 4),
        ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S)).map
          e.toMonoidHom := by
  set Φ := autEquiv e with hΦ
  set HS := ⨆ (W : Subgroup (MulAut S)) (_ : W ≤ E₀) (_ : Nat.card W = 4),
    ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) with hHS
  refine iSup_le fun W' => iSup_le fun hW'E => iSup_le fun hW'4 => ?_
  intro s' hs'
  change incl F s' ∈ centralizer (W' : Set (PGammaL2 F)) at hs'
  set W := W'.map Φ.symm.toMonoidHom with hW
  have hWE : W ≤ E₀ := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hW'E hw
    change Φ.symm (Φ x) ∈ E₀
    rw [MulEquiv.symm_apply_apply]
    exact hx
  have hW4 : Nat.card W = 4 := by rw [hW, card_map_of_injective Φ.symm.injective, hW'4]
  have hmem : e.symm s' ∈ ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom
      (MonoidHom.id S) := by
    rw [mem_iInf]
    intro w
    rw [mem_iInf]
    rintro ⟨w', hw', rfl⟩
    change Φ.symm w' (e.symm s') = e.symm s'
    rw [apply_eq_iff_commute e, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact mem_centralizer_iff.mp hs' w' hw'
  refine ⟨e.symm s', ?_, MulEquiv.apply_symm_apply e s'⟩
  exact (show (⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S)) ≤ HS
    from le_iSup₂_of_le W hWE (le_iSup_of_le hW4 le_rfl)) hmem

theorem foote47FourgroupGeneration_nine
    {S : Type} [Group S] [Finite S] {p f : ℕ} (h9 : p ^ f = 9)
    (hL : Blueprint.LieModel S .PSL 2 p f) (T : Subgroup (MulAut S)) (hT2 : IsPGroup 2 T)
    (hT : ∃ F : Subgroup (MulAut S), F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8)
    (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) :
    ⨆ (W : Subgroup (MulAut S)) (_ : IsKleinFour W)
      (_ : ∃ F : Subgroup (MulAut S), W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8),
        ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) = ⊤ := by
  obtain ⟨-, -, -, -, K, _, _, hK, ⟨e⟩⟩ := lieModel_psl2_data hL
  have hK9 : Nat.card K = 3 ^ 2 := by rw [hK, h9]; norm_num
  set Φ := autEquiv e with hΦ
  obtain ⟨F₀, hF₀T, hF₀2, hF₀8⟩ := hT
  have hmap2 : ∀ A : Subgroup (MulAut S), (∀ x ∈ A, x * x = 1) →
      ∀ x ∈ A.map Φ.toMonoidHom, x * x = 1 := by
    rintro A hA _ ⟨x, hx, rfl⟩
    rw [← map_mul, hA x hx, map_one]
  have hnab' : ∃ x ∈ T.map Φ.toMonoidHom, ∃ y ∈ T.map Φ.toMonoidHom, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    refine ⟨Φ x, mem_map_of_mem _ hx, Φ y, mem_map_of_mem _ hy, fun h => hxy ?_⟩
    apply Φ.injective
    rw [map_mul, map_mul]
    exact h
  obtain ⟨E', hE'T, hE'2, hE'8, htop⟩ := fourFixSup_sup_eq_top_of_nine hK9 (hT2.map _)
    (map_mono hF₀T) (hmap2 F₀ hF₀2) (by rw [card_map_of_injective Φ.injective, hF₀8]) hnab'
  set E₁ := E'.map Φ.symm.toMonoidHom with hE₁def
  have hE₁ : E₁.map Φ.toMonoidHom = E' := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      change Φ (Φ.symm y) ∈ E'
      rw [MulEquiv.apply_symm_apply]
      exact hy
    · intro hx
      exact ⟨Φ.symm x, ⟨x, hx, rfl⟩, MulEquiv.apply_symm_apply Φ x⟩
  have hE₁T : E₁ ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hE'T hy
    change Φ.symm (Φ x) ∈ T
    rw [MulEquiv.symm_apply_apply]
    exact hx
  have hE₁2 : ∀ x ∈ E₁, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, hE'2 y hy, map_one]
  have hE₁8 : Nat.card E₁ = 8 := by rw [hE₁def, card_map_of_injective Φ.symm.injective, hE'8]
  set A₀ := ⨆ (W : Subgroup (MulAut S)) (_ : W ≤ F₀) (_ : Nat.card W = 4),
    ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) with hA₀
  set A₁ := ⨆ (W : Subgroup (MulAut S)) (_ : W ≤ E₁) (_ : Nat.card W = 4),
    ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) with hA₁
  have h0 : fourFixSup (F₀.map Φ.toMonoidHom) ≤ A₀.map e.toMonoidHom := fourFixSup_map_le e F₀
  have h1 : fourFixSup E' ≤ A₁.map e.toMonoidHom := by
    rw [← hE₁]
    exact fourFixSup_map_le e E₁
  have hA : A₀ ⊔ A₁ = ⊤ := by
    have htop' : ⊤ ≤ (A₀ ⊔ A₁).map e.toMonoidHom := by
      rw [← htop, Subgroup.map_sup]
      exact sup_le_sup h0 h1
    rw [eq_top_iff]
    intro s _
    obtain ⟨s₀, hs₀, hs₀e⟩ := htop' (mem_top (e s))
    rw [← e.injective hs₀e]
    exact hs₀
  have hle : ∀ E₀ : Subgroup (MulAut S), E₀ ≤ T → (∀ x ∈ E₀, x * x = 1) → Nat.card E₀ = 8 →
      (⨆ (W : Subgroup (MulAut S)) (_ : W ≤ E₀) (_ : Nat.card W = 4),
        ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S)) ≤
      ⨆ (W : Subgroup (MulAut S)) (_ : IsKleinFour W)
        (_ : ∃ F : Subgroup (MulAut S), W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8),
          ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) := by
    intro E₀ hE₀T hE₀2 hE₀8
    refine iSup_le fun W => iSup_le fun hWE => iSup_le fun hW4 => ?_
    have hWK : IsKleinFour W := isKleinFour_of_card_four_sq hW4 fun x =>
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hE₀2 _ (hWE x.2))
    exact le_iSup₂_of_le W hWK (le_iSup_of_le ⟨E₀, hWE, hE₀T, hE₀2, hE₀8⟩ le_rfl)
  rw [eq_top_iff, ← hA]
  exact sup_le (hle F₀ hF₀T hF₀2 hF₀8) (hle E₁ hE₁T hE₁2 hE₁8)

end CFSG.ComponentClassification.Foote47.Nine
