module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenCoatom

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem map_fourFixSup_conj_le (g : PSL2 F) (E : Subgroup (PGammaL2 F)) :
    (fourFixSup (E.map (MulAut.conj (incl F g)).toMonoidHom)).map
      (MulAut.conj g⁻¹).toMonoidHom ≤ fourFixSup E := by
  rw [map_le_iff_le_comap]
  refine iSup_le fun W => iSup_le fun hWE => iSup_le fun hW4 => ?_
  intro s hs
  change incl F s ∈ centralizer (W : Set (PGammaL2 F)) at hs
  set W' := W.map (MulAut.conj (incl F g)⁻¹).toMonoidHom with hW'
  have hW'E : W' ≤ E := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hWE hw
    change (incl F g)⁻¹ * (incl F g * x * (incl F g)⁻¹) * (incl F g)⁻¹⁻¹ ∈ E
    rw [inv_inv, show (incl F g)⁻¹ * (incl F g * x * (incl F g)⁻¹) * incl F g = x by group]
    exact hx
  have hW'4 : Nat.card W' = 4 := by
    rw [hW', card_map_of_injective (MulAut.conj _).injective, hW4]
  have hmem : (MulAut.conj g⁻¹).toMonoidHom s ∈ fixPSL W' := by
    change incl F (g⁻¹ * s * g⁻¹⁻¹) ∈ centralizer (W' : Set (PGammaL2 F))
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have h1 := mem_centralizer_iff.mp hs w hw
    change (incl F g)⁻¹ * w * (incl F g)⁻¹⁻¹ * incl F (g⁻¹ * s * g⁻¹⁻¹) =
      incl F (g⁻¹ * s * g⁻¹⁻¹) * ((incl F g)⁻¹ * w * (incl F g)⁻¹⁻¹)
    simp only [map_mul, map_inv, inv_inv]
    calc (incl F g)⁻¹ * w * incl F g * ((incl F g)⁻¹ * incl F s * incl F g)
        = (incl F g)⁻¹ * (w * incl F s) * incl F g := by group
      _ = (incl F g)⁻¹ * (incl F s * w) * incl F g := by rw [h1]
      _ = (incl F g)⁻¹ * incl F s * incl F g * ((incl F g)⁻¹ * w * incl F g) := by group
  exact (show fixPSL W' ≤ fourFixSup E from le_iSup₂_of_le W' hW'E (le_iSup_of_le hW'4 le_rfl))
    hmem

theorem mem_pslRange_of_right_eq_one (hodd : IsOddPrimePower (Nat.card F))
    {E : Subgroup (PGammaL2 F)} (hE2 : ∀ x ∈ E, x * x = 1) {x₀ : PGammaL2 F} (hx₀E : x₀ ∈ E)
    (hx₀r : x₀.right ≠ 1) {v : PGammaL2 F} (hvE : v ∈ E) (hvr : v.right = 1) :
    v ∈ pGammaL2PSLRange F := by
  have horder : ∀ x ∈ E, x.right ≠ 1 → orderOf x = 2 := fun x hx hr =>
    orderOf_eq_prime (by rw [pow_two]; exact hE2 x hx) (fun h => hr (by rw [h]; rfl))
  have hx₀v : x₀ * v ∈ E := E.mul_mem hx₀E hvE
  have hr : (x₀ * v).right ≠ 1 := by rwa [SemidirectProduct.mul_right, hvr, mul_one]
  have hs1 := sqLeft_of_involution hodd (horder _ hx₀E hx₀r) hx₀r
  have hs2 := sqLeft_of_involution hodd (horder _ hx₀v hr) hr
  rw [mem_pslRange_iff]
  exact ⟨hvr, ((sqLeft_mul _ _).mp hs2).mp hs1⟩

theorem fourFixSup_eq_top {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (h13 : 13 ≤ p ^ f) {E : Subgroup (PGammaL2 F)} (hE2 : ∀ x ∈ E, x * x = 1)
    (hE8 : Nat.card E = 8) : fourFixSup E = ⊤ := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h13
      omega
    · exact h
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩
  obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E hE2 hE8.ge
  have hψ2 : x₀.right * x₀.right = 1 := by
    have := congrArg SemidirectProduct.right (hE2 x₀ hx₀E)
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at this
  obtain ⟨m, hm⟩ := even_of_ringAut hp hF hψ2 hx₀r
  have hF' : Nat.card F = p ^ (2 * m) := by rw [hF, hm, two_mul]
  have hsq : IsSquare (-1 : F) := isSquare_neg_one_of_card_sq hp hp2 hF'
  have h4 : p ^ f % 4 = 1 := by
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := m)
    rw [hm, ← two_mul, pow_mul', hk, show (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 by ring]
    omega
  obtain ⟨A₁, hA₁, A₂, hA₂, hA₁1, hA₂1, hA₁₂⟩ :=
    exists_two_ne_of_card_four (linearPart E) (card_linearPart_of_card_eight hodd hE2 hE8)
  have hinv : ∀ A : PGL2 F, SemidirectProduct.inl A ∈ E → A ≠ 1 →
      ∃ t : PSL2 F, incl F t = SemidirectProduct.inl A ∧ orderOf t = 2 := by
    intro A hA hA1
    obtain ⟨t, ht⟩ := mem_pslRange_of_right_eq_one hodd hE2 hx₀E hx₀r hA
      (SemidirectProduct.right_inl A)
    change incl F t = SemidirectProduct.inl A at ht
    refine ⟨t, ht, orderOf_eq_prime ?_ ?_⟩
    · apply incl_injective F
      change incl F (t ^ 2) = incl F 1
      rw [map_pow, ht, map_one, pow_two]
      exact hE2 _ hA
    · intro h
      apply hA1
      have h' : (SemidirectProduct.inl A : PGammaL2 F) = SemidirectProduct.inl 1 := by
        rw [← ht, h, map_one, map_one]
      exact SemidirectProduct.inl_injective h'
  obtain ⟨t₁, ht₁, ht₁2⟩ := hinv A₁ hA₁ hA₁1
  obtain ⟨t₂, ht₂, ht₂2⟩ := hinv A₂ hA₂ hA₂1
  have ht₁₂ : t₁ ≠ t₂ := by
    intro h
    apply hA₁₂
    have h' : (SemidirectProduct.inl A₁ : PGammaL2 F) = SemidirectProduct.inl A₂ := by
      rw [← ht₁, ← ht₂, h]
    exact SemidirectProduct.inl_injective h'
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
  have hcent : ∀ t : PSL2 F, incl F t ∈ E → orderOf t = 2 →
      centralizer ({t} : Set (PSL2 F)) ≤ fourFixSup E := by
    intro t htE ht2
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
  have hco := isCoatom_centralizer_involution hp hp2 hF h4 (by omega) ht₁2
  rcases hco.le_iff.mp (hcent t₁ (by rw [ht₁]; exact hA₁) ht₁2) with h | h
  · exact h
  · exfalso
    apply centralizer_ne_of_involution hp hp2 hF h4 (by omega) ht₁2 ht₂2 ht₁₂
    have hf0 : 0 < f := hf1
    have : Fact p.Prime := ⟨hp⟩
    have hc₁ := ((CFSG.Walter.psl2_centralizer_involution F hF (hp.odd_of_ne_two hp2) hf0
      ht₁2).1 h4).1
    have hc₂ := ((CFSG.Walter.psl2_centralizer_involution F hF (hp.odd_of_ne_two hp2) hf0
      ht₂2).1 h4).1
    refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hc₁, hc₂])).symm
    rw [← h]
    exact hcent t₂ (by rw [ht₂]; exact hA₂) ht₂2

theorem fourgroup_fix_generation {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h13 : 13 ≤ p ^ f) (hS : Blueprint.LieModel S .PSL 2 p f)
    {E : Subgroup (MulAut S)} (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8) :
    ⨆ (W : Subgroup (MulAut S)) (_ : W ≤ E) (_ : Nat.card W = 4),
      ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) = ⊤ := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  set Φ := autEquiv e with hΦ
  set E' := E.map Φ.toMonoidHom with hE'
  have hE'2 : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change Φ x * Φ x = 1
    rw [← map_mul, hE2 x hx, map_one]
  have hE'8 : Nat.card E' = 8 := by rw [hE', card_map_of_injective Φ.injective, hE8]
  have htop := fourFixSup_eq_top hp hp2 hF h13 hE'2 hE'8
  set HS := ⨆ (W : Subgroup (MulAut S)) (_ : W ≤ E) (_ : Nat.card W = 4),
      ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) with hHS
  have hle : fourFixSup E' ≤ HS.map e.toMonoidHom := by
    refine iSup_le fun W' => iSup_le fun hW'E => iSup_le fun hW'4 => ?_
    intro s' hs'
    change incl F s' ∈ centralizer (W' : Set (PGammaL2 F)) at hs'
    set W := W'.map Φ.symm.toMonoidHom with hW
    have hWE : W ≤ E := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hW'E hw
      change Φ.symm (Φ x) ∈ E
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
  rw [htop] at hle
  rw [eq_top_iff]
  intro s _
  obtain ⟨s₀, hs₀, hs₀e⟩ := hle (mem_top (e s))
  rw [← e.injective hs₀e]
  exact hs₀

end CFSG.ComponentClassification.AutL2Facts
