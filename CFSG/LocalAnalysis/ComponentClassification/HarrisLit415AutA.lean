module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutInputs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup GorensteinWalter AutL2Facts

namespace AutA

variable {F : Type} [Field F] [Finite F]

theorem sq_eq_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hF : Nat.card F = p ^ n) (D : Sylow 2 (PSL2 F)) (hD : 8 ≤ Nat.card D) (g : PGammaL2 F)
    {k : ℕ} (hk : g ^ 2 ^ k = 1)
    (hgD : ∀ d ∈ (D : Subgroup (PSL2 F)), g * incl F d = incl F d * g) : g * g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hn hF
  have hk' : g.right ^ 2 ^ k = 1 := by
    have := congrArg (fieldProj F) hk
    rwa [map_pow, map_one] at this
  rcases Nat.even_or_odd n with hne | hno
  ·
    have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hne
    have hsq : IsSquare (-1 : F) := by
      have : Fintype F := Fintype.ofFinite F
      classical
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) D
    have hn3 : 3 ≤ twoVal F := by
      have hc : Nat.card D = 2 ^ twoVal F := by
        rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (stdSylow F hodd hsq hq4),
          coe_stdSylow, card_stdT hodd hsq]
      rw [hc] at hD
      by_contra h3
      have : 2 ^ twoVal F ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set c := incl F h with hc
    set g' := c⁻¹ * g * c with hg'
    have hD' : ∀ t ∈ stdT F, h * t * h⁻¹ ∈ (D : Subgroup (PSL2 F)) := by
      intro t ht
      rw [← hh, mem_smul_sylow_iff, show h⁻¹ * (h * t * h⁻¹) * h = t by group, coe_stdSylow]
      exact ht
    have hg'T : ∀ t ∈ stdT F, g' * incl F t = incl F t * g' := by
      intro t ht
      have h1 := hgD _ (hD' t ht)
      have e1 : incl F (h * t * h⁻¹) = c * incl F t * c⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [e1] at h1
      calc g' * incl F t = c⁻¹ * (g * (c * incl F t * c⁻¹)) * c := by rw [hg']; group
        _ = c⁻¹ * ((c * incl F t * c⁻¹) * g) * c := by rw [h1]
        _ = incl F t * g' := by rw [hg']; group
    obtain ⟨t₀, ht₀⟩ := torSub_stdGen_le_range hsq ⟨stdGen F ^ 2, mem_zpowers _, false,
      (mul_one _).symm⟩
    obtain ⟨t₁, ht₁⟩ := torSub_stdGen_le_range hsq
      (show sw F ∈ torSub F (zpowers (stdGen F ^ 2)) from ⟨1, one_mem _, true, by simp⟩)
    have ht₀T : t₀ ∈ stdT F := by
      change Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ ∈ torSub F _
      rw [ht₀]
      exact ⟨stdGen F ^ 2, mem_zpowers _, false, (mul_one _).symm⟩
    have ht₁T : t₁ ∈ stdT F := by
      change Matrix.ProjectiveSpecialLinearGroup.toPGL t₁ ∈ torSub F _
      rw [ht₁]
      exact (show sw F ∈ torSub F (zpowers (stdGen F ^ 2)) from ⟨1, one_mem _, true, by simp⟩)
    have hi₀ : incl F t₀ = nm F (stdGen F ^ 2) false 1 := by
      rw [incl_apply, ht₀, ← inl_tor]
    have hi₁ : incl F t₁ = nm F 1 true 1 := by
      rw [incl_apply, ht₁]
      apply SemidirectProduct.ext <;> simp
    have hc₀ := hg'T t₀ ht₀T
    have hc₁ := hg'T t₁ ht₁T
    rw [hi₀] at hc₀
    rw [hi₁] at hc₁
    have hμ1 : stdGen F ^ 2 ≠ 1 := by
      intro h1
      have h2 := orderOf_stdGen_sq (F := F) hodd
      rw [h1, orderOf_one] at h2
      have : 2 ≤ 2 ^ (twoVal F - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨b, ε, hb⟩ := exists_nm_of_conj_tor g' hμ1 (ν := stdGen F ^ 2)
      (by rw [inl_tor, hc₀, mul_inv_cancel_right])
    rw [hb, nm_mul, nm_mul, nm_eq_nm_iff] at hc₁
    obtain ⟨hb1, -, -⟩ := hc₁
    have hfu1 : fu F g'.right 1 = 1 := map_one _
    have hfu2 : fu F 1 b = b := rfl
    rw [hfu1, hfu2] at hb1
    have hb3 : b = b⁻¹ := by
      cases ε
      · simpa using hb1
      · simpa using hb1
    have hbb : b ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hb3]
      exact mul_inv_cancel b
    have hright : g'.right = g.right := by
      simp [hg', hc, incl_apply]
    have hσ := fieldProj_sq_of_commute_tor hp hp2 hF g' (orderOf_stdGen_sq hodd) (by omega)
      (by rw [inl_tor]; exact hc₀) (k := k) (by rw [hright]; exact hk')
    have hfub : fu F g'.right b = b := by
      rcases units_eq_one_or_neg_one hbb with h1 | h1 <;> rw [h1]
      · exact map_one _
      · ext
        simp
    have hg'2 : g' * g' = 1 := by
      rw [hb, nm_mul, Bool.xor_self, hfub]
      have htw : b * twist F ε b = 1 := by
        cases ε
        · simp only [twist]
          rw [← sq]
          exact hbb
        · simp only [twist, mul_inv_cancel]
      rw [htw, ← pow_two, hσ, nm_one]
    calc g * g = c * (g' * g') * c⁻¹ := by rw [hg']; group
      _ = 1 := by rw [hg'2]; group
  ·
    have hr : g.right = 1 := eq_one_of_two_power_ringAut hp hF hno g.right k hk'
    obtain ⟨d, ⟨hdD, hdc⟩, rfl⟩ := mem_center_of_right_eq_one hodd D hD g hr hk hgD
    obtain ⟨-, hZ⟩ := sylow_noncomm_center hodd D hD
    have hd2 : d * d = 1 := by
      have hmem : (⟨d, ⟨hdD, hdc⟩⟩ : ↥((D : Subgroup (PSL2 F)) ⊓
          centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)))) ^ 2 = 1 := by
        have := _root_.orderOf_dvd_natCard (⟨d, ⟨hdD, hdc⟩⟩ : ↥((D : Subgroup (PSL2 F)) ⊓
          centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F))))
        rw [hZ] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      have := congrArg Subtype.val hmem
      simpa [sq] using this
    rw [← map_mul, hd2, map_one]

end AutA

theorem autPSL2RCentralizer : AutPSL2RCentralizerInput := by
  intro Y _ _ p n hp hp2 hY R ⟨Q, hQ⟩ hR8 a ⟨k, hk⟩ hfix
  obtain ⟨-, hn1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  set Φ := autEquiv e with hΦ
  have hg2 : Φ a ^ 2 ^ k = 1 := by rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  have hD8 : 8 ≤ Nat.card (sylowMap e Q) := by rw [card_sylowMap, hQ]; exact hR8
  have hgD : ∀ d ∈ (sylowMap e Q : Subgroup (PSL2 F)), Φ a * incl F d = incl F d * Φ a := by
    intro d hd
    rw [coe_sylowMap] at hd
    obtain ⟨y, hy, rfl⟩ := hd
    have hya : a y = y := hfix y (hQ ▸ hy)
    have h1 : a * MulAut.conj y = MulAut.conj y * a := by
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hya]
    change Φ a * incl F (e y) = incl F (e y) * Φ a
    rw [← autEquiv_conj, ← map_mul, ← map_mul, h1]
  have h := AutA.sq_eq_one hp hp2 hn1 hF (sylowMap e Q) hD8 (Φ a) hg2 hgD
  apply Φ.injective
  rw [map_mul, map_one]
  exact h

end CFSG.ComponentClassification.HarrisLit
