module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81FieldOrd

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG GorensteinWalter Subgroup AutL2Facts
open scoped commutatorElement

namespace Diag

universe u

variable {F : Type u} [Field F]

theorem eq_one_or_eq_neg_one {y : Fˣ} (h : y * y = 1) : y = 1 ∨ y = -1 := by
  have h' : (y : F) * y = 1 := by rw [← Units.val_mul, h, Units.val_one]
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))

theorem twist_fu_of_mul_self {b : Fˣ} (hb : b * b = 1) (ε : Bool) (σ : F ≃+* F) :
    twist F ε (fu F σ b) = b := by
  have hfu : fu F σ b = b := by
    rcases eq_one_or_eq_neg_one hb with rfl | rfl
    · exact map_one _
    · exact Units.ext (by simp)
  rw [hfu]
  cases ε
  · rfl
  · exact inv_eq_of_mul_eq_one_right hb

theorem twist_zpow (ε : Bool) (a : Fˣ) (j : ℤ) : twist F ε (a ^ j) = twist F ε a ^ j := by
  cases ε
  · rfl
  · exact (inv_zpow a j).symm

theorem nm_conj_sw (c : Fˣ) (ε : Bool) (τ : F ≃+* F) :
    nm F c ε τ * nm F 1 true 1 * (nm F c ε τ)⁻¹ = nm F (c * c) true 1 := by
  rw [nm_inv, nm_mul, nm_mul, nm_eq_nm_iff, map_one, fu_twist, mul_one, fu_fu_inv, twist_twist]
  cases ε <;> simp

theorem commutator_nm_mem (μ : Fˣ) {y y' : Fˣ} (hy : y ∈ zpowers μ) (hy' : y' ∈ zpowers μ)
    (ε ε' : Bool) :
    ∃ v ∈ zpowers (μ ^ 2), ⁅nm F y ε 1, nm F y' ε' 1⁆ = nm F v false 1 := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy'
  rw [commutatorElement_def, nm_inv, nm_inv, nm_mul, nm_mul, nm_mul]
  simp only [inv_one, fu_one, mul_one]
  cases ε <;> cases ε'
  · refine ⟨1, one_mem _, ?_⟩
    rw [nm_eq_nm_iff]
    simp
  · refine ⟨(μ ^ 2) ^ i, zpow_mem (mem_zpowers _) i, ?_⟩
    rw [nm_eq_nm_iff]
    simp
    rw [← zpow_natCast μ 2, ← zpow_mul]
    group
  · refine ⟨(μ ^ 2) ^ (-j), zpow_mem (mem_zpowers _) (-j), ?_⟩
    rw [nm_eq_nm_iff]
    simp
    rw [← zpow_natCast μ 2, ← zpow_mul]
    group
  · refine ⟨(μ ^ 2) ^ (i - j), zpow_mem (mem_zpowers _) (i - j), ?_⟩
    rw [nm_eq_nm_iff]
    simp
    rw [← zpow_natCast μ 2, ← zpow_mul]
    group

variable [Finite F]

theorem commutator_le (hsq : IsSquare (-1 : F)) :
    ⁅(stdT F).map (incl F), (stdT F).map (incl F)⁆ ≤
      (zpowers ((stdGen F ^ 2) ^ 2)).map
        ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (tor F)) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨y, hy, ε, rfl⟩ := (mem_map_stdT_iff hsq _).mp ha
  obtain ⟨y', hy', ε', rfl⟩ := (mem_map_stdT_iff hsq _).mp hb
  obtain ⟨v, hv, hve⟩ := commutator_nm_mem _ hy hy' ε ε'
  rw [hve]
  exact ⟨v, hv, by rw [MonoidHom.comp_apply, inl_tor]⟩

theorem not_mem_commutator (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hn : 3 ≤ twoVal F)
    (g : PGammaL2 F) (hgT : ∀ s ∈ (stdT F).map (incl F), g * s = s * g)
    (z : PGammaL2 F) (hzT : z ∈ (stdT F).map (incl F))
    (hzc : ∀ s ∈ (stdT F).map (incl F), z * s = s * z) (hz1 : z ≠ 1)
    (x : PGammaL2 F) (hxN : ∀ s ∈ (stdT F).map (incl F), x * s * x⁻¹ ∈ (stdT F).map (incl F))
    (hxg : x⁻¹ * g * x = z * g) :
    x * nm F 1 true 1 * x⁻¹ * (nm F 1 true 1)⁻¹ ∉
      ⁅(stdT F).map (incl F), (stdT F).map (incl F)⁆ := by
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  set μ := stdGen F ^ 2 with hμ
  have hμord : orderOf μ = 2 ^ (twoVal F - 1) := orderOf_stdGen_sq hodd
  have h4 : 2 ^ 2 ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hμord
    omega
  have hμμ : μ * μ ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one (show μ ^ 2 = 1 by rw [pow_two]; exact h)
    rw [hμord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hμT : nm F μ false 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨μ, mem_zpowers _, false, rfl⟩
  have hswT : nm F 1 true 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨1, one_mem _, true, rfl⟩
  have hgμ := hgT _ hμT
  obtain ⟨b, δ, hgb⟩ := exists_nm_of_conj_tor g hμ1 (ν := μ)
    (by rw [inl_tor, hgμ, mul_inv_cancel_right])
  set σ := g.right with hσ
  have hψμ := (nm_commute_tor_iff b μ δ σ).mp (by rw [← hgb]; exact hgμ)
  have hbb : b * b = 1 := by
    have h := hgT _ hswT
    rw [hgb, nm_mul, nm_mul, nm_eq_nm_iff] at h
    obtain ⟨h1, -, -⟩ := h
    have h1' : twist F δ 1 = 1 := by cases δ <;> simp
    rw [map_one, fu_one, one_mul, twist_true, h1', mul_one] at h1
    have h3 : b * b = b⁻¹ * b := congrArg (· * b) h1
    rw [h3, inv_mul_cancel]
  obtain ⟨y₀, -, ε₀, hz⟩ := (mem_map_stdT_iff hsq _).mp hzT
  have hε₀ : ε₀ = false := by
    by_contra hne
    have hne' : ε₀ = true := by simpa using hne
    have h := hzc _ hμT
    rw [hz, hne', nm_mul, nm_mul, nm_eq_nm_iff] at h
    obtain ⟨h1, -, -⟩ := h
    simp only [fu_one, twist_true, twist_false] at h1
    rw [mul_comm μ y₀] at h1
    have h3 : μ⁻¹ = μ := mul_left_cancel h1
    apply hμμ
    calc μ * μ = μ⁻¹ * μ := by rw [h3]
      _ = 1 := inv_mul_cancel μ
  have hy₀ : y₀ = -1 := by
    have h := hzc _ hswT
    rw [hz, hε₀, nm_mul, nm_mul, nm_eq_nm_iff] at h
    obtain ⟨h1, -, -⟩ := h
    simp only [fu_one, twist_true, twist_false, one_mul, mul_one, map_one] at h1
    have h3 : y₀ * y₀ = y₀⁻¹ * y₀ := congrArg (· * y₀) h1
    rw [inv_mul_cancel] at h3
    rcases eq_one_or_eq_neg_one h3 with h | h
    · exact absurd (by rw [hz, hε₀, h, nm_one]) hz1
    · exact h
  obtain ⟨y₁, -, ε₁, hy₁⟩ := (mem_map_stdT_iff hsq _).mp (hxN _ hμT)
  have hε₁ : ε₁ = false := by
    by_contra hne
    have hne' : ε₁ = true := by simpa using hne
    rw [hne'] at hy₁
    have hsq1 : x * (nm F μ false 1 * nm F μ false 1) * x⁻¹ = 1 := by
      calc x * (nm F μ false 1 * nm F μ false 1) * x⁻¹ =
          (x * nm F μ false 1 * x⁻¹) * (x * nm F μ false 1 * x⁻¹) := by group
        _ = 1 := by rw [hy₁, nm_true_mul_self]
    rw [conj_eq_one_iff, nm_mul, ← nm_one, nm_eq_nm_iff] at hsq1
    simp only [twist_false, fu_one] at hsq1
    exact hμμ hsq1.1
  rw [hε₁] at hy₁
  obtain ⟨c, ε, hxc⟩ := exists_nm_of_conj_tor x hμ1 (ν := y₁)
    (by rw [inl_tor, inl_tor]; exact hy₁)
  set τ := x.right with hτ
  have hψc : twist F δ (fu F σ c) = -c := by
    have h : g * x = x * (z * g) := by rw [← hxg]; group
    rw [hgb, hxc, hz, hε₀, hy₀, nm_mul, nm_mul, nm_mul, nm_eq_nm_iff] at h
    obtain ⟨h1, -, -⟩ := h
    rw [fu_one, twist_false, map_mul, twist_mul, twist_fu_of_mul_self hbb,
      twist_fu_of_mul_self (b := -1) (by rw [neg_one_mul, neg_neg])] at h1
    apply mul_left_cancel (a := b)
    rw [h1, neg_one_mul, mul_neg, mul_neg, mul_comm]
  intro hmem
  have hval : x * nm F 1 true 1 * x⁻¹ * (nm F 1 true 1)⁻¹ = nm F (c * c) false 1 := by
    rw [hxc, nm_conj_sw, nm_inv, nm_mul, nm_eq_nm_iff]
    simp [fu_one]
  rw [hval] at hmem
  obtain ⟨v, hv, hve⟩ := commutator_le hsq hmem
  rw [MonoidHom.comp_apply, inl_tor, nm_eq_nm_iff] at hve
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hv
  have hμj : (μ ^ 2) ^ j = μ ^ j * μ ^ j := by
    rw [← zpow_natCast μ 2, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    ring
  set d := c * (μ ^ j)⁻¹ with hd
  have hdd : d * d = 1 := by
    rw [hd, mul_mul_mul_comm, ← hve.1, ← hj, hμj]
    group
  have hcd : c = d * μ ^ j := by rw [hd, inv_mul_cancel_right]
  have hψc' : twist F δ (fu F σ c) = c := by
    rw [hcd, map_mul, twist_mul, twist_fu_of_mul_self hdd, map_zpow, twist_zpow, hψμ]
  have hc : (2 : F) * c = 0 := by
    have := congrArg (fun u : Fˣ => (u : F)) (hψc'.symm.trans hψc)
    simp only [Units.val_neg] at this
    linear_combination this
  rcases mul_eq_zero.mp hc with h | h
  · exact h2 h
  · exact c.ne_zero h

theorem exists_equiv_std {Y : Type*} [Group Y] [Finite Y] (e₀ : Y ≃* PSL2 F)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hq4 : Nat.card F % 4 = 1)
    (T : Sylow 2 Y) :
    ∃ e : Y ≃* PSL2 F, (T : Subgroup Y).map e.toMonoidHom = stdT F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) (sylowMap e₀ T)
  have hmem : ∀ d : PSL2 F, d ∈ (T : Subgroup Y).map e₀.toMonoidHom ↔ h⁻¹ * d * h ∈ stdT F := by
    intro d
    rw [← coe_sylowMap, ← hh, mem_smul_sylow_iff, coe_stdSylow]
  refine ⟨e₀.trans (MulAut.conj h⁻¹), ?_⟩
  ext s
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (hmem (e₀ y)).mp ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using this
  · intro hs
    obtain ⟨y, hy, hye⟩ := (hmem (h * s * h⁻¹)).mpr (by simpa [mul_assoc] using hs)
    refine ⟨y, hy, ?_⟩
    change h⁻¹ * e₀ y * h⁻¹⁻¹ = s
    rw [show e₀ y = h * s * h⁻¹ from hye]
    group

end Diag

open Diag in
theorem cf81Diag : CF81Diag := by
  intro Y _ _ p f hp hp2 hf hY T hT φ hφ2 hφT hφT' ζ hζT hζc hζ1 w hwN hwφ
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e₀⟩⟩ := lieModel_psl2_data hY
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hσ1 := FieldOrd.right_ne_one hp hp2 hf hF (sylowMap e₀ T)
    (by rw [card_sylowMap]; exact hT) (autEquiv e₀ φ) (by rw [← map_mul, hφ2, map_one])
    (by
      intro t ht
      rw [coe_sylowMap] at ht
      exact centralizes_map_autEquiv e₀ T (zpowers φ) (zpowers_le.mpr hφT) _
        (mem_map_of_mem _ (mem_zpowers φ)) t ht)
    (by
      rintro ⟨t, ht, hte⟩
      rw [coe_sylowMap] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      apply hφT'
      refine ⟨s, hs, (autEquiv e₀).injective ?_⟩
      rw [autEquiv_conj]
      exact hte)
  have hσσ : (autEquiv e₀ φ).right * (autEquiv e₀ φ).right = 1 := by
    have := congrArg SemidirectProduct.right (show autEquiv e₀ φ * autEquiv e₀ φ = 1 by
      rw [← map_mul, hφ2, map_one])
    simpa using this
  obtain ⟨hq4, hsq⟩ := FieldOrd.mod_four_of_involution hp hp2 hF hσσ hσ1
  have hn : 3 ≤ twoVal F := by
    have h1 := FieldOrd.card_sylow hodd hsq hq4 (sylowMap e₀ T)
    rw [card_sylowMap] at h1
    have h8 : 2 ^ 3 ≤ 2 ^ twoVal F := by rw [← h1]; exact hT
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h8
  obtain ⟨e, he⟩ := exists_equiv_std e₀ hodd hsq hq4 T
  have hinn : (innOf (T : Subgroup Y)).map (autEquiv e).toMonoidHom = (stdT F).map (incl F) := by
    rw [innOf, map_autEquiv_innOf, he]
  have hmem : ∀ α ∈ innOf (T : Subgroup Y), autEquiv e α ∈ (stdT F).map (incl F) := by
    intro α hα
    rw [← hinn]
    exact mem_map_of_mem _ hα
  have hcent : ∀ β ∈ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)),
      ∀ s ∈ (stdT F).map (incl F), autEquiv e β * s = s * autEquiv e β := by
    intro β hβ s hs
    rw [← hinn] at hs
    obtain ⟨α, hα, rfl⟩ := hs
    change autEquiv e β * autEquiv e α = autEquiv e α * autEquiv e β
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hβ α hα]
  obtain ⟨s₀, hs₀, hs₀e⟩ : nm F 1 true 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨1, one_mem _, true, rfl⟩
  have hs₀T : e.symm s₀ ∈ (T : Subgroup Y) := by
    rw [← he] at hs₀
    obtain ⟨y, hy, hye⟩ := hs₀
    rw [← hye]
    change e.symm (e y) ∈ (T : Subgroup Y)
    rw [MulEquiv.symm_apply_apply]
    exact hy
  refine ⟨MulAut.conj (e.symm s₀), ⟨e.symm s₀, hs₀T, rfl⟩, fun hc => ?_⟩
  have hmap := mem_map_of_mem (autEquiv e).toMonoidHom hc
  rw [map_commutator, hinn] at hmap
  refine not_mem_commutator hodd hsq hn (autEquiv e φ) (hcent φ hφT) (autEquiv e ζ)
    (hmem ζ hζT) (hcent ζ hζc) (fun h => hζ1 ((autEquiv e).injective (h.trans (map_one _).symm)))
    (autEquiv e w) ?_ (by rw [← map_inv, ← map_mul, ← map_mul, hwφ, map_mul]) ?_
  · intro s hs
    rw [← hinn] at hs ⊢
    obtain ⟨α, hα, rfl⟩ := hs
    refine ⟨w * α * w⁻¹, (mem_normalizer_iff.mp hwN α).mp hα, ?_⟩
    simp
  · have h1 : autEquiv e (MulAut.conj (e.symm s₀)) = nm F 1 true 1 := by
      rw [autEquiv_conj, MulEquiv.apply_symm_apply, hs₀e]
    simpa [h1] using hmap

end CFSG.ComponentClassification.GSThmB
