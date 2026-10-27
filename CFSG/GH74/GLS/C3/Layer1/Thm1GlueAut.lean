module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7
public import CFSG.GH74.GLS.C3.Layer1.Thm1P310Two
public import CFSG.GH74.GLS.IVK.L2.KI2Aux
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK


theorem isPGroup_zpowers_of_pow_eq_one {X : Type} [Group X] {w : X} (h : ∃ k : ℕ, w ^ (2 ^ k) = 1) :
    IsPGroup 2 ↥(zpowers w) := by
  obtain ⟨k, hk⟩ := h
  intro g
  obtain ⟨g, j, rfl⟩ := g
  refine ⟨k, Subtype.ext ?_⟩
  show (w ^ j) ^ (2 ^ k) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem mem_of_isSylowOf_of_commute {X : Type} [Group X] [Finite X] {Pb H : Subgroup X}
    (hSyl : IsSylowOf 2 Pb H) {w : X} (hwH : w ∈ H) (hwc : ∀ q ∈ Pb, w * q = q * w)
    (hw2 : ∃ k : ℕ, w ^ (2 ^ k) = 1) : w ∈ Pb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwcent : w ∈ centralizer (Pb : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hwc q hq).symm
  have hN : zpowers w ≤ normalizer (Pb : Set X) :=
    ((zpowers_le).2 hwcent).trans (Subgroup.centralizer_le_normalizer _)
  have hP2 : IsPGroup 2 ↥(Pb ⊔ zpowers w) :=
    hSyl.isPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_eq_one hw2) hN
  have hle : Pb ⊔ zpowers w ≤ H := sup_le hSyl.le ((zpowers_le).2 hwH)
  have heq := hSyl.eq_of_le le_sup_left hle hP2
  rw [← heq]
  exact Subgroup.mem_sup_right (mem_zpowers w)


@[expose] def AutLevelC (Kb : Type) [Group Kb] : Prop :=
  ∀ Pb : Subgroup (MulAut Kb), Pb ≤ innAut Kb → IsSylowOf 2 Pb (innAut Kb) →
    (∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥Pb n) →
    ∀ σ γ : MulAut Kb, orderOf σ = 2 → σ ∉ innAut Kb → (∀ q ∈ Pb, σ * q = q * σ) →
      (∀ q ∈ Pb, γ * q = q * γ) → σ * γ = γ * σ → (∃ k : ℕ, γ ^ (2 ^ k) = 1) →
      ∃ z ∈ Pb, orderOf z = 2 ∧ (∀ q ∈ Pb, z * q = q * z) ∧ γ ∈ zpowers z ⊔ zpowers σ

theorem autLevelC_of_A7 {Kb : Type} [Group Kb] [Finite Kb] (e7 : Kb ≃* alternatingGroup (Fin 7)) :
    AutLevelC Kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Kb) := Finite.of_equiv _ (psiEquiv e7).symm.toEquiv
  intro Pb hPinn hSyl hdih σ γ hσ2 hσinn hσc hγc hσγ hγ2
  obtain ⟨n, hn3, hn⟩ := hdih
  obtain ⟨z, hzP, hz2, hzc, hzu⟩ := exists_dihedral_center (H := Pb) hn3 hn
  refine ⟨z, hzP, hz2, hzc, ?_⟩
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hsign : ∀ w : MulAut Kb, w ∈ innAut Kb ↔ Equiv.Perm.sign (psiEquiv e7 w) = 1 := by
    intro w
    have h1 : psiEquiv e7 w ∈ (innAut Kb).map (psiEquiv e7).toMonoidHom ↔ w ∈ innAut Kb :=
      Subgroup.mem_map_iff_mem (psiEquiv e7).injective
    rw [← h1, psi_map_innAut e7, Equiv.Perm.mem_alternatingGroup]
  by_cases hγinn : γ ∈ innAut Kb
  · have hγP : γ ∈ Pb := mem_of_isSylowOf_of_commute hSyl hγinn hγc hγ2
    rcases hzu γ hγP (fun q hq => (hγc q hq)) with h | h
    · rw [h]; exact (zpowers z ⊔ zpowers σ).one_mem
    · rw [h]; exact Subgroup.mem_sup_left (mem_zpowers z)
  · have hγσinn : γ * σ ∈ innAut Kb := by
      rw [hsign] at hγinn hσinn ⊢
      have h1 : Equiv.Perm.sign (psiEquiv e7 γ) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (psiEquiv e7 γ)) with h | h
        · exact absurd h hγinn
        · exact h
      have h2 : Equiv.Perm.sign (psiEquiv e7 σ) = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign (psiEquiv e7 σ)) with h | h
        · exact absurd h hσinn
        · exact h
      rw [map_mul, map_mul, h1, h2]
      decide
    obtain ⟨k, hk⟩ := hγ2
    have hcomm : Commute γ σ := hσγ.symm
    have hγσ2 : ∃ k : ℕ, (γ * σ) ^ (2 ^ k) = 1 := by
      refine ⟨k + 1, ?_⟩
      have hσ' : σ ^ 2 = 1 := by rw [sq]; exact hσσ
      have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hcomm.mul_pow, e, pow_mul', pow_mul, hk, hσ', one_pow, one_pow, one_mul]
    have hγσc : ∀ q ∈ Pb, γ * σ * q = q * (γ * σ) := by
      intro q hq
      calc γ * σ * q = γ * (σ * q) := by group
        _ = γ * (q * σ) := by rw [hσc q hq]
        _ = (γ * q) * σ := by group
        _ = (q * γ) * σ := by rw [hγc q hq]
        _ = q * (γ * σ) := by group
    have hγσP : γ * σ ∈ Pb := mem_of_isSylowOf_of_commute hSyl hγσinn hγσc hγσ2
    have hγ_eq : γ = (γ * σ) * σ := by
      calc γ = γ * (σ * σ) := by rw [hσσ, mul_one]
        _ = (γ * σ) * σ := by group
    rcases hzu (γ * σ) hγσP (fun q hq => (hγσc q hq)) with h | h
    · rw [hγ_eq, h, one_mul]; exact Subgroup.mem_sup_right (mem_zpowers σ)
    · rw [hγ_eq, h]
      exact (zpowers z ⊔ zpowers σ).mul_mem (Subgroup.mem_sup_left (mem_zpowers z))
        (Subgroup.mem_sup_right (mem_zpowers σ))


theorem autLevelC_of_L2
    {F : Type} [Field F] [Finite F] {Kb : Type} [Group Kb] [Finite Kb] (hF : L2Field F)
    (e : Kb ≃* L2 F) : AutLevelC Kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Pb hPinn hSyl hdih σ γ hσ2 hσinn hσc hγc hσγ hγ2
  obtain ⟨n, hn3, hn⟩ := hdih
  obtain ⟨z, hzP, hz2, hzc, hzu⟩ := exists_dihedral_center (H := Pb) hn3 hn
  refine ⟨z, hzP, hz2, hzc, ?_⟩
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ2
    omega
  obtain ⟨V₄, hV₄P, hV₄⟩ : ∃ V : Subgroup (MulAut Kb), V ≤ Pb ∧ IsKleinFour ↥V := by
    obtain ⟨-, k, hk, hk2, ⟨φ⟩⟩ := hn
    have hkn : k = 2 ^ (n - 1) := by
      have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    subst hkn
    exact CFSG.GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv Pb (by omega) φ
  have hV₄sq : ∀ v ∈ V₄, v * v = 1 := by
    intro v hv
    have h1 : (⟨v, hv⟩ : ↥V₄) ^ Monoid.exponent ↥V₄ = 1 := Monoid.pow_exponent_eq_one _
    rw [IsKleinFour.exponent_two, sq] at h1
    exact congrArg Subtype.val h1
  have hV₄comm : ∀ v ∈ V₄, ∀ w ∈ V₄, v * w = w * v := by
    intro v hv w hw
    have h1 : v * w * (v * w) = 1 := hV₄sq _ (V₄.mul_mem hv hw)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV₄sq v hv)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hV₄sq w hw)
    have h2 : v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hv', hw']
  have hV₄σ : ∀ v ∈ V₄, ∀ c ∈ zpowers σ, v * c = c * v := by
    intro v hv c hc
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc
    exact (Commute.zpow_right (show Commute v σ from (hσc v (hV₄P hv)).symm) j).eq
  set E : Subgroup (MulAut Kb) := V₄ ⊔ zpowers σ with hEdef
  have hE : IsElementaryAbelian 2 ↥E := by
    refine isElementaryAbelian_two E ?_ ?_
    · intro x hx y hy
      obtain ⟨v₁, hv₁, c₁, hc₁, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hV₄σ hx
      obtain ⟨v₂, hv₂, c₂, hc₂, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hV₄σ hy
      have h12 : c₁ * c₂ = c₂ * c₁ := by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc₁
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc₂
        exact (Commute.zpow_zpow_self σ i j).eq
      calc v₁ * c₁ * (v₂ * c₂) = v₁ * (c₁ * v₂) * c₂ := by group
        _ = v₁ * (v₂ * c₁) * c₂ := by rw [← hV₄σ v₂ hv₂ c₁ hc₁]
        _ = (v₁ * v₂) * (c₁ * c₂) := by group
        _ = (v₂ * v₁) * (c₂ * c₁) := by rw [hV₄comm v₁ hv₁ v₂ hv₂, h12]
        _ = v₂ * (v₁ * c₂) * c₁ := by group
        _ = v₂ * (c₂ * v₁) * c₁ := by rw [hV₄σ v₁ hv₁ c₂ hc₂]
        _ = v₂ * c₂ * (v₁ * c₁) := by group
    · intro x hx
      obtain ⟨v, hv, c, hc, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hV₄σ hx
      have hcc : c * c = 1 := by
        rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hσσ hc with rfl | rfl
        · simp
        · exact hσσ
      calc v * c * (v * c) = v * (c * v) * c := by group
        _ = v * (v * c) * c := by rw [← hV₄σ v hv c hc]
        _ = (v * v) * (c * c) := by group
        _ = 1 := by rw [hV₄sq v hv, hcc, one_mul]
  have hσE : σ ∈ E := Subgroup.mem_sup_right (mem_zpowers σ)
  have hσV₄ : σ ∉ V₄ := fun h => hσinn (hPinn (hV₄P h))
  have hE8 : 8 ≤ Nat.card ↥E := by
    by_contra hlt
    push Not at hlt
    have hle : V₄ ≤ E := le_sup_left
    have hdvd : Nat.card ↥V₄ ∣ Nat.card ↥E := Subgroup.card_dvd_of_le hle
    rw [IsKleinFour.card_four] at hdvd
    have hpos : 0 < Nat.card ↥E := Nat.card_pos
    have h4 : Nat.card ↥E = 4 := by
      obtain ⟨t, ht⟩ := hdvd
      omega
    have heq : V₄ = E := Subgroup.eq_of_le_of_card_ge hle (by rw [h4, IsKleinFour.card_four])
    exact hσV₄ (heq ▸ hσE)
  have hσcent : σ ∈ centralizer (Pb : Set (MulAut Kb)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hσc q hq).symm
  have hN : zpowers σ ≤ normalizer (Pb : Set (MulAut Kb)) :=
    ((zpowers_le).2 hσcent).trans (Subgroup.centralizer_le_normalizer _)
  have hB : IsPGroup 2 ↥(Pb ⊔ zpowers σ) :=
    hSyl.isPGroup.to_sup_of_normal_left'
      (Thm1.isPGroup_zpowers_of_pow_eq_one ⟨1, by simpa [sq] using hσσ⟩) hN
  have hBinn : (Pb ⊔ zpowers σ) ⊓ innAut Kb = Pb :=
    hSyl.eq_of_le (le_inf le_sup_left hSyl.le) inf_le_right hB.to_inf_left
  have hSylB : IsSylowOf 2 ((Pb ⊔ zpowers σ) ⊓ innAut Kb) (innAut Kb) := by
    rw [hBinn]; exact hSyl
  have hEB : E ≤ Pb ⊔ zpowers σ := sup_le (hV₄P.trans le_sup_left) le_sup_right
  obtain ⟨e', N, -, -, -, -, hPeq, -, -, -, -, -, -⟩ :=
    exists_notation_field_inv hF e (Pb ⊔ zpowers σ) hB hSylB E hEB hE hE8
  have hNP : N.P = Pb := hPeq.trans hBinn
  have hzu' : ∀ w ∈ N.P, (∀ q ∈ N.P, w * q = q * w) → w = 1 ∨ w = z :=
    fun w hw hwc => hzu w (hNP ▸ hw) (fun q hq => hwc q (hNP ▸ hq))
  obtain ⟨Ef, hEcyc, -, ⟨m, hmodd, hEcard⟩, hcent, -, -⟩ := ivk_1_4j F hF Kb e' N
  have hEcentral : ∀ ε ∈ Ef, ∀ q ∈ N.P, q * ε = ε * q := by
    intro ε hε q hq
    have : ε ∈ centralizer (N.P : Set (MulAut Kb)) := by
      rw [hcent]
      exact Subgroup.mem_sup_right hε
    exact mem_centralizer_iff.1 this q hq
  have hZE : ∀ ζ ∈ (center ↥N.P).map N.P.subtype, ∀ ε ∈ Ef, ζ * ε = ε * ζ := by
    intro ζ hζ ε hε
    obtain ⟨ζ', _, rfl⟩ := hζ
    exact hEcentral ε hε ζ' ζ'.2
  have hdecomp : ∀ w ∈ centralizer (N.P : Set (MulAut Kb)), ∃ ζ ∈ N.P, (ζ = 1 ∨ ζ = z) ∧
      ∃ ε ∈ Ef, ζ * ε = ε * ζ ∧ w = ζ * ε := by
    intro w hw
    rw [hcent] at hw
    obtain ⟨ζ, hζ, ε, hε, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hZE hw
    have hcomm := hZE ζ hζ ε hε
    obtain ⟨ζ', hζ', rfl⟩ := hζ
    refine ⟨ζ', ζ'.2, hzu' ζ' ζ'.2 (fun q hq => ?_), ε, hε, hcomm, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hζ' ⟨q, hq⟩).symm
  have hγN : γ ∈ centralizer (N.P : Set (MulAut Kb)) :=
    mem_centralizer_iff.2 fun q hq => (hγc q (hNP ▸ hq)).symm
  have hσN : σ ∈ centralizer (N.P : Set (MulAut Kb)) :=
    mem_centralizer_iff.2 fun q hq => (hσc q (hNP ▸ hq)).symm
  obtain ⟨ζ, hζP, hζ, ε, hε, hζε, hγeq⟩ := hdecomp γ hγN
  obtain ⟨ζ', hζ'P, hζ', ε', hε', hζ'ε', hσeq⟩ := hdecomp σ hσN
  have hζζ : ζ * ζ = 1 := by
    rcases hζ with h | h
    · rw [h, one_mul]
    · rw [h]; exact hzz
  have hζ'ζ' : ζ' * ζ' = 1 := by
    rcases hζ' with h | h
    · rw [h, one_mul]
    · rw [h]; exact hzz
  have hε'1 : ε' ≠ 1 := by
    intro h
    apply hσinn
    rw [hσeq, h, mul_one]
    exact hPinn (hNP ▸ hζ'P)
  have hε'ε' : ε' * ε' = 1 := by
    have h1 : σ * σ = ζ' * ζ' * (ε' * ε') := by
      rw [hσeq]
      calc ζ' * ε' * (ζ' * ε') = ζ' * (ε' * ζ') * ε' := by group
        _ = ζ' * (ζ' * ε') * ε' := by rw [hζ'ε']
        _ = ζ' * ζ' * (ε' * ε') := by group
    rw [h1, hζ'ζ', one_mul] at hσσ
    exact hσσ
  have hεε : ε * ε = 1 := by
    obtain ⟨k, hk⟩ := hγ2
    have hcom : Commute ζ ε := hζε
    have e2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h1 : ε ^ (2 ^ (k + 1)) = 1 := by
      have h2 : γ ^ (2 ^ (k + 1)) = 1 := by
        rw [e2, pow_mul', hk, one_pow]
      rw [hγeq, hcom.mul_pow] at h2
      have hζ2 : ζ ^ (2 ^ (k + 1)) = 1 := by
        rw [e2, pow_mul]
        have : ζ ^ 2 = 1 := by rw [sq]; exact hζζ
        rw [this, one_pow]
      rw [hζ2, one_mul] at h2
      exact h2
    have hdvd1 : orderOf ε ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one h1
    have hdvd2 : orderOf ε ∣ Nat.card ↥Ef := by
      have := orderOf_dvd_natCard (⟨ε, hε⟩ : ↥Ef)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
    have hi1 : i ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h4 : 2 ^ 2 ∣ orderOf ε := by rw [hio]; exact pow_dvd_pow 2 (by omega)
      have h4' := h4.trans hdvd2
      obtain ⟨u, hu⟩ := hmodd
      rcases hEcard with h | h
      · rw [h] at h4'; obtain ⟨t, ht⟩ := h4'; omega
      · rw [h] at h4'; obtain ⟨t, ht⟩ := h4'; omega
    have hord2 : orderOf ε ∣ 2 := by
      rw [hio]; interval_cases i <;> simp
    have := orderOf_dvd_iff_pow_eq_one.1 hord2
    rwa [sq] at this
  have hε1ε' : ε = 1 ∨ ε = ε' := by
    by_cases hε1 : ε = 1
    · exact Or.inl hε1
    · right
      have := hEcyc
      have h := CFSG.GH74.GLS.IVK.DihedralAux.cyclic_unique_involution (G := ↥Ef)
        (a := ⟨ε, hε⟩) (b := ⟨ε', hε'⟩)
        (fun h => hε1 (congrArg Subtype.val h)) (fun h => hε'1 (congrArg Subtype.val h))
        (Subtype.ext hεε) (Subtype.ext hε'ε')
      exact congrArg Subtype.val h
  have hζz : ζ ∈ zpowers z := by
    rcases hζ with h | h
    · rw [h]; exact (zpowers z).one_mem
    · rw [h]; exact mem_zpowers z
  have hζ'z : ζ' ∈ zpowers z := by
    rcases hζ' with h | h
    · rw [h]; exact (zpowers z).one_mem
    · rw [h]; exact mem_zpowers z
  rcases hε1ε' with h | h
  · rw [hγeq, h, mul_one]
    exact Subgroup.mem_sup_left hζz
  · have hε'eq : ε' = ζ'⁻¹ * σ := by rw [hσeq]; group
    rw [hγeq, h, hε'eq]
    exact (zpowers z ⊔ zpowers σ).mul_mem (Subgroup.mem_sup_left hζz)
      ((zpowers z ⊔ zpowers σ).mul_mem (Subgroup.mem_sup_left ((zpowers z).inv_mem hζ'z))
        (Subgroup.mem_sup_right (mem_zpowers σ)))


theorem autLevelC_of_shape
    {Kb : Type} [Group Kb] [Finite Kb]
    (hshape : HasL2Model Kb Odd ∨ Nonempty (Kb ≃* alternatingGroup (Fin 7))) : AutLevelC Kb := by
  rcases hshape with h | ⟨⟨e7⟩⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
    exact autLevelC_of_L2 hF e
  · exact autLevelC_of_A7 e7

end CFSG.GH74.GLS.C3.Layer1.Thm1
