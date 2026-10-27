module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldConj
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldNF

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section GraphFieldPlanes


theorem exists_inner_ne_one_of_graphField {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2)
    (hF : ¬ ∃ α ∈ E, D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1)
    {β : MulAut ↥(adjointGroup Tag.D4 K)} (hβE : β ∈ E) {ε₀ : ℕ} {σ₀ : K ≃+* K}
    (hε₀ : ε₀ = 1 ∨ ε₀ = 2) (hβ : HasNF β ε₀ σ₀) :
    ∃ ι ∈ E, ι ≠ 1 ∧ ι ∈ inner (adjointGroup Tag.D4 K) := by
  classical
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  obtain ⟨x, hxE, hxβ⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers β := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers β := fun x hx => h x hx
    have h1 : Nat.card E ∣ Nat.card (Subgroup.zpowers β) := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hEc] at h1
    have h2 := h1.trans (orderOf_dvd_of_pow_eq_one hβ3)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    norm_num at h3
  have hx3 : x ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x hxE
  by_cases hxin : x ∈ inner (adjointGroup Tag.D4 K)
  · exact ⟨x, hxE, fun h => hxβ (h ▸ one_mem _), hxin⟩
  obtain ⟨g, a, σ, ε, hε, hxeq, hσ3, hcase⟩ := outer_cube_normal_form_cases x hx3 hxin
  have hε0 : ε ≠ 0 := by
    rcases hcase with ⟨h, hσ1⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd ⟨x, hxE, g, a, σ, ε, hε, hσ3, ⟨h, hσ1⟩, hxeq⟩ hF
    · exact h
    · exact h
  have hxNF : HasNF x ε σ := ⟨g, a, hxeq⟩
  obtain ⟨y, hyE, hyNF, hyβ⟩ : ∃ y ∈ E, (∃ σ' : K ≃+* K, HasNF y 0 σ') ∧
      (y = 1 → x ∈ Subgroup.zpowers β) := by
    by_cases hεε : ε₀ = ε
    · refine ⟨β * (x * x), E.mul_mem hβE (E.mul_mem hxE hxE), ⟨σ₀ * (σ * σ), ?_⟩, ?_⟩
      · have h := hβ.mul (hxNF.mul hxNF)
        have h' := h.mod_three
        rwa [show (ε₀ + (ε + ε)) % 3 = 0 by omega] at h'
      · intro hy
        have h1 : x * x = β⁻¹ := eq_inv_of_mul_eq_one_right hy
        have h2 : x = β⁻¹ * β⁻¹ := by
          have h3 : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
          calc x = 1 * x := (one_mul x).symm
            _ = x * (x * x) * x := by rw [h3]
            _ = x * x * (x * x) := by group
            _ = β⁻¹ * β⁻¹ := by rw [h1]
        rw [h2]
        exact mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers β))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers β))
    · refine ⟨β * x, E.mul_mem hβE hxE, ⟨σ₀ * σ, ?_⟩, ?_⟩
      · have h' := (hβ.mul hxNF).mod_three
        have h3 : ε₀ + ε = 3 := by omega
        rwa [h3, show 3 % 3 = 0 from rfl] at h'
      · intro hy
        have h1 : x = β⁻¹ := eq_inv_of_mul_eq_one_right hy
        rw [h1]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers β)
  obtain ⟨σ', g', a', hy⟩ : ∃ σ' : K ≃+* K, ∃ (g' : adjointGroup Tag.D4 K)
      (a' : Fin Tag.D4.rank → Kˣ), y = MulAut.conj g' * (exactNormalAut Tag.D4 K a' σ' 0 *
        d4Graph K 0) := by
    obtain ⟨σ', g', a', h⟩ := hyNF
    exact ⟨σ', g', a', h⟩
  have hy3 : y ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian y hyE
  have hσ'3 : σ' ^ 3 = 1 := cube_normal_form_sigma_cube (hy ▸ hy3)
  by_cases hσ' : σ' = 1
  · subst hσ'
    refine ⟨y, hyE, fun h => hxβ (hyβ h), ?_⟩
    rw [hy]
    exact mem_inner_of_normal_form_one g' a' (hy ▸ hy3)
  · exact absurd ⟨y, hyE, g', a', σ', 0, by norm_num, hσ'3, ⟨rfl, hσ'⟩, hy⟩ hF

variable {K : Type} [Field K]

theorem fixedSubgroup_d4Twist_ne_top [Finite K] (σ : K ≃+* K) :
    fixedSubgroup (d4Twist 1 σ) ≠ ⊤ := by
  intro h
  have h0 : adjX Tag.D4 K ⟨0, by decide⟩ 1 ∈ fixedSubgroup (d4Twist 1 σ) :=
    h ▸ Subgroup.mem_top _
  have h1 : d4Twist 1 σ (adjX Tag.D4 K ⟨0, by decide⟩ 1) = adjX Tag.D4 K ⟨0, by decide⟩ 1 := h0
  have r0 : d4Rho (⟨0, by decide⟩ : Fin Tag.D4.rank) = ⟨1, by decide⟩ := by decide
  rw [d4Twist_one_adjX, map_one, r0] at h1
  have h2 := congrArg (fun g : adjointGroup Tag.D4 K =>
    rootCoord (FieldGraphFieldPointwise.single_pos
      (⟨0, by decide⟩ : Fin Tag.D4.rank)) (g : ModGL Tag.D4 K)) h1
  simp only [adjX] at h2
  rw [FieldGraphFieldPointwise.rootCoord_single_xUnit,
    FieldGraphFieldPointwise.rootCoord_single_xUnit] at h2
  simp at h2

theorem d4GfTwist_eq_or (T σ : K ≃+* K) (ε : ℕ) :
    d4GfTwist T σ ε = T ∨ d4GfTwist T σ ε = T⁻¹ := by
  unfold d4GfTwist
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] def D4TwistedSubfieldMaximal : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → ∀ σ : K ≃+* K, orderOf σ = 3 →
    ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), fixedSubgroup (d4Twist 1 σ) ≤ M →
      M = fixedSubgroup (d4Twist 1 σ) ∨ M = ⊤

theorem d4ThreeGraphFieldPlanes_of_maximal (hmax : D4TwistedSubfieldMaximal) :
    D4ThreeGraphFieldPlanes := by
  unfold D4ThreeGraphFieldPlanes
  intro K _ _ hK3 E hE hEc hnoF hGF
  obtain ⟨β, hβE, g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hβ⟩ := hGF
  classical
  haveI := hE
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  obtain ⟨e, T, he0, hef, hT, hT3, hσT⟩ := exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hef]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_left hℓ.two_le _
  have hσ' : σ = T ∨ σ = T⁻¹ := by
    rcases hσT with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)).symm)
  have hε12 : ε = 1 ∨ ε = 2 := by omega
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  obtain ⟨ι, hιE, hι1, hιin⟩ := exists_inner_ne_one_of_graphField hEc hnoF hβE hε12 ⟨g, a, hβ⟩
  obtain ⟨k, rfl⟩ := hιin
  have hββ3 : (β * MulAut.conj k) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian _ (E.mul_mem hβE hιE)
  have hNF : HasNF (β * MulAut.conj k) ε σ := by
    have h := (show HasNF β ε σ from ⟨g, a, hβ⟩).mul (hasNF_conj k)
    simpa only [add_zero, mul_one] using h
  obtain ⟨g₂, a₂, hβ₂⟩ := hNF
  obtain ⟨ψa, hFa⟩ := exists_conj_fixedSubgroup_D4_graphField hK hK4 he0 hef T σ hT hT3 hT1 hσ'
    hε12 g a β hβ3 hβ
  obtain ⟨ψb, hFb⟩ := exists_conj_fixedSubgroup_D4_graphField hK hK4 he0 hef T σ hT hT3 hT1 hσ'
    hε12 g₂ a₂ (β * MulAut.conj k) hββ3 hβ₂
  have hord : orderOf (d4GfTwist T σ ε) = 3 := by
    have hT' : orderOf T = 3 := orderOf_eq_prime hT3 hT1
    rcases d4GfTwist_eq_or T σ ε with h | h
    · rw [h]; exact hT'
    · rw [h, orderOf_inv]; exact hT'
  have hΓne := fixedSubgroup_d4Twist_ne_top (d4GfTwist T σ ε)
  have hβ1 : β ≠ 1 := by
    rintro rfl
    rw [fixedSubgroup_conj_one] at hFa
    exact hΓne hFa.symm
  have hββ1 : β * MulAut.conj k ≠ 1 := by
    intro h
    rw [h, fixedSubgroup_conj_one] at hFb
    exact hΓne hFb.symm
  haveI := inner_normal (adjointGroup Tag.D4 K)
  refine closure_fixUnion_eq_top_of_kernel_escape (N := inner (adjointGroup Tag.D4 K))
    (hmax K hK3 (d4GfTwist T σ ε) hord) ?_ hβE hιE hβ1 hββ1 hι1 ⟨k, rfl⟩ hFa hFb
  intro ι' hι' hfix
  obtain ⟨z, rfl⟩ := hι'
  have hz : z = 1 := by
    refine eq_one_of_commute_fixed_twisted_D4 (d4GfTwist T σ ε) fun u hu => ?_
    have h1 := hfix u hu
    rw [MulAut.conj_apply] at h1
    calc z * u = (z * u * z⁻¹) * z := by group
      _ = u * z := by rw [h1]
  rw [hz, map_one]

end GraphFieldPlanes

end CFSG.LieType.SeitzGeneration.ExcWideThree
