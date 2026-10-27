module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightM

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Lifts

variable {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}

theorem IsPermAction.exists_commuting_lifts (hρ : IsPermAction θ ρ) [Finite X] {s t f : X}
    (hsN : s ∈ normalizer (M : Set X)) (htN : t ∈ normalizer (M : Set X))
    (hfN : f ∈ normalizer (M : Set X)) (hs2 : s * s = 1) (ht2 : t * t = 1)
    (hf4 : f * f * (f * f) = 1) (hst : s * t = t * s) (hfs : f * s = s * f)
    (hft : f * t = t * f) (ht1 : ρ ⟨t, htN⟩ = 1) {v : Fin 4 → Perm (Fin 9)}
    (hv0 : v 0 = ρ ⟨f, hfN⟩) (hvs : ∀ i, v i * ρ ⟨s, hsN⟩ = ρ ⟨s, hsN⟩ * v i)
    (hvv : ∀ i j, v i * v j = v j * v i) (hv2 : ∀ i, v i * v i = 1)
    (hvA : ∀ i, v i * v 0 ∈ alternatingGroup (Fin 9)) (hv1 : ∀ i, i ≠ 0 → v i * v 0 ≠ 1) :
    ∃ μ : Fin 4 → X, ∃ hμM : ∀ i, μ i ∈ M, μ 0 = 1 ∧ (∀ i, μ i * s = s * μ i) ∧
      (∀ i, μ i * t = t * μ i) ∧ (∀ i, μ i * f = f * μ i) ∧ (∀ i j, μ i * μ j = μ j * μ i) ∧
      (∀ i, μ i * μ i = 1) ∧ ∀ i, ρ ⟨μ i, le_normalizer (hμM i)⟩ = v i * v 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Cb : Perm (Fin 9) → Subgroup X := fun b =>
    ((centralizer ({b} : Set (Perm (Fin 9)))).comap ρ).map (normalizer (M : Set X)).subtype
  have hgen : ∀ (b : Perm (Fin 9)) (x : X) (hx : x ∈ normalizer (M : Set X)),
      ρ ⟨x, hx⟩ * b = b * ρ ⟨x, hx⟩ → zpowers x ≤ Cb b := by
    intro b x hx h
    rw [zpowers_le]
    exact ⟨⟨x, hx⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr h), rfl⟩
  have hext : ∀ (b : Perm (Fin 9)) (B : Subgroup X) (hBN : B ≤ normalizer (M : Set X)),
      B ≤ Cb b → ∀ (g : X) (hg : g ∈ B), b * ρ ⟨g, hBN hg⟩ = ρ ⟨g, hBN hg⟩ * b := by
    intro b B hBN hB g hg
    obtain ⟨z, hz, hzg⟩ := hB hg
    have h1 : z = ⟨g, hBN hg⟩ := Subtype.ext hzg
    rw [← h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hz)).symm
  have hcomm2 : ∀ a x y : Perm (Fin 9), a * x = x * a → a * y = y * a →
      a * (x * y) = x * y * a := by
    intro a x y h1 h2
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have hvc : ∀ i j, (v j * v 0) * (v i * v 0) = (v i * v 0) * (v j * v 0) := fun i j =>
    hcomm2 _ _ _ (by rw [mul_assoc, hvv 0 i, ← mul_assoc, hvv j i, mul_assoc])
      (by rw [mul_assoc, hv2 0, mul_one, hvv j 0, ← mul_assoc, hv2 0, one_mul])
  have hb2 : ∀ i, v i * v 0 * (v i * v 0) = 1 := fun i => by
    rw [mul_assoc, ← mul_assoc (v 0), hvv 0 i, mul_assoc, hv2 0, mul_one, hv2 i]
  have hcs : ∀ i, ρ ⟨s, hsN⟩ * (v i * v 0) = v i * v 0 * ρ ⟨s, hsN⟩ := fun i =>
    hcomm2 _ _ _ (hvs i).symm (hvs 0).symm
  have hcf : ∀ i, ρ ⟨f, hfN⟩ * (v i * v 0) = v i * v 0 * ρ ⟨f, hfN⟩ := fun i => by
    rw [← hv0]
    exact hcomm2 _ _ _ (hvv 0 i) rfl
  have hct : ∀ i, ρ ⟨t, htN⟩ * (v i * v 0) = v i * v 0 * ρ ⟨t, htN⟩ := fun i => by
    rw [ht1, one_mul, mul_one]
  have hf2g : IsPGroup 2 (zpowers f) := by
    have h4 : f ^ 4 = 1 := by
      rw [show f ^ 4 = f * f * (f * f) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact hf4
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one h4 : orderOf f ∣ 2 ^ 2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  set B₁ : Subgroup X := zpowers s ⊔ zpowers t ⊔ zpowers f with hB₁def
  have hB₁2 : IsPGroup 2 B₁ :=
    isPGroup_sup_zpowers_of_le_centralizer
      (isPGroup_sup_zpowers_of_le_centralizer (isPGroup_zpowers_of_mul_self hs2)
        (isPGroup_zpowers_of_mul_self ht2)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hst)))
      hf2g (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hfs.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hft.symm)))
  have hB₁N : B₁ ≤ normalizer (M : Set X) :=
    sup_le (sup_le (zpowers_le.mpr hsN) (zpowers_le.mpr htN)) (zpowers_le.mpr hfN)
  have hsB : s ∈ B₁ := mem_sup_left (mem_sup_left (mem_zpowers s))
  have htB : t ∈ B₁ := mem_sup_left (mem_sup_right (mem_zpowers t))
  have hfB : f ∈ B₁ := mem_sup_right (mem_zpowers f)
  have hB₁C : ∀ i, B₁ ≤ Cb (v i * v 0) := fun i =>
    sup_le (sup_le (hgen _ s hsN (hcs i)) (hgen _ t htN (hct i))) (hgen _ f hfN (hcf i))
  obtain ⟨m₁, hm₁M, hm₁C, hm₁2, hm₁ρ⟩ := hρ.exists_involution_lift_of_two_group hB₁N hB₁2
    (hvA 1) (hb2 1) (hv1 1 (by decide)) (hext _ B₁ hB₁N (hB₁C 1))
  have hcen : ∀ (B : Subgroup X) (m : X), m ∈ centralizer (B : Set X) →
      B ≤ centralizer ({m} : Set X) := fun B m hm y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hm y hy)
  set B₂ : Subgroup X := B₁ ⊔ zpowers m₁ with hB₂def
  have hB₂2 : IsPGroup 2 B₂ := isPGroup_sup_zpowers_of_le_centralizer hB₁2
    (isPGroup_zpowers_of_mul_self hm₁2) (hcen B₁ m₁ hm₁C)
  have hB₂N : B₂ ≤ normalizer (M : Set X) :=
    sup_le hB₁N (zpowers_le.mpr (le_normalizer hm₁M))
  have hB₁₂ : B₁ ≤ B₂ := le_sup_left
  have hm₁B : m₁ ∈ B₂ := mem_sup_right (mem_zpowers m₁)
  have hB₂C : ∀ i, B₂ ≤ Cb (v i * v 0) := fun i =>
    sup_le (hB₁C i) (hgen _ m₁ (le_normalizer hm₁M) (by rw [hm₁ρ]; exact hvc i 1))
  obtain ⟨m₂, hm₂M, hm₂C, hm₂2, hm₂ρ⟩ := hρ.exists_involution_lift_of_two_group hB₂N hB₂2
    (hvA 2) (hb2 2) (hv1 2 (by decide)) (hext _ B₂ hB₂N (hB₂C 2))
  set B₃ : Subgroup X := B₂ ⊔ zpowers m₂ with hB₃def
  have hB₃2 : IsPGroup 2 B₃ := isPGroup_sup_zpowers_of_le_centralizer hB₂2
    (isPGroup_zpowers_of_mul_self hm₂2) (hcen B₂ m₂ hm₂C)
  have hB₃N : B₃ ≤ normalizer (M : Set X) :=
    sup_le hB₂N (zpowers_le.mpr (le_normalizer hm₂M))
  have hB₂₃ : B₂ ≤ B₃ := le_sup_left
  have hm₂B : m₂ ∈ B₃ := mem_sup_right (mem_zpowers m₂)
  have hB₃C : ∀ i, B₃ ≤ Cb (v i * v 0) := fun i =>
    sup_le (hB₂C i) (hgen _ m₂ (le_normalizer hm₂M) (by rw [hm₂ρ]; exact hvc i 2))
  obtain ⟨m₃, hm₃M, hm₃C, hm₃2, hm₃ρ⟩ := hρ.exists_involution_lift_of_two_group hB₃N hB₃2
    (hvA 3) (hb2 3) (hv1 3 (by decide)) (hext _ B₃ hB₃N (hB₃C 3))
  have hC₁ : ∀ m, m ∈ centralizer (B₁ : Set X) → m * s = s * m ∧ m * t = t * m ∧ m * f = f * m :=
    fun m hm => ⟨(mem_centralizer_iff.mp hm s hsB).symm, (mem_centralizer_iff.mp hm t htB).symm,
      (mem_centralizer_iff.mp hm f hfB).symm⟩
  have hm₂C₁ : m₂ ∈ centralizer (B₁ : Set X) :=
    centralizer_le (SetLike.coe_subset_coe.mpr hB₁₂) hm₂C
  have hm₃C₁ : m₃ ∈ centralizer (B₁ : Set X) :=
    centralizer_le (SetLike.coe_subset_coe.mpr (hB₁₂.trans hB₂₃)) hm₃C
  have c12 : m₁ * m₂ = m₂ * m₁ := mem_centralizer_iff.mp hm₂C m₁ hm₁B
  have c13 : m₁ * m₃ = m₃ * m₁ := mem_centralizer_iff.mp hm₃C m₁ (hB₂₃ hm₁B)
  have c23 : m₂ * m₃ = m₃ * m₂ := mem_centralizer_iff.mp hm₃C m₂ hm₂B
  have hμC : ∀ i, (![1, m₁, m₂, m₃] : Fin 4 → X) i ∈ centralizer (B₁ : Set X) := by
    intro i
    fin_cases i
    exacts [one_mem _, hm₁C, hm₂C₁, hm₃C₁]
  refine ⟨![1, m₁, m₂, m₃], fun i => ?_, rfl, fun i => (hC₁ _ (hμC i)).1,
    fun i => (hC₁ _ (hμC i)).2.1, fun i => (hC₁ _ (hμC i)).2.2, fun i j => ?_, fun i => ?_,
    fun i => ?_⟩
  · fin_cases i
    exacts [one_mem _, hm₁M, hm₂M, hm₃M]
  · fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact (one_mul _).trans (mul_one _).symm
      | exact (mul_one _).trans (one_mul _).symm
      | exact c12 | exact c12.symm | exact c13 | exact c13.symm | exact c23 | exact c23.symm
  · fin_cases i
    exacts [one_mul _, hm₁2, hm₂2, hm₃2]
  · fin_cases i
    · exact (map_one ρ).trans (hv2 0).symm
    · exact hm₁ρ
    · exact hm₂ρ
    · exact hm₃ρ

end Lifts

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem rho_conj_ne_one_of_support_le_four (S : Sig36 X t J 9 e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {Q : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    (hCt : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {N : Subgroup X}
    (hNodd : ∀ k ∈ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M, k ∈ N ↔ Odd (orderOf k))
    (hNt : ∀ k ∈ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M, k ∈ N ∨ k * t ∈ N)
    {s g : X} (hgs : g⁻¹ * t * g = s) {y : X}
    (hyH : y ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hy2 : y * y = 1)
    (hys : y * s = s * y) (hyt : y * t = t * y) (hy1 : ρ ⟨y, hHN hyH⟩ ≠ 1)
    (hy4 : (ρ ⟨y, hHN hyH⟩).support.card ≤ 4) (hyN : g * y * g⁻¹ ∈ normalizer (M : Set X)) :
    ρ ⟨g * y * g⁻¹, hyN⟩ ≠ 1 := by
  classical
  intro h1
  have hto : orderOf t = 2 := S.pair.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← hto, pow_orderOf_eq_one]
  have htH := (hQK htQ).1
  have htK := (hQK htQ).2
  have hyx : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  generalize hxdef : g * y * g⁻¹ = x at hyN h1 hyx
  have hts : t = g * s * g⁻¹ := by rw [← hgs]; group
  have hxt : x * t = t * x := by
    rw [hts, ← hxdef]
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hys]
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  have hxK : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M :=
    ⟨hCt (mem_centralizer_singleton_iff.mpr hxt), hρ.mem_coreActionKernel hyN h1⟩
  have hx2 : x * x = 1 := by
    rw [← hxdef]
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hx1 : x ≠ 1 := by
    intro hx
    apply hy1
    have hy : y = 1 := by rw [hyx, hx]; group
    have h2 : (⟨y, hHN hyH⟩ : ↥(normalizer (M : Set X))) = 1 := Subtype.ext hy
    rw [h2, map_one]
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hxN : x ∉ N := by
    intro hxN
    have h2 := (hNodd x hxK).mp hxN
    rw [hxo] at h2
    exact (by decide : ¬ Odd 2) h2
  have hnN : x * t ∈ N := (hNt x hxK).resolve_left hxN
  have hnodd : Odd (orderOf (x * t)) := (hNodd _ (mul_mem hxK ⟨htH, htK⟩)).mp hnN
  have hxeq : x * t * t = x := by rw [mul_assoc, ht2, mul_one]
  obtain ⟨c, hc⟩ := exists_eq_conj_of_odd_orderOf hnodd ht2 (by rw [hxeq]; exact hx2)
  rw [hxeq] at hc
  have hgy : (c⁻¹ * g)⁻¹ * t * (c⁻¹ * g) = y := by
    rw [hyx, hc]; group
  exact S.false_of_support_le_four_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ
    (fun q hq => (hQK hq).1) (fun q hq => (hQK hq).2) hQ2 htQ hyH htQ hgy htH hto htK hyt.symm
    hCt hy1 hy4

end Sig36

end CFSG.ComponentClassification.SolMax
