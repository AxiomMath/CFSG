module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApSing
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApZ0
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneMinus
public import CFSG.RankThree.PartOne.KE.FiniteFieldAlgClosure

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Kernel

theorem ap_kerB {L : Type} [Field L] {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    rootCharKernel (τ := TwistTag.D4.tag) (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) ⊆
        threeRootSet d4Qr₁ d4Qr₂ d4Qr₃ ∧
      ∀ α ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃,
        rootChar (τ := TwistTag.D4.tag)
          (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ α : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar (τ := TwistTag.D4.tag) (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) α =
        ω ^ α 2 := fun α => by
    have e := rootChar_d4_apply (K := L) (![1, 1, ω, 1] : Fin TwistTag.D4.tag.rank → Lˣ) α
    rw [e]
    simp
    rfl
  refine ⟨fun α ⟨hα, h1⟩ => ?_, fun α hα => ?_⟩
  · rw [hc] at h1
    have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    have hdvd : (3 : ℤ) ∣ α 2 := by
      have := orderOf_dvd_iff_zpow_eq_one.2 h1
      rw [hord] at this
      exact_mod_cast this
    obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα
    have key : ∀ k : Fin 24, (3 : ℤ) ∣ d4RootVec k 2 →
        ((d4RootVec k 0 = 1 ∧ d4RootVec k 1 = 0 ∧ d4RootVec k 2 = 0 ∧ d4RootVec k 3 = 0) ∨
          (d4RootVec k 0 = -1 ∧ d4RootVec k 1 = 0 ∧ d4RootVec k 2 = 0 ∧ d4RootVec k 3 = 0) ∨
          (d4RootVec k 0 = 0 ∧ d4RootVec k 1 = -1 ∧ d4RootVec k 2 = 0 ∧ d4RootVec k 3 = 0) ∨
          (d4RootVec k 0 = 0 ∧ d4RootVec k 1 = 1 ∧ d4RootVec k 2 = 0 ∧ d4RootVec k 3 = 0) ∨
          (d4RootVec k 0 = 0 ∧ d4RootVec k 1 = 0 ∧ d4RootVec k 2 = 0 ∧ d4RootVec k 3 = 1) ∨
          (d4RootVec k 0 = 0 ∧ d4RootVec k 1 = 0 ∧ d4RootVec k 2 = 0 ∧ d4RootVec k 3 = -1)) := by
      decide +kernel
    simp only [threeRootSet]
    rcases key k hdvd with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
        ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact Or.inl (by funext i; fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3)
    · exact Or.inr (Or.inl (by
        funext i; fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3))
    · exact Or.inr (Or.inr (Or.inl (by
        funext i; fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        funext i; fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        funext i; fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
        funext i; fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3)))))
  · have h0 : α 2 = 0 := by
      simp only [threeRootSet] at hα
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hc, h0, zpow_zero]

end Kernel

theorem ap_plane_good {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) (hT : D4PlaneInTorusMinus p f hp K σ E) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      D4PlaneGood σ (p ^ f) (E.map (β⁻¹).toMonoidHom) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L, hLF, hLA, hLcl, hLchar, g₀, hg₀, β, hβ⟩ := hT
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg₀C, -, hg₀F⟩ := hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hq4 : 4 ≤ p ^ f := le_trans (by omega) (le_trans hp5 (Nat.le_self_pow (by omega) p))
  have hq2 : 2 < p ^ f := by omega
  set E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := E.map (β⁻¹).toMonoidHom
    with hE'
  have hE'ea : IsElementaryAbelian 3 E' := IsElementaryAbelian.map (β⁻¹).toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hE'3 : ∀ e ∈ E', e ^ 3 = 1 := fun e he => elemPow_eq_one_of_isElementaryAbelian e he
  have hEψ : ∀ e ∈ E', g₀⁻¹ * triEmb K σ L e * g₀ ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L Fr) := by
    rintro _ ⟨e₀, he₀, rfl⟩
    exact hβ e₀ he₀
  refine ⟨β, ?_, ?_⟩
  ·
    obtain ⟨ω, hω3, hω1, xA, hxA, -, -, hbA, -⟩ := ap_plane_elements hq E' hcard' hE'3 hEψ
    have hωne : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, a ≠ 1 → ∀ x : graphFixedRootGroup
        TwistTag.D4 K σ.toRingHom, rootDiagUnit TwistTag.D4.tag a = g₀⁻¹ * triEmb K σ L x * g₀ →
        x ≠ 1 := by
      intro a ha1 x hxa hx1
      apply ha1
      apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
      rw [hxa, hx1, map_one, mul_one, inv_mul_cancel, rootDiagUnit_one]
    have hAne : (![ω, ω, 1, ω] : Fin TwistTag.D4.tag.rank → Lˣ) ≠ 1 := fun h =>
      hω1 (by simpa using congrFun h 0)
    have hxA1 : xA ≠ 1 := hωne _ hAne xA hbA
    refine ⟨xA, hxA, hxA1, ap_singular hp2 hp3 hf hq hK hσ hω3 hω1 hg₀C hg₀F ?_⟩
    rw [hbA]
    group
  ·
    intro Z₀ hZc hZab hZn _ t ht
    have hzM := trialityOpposition_mem_monomialSubgroup (K := L)
    have hzW := weylQuotientHom_trialityOpposition_smul (K := L)
    obtain ⟨k, hkF, hkAlg, hkcl, hkcard⟩ := exists_finite_field_isAlgClosure p f hf K L
    obtain ⟨PA, hAfin, hAq, hAQ, hAR, hAadj, hAnorm, hAcent, -⟩ :=
      d4Q_a2_family (L := L) (k := k) hf hkcard hq2 Fr hFr (trialityOpposition L) hzM hzW
    obtain ⟨PB, hBfin, hBq, hBQ, hBR, hBadj, hBnorm, hBcent⟩ :=
      d4Q_a3_family (ℓ := p) (f := f) (L := L) hf hq4 hzM hzW
    have hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
        (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) → P ≤ (triEmb K σ L).range := by
      intro P hPC hPF
      rw [triEmb_range hp hf hK hσ Fr hFr]
      exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
    obtain ⟨hB1, hB2, hB3⟩ := d4Q_isRoot
    have hSB : ∀ α ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃, IsRoot TwistTag.D4.tag α := by
      intro α hα
      simp only [threeRootSet] at hα
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hB1, IsRoot.neg hB1, hB2, IsRoot.neg hB2, hB3, IsRoot.neg hB3]
    have hSBn : ∀ α ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃, -α ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃ := by
      intro α hα
      simp only [threeRootSet] at hα ⊢
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · rw [neg_neg]
        exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [neg_neg]
        exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · rw [neg_neg]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hAroot : (Pi.single (2 : Fin TwistTag.D4.tag.rank) 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈
        d4LongA2 :=
      d4LongA2_mem_iff.2 (Or.inl (by funext j; fin_cases j <;> rfl))
    have hBroot : ∀ i : Fin TwistTag.D4.tag.rank, i ≠ 2 →
        (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃ := by
      intro i hi
      simp only [threeRootSet]
      fin_cases i
      · exact Or.inl (by funext j; fin_cases j <;> rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by funext j; fin_cases j <;> rfl))))
      · exact absurd rfl hi
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by funext j; fin_cases j <;> rfl)))))
    exact ap_Z0_of_families hq hg₀C hg₀F hperf hcomm (SA := d4LongA2)
      (SB := threeRootSet d4Qr₁ d4Qr₂ d4Qr₃) (fun _ h => d4LongA2_isRoot h)
      (fun _ h => d4LongA2_neg_mem h) hSB hSBn
      ⟨PA, hAfin, hAq, hAQ, hAR, hAadj, hAnorm, hAcent⟩
      ⟨PB, hBfin, hBq, hBQ, hBR, hBadj, hBnorm, hBcent⟩
      (fun ω hω3 hω1 => ⟨fun α hα => (d4Minus_rootCharKernel hω3 hω1 α).1 hα,
        fun α hα => ((d4Minus_rootCharKernel hω3 hω1 α).2 hα).2⟩)
      (fun ω hω3 hω1 => ap_kerB hω3 hω1) hAroot hBroot E' hcard' hE'3 hEψ Z₀ hZc hZab hZn t ht

end CFSG.GH74.GLS.Stage2.Bender.Thm1
