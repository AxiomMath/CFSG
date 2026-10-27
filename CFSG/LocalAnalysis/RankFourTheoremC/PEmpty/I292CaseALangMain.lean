module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALinRed
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangField
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangGraph
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace I292CaseALang

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem exists_conj_standard_of_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {σ : K ≃+* K} (A : GL (Fin n) K) {ε : ℕ} (hε : ε ≤ 1)
    (ht : (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) ^ orderOf σ = 1)
    (hev : ε = 1 → Even (orderOf σ)) :
    ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ * dualAut n K ^ ε =
      conjAut n K H * (fieldAut n K σ * dualAut n K ^ ε) * (conjAut n K H)⁻¹ := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at ht
    obtain ⟨M, hM⟩ := exists_conj_of_pow_orderOf_eq_one hn A σ ht
    exact ⟨M, by rw [pow_zero, mul_one]; exact hM⟩
  · have hev' : Even (orderOf σ) := hev rfl
    rw [pow_one] at ht ⊢
    obtain ⟨r, hr⟩ := hev'
    have hτ : orderOf (σ * σ) = r := by
      rw [← sq, orderOf_pow_of_dvd two_ne_zero ⟨r, by omega⟩]
      omega
    set t := conjAut n K A * fieldAut n K σ * dualAut n K with htdef
    set X : GL (Fin n) K := A * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose A) with hX
    have hsq : t ^ 2 = conjAut n K X * fieldAut n K (σ * σ) :=
      sq_conjAut_fieldAut_dualAut A σ
    have hpow : (conjAut n K X * fieldAut n K (σ * σ)) ^ orderOf (σ * σ) = 1 := by
      rw [← hsq, hτ, ← pow_mul, show 2 * r = orderOf σ by omega]
      exact ht
    obtain ⟨M₁, hM₁⟩ := exists_conj_of_pow_orderOf_eq_one hn X (σ * σ) hpow
    have hform : (conjAut n K M₁)⁻¹ * t * conjAut n K M₁ =
        conjAut n K (M₁⁻¹ * A * GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose M₁)) * fieldAut n K σ * dualAut n K := by
      rw [htdef, map_mul, map_mul, map_inv]
      calc (conjAut n K M₁)⁻¹ * (conjAut n K A * fieldAut n K σ * dualAut n K) *
            conjAut n K M₁
          = (conjAut n K M₁)⁻¹ * conjAut n K A * fieldAut n K σ *
              (dualAut n K * conjAut n K M₁) := by group
        _ = (conjAut n K M₁)⁻¹ * conjAut n K A * fieldAut n K σ *
              (conjAut n K (GeneralLinearGroup.inverseTranspose M₁) * dualAut n K) := by
            rw [dualAut_mul_conjAut]
        _ = (conjAut n K M₁)⁻¹ * conjAut n K A * (fieldAut n K σ *
              conjAut n K (GeneralLinearGroup.inverseTranspose M₁)) * dualAut n K := by group
        _ = _ := by rw [fieldAut_mul_conjAut]; group
    have hsq' : (conjAut n K (M₁⁻¹ * A * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose M₁)) * fieldAut n K σ * dualAut n K) ^ 2 =
        fieldAut n K (σ * σ) := by
      rw [← hform, sq]
      have h3 : (conjAut n K M₁)⁻¹ * t * conjAut n K M₁ *
          ((conjAut n K M₁)⁻¹ * t * conjAut n K M₁) =
          (conjAut n K M₁)⁻¹ * t ^ 2 * conjAut n K M₁ := by rw [sq]; group
      rw [h3, hsq, hM₁]
      group
    obtain ⟨H', hH'⟩ := exists_conj_of_sq_eq hn ⟨r, hr⟩ _ hsq'
    refine ⟨M₁ * H', ?_⟩
    calc t = conjAut n K M₁ * ((conjAut n K M₁)⁻¹ * t * conjAut n K M₁) *
          (conjAut n K M₁)⁻¹ := by group
      _ = conjAut n K M₁ * (conjAut n K H' * (fieldAut n K σ * dualAut n K) *
          (conjAut n K H')⁻¹) * (conjAut n K M₁)⁻¹ := by rw [hform, hH']
      _ = _ := by rw [map_mul, _root_.mul_inv_rev]; group

theorem isCyclic_ringEquiv (K : Type) [Field K] [Finite K] : IsCyclic (K ≃+* K) := by
  obtain ⟨p, f, hp, hf, hK⟩ := exists_card_eq_prime_pow K
  obtain ⟨σ, -, -, hσ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK
  refine ⟨⟨σ, fun x => Subgroup.mem_zpowers_iff.1 ?_⟩⟩
  rw [hσ]
  exact Subgroup.mem_top x

end I292CaseALang

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem kd292LangConjInput_holds : KD292LangConjInput := by
  intro K _ _ n hn T hT hTD
  classical
  haveI : IsCyclic (K ≃+* K) := I292CaseALang.isCyclic_ringEquiv K
  set φ := ProjectivePlane.linearFieldPart K hn with hφ
  have hφT : ∀ t ∈ T, φ t = 1 → t = 1 := by
    intro t htT h1
    obtain ⟨σ, A, ε, hε, hdec⟩ := ProjectivePlane.exists_standard_form K n hn t
    have hσ : σ = 1 := by
      have h2 := ProjectivePlane.linearFieldPart_eq hn (A := A) (σ := σ) hε
      rw [← hdec] at h2
      exact h2.symm.trans h1
    subst hσ
    apply hTD t htT
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · left
      rw [hdec, pow_zero, mul_one, map_one, mul_one]
      exact conjAut_mem_linearAutGroup A
    · right
      exact ⟨A, by rw [hdec, pow_one, map_one, mul_one]⟩
  let ψ : T →* (K ≃+* K) := φ.comp T.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hφT x x.2 hx)
  haveI : IsCyclic T := isCyclic_of_injective ψ hψ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  set t : MulAut (projectiveSL n K) := (g : MulAut (projectiveSL n K)) with htdef
  have htT : t ∈ T := g.2
  have hord2 : ∃ j : ℕ, orderOf t = 2 ^ j := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hT) g
    exact ⟨j, by rw [htdef, Subgroup.orderOf_coe]; exact hj⟩
  have hfo : IsOfFinOrder g := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hT) g
    exact orderOf_pos_iff.1 (by rw [hj]; positivity)
  have hgen : ∀ x ∈ T, ∃ k : ℕ, x = t ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := (hfo.mem_powers_iff_mem_zpowers).2 (hg ⟨x, hx⟩)
    refine ⟨k, ?_⟩
    have h1 := congrArg (fun y : T => (y : MulAut (projectiveSL n K))) hk
    simpa [htdef] using h1.symm
  by_cases ht1 : t = 1
  · refine ⟨1, one_mem _, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := hgen x hx
    exact ⟨1, 0, zero_le_one, by simp [ht1]⟩
  · obtain ⟨σ, A, ε, hε, hdec⟩ := ProjectivePlane.exists_standard_form K n hn t
    have hφt : φ t = σ := by
      rw [hdec]
      exact ProjectivePlane.linearFieldPart_eq hn hε
    have hord : orderOf t = orderOf σ := by
      have h1 := orderOf_injective ψ hψ ⟨t, htT⟩
      have e1 : ψ ⟨t, htT⟩ = σ := hφt
      rw [e1, Subgroup.orderOf_mk] at h1
      exact h1.symm
    have hpow : t ^ orderOf σ = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one t
    have hev : ε = 1 → Even (orderOf σ) := by
      intro _
      obtain ⟨j, hj⟩ := hord2
      rw [← hord, hj]
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact ht1 (orderOf_eq_one_iff.1 (by rw [hj, pow_zero]))
      exact Nat.even_pow.2 ⟨even_two, hj0⟩
    obtain ⟨H, hH⟩ := I292CaseALang.exists_conj_standard_of_pow hn A hε
      (by rw [← hdec]; exact hpow) hev
    refine ⟨(conjAut n K H)⁻¹, inv_mem (conjAut_mem_linearAutGroup H), fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := hgen x hx
    have h1 : (conjAut n K H)⁻¹ * t * ((conjAut n K H)⁻¹)⁻¹ =
        fieldAut n K σ * dualAut n K ^ ε := by
      rw [hdec, hH]
      group
    rw [← conj_pow, h1]
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · exact ⟨σ ^ k, 0, zero_le_one, by rw [pow_zero, mul_one, mul_one, map_pow]⟩
    · have hδδ : dualAut n K ^ 2 = 1 := by
        rw [sq]
        exact (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
      have hcomm : Commute (fieldAut n K σ) (dualAut n K) := (dualAut_mul_fieldAut σ).symm
      refine ⟨σ ^ k, k % 2, by omega, ?_⟩
      rw [pow_one, hcomm.mul_pow, map_pow, pow_eq_pow_mod k hδδ]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
