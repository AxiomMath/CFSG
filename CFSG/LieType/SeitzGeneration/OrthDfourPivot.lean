module

public import CFSG.LieType.SeitzGeneration.OrthDfourComm
public import CFSG.LieType.SeitzGeneration.OrthGenLinear
public import CFSG.LieType.SeitzGeneration.OrthSdLines

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Choice

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_d4_choice (QW : QuadraticForm K W) (ℓ : W →ₗ[K] K) (ŝ : W)
    (h3 : 3 ≤ finrank K ↥(LinearMap.ker ℓ)) (hŝ : ℓ ŝ = 0) (hŝ0 : ŝ ≠ 0)
    (hstar : ∀ c : K, ∃ z, polar QW z ŝ ≠ c * ℓ z) :
    ∃ z₁ z₂ : W, ℓ z₁ = 0 ∧ ℓ z₂ = 0 ∧ QW z₁ = 0 ∧ z₁ ≠ 0 ∧ polar QW z₁ z₂ = 0 ∧
      (∀ c₁ c₂ : K, z₁ ≠ c₁ • ŝ + c₂ • z₂) ∧ (∀ c : K, z₂ ≠ c • z₁) := by
  classical
  have hŝY : ŝ ∈ LinearMap.ker ℓ := hŝ
  obtain ⟨z₁, hz₁Y, hz₁Q, hz₁0, hz₁ŝ⟩ : ∃ z₁ ∈ LinearMap.ker ℓ, QW z₁ = 0 ∧ z₁ ≠ 0 ∧
      ∀ c : K, z₁ ≠ c • ŝ := by
    by_cases hŝQ : QW ŝ = 0
    ·
      have hŝŝ : polar QW ŝ ŝ = 0 := polar_self_eq_zero hŝQ
      obtain ⟨y, hyY, hy⟩ : ∃ y ∈ LinearMap.ker ℓ, polar QW y ŝ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        by_cases hℓ : ∀ z, ℓ z = 0
        · obtain ⟨z, hz⟩ := hstar 0
          exact hz (by rw [zero_mul]; exact hcon z (hℓ z))
        · push Not at hℓ
          obtain ⟨z', hz'⟩ := hℓ
          obtain ⟨z, hz⟩ := hstar (polar QW z' ŝ / ℓ z')
          apply hz
          have hy : z - (ℓ z / ℓ z') • z' ∈ LinearMap.ker ℓ := by
            rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz', sub_self]
          have h0 := hcon _ hy
          rw [polar_sub_left, polar_smul_left_eq] at h0
          linear_combination h0
      obtain ⟨m, hm⟩ : ∃ m : K, m = polar QW y ŝ := ⟨_, rfl⟩
      have hm0 : m ≠ 0 := hm ▸ hy
      obtain ⟨z₁, hz₁⟩ : ∃ z₁ : W, z₁ = m⁻¹ • y + (-(m⁻¹ ^ 2 * QW y)) • ŝ := ⟨_, rfl⟩
      have hz₁Y : z₁ ∈ LinearMap.ker ℓ := by
        rw [hz₁]
        exact (LinearMap.ker ℓ).add_mem ((LinearMap.ker ℓ).smul_mem _ hyY)
          ((LinearMap.ker ℓ).smul_mem _ hŝY)
      have hz₁ŝ' : polar QW z₁ ŝ = 1 := by
        rw [hz₁, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hŝŝ, ← hm]
        field_simp
        ring
      have hz₁Q : QW z₁ = 0 := by
        rw [hz₁, QuadraticMap.map_add QW, map_smul_eq_sq, map_smul_eq_sq, hŝQ, polar_smul_left_eq,
          polar_smul_right_eq, ← hm]
        field_simp
        ring
      refine ⟨z₁, hz₁Y, hz₁Q, fun h => ?_, fun c hc => ?_⟩
      · rw [h, polar_zero_left] at hz₁ŝ'
        exact zero_ne_one hz₁ŝ'
      · rw [hc, polar_smul_left_eq, hŝŝ, mul_zero] at hz₁ŝ'
        exact zero_ne_one hz₁ŝ'
    · obtain ⟨z₁, hz₁Y, hz₁0, hz₁Q⟩ := exists_singular_of_three_le_any (Q := QW) h3
      refine ⟨z₁, hz₁Y, hz₁Q, hz₁0, fun c hc => ?_⟩
      have hQ : QW z₁ = c ^ 2 * QW ŝ := by rw [hc, map_smul_eq_sq]
      have hc0 : c = 0 := by
        by_contra hc0
        exact mul_ne_zero (pow_ne_zero 2 hc0) hŝQ (by rw [← hQ, hz₁Q])
      exact hz₁0 (by rw [hc, hc0, zero_smul])
  obtain ⟨z₂, hz₂Y, hz₂, hz₂span, hz₂c⟩ : ∃ z₂ ∈ LinearMap.ker ℓ, polar QW z₁ z₂ = 0 ∧
      (∀ c : K, z₂ ≠ c • z₁) ∧ (polar QW z₁ ŝ ≠ 0 ∨ z₂ = ŝ) := by
    by_cases hp : polar QW z₁ ŝ = 0
    · refine ⟨ŝ, hŝY, hp, fun c hc => ?_, Or.inr rfl⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hŝ0 (by rw [hc, zero_smul])
      exact hz₁ŝ c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
    · obtain ⟨z₂, hz₂Y, hz₂, hz₂span⟩ :=
        exists_mem_orth_not_span (Q := QW) (S := LinearMap.ker ℓ) h3 z₁
      refine ⟨z₂, hz₂Y, hz₂, fun c hc => hz₂span ?_, Or.inl hp⟩
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z₁)
  refine ⟨z₁, z₂, hz₁Y, hz₂Y, hz₁Q, hz₁0, hz₂, fun c₁ c₂ h => ?_, hz₂span⟩
  rcases hz₂c with hp | rfl
  · have h1 := congrArg (polar QW z₁) h
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hz₂, polar_self_eq_zero hz₁Q,
      mul_zero, add_zero] at h1
    have hc₁ : c₁ = 0 := (mul_eq_zero.mp h1.symm).resolve_right hp
    rw [hc₁, zero_smul, zero_add] at h
    have hc₂ : c₂ ≠ 0 := by
      rintro rfl
      exact hz₁0 (by rw [h, zero_smul])
    exact hz₂span c₂⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hc₂, one_smul]) |>.elim
  · exact hz₁ŝ (c₁ + c₂) (by rw [h, add_smul])

end Choice

section Pivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem exists_d4_pivot (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιB : Function.Injective ιB) (hα : Function.Injective α) (hιA : Function.Injective ιA)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (hW4 : 4 ≤ finrank K W) (hsurj : ∀ s ∈ lineSpace N, ∃ z, ιB (β z) = s)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthCentralizerSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (hstar : ∀ z : W, z ≠ 0 → ∀ c : K, ∃ z' : W,
      polar Q (ιA z') (ιA z) ≠ c * polar Q (ιB (β z')) (ιB (β z)))
    {s : V} (hsN : s ∈ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0) :
    ∃ y ∈ lineSpace L, y ≠ 0 ∧ y ∈ rootSet Q (orthCentralizerSpan Q E) s := by
  classical
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hAN : ∀ v ∈ lineSpace L, ∀ w ∈ lineSpace N, polar Q v w = 0 :=
    orthSep_lineSpace hK hL hN hLN
  have hNreg : PolarNondegOn Q (lineSpace N) :=
    polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : W →ₗ[K] V, b = ιB ∘ₗ β := ⟨_, rfl⟩
  have hbapp : ∀ z, b z = ιB (β z) := fun z => by rw [hb]; rfl
  have hbinj : Function.Injective b := fun z z' h =>
    hβ (hιB (by rw [← hbapp, ← hbapp]; exact h))
  have hbN : ∀ z, b z ∈ lineSpace N := fun z => by rw [hbapp]; exact hιBN _
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  let QW : QuadraticForm K W := Q.comp ιA
  have hQW : ∀ z, QW z = Q (ιA z) := fun z => rfl
  have hpolW : ∀ z z', polar QW z z' = polar Q (ιA z) (ιA z') := fun z z' => by
    simp only [QuadraticMap.polar, QW, QuadraticMap.comp_apply, map_add]
  let ℓ : W →ₗ[K] K := (polarBilin Q).flip s ∘ₗ b
  have hℓ : ∀ z, ℓ z = polar Q (b z) s := fun z => by simp [ℓ, polarBilin_apply_apply]
  obtain ⟨ŝ, hŝ⟩ := hsurj s hsN
  have hbŝ : b ŝ = s := by rw [hbapp, hŝ]
  have hŝ0 : ŝ ≠ 0 := by
    rintro rfl
    exact hs0 (by rw [← hbŝ, map_zero])
  have hℓŝ : ℓ ŝ = 0 := by rw [hℓ, hbŝ]; exact polar_self_eq_zero hsQ
  have h3 : 3 ≤ finrank K ↥(LinearMap.ker ℓ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ℓ
    have h2 : finrank K (LinearMap.range ℓ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range ℓ)
      simpa using this
    omega
  have hstar' : ∀ c : K, ∃ z, polar QW z ŝ ≠ c * ℓ z := by
    intro c
    obtain ⟨z', hz'⟩ := hstar ŝ hŝ0 c
    refine ⟨z', ?_⟩
    have : polar Q (b z') s = polar Q (ιB (β z')) (ιB (β ŝ)) := by rw [hbapp, hŝ]
    rw [hpolW, hℓ, this]
    exact hz'
  obtain ⟨z₁, z₂, hz₁ℓ, hz₂ℓ, hz₁Q, hz₁0, hz₁z₂, hind, hspan⟩ :=
    exists_d4_choice QW ℓ ŝ h3 hℓŝ hŝ0 hstar'
  have hz₁s : polar Q (b z₁) s = 0 := by rw [← hℓ]; exact hz₁ℓ
  have hz₂s : polar Q (b z₂) s = 0 := by rw [← hℓ]; exact hz₂ℓ
  have hind' : ∀ c₁ c₂ : K, b z₁ ≠ c₁ • s + c₂ • b z₂ := by
    intro c₁ c₂ h
    apply hind c₁ c₂
    apply hbinj
    rw [map_add, map_smul, map_smul, hbŝ]
    exact h
  obtain ⟨t, htN, hts, htb₂, htb₁⟩ := exists_perp_not_perp_two hNreg (hbN z₁) hsN (hbN z₂) hind'
  obtain ⟨u, hu⟩ : ∃ u, u = g (ιA z₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = g (ιA z₂) := ⟨_, rfl⟩
  have hu' : u = ιA (α z₁) + b z₁ := by rw [hu, hgact, hbapp]
  have hy' : y = ιA (α z₂) + b z₂ := by rw [hy, hgact, hbapp]
  have huQ : Q u = 0 := by rw [hu, hQg, ← hQW, hz₁Q]
  have huy : polar Q u y = 0 := by rw [hu, hy, hOg, ← hpolW, hz₁z₂]
  have hus : polar Q u s = 0 := by
    rw [hu', polar_add_left, hAN _ (hιAL _) s hsN, zero_add, hz₁s]
  have hsy : polar Q s y = 0 := by
    rw [hy', polar_add_right, polar_comm Q s (ιA (α z₂)), hAN _ (hιAL _) s hsN, zero_add,
      polar_comm, hz₂s]
  have hst : polar Q s t = 0 := by rw [polar_comm]; exact hts
  have hyt : polar Q y t = 0 := by
    rw [hy', polar_add_left, hAN _ (hιAL _) t htN, zero_add, polar_comm, htb₂]
  have hθ : polar Q u t ≠ 0 := by
    rw [hu', polar_add_left, hAN _ (hιAL _) t htN, zero_add, polar_comm]
    exact htb₁
  have hC : eichler Q s t ∈ orthCentralizerSpan Q E :=
    eichler_mem_span_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN) (Submodule.mem_sup_right htN)
  have hE : eichler Q u y ∈ orthCentralizerSpan Q E := by
    rw [hu, hy, ← eichler_conj hgO]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (eichler_mem_span_of_mem_sup hEΩ hL0
      (Submodule.mem_sup_right (hιAL z₁)) (Submodule.mem_sup_right (hιAL z₂))))
      (Subgroup.inv_mem _ hgH)
  have hmem := eichler_pivot_mem huQ hsQ hus huy hsy hst hyt hC hE
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = polar Q u t := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = Q y := ⟨_, rfl⟩
  rw [← hθdef, ← hcdef] at hmem
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = -(θ • ιA (α (z₂ + c • z₁))) := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = -(θ • (b z₂ + c • b z₁)) := ⟨_, rfl⟩
  have hsplit : -(θ • (y + c • u)) = y₀ + n₀ := by
    rw [hy', hu', hy₀, hn₀]
    simp only [map_add, map_smul]
    module
  have hy₀L : y₀ ∈ lineSpace L := by
    rw [hy₀]
    exact (lineSpace L).neg_mem ((lineSpace L).smul_mem _ (hιAL _))
  have hn₀N : n₀ ∈ lineSpace N := by
    rw [hn₀]
    exact (lineSpace N).neg_mem ((lineSpace N).smul_mem _ ((lineSpace N).add_mem (hbN _)
      ((lineSpace N).smul_mem _ (hbN _))))
  have hsy₀ : polar Q s y₀ = 0 := by
    rw [polar_comm]
    exact hAN _ hy₀L s hsN
  have hsn₀ : polar Q s n₀ = 0 := by
    rw [hn₀, polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq,
      polar_comm Q s (b z₂), polar_comm Q s (b z₁), hz₂s, hz₁s]
    ring
  have hn₀H : eichler Q s n₀ ∈ orthCentralizerSpan Q E :=
    eichler_mem_span_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN) (Submodule.mem_sup_right hn₀N)
  have hy₀H : eichler Q s y₀ ∈ orthCentralizerSpan Q E := by
    have h1 : eichler Q s y₀ * eichler Q s n₀ = eichler Q s (y₀ + n₀) := eichler_mul hsy₀ hsn₀
    have h2 : eichler Q s y₀ = eichler Q s (y₀ + n₀) * (eichler Q s n₀)⁻¹ := by
      rw [← h1]
      group
    rw [h2, ← hsplit]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hn₀H)
  refine ⟨y₀, hy₀L, ?_, hsy₀, hy₀H⟩
  rw [hy₀]
  refine neg_ne_zero.mpr (smul_ne_zero (hθdef ▸ hθ) ((map_ne_zero_iff ιA hιA).mpr
    ((map_ne_zero_iff α hα).mpr fun h0 => hspan (-c) ?_)))
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h0

end Pivot

end CFSG.LieType.SeitzGeneration.OrthBlk
