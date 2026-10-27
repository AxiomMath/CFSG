module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


abbrev g2e (j : Fin 2) : Fin Tag.G2.rank := j

theorem g2_fin_cases (i : Fin Tag.G2.rank) : i = g2e 0 ∨ i = g2e 1 := by
  revert i
  decide

theorem g2e_ne : g2e 0 ≠ g2e 1 := by decide

def detG2 (u v : Fin Tag.G2.rank → ℤ) : ℤ := u (g2e 0) * v (g2e 1) - u (g2e 1) * v (g2e 0)

theorem g2_det_check :
    ∀ k l : Fin 12,
      iform ((Tag.rootCertificate .G2).root k) ((Tag.rootCertificate .G2).root l) ≠ 0 →
      (Tag.rootCertificate .G2).root l ≠ (Tag.rootCertificate .G2).root k →
      (Tag.rootCertificate .G2).root l ≠ -(Tag.rootCertificate .G2).root k →
      (detG2 ((Tag.rootCertificate .G2).root k) ((Tag.rootCertificate .G2).root l)).natAbs ∈
        ({1, 2, 3} : Finset ℕ) := by
  decide +kernel

theorem g2_det_natAbs_mem {α β : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α)
    (hβ : IsRoot Tag.G2 β) (h : iform α β ≠ 0) (h1 : β ≠ α) (h2 : β ≠ -α) :
    (detG2 α β).natAbs ∈ ({1, 2, 3} : Finset ℕ) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hα
  obtain ⟨l, hl, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hβ
  have hk' : k < 12 := hk
  have hl' : l < 12 := hl
  exact g2_det_check ⟨k, hk'⟩ ⟨l, hl'⟩ h h1 h2

theorem chi_eq_one_of_single {M : Type*} [CommGroup M] {τ : Tag}
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (h : ∀ j, χ (Multiplicative.ofAdd (Pi.single j 1 : Fin τ.rank → ℤ)) = 1)
    (v : Fin τ.rank → ℤ) : χ (Multiplicative.ofAdd v) = 1 := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, ofAdd_sum, map_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [ofAdd_zsmul, map_zpow, h j, one_zpow]

theorem g2_chi_single_eq_one {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.G2.rank → ℤ) →* M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hχp : ∀ γ, IsRoot Tag.G2 γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    {α β : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) (hβ : IsRoot Tag.G2 β)
    (hαχ : χ (Multiplicative.ofAdd α) = 1) (hβχ : χ (Multiplicative.ofAdd β) = 1)
    (h : iform α β ≠ 0) (h1 : β ≠ α) (h2 : β ≠ -α) (j : Fin Tag.G2.rank) :
    χ (Multiplicative.ofAdd (Pi.single j 1 : Fin Tag.G2.rank → ℤ)) = 1 := by
  have hD := g2_det_natAbs_mem hα hβ h h1 h2
  have hcomb : ∀ a b : ℤ, χ (Multiplicative.ofAdd (a • α + b • β)) = 1 := fun a b => by
    rw [ofAdd_add, map_mul, ofAdd_zsmul, ofAdd_zsmul, map_zpow, map_zpow, hαχ, hβχ, one_zpow,
      one_zpow, mul_one]
  have hmul : χ (Multiplicative.ofAdd (detG2 α β • (Pi.single j 1 : Fin Tag.G2.rank → ℤ))) = 1 := by
    have e : ∃ a b : ℤ, detG2 α β • (Pi.single j 1 : Fin Tag.G2.rank → ℤ) = a • α + b • β := by
      rcases g2_fin_cases j with rfl | rfl
      · refine ⟨β (g2e 1), -α (g2e 1), ?_⟩
        funext i
        rcases g2_fin_cases i with rfl | rfl <;>
          simp [detG2, g2e_ne.symm] <;> ring
      · refine ⟨-β (g2e 0), α (g2e 0), ?_⟩
        funext i
        rcases g2_fin_cases i with rfl | rfl <;>
          simp [detG2, g2e_ne] <;> ring
    obtain ⟨a, b, e⟩ := e
    rw [e]
    exact hcomb a b
  set g := χ (Multiplicative.ofAdd (Pi.single j 1 : Fin Tag.G2.rank → ℤ)) with hg
  have hgD : g ^ detG2 α β = 1 := by
    rw [hg, ← map_zpow, ← ofAdd_zsmul]
    exact hmul
  have hgp : g ^ p = 1 := hχp _ (isRoot_single _ _)
  have h1' : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have h2' : (orderOf g : ℤ) ∣ detG2 α β := (orderOf_dvd_iff_zpow_eq_one).2 hgD
  have h3' : orderOf g ∣ (detG2 α β).natAbs := Int.natCast_dvd.1 h2'
  rcases (Nat.dvd_prime hp).1 h1' with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h3'
    have hpos : 0 < (detG2 α β).natAbs := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hD
      omega
    have := Nat.le_of_dvd hpos h3'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    omega

theorem g2_component_rank_one {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin Tag.G2.rank → ℤ) →* M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hχp : ∀ γ, IsRoot Tag.G2 γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    (hχ1 : ∃ γ, IsRoot Tag.G2 γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1)
    (i : KernelComponent χ) :
    ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α := by
  intro α hα δ hδ
  by_contra hne
  push Not at hne
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hneg : -α ∈ componentRoots χ i := hΨ.neg_mem α hα
  have hS : ({α, -α} : Set (Fin Tag.G2.rank → ℤ)) ⊆ componentRoots χ i := by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hα, hneg]
  have hnot : ¬ ∀ a ∈ ({α, -α} : Set (Fin Tag.G2.rank → ℤ)), ∀ b ∈ componentRoots χ i,
      b ∉ ({α, -α} : Set (Fin Tag.G2.rank → ℤ)) → iform a b = 0 := by
    intro h
    rcases hΨ.irreducible _ hS h with h0 | h0
    · exact (Set.eq_empty_iff_forall_notMem.1 h0) α (Set.mem_insert _ _)
    · have : δ ∈ ({α, -α} : Set (Fin Tag.G2.rank → ℤ)) := h0 ▸ hδ
      rcases this with h | h
      · exact hne.1 h
      · exact hne.2 h
  push Not at hnot
  obtain ⟨a, ha, b, hb, hbS, hab⟩ := hnot
  have hbS' : b ≠ α ∧ b ≠ -α := by
    simpa [not_or] using hbS
  have hαb : iform α b ≠ 0 := by
    rcases ha with rfl | rfl
    · exact hab
    · rw [← neg_one_smul ℤ α, iform_smul_left] at hab
      intro h0
      exact hab (by rw [h0, mul_zero])
  obtain ⟨hαk, -⟩ := hα
  obtain ⟨hbk, -⟩ := hb
  have hsing := fun j => g2_chi_single_eq_one χ hp hp5 hχp hαk.1 hbk.1 hαk.2 hbk.2 hαb hbS'.1
    hbS'.2 j
  obtain ⟨γ, hγ, hγ1⟩ := hχ1
  exact hγ1 (chi_eq_one_of_single χ hsing γ)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
