module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBasic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits

theorem isQuasisimple_modelUniv (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) :
    CFSG.Open.IsQuasisimple (modelUniv t n p e hp).K := by
  have hfund' : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    cases t <;> trivial
  exact (modelClauseZero t n p e hp hfund' hadm).1

theorem mem_map_conj_of_mem_center {K : Type*} [Group K] {r : K} (hrc : r ∈ Subgroup.center K)
    {S : Subgroup K} (hrS : r ∈ S) (g : K) : r ∈ S.map (MulAut.conj g).toMonoidHom := by
  refine ⟨r, hrS, ?_⟩
  show g * r * g⁻¹ = r
  rw [mul_inv_eq_iff_eq_mul]
  exact Subgroup.mem_center_iff.mp hrc g

theorem eq_one_of_mem_center_of_conj {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hconj : ∀ γ γ' : Fin D.rank → ℤ, IsLongestRoot D γ → IsLongestRoot D γ' →
      ∃ g : K, (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom =
        D.rootGroup γ' ⊔ D.rootGroup (-γ'))
    {γ₀ : Fin D.rank → ℤ} (hγ₀ : IsLongestRoot D γ₀)
    (hcen : ∀ r ∈ Subgroup.center K, r ∈ D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀) → r = 1)
    {γ : Fin D.rank → ℤ} (hγ : IsLongestRoot D γ) {g : K} {r : K}
    (hrR : r ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom)
    (hrc : r ∈ Subgroup.center K) : r = 1 := by
  obtain ⟨r', hr', hrr'⟩ := hrR
  have hr'eq : r' = r := by
    have h1 : g * r' * g⁻¹ = r := hrr'
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact mul_left_cancel (h1.trans (Subgroup.mem_center_iff.mp hrc g).symm)
  rw [hr'eq] at hr'
  obtain ⟨g₀, hg₀⟩ := hconj γ γ₀ hγ hγ₀
  refine hcen r hrc ?_
  have h := mem_map_conj_of_mem_center hrc hr' g₀
  rw [hg₀] at h
  exact h

theorem eq_one_of_mem_center_of_longest_root (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {γ₀ : Fin (modelUniv t n p e hp).D.rank → ℤ}
    (hγ₀ : IsLongestRoot (modelUniv t n p e hp).D γ₀)
    (hcen : ∀ r ∈ Subgroup.center (modelUniv t n p e hp).K,
      r ∈ (modelUniv t n p e hp).D.rootGroup γ₀ ⊔ (modelUniv t n p e hp).D.rootGroup (-γ₀) →
        r = 1)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e hp).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D)
    {r : (modelUniv t n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv t n p e hp).K) : r = 1 := by
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hγ' : IsLongestRoot (modelUniv t n p e hp).D γ := by
    rcases hγ with h | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact h
    · exact absurd ht hG2
    · exact absurd ht hD4
  exact eq_one_of_mem_center_of_conj
    (fun γ γ' h h' => exists_conj_of_isLongestRoot t n p e hp hfund hadm h h') hγ₀ hcen hγ' hrR
    hrc

theorem eq_one_of_mem_center_of_longest_node (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {k : Fin (modelUniv t n p e hp).D.rank}
    (hk : IsLongestRoot (modelUniv t n p e hp).D (Pi.single k 1))
    (hcen : ∀ r ∈ Subgroup.center (modelUniv t n p e hp).K,
      r ∈ rankOne (modelUniv t n p e hp).D.rootGroup k → r = 1)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e hp).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D)
    {r : (modelUniv t n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv t n p e hp).K) : r = 1 :=
  eq_one_of_mem_center_of_longest_root t n p e hp hG2 hD4 hk hcen hfund hadm hR hrR hrc

theorem eq_one_of_mem_center_of_two_long_nodes (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hrank : 2 ≤ (modelUniv t n p e hp).D.rank) (h0 : IsLongNode t n 0) (h1 : IsLongNode t n 1)
    {R : Subgroup (modelUniv t n p e hp).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D)
    {r : (modelUniv t n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv t n p e hp).K) : r = 1 := by
  obtain ⟨_, _, hct, hext⟩ := hasBruhatDatum t n p e hp hfund hadm
  let i₀ : Fin (modelUniv t n p e hp).D.rank := ⟨0, by omega⟩
  let i₁ : Fin (modelUniv t n p e hp).D.rank := ⟨1, by omega⟩
  have hL0 := isLongestRoot_single t n p e hp hfund hadm i₀ h0
  have hL1 := isLongestRoot_single t n p e hp hfund hadm i₁ h1
  have hG2 : t ≠ .G2 := fun h => by subst h; exact absurd h1 (by simp [IsLongNode])
  have hD4 : t ≠ .trialityD4 := fun h => by subst h; exact absurd h1 (by simp [IsLongNode])
  obtain ⟨g₁, hg₁⟩ := exists_conj_of_isLongestRoot t n p e hp hfund hadm hL0 hL1
  have hij : i₀ ≠ i₁ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  exact eq_one_of_mem_center_of_longest_node t n p e hp hG2 hD4 hL0
    (fun r hr hri => eq_one_of_mem_center_of_mem_rankOne hct hext hij ⟨g₁, hg₁⟩ hr hri)
    hfund hadm hR hrR hrc

theorem eq_one_of_mem_center_of_easy (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hne : ¬ (t = .PSL ∧ n = 2))
    (hPSp : t ≠ .PSp) (hPSU : t ≠ .PSU) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t n p e hp).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D)
    {r : (modelUniv t n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv t n p e hp).K) : r = 1 := by
  have hrank := two_le_rank t n p e hp hfund hadm hne (fun h => hPSU h.1)
  have h01 : IsLongNode t n 0 ∧ IsLongNode t n 1 := by
    cases t with
    | PSL => exact ⟨trivial, trivial⟩
    | PSU => exact absurd rfl hPSU
    | PSp => exact absurd rfl hPSp
    | POmegaOdd =>
      have : 3 ≤ n := hadm.2.2.1
      exact ⟨by show 0 + 1 < n; omega, by show 1 + 1 < n; omega⟩
    | POmegaPlus => exact ⟨trivial, trivial⟩
    | POmegaMinus =>
      have : 4 ≤ n := hadm.2.2
      exact ⟨by show 0 + 2 < n; omega, by show 1 + 2 < n; omega⟩
    | G2 => exact absurd rfl hG2
    | F4 => exact ⟨by show 0 < 2; decide, by show 1 < 2; decide⟩
    | E6 => exact ⟨trivial, trivial⟩
    | E7 => exact ⟨trivial, trivial⟩
    | E8 => exact ⟨trivial, trivial⟩
    | twistedE6 => exact ⟨by show 0 < 2; decide, by show 1 < 2; decide⟩
    | trialityD4 => exact absurd rfl hD4
    | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])
  exact eq_one_of_mem_center_of_two_long_nodes t n p e hp hfund hadm hrank h01.1 h01.2 hR hrR hrc

theorem eq_one_of_mem_center_of_all_nodes (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hcen : ∀ k : Fin (modelUniv t n p e hp).D.rank,
      ∀ r ∈ Subgroup.center (modelUniv t n p e hp).K,
        r ∈ rankOne (modelUniv t n p e hp).D.rootGroup k → r = 1)
    {R : Subgroup (modelUniv t n p e hp).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D)
    {r : (modelUniv t n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv t n p e hp).K) : r = 1 := by
  obtain ⟨_, _, hct, hext⟩ := hasBruhatDatum t n p e hp hfund hadm
  obtain ⟨g, γ, hγ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨r', hr', hrr'⟩ := hrR
  have hr'eq : r' = r := by
    have h1 : g * r' * g⁻¹ = r := hrr'
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact mul_left_cancel (h1.trans (Subgroup.mem_center_iff.mp hrc g).symm)
  rw [hr'eq] at hr'
  obtain ⟨g₀, k, hle⟩ := exists_le_map_conj_rankOne hct hext hγ
  obtain ⟨r'', hr'', hrr''⟩ := hle hr'
  have hr''eq : r'' = r := by
    have h1 : g₀ * r'' * g₀⁻¹ = r := hrr''
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact mul_left_cancel (h1.trans (Subgroup.mem_center_iff.mp hrc g₀).symm)
  rw [hr''eq] at hr''
  exact hcen k r hrc hr''

end CFSG.ClassicalInvolution.ModelFacts
