module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Involutions

variable {G : Type*} [Group G]

theorem exists_conj_involution {S R F : Subgroup G} (hSR : S ≤ Subgroup.normalizer (R : Set G))
    (hFS : F ≤ S) (hRF : R ⊓ F = ⊥) (hRFS : R ⊔ F = S)
    (hfus : ∀ f ∈ F, f ≠ 1 → f ^ 2 = 1 → ∀ r ∈ R, (f * r) ^ 2 = 1 →
      ∃ c ∈ R, c⁻¹ * f * c = f * r)
    {s : G} (hs : s ∈ S) (hsR : s ∉ R) (hs2 : s ^ 2 = 1) :
    ∃ f ∈ F, f ≠ 1 ∧ f ^ 2 = 1 ∧ ∃ c ∈ R, c⁻¹ * f * c = s := by
  have hFN : F ≤ Subgroup.normalizer (R : Set G) := hFS.trans hSR
  obtain ⟨r, hr, f, hf, rfl⟩ := (mem_sup_iff_of_le_normalizer hFN).mp (hRFS ▸ hs)
  have hfN : f ∈ Subgroup.normalizer (R : Set G) := hFN hf
  have hrf : f * r * f⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hfN r).mp hr
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hsR (by simpa using hr)
  have hf2 : f ^ 2 = 1 := by
    have hmem : f ^ 2 ∈ R ⊓ F := by
      refine ⟨?_, F.pow_mem hf 2⟩
      have e : f ^ 2 = (f * r * f⁻¹)⁻¹ * r⁻¹ := by
        have h' : r * f * r = f⁻¹ :=
          eq_inv_of_mul_eq_one_left (by simpa [pow_two, mul_assoc] using hs2)
        calc f ^ 2 = f * r⁻¹ * (r * f * r) * r⁻¹ := by rw [pow_two]; group
          _ = f * r⁻¹ * f⁻¹ * r⁻¹ := by rw [h']
          _ = (f * r * f⁻¹)⁻¹ * r⁻¹ := by group
      rw [e]
      exact R.mul_mem (R.inv_mem hrf) (R.inv_mem hr)
    rw [hRF] at hmem
    simpa using hmem
  refine ⟨f, hf, hf1, hf2, ?_⟩
  have hr2 : f⁻¹ * r * f ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hfN) r).mp hr
    simpa using this
  have e : r * f = f * (f⁻¹ * r * f) := by group
  have hsq : (f * (f⁻¹ * r * f)) ^ 2 = 1 := by rw [← e]; exact hs2
  obtain ⟨c, hc, hcf⟩ := hfus f hf hf1 hf2 _ hr2 hsq
  exact ⟨c, hc, by rw [hcf, ← e]⟩

end Involutions

section Conjugacy

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_involutions {S R F : Subgroup G} (hSR : S ≤ Subgroup.normalizer (R : Set G))
    (hFS : F ≤ S) (hcyc : IsCyclic F) (hRF : R ⊓ F = ⊥) (hRFS : R ⊔ F = S)
    (hfus : ∀ f ∈ F, f ≠ 1 → f ^ 2 = 1 → ∀ r ∈ R, (f * r) ^ 2 = 1 →
      ∃ c ∈ R, c⁻¹ * f * c = f * r)
    {s s' : G} (hs : s ∈ S) (hsR : s ∉ R) (hs2 : s ^ 2 = 1) (hs'S : s' ∈ S) (hs'R : s' ∉ R)
    (hs'2 : s' ^ 2 = 1) : ∃ c ∈ R, c⁻¹ * s * c = s' := by
  obtain ⟨f₁, hf₁, hf₁1, hf₁2, c₁, hc₁, hc₁s⟩ :=
    exists_conj_involution hSR hFS hRF hRFS hfus hs hsR hs2
  obtain ⟨f₂, hf₂, hf₂1, hf₂2, c₂, hc₂, hc₂s⟩ :=
    exists_conj_involution hSR hFS hRF hRFS hfus hs'S hs'R hs'2
  have hf : f₁ = f₂ := by
    have h1 : (⟨f₁, hf₁⟩ : F) = ⟨f₂, hf₂⟩ := by
      refine eq_of_sq_eq_one_of_isCyclic ?_ ?_ ?_ ?_
      · exact Subtype.ext (by simpa [pow_two] using hf₁2)
      · exact Subtype.ext (by simpa [pow_two] using hf₂2)
      · exact fun h => hf₁1 (by simpa using congrArg Subtype.val h)
      · exact fun h => hf₂1 (by simpa using congrArg Subtype.val h)
    simpa using congrArg Subtype.val h1
  subst hf
  refine ⟨c₁⁻¹ * c₂, R.mul_mem (R.inv_mem hc₁) hc₂, ?_⟩
  rw [← hc₂s, ← hc₁s]
  group

end Conjugacy


section Frattini

variable {G : Type*} [Group G] [Finite G]

theorem eq_sup_centralizer_involution {T S R F : Subgroup G} (hRS : R ≤ S) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hFS : F ≤ S) (hcyc : IsCyclic F) (hRF : R ⊓ F = ⊥) (hRFS : R ⊔ F = S)
    (hfus : ∀ f ∈ F, f ≠ 1 → f ^ 2 = 1 → ∀ r ∈ R, (f * r) ^ 2 = 1 →
      ∃ c ∈ R, c⁻¹ * f * c = f * r)
    {s : G} (hs : s ∈ S) (hsR : s ∉ R) (hs2 : s ^ 2 = 1) :
    T = R ⊔ (T ⊓ Subgroup.centralizer ({s} : Set G)) := by
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := hST.trans hTR
  apply le_antisymm
  · intro t ht
    set s' := t * s * t⁻¹ with hs'
    have hs'S : s' ∈ S := (Subgroup.mem_normalizer_iff.mp (hTS ht) s).mp hs
    have hs'2 : s' ^ 2 = 1 := by
      have : s' ^ 2 = t * s ^ 2 * t⁻¹ := by simp only [hs', pow_two]; group
      rw [this, hs2]; simp
    have hs'R : s' ∉ R := by
      intro h
      apply hsR
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem (hTR ht))
        s').mp h
      have e : t⁻¹ * s' * t⁻¹⁻¹ = s := by simp only [hs']; group
      rw [e] at this
      exact this
    obtain ⟨f₁, hf₁, hf₁1, hf₁2, c₁, hc₁, hc₁s⟩ :=
      exists_conj_involution hSR hFS hRF hRFS hfus hs hsR hs2
    obtain ⟨f₂, hf₂, hf₂1, hf₂2, c₂, hc₂, hc₂s⟩ :=
      exists_conj_involution hSR hFS hRF hRFS hfus hs'S hs'R hs'2
    have hf : f₁ = f₂ := by
      have h1 : (⟨f₁, hf₁⟩ : F) = ⟨f₂, hf₂⟩ := by
        refine eq_of_sq_eq_one_of_isCyclic ?_ ?_ ?_ ?_
        · exact Subtype.ext (by simpa [pow_two] using hf₁2)
        · exact Subtype.ext (by simpa [pow_two] using hf₂2)
        · exact fun h => hf₁1 (by simpa using congrArg Subtype.val h)
        · exact fun h => hf₂1 (by simpa using congrArg Subtype.val h)
      simpa using congrArg Subtype.val h1
    subst hf
    have hcc : (c₁⁻¹ * c₂) ∈ R := R.mul_mem (R.inv_mem hc₁) hc₂
    have hconj : s' = (c₁⁻¹ * c₂)⁻¹ * s * (c₁⁻¹ * c₂) := by
      rw [← hc₂s, ← hc₁s]; group
    have hcts : (c₁⁻¹ * c₂) * t ∈ T ⊓ Subgroup.centralizer ({s} : Set G) := by
      refine ⟨T.mul_mem (hST (hRS hcc)) ht, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : (c₁⁻¹ * c₂)⁻¹ * s * (c₁⁻¹ * c₂) = t * s * t⁻¹ := hconj.symm.trans hs'.symm ▸ rfl
      calc (c₁⁻¹ * c₂) * t * s = (c₁⁻¹ * c₂) * (t * s * t⁻¹) * t := by group
        _ = (c₁⁻¹ * c₂) * ((c₁⁻¹ * c₂)⁻¹ * s * (c₁⁻¹ * c₂)) * t := by rw [h1]
        _ = s * ((c₁⁻¹ * c₂) * t) := by group
    have : t = (c₁⁻¹ * c₂)⁻¹ * ((c₁⁻¹ * c₂) * t) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (R.inv_mem hcc) hcts
  · exact sup_le (hRS.trans hST) inf_le_left

omit [Finite G] in
theorem exists_mem_centralizer_not_mem {T S R : Subgroup G} (hRS : R ≤ S) (hne : S ≠ T)
    (hST : S ≤ T) {s : G}
    (hT : T = R ⊔ (T ⊓ Subgroup.centralizer ({s} : Set G))) :
    ∃ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S := by
  by_contra hcon
  apply hne
  refine le_antisymm hST ?_
  rw [hT]
  refine sup_le hRS fun x hx => ?_
  by_contra hxS
  exact hcon ⟨x, hx, hxS⟩

end Frattini

end CFSG.QuasithinUnique.Lin2
