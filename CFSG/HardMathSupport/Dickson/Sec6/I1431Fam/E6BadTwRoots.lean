module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section

variable {K : Type} [Field K]

private theorem isRoot_foldr_reflect (j : Fin Tag.E6.rank) (l : List (Fin Tag.E6.rank)) :
    IsRoot .E6 (l.foldr (reflect .E6) (Pi.single j 1)) := by
  induction l with
  | nil => exact .basis j
  | cons i l ih => exact .reflect i ih

theorem isRoot_twB1 : IsRoot .E6 twB1 := .basis (nd 3)

theorem isRoot_twB2 : IsRoot .E6 twB2 := by
  have e : twB2 = reflect .E6 (nd 2) (reflect .E6 (nd 4) twB1) := by decide +kernel
  rw [e]
  exact (isRoot_twB1.reflect (nd 4)).reflect (nd 2)

theorem isRoot_twB3 : IsRoot .E6 twB3 := by
  have e : twB3 = reflect .E6 (nd 0) (reflect .E6 (nd 5) twB2) := by decide +kernel
  rw [e]
  exact (isRoot_twB2.reflect (nd 5)).reflect (nd 0)

theorem isRoot_twTheta : IsRoot .E6 twTheta := by
  have e : twTheta = [nd 1, nd 3, nd 4, nd 2, nd 3, nd 5, nd 0, nd 4, nd 2, nd 3].foldr
      (reflect .E6) (Pi.single (nd 1) 1) := by decide +kernel
  rw [e]
  exact isRoot_foldr_reflect _ _

private theorem reflect_neg (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    reflect .E6 i (-v) = -reflect .E6 i v := by
  rw [← reflectHom_apply, map_neg, reflectHom_apply]

private theorem nm_conj_rootGroup {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (i : Fin Tag.E6.rank) {g : e6Data_valid.minGroup K} (hg : g ∈ e6Data_valid.rootGroup K γ) :
    e6Data_valid.nm K i * g * (e6Data_valid.nm K i)⁻¹ ∈
      e6Data_valid.rootGroup K (reflect .E6 i γ) := by
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
  obtain ⟨σ, -, h⟩ := e6Data_valid.nm_conj_xm K hγ i
  rw [h c]
  exact e6Data_valid.xm_mem_rootGroup K _ _

private theorem nm_conj_rootPair {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (i : Fin Tag.E6.rank) {g : e6Data_valid.minGroup K} (hg : g ∈ rootPair K γ) :
    e6Data_valid.nm K i * g * (e6Data_valid.nm K i)⁻¹ ∈ rootPair K (reflect .E6 i γ) := by
  have hle : rootPair K γ ≤ (rootPair K (reflect .E6 i γ)).comap
      (MulAut.conj (e6Data_valid.nm K i)).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_sup_left (nm_conj_rootGroup hγ i hx)
    · have h := nm_conj_rootGroup (IsRoot.neg hγ) i hx
      rw [reflect_neg] at h
      exact Subgroup.mem_sup_right h
  exact hle hg

theorem nHat2_conj_rootPair {g : e6Data_valid.minGroup K} (hg : g ∈ rootPair K twB1) :
    nHatE K (nf 2) * g * (nHatE K (nf 2))⁻¹ ∈ rootPair K twB2 := by
  have h4 := nm_conj_rootPair isRoot_twB1 (nd 4) hg
  have h2 := nm_conj_rootPair (isRoot_twB1.reflect (nd 4)) (nd 2) h4
  have e : reflect .E6 (nd 2) (reflect .E6 (nd 4) twB1) = twB2 := by decide +kernel
  rw [e] at h2
  have hn : nHatE K (nf 2) = e6Data_valid.nm K (nd 2) * e6Data_valid.nm K (nd 4) := rfl
  rw [hn, mul_inv_rev]
  simpa only [mul_assoc] using h2

theorem nHat3_conj_rootPair {g : e6Data_valid.minGroup K} (hg : g ∈ rootPair K twB2) :
    nHatE K (nf 3) * g * (nHatE K (nf 3))⁻¹ ∈ rootPair K twB3 := by
  have h5 := nm_conj_rootPair isRoot_twB2 (nd 5) hg
  have h0 := nm_conj_rootPair (isRoot_twB2.reflect (nd 5)) (nd 0) h5
  have e : reflect .E6 (nd 0) (reflect .E6 (nd 5) twB2) = twB3 := by decide +kernel
  rw [e] at h0
  have hn : nHatE K (nf 3) = e6Data_valid.nm K (nd 0) * e6Data_valid.nm K (nd 5) := rfl
  rw [hn, mul_inv_rev]
  simpa only [mul_assoc] using h0

private theorem commute_of_sup {G : Type*} [Group G] {A₁ A₂ : Subgroup G} {y : G}
    (h₁ : ∀ x ∈ A₁, Commute x y) (h₂ : ∀ x ∈ A₂, Commute x y) {x : G} (hx : x ∈ A₁ ⊔ A₂) :
    Commute x y := by
  have hle : A₁ ⊔ A₂ ≤ Subgroup.centralizer {y} :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h₁ x hx))
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h₂ x hx))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

private theorem commute_of_sup_sup {G : Type*} [Group G] {A₁ A₂ B₁ B₂ : Subgroup G}
    (h₁₁ : ∀ x ∈ A₁, ∀ y ∈ B₁, Commute x y) (h₁₂ : ∀ x ∈ A₁, ∀ y ∈ B₂, Commute x y)
    (h₂₁ : ∀ x ∈ A₂, ∀ y ∈ B₁, Commute x y) (h₂₂ : ∀ x ∈ A₂, ∀ y ∈ B₂, Commute x y)
    {x y : G} (hx : x ∈ A₁ ⊔ A₂) (hy : y ∈ B₁ ⊔ B₂) : Commute x y := by
  have hA₁ : ∀ x ∈ A₁, ∀ y ∈ B₁ ⊔ B₂, Commute x y := fun x hx y hy =>
    (commute_of_sup (fun y hy => (h₁₁ x hx y hy).symm) (fun y hy => (h₁₂ x hx y hy).symm) hy).symm
  have hA₂ : ∀ x ∈ A₂, ∀ y ∈ B₁ ⊔ B₂, Commute x y := fun x hx y hy =>
    (commute_of_sup (fun y hy => (h₂₁ x hx y hy).symm) (fun y hy => (h₂₂ x hx y hy).symm) hy).symm
  exact commute_of_sup (fun x hx => hA₁ x hx y hy) (fun x hx => hA₂ x hx y hy) hx

private theorem commute_rootGroup {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (h1 : ¬ IsRoot .E6 (γ + δ)) (h3 : γ + δ ≠ 0)
    {x y : e6Data_valid.minGroup K} (hx : x ∈ e6Data_valid.rootGroup K γ)
    (hy : y ∈ e6Data_valid.rootGroup K δ) : Commute x y := by
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hx
  obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hy
  exact commute_xm hγ hδ h3 h1 c d

theorem commute_rootPair_of_orth {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (h1 : ¬ IsRoot .E6 (γ + δ)) (h2 : ¬ IsRoot .E6 (γ - δ))
    (h3 : γ + δ ≠ 0) (h4 : γ - δ ≠ 0) {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K γ)
    (hy : y ∈ rootPair K δ) : Commute x y := by
  have h1' : ¬ IsRoot .E6 (-γ + -δ) := fun h => h1 (by
    have := IsRoot.neg h
    rwa [show -(-γ + -δ) = γ + δ by abel] at this)
  have h2' : ¬ IsRoot .E6 (γ + -δ) := by rwa [← sub_eq_add_neg]
  have h2'' : ¬ IsRoot .E6 (-γ + δ) := fun h => h2 (by
    have := IsRoot.neg h
    rwa [show -(-γ + δ) = γ - δ by abel] at this)
  have h3' : -γ + -δ ≠ 0 := fun h => h3 (by
    rw [show γ + δ = -(-γ + -δ) by abel, h, neg_zero])
  have h4' : γ + -δ ≠ 0 := by rwa [← sub_eq_add_neg]
  have h4'' : -γ + δ ≠ 0 := fun h => h4 (by
    rw [show γ - δ = -(-γ + δ) by abel, h, neg_zero])
  exact commute_of_sup_sup
    (fun _ hx _ hy => commute_rootGroup hγ hδ h1 h3 hx hy)
    (fun _ hx _ hy => commute_rootGroup hγ (IsRoot.neg hδ) h2' h4' hx hy)
    (fun _ hx _ hy => commute_rootGroup (IsRoot.neg hγ) hδ h2'' h4'' hx hy)
    (fun _ hx _ hy => commute_rootGroup (IsRoot.neg hγ) (IsRoot.neg hδ) h1' h3' hx hy) hx hy

theorem commute_rootPair_B12 {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K twB1)
    (hy : y ∈ rootPair K twB2) : Commute x y :=
  commute_rootPair_of_orth isRoot_twB1 isRoot_twB2 (not_isRoot_of_form (by decide +kernel))
    (not_isRoot_of_form (by decide +kernel)) (by decide +kernel) (by decide +kernel) hx hy

theorem commute_rootPair_B13 {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K twB1)
    (hy : y ∈ rootPair K twB3) : Commute x y :=
  commute_rootPair_of_orth isRoot_twB1 isRoot_twB3 (not_isRoot_of_form (by decide +kernel))
    (not_isRoot_of_form (by decide +kernel)) (by decide +kernel) (by decide +kernel) hx hy

theorem commute_rootPair_B23 {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K twB2)
    (hy : y ∈ rootPair K twB3) : Commute x y :=
  commute_rootPair_of_orth isRoot_twB2 isRoot_twB3 (not_isRoot_of_form (by decide +kernel))
    (not_isRoot_of_form (by decide +kernel)) (by decide +kernel) (by decide +kernel) hx hy

theorem commute_rootPair_B1T {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K twB1)
    (hy : y ∈ rootPair K twTheta) : Commute x y :=
  commute_rootPair_of_orth isRoot_twB1 isRoot_twTheta (not_isRoot_of_form (by decide +kernel))
    (not_isRoot_of_form (by decide +kernel)) (by decide +kernel) (by decide +kernel) hx hy

theorem commute_rootPair_B2T {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K twB2)
    (hy : y ∈ rootPair K twTheta) : Commute x y :=
  commute_rootPair_of_orth isRoot_twB2 isRoot_twTheta (not_isRoot_of_form (by decide +kernel))
    (not_isRoot_of_form (by decide +kernel)) (by decide +kernel) (by decide +kernel) hx hy

theorem commute_rootPair_B3T {x y : e6Data_valid.minGroup K} (hx : x ∈ rootPair K twB3)
    (hy : y ∈ rootPair K twTheta) : Commute x y :=
  commute_rootPair_of_orth isRoot_twB3 isRoot_twTheta (not_isRoot_of_form (by decide +kernel))
    (not_isRoot_of_form (by decide +kernel)) (by decide +kernel) (by decide +kernel) hx hy

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
