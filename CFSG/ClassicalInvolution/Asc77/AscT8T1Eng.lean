module

public import CFSG.ClassicalInvolution.Asc77.AscT3SConfEng
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {R T W : Subgroup G} {z t : G}

theorem exists_triFrame_of_std8E (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    (huniq : ∀ {M : Subgroup G}, M ∈ Ω → ∃ u : G, IsUniqueInvolution M u)
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hJ : J ∈ omegaNbr Ω K)
    (ρK ρJ : Rep Ω W) (hρKK : ρK.K = K) (hρKR : ρK.R = R) (hρJK : ρJ.K = J) (hρJR : ρJ.R = T)
    (hthird : ∃ τ : Rep Ω W, τ.K ≠ K ∧ τ.K ≠ J)
    (hrcomm : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K →
      (T8.repElt ρ * T8.repElt σ = T8.repElt σ * T8.repElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K))
    (hrle : ∀ ρ σ : Rep Ω W, (σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K) → ∀ {v : G},
      IsUniqueInvolution σ.K v → ρ.R ≤ Subgroup.centralizer ({v} : Set G))
    (hzt : z * t = t * z)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x)
    (hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
      z' ≠ z * t) :
    ∃ (K' R' : Subgroup G) (z' : G), (∀ i : Fin 3, ![K, J, K'] i ∈ Ω) ∧
      (∀ i : Fin 3, IsUniqueInvolution (![K, J, K'] i) (![z, t, z'] i)) ∧
      (∀ i j : Fin 3, i ≠ j → ![K, J, K'] j ∈ omegaNbr Ω (![K, J, K'] i)) ∧
      (∀ i : Fin 3, IsSylow2In (![R, T, R'] i) (![K, J, K'] i)) ∧
      (∀ i j : Fin 3, ![R, T, R'] i ≤ Subgroup.centralizer ({![z, t, z'] j} : Set G)) ∧
      z' ∉ Subgroup.closure ({z, t} : Set G) := by
  obtain ⟨τ, hτK, hτJ⟩ := hthird
  obtain ⟨z₂, hz₂⟩ := huniq τ.hK
  let ρ : Fin 3 → Rep Ω W := ![ρK, ρJ, τ]
  let zz : Fin 3 → G := ![z, t, z₂]
  have hKE : ∀ i, (ρ i).K = ![K, J, τ.K] i := by
    intro i
    fin_cases i
    · exact hρKK
    · exact hρJK
    · rfl
  have hRE : ∀ i, (ρ i).R = ![R, T, τ.R] i := by
    intro i
    fin_cases i
    · exact hρKR
    · exact hρJR
    · rfl
  have hzE : ∀ i, zz i = ![z, t, z₂] i := by
    intro i
    fin_cases i <;> rfl
  have hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i) := by
    intro i
    rw [hKE i, hzE i]
    fin_cases i
    · exact hz
    · exact ht
    · exact hz₂
  have hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hKE i, hKE j]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hJ.2.1.symm
    · exact hτK.symm
    · exact hJ.2.1
    · exact absurd rfl hij
    · exact hτJ.symm
    · exact hτK
    · exact hτJ
    · exact absurd rfl hij
  have hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    refine (hrcomm (ρ i) (ρ j) (hne i j hij)).mp ?_
    exact Subtype.ext (hab _ (T8.repElt (ρ i)).2 _ (T8.repElt (ρ j)).2)
  have hrel : ∀ i j, (ρ j).K = (ρ i).K ∨ (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j
    by_cases h : i = j
    · subst h
      exact Or.inl rfl
    · exact Or.inr (hnbr i j h)
  have hmemF : ∀ i : Fin 3, ![K, J, τ.K] i ∈ Ω := fun i => by
    rw [← hKE i]
    exact (ρ i).hK
  have hinvF : ∀ i : Fin 3, IsUniqueInvolution (![K, J, τ.K] i) (![z, t, z₂] i) := fun i => by
    rw [← hKE i, ← hzE i]
    exact hzz i
  have hnbrF : ∀ i j : Fin 3, i ≠ j → ![K, J, τ.K] j ∈ omegaNbr Ω (![K, J, τ.K] i) :=
    fun i j hij => by
      rw [← hKE i, ← hKE j]
      exact hnbr i j hij
  have hsylF : ∀ i : Fin 3, IsSylow2In (![R, T, τ.R] i) (![K, J, τ.K] i) := fun i => by
    rw [← hKE i, ← hRE i]
    exact (ρ i).hRK
  have hcentF : ∀ i j : Fin 3, ![R, T, τ.R] i ≤ Subgroup.centralizer ({![z, t, z₂] j} : Set G) :=
    fun i j => by
      rw [← hRE i, ← hzE j]
      exact hrle (ρ i) (ρ j) (hrel i j) (hzz j)
  refine ⟨τ.K, τ.R, z₂, hmemF, hinvF, hnbrF, hsylF, hcentF, ?_⟩
  intro hmem
  have hz₂1 : z₂ ≠ 1 := hz₂.ne_one
  have hxne : ∀ {i j : Fin 3}, i ≠ j → ![z, t, z₂] i ≠ ![z, t, z₂] j := by
    intro i j hij h
    have hj : IsUniqueInvolution (![K, J, τ.K] j) (![z, t, z₂] i) := by
      rw [h]
      exact hinvF j
    exact (hnbrF i j hij).2.1 (hnt _ (hmemF i) _ ⟨hmemF j, ![z, t, z₂] i, hinvF i, hj⟩)
  have hnz : z₂ ≠ z := fun h => hxne (i := 0) (j := 2) (by decide) h.symm
  have hnt' : z₂ ≠ t := fun h => hxne (i := 1) (j := 2) (by decide) h.symm
  rcases T3CII.closure_pair_cases hz.sq ht.sq hzt hmem with h | h | h | h
  · exact hz₂1 h
  · exact hnz h
  · exact hnt' h
  · exact hE8 τ.K (hnbrF 0 2 (by decide)) (hnbrF 1 2 (by decide)) z₂ hz₂ h

end T8T

end CFSG.ClassicalInvolution.Asc77
