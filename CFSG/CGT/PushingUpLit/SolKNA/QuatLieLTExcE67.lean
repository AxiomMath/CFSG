module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTExc

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Universal CFSG.LieType.CurtisTits
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem exists_factor_of_surjective {K A X : Type*} [Group K] [Group A] [Group X] (θ : K →* A)
    (hθ : Function.Surjective θ) (ψ : K →* X) (h : θ.ker ≤ ψ.ker) :
    ∃ κ : A →* X, ∀ k, κ (θ k) = ψ k :=
  ⟨θ.liftOfSurjective hθ ⟨ψ, h⟩, fun k => θ.liftOfRightInverse_comp_apply _
    (Function.rightInverse_surjInv hθ) ⟨ψ, h⟩ k⟩

theorem exists_iso_of_cover {K A X : Type*} [Group K] [Group A] [Group X] (θ : K →* A)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center K) (hA : Subgroup.center A = ⊥)
    (ψ : K →* X) (hψ : Function.Surjective ψ) (hψk : ψ.ker = Subgroup.center K) :
    ∃ κ : A →* X, Function.Surjective κ ∧ Function.Injective κ ∧ ∀ k, κ (θ k) = ψ k := by
  obtain ⟨κ, hκ⟩ := exists_factor_of_surjective θ hθ ψ (hψk ▸ hker)
  refine ⟨κ, fun x => ?_, ?_, hκ⟩
  · obtain ⟨k, rfl⟩ := hψ x
    exact ⟨θ k, hκ k⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := hθ a
    have hk : k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hκ]
      exact ha
    have hc : θ k ∈ Subgroup.center A :=
      Subgroup.map_center_le_center hθ ⟨k, hψk ▸ hk, rfl⟩
    rwa [hA] at hc

theorem map_conj_map_hom {K A : Type*} [Group K] [Group A] (θ : K →* A) (H : Subgroup K)
    (g : K) :
    (H.map (MulAut.conj g).toMonoidHom).map θ = (H.map θ).map (MulAut.conj (θ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

section Cover


theorem kill_of_cover (τ : Tag) (i : Fin τ.rank) (wit : List ℕ)
    (hc : isolatedCheck τ i wit = true) (hsym : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i)
    (hj : ∃ j : Fin τ.rank, j ≠ i ∧ τ.cartan i j = 0) {K X : Type} [Group K] [Group X]
    [Finite X] (θ : K →* ↥(adjointGroup τ (GaloisField 3 1))) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hψk : ψ.ker = Subgroup.center K) {R : Subgroup K} {g : K}
    (hR : rankOneGroup (adjDatum (rootOperatorFamily τ) (GaloisField 3 1)) (Pi.single i 1) =
      (R.map θ).map (MulAut.conj (θ g)).toMonoidHom)
    {t : X} (ht : t ∈ R.map ψ) (ht2 : orderOf t = 2) :
    ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
      CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  obtain ⟨κ, hκs, hκi, hκ⟩ := exists_iso_of_cover θ hθ hker center_adjointGroup_eq_bot ψ hψ hψk
  have hmap : (R.map θ).map κ = R.map ψ := by
    rw [Subgroup.map_map]
    congr 1
    ext k
    exact hκ k
  exact kill_adjoint τ i wit hc hsym hj κ hκs
    (((MonoidHom.ker_eq_bot_iff κ).2 hκi).le.trans bot_le) hR (hmap ▸ ht) ht2

end Cover

section E6


theorem kill_E6_aux {X : Type} [Group X] [Finite X]
    (ψ : ↥(e6Data_valid.minGroup (GaloisField 3 1)) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center _) {R : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    {g : ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    (hg : (e6Datum (GaloisField 3 1)).rootGroup (Pi.single (idx0 .E6) 1) ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-Pi.single (idx0 .E6) 1) =
        R.map (MulAut.conj g).toMonoidHom)
    {t : X} (ht : t ∈ R.map ψ) (ht2 : orderOf t = 2) :
    ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
      CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hγ : IsRoot .E6 (Pi.single (idx0 .E6) 1 : Fin (Tag.rank .E6) → ℤ) := isRoot_single .E6 _
  have hRimg : rankOneGroup (adjDatum (rootOperatorFamily .E6) (GaloisField 3 1))
      (Pi.single (idx0 .E6) 1) = ((e6Datum (GaloisField 3 1)).rootGroup (Pi.single (idx0 .E6) 1) ⊔
        (e6Datum (GaloisField 3 1)).rootGroup (-Pi.single (idx0 .E6) 1)).map
          (e6Isogeny (GaloisField 3 1)) := by
    rw [Subgroup.map_sup, CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ hγ,
      CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ (IsRoot.neg hγ)]
  have hker' : (e6Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField 3 1)) (e6Isogeny_ne_one _)
  refine kill_of_cover .E6 (idx0 .E6) witE6 isolatedCheck_E6 (symmetrizer_le_one .E6 rfl _)
    (by decide) (e6Isogeny (GaloisField 3 1)) (e6Isogeny_surjective _) hker' ψ hψ hker
    (R := R) (g := g) ?_ ht ht2
  rw [hRimg, hg, map_conj_map_hom]

theorem kill3At_E6 : Kill3At .E6 0 := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  right
  have hadm : StatedLieAdmissible .E6 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E6 0 3 1
    Nat.prime_three trivial hadm
  have hR₀ : (e6Datum (GaloisField 3 1)).rootGroup (Pi.single (idx0 .E6) 1) ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-Pi.single (idx0 .E6) 1) ∈
        fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Nat.prime_three).D :=
    ⟨1, Pi.single (idx0 .E6) 1, Or.inl (hlong (idx0 .E6) trivial), (conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E6 0 3 1
    Nat.prime_three trivial hadm (by decide) (by decide) R hR _ hR₀
  exact kill_E6_aux ψ hψ hker (R := R) (g := g) hg ht ht2

end E6

section E7


theorem kill_E7_aux {X : Type} [Group X] [Finite X]
    (ψ : ↥(e7Data_valid.minGroup (GaloisField 3 1)) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center _) {R : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1))}
    {g : ↥(e7Data_valid.minGroup (GaloisField 3 1))}
    (hg : (e7Datum (GaloisField 3 1)).rootGroup (Pi.single (idx0 .E7) 1) ⊔
      (e7Datum (GaloisField 3 1)).rootGroup (-Pi.single (idx0 .E7) 1) =
        R.map (MulAut.conj g).toMonoidHom)
    {t : X} (ht : t ∈ R.map ψ) (ht2 : orderOf t = 2) :
    ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
      CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hγ : IsRoot .E7 (Pi.single (idx0 .E7) 1 : Fin (Tag.rank .E7) → ℤ) := isRoot_single .E7 _
  have hRimg : rankOneGroup (adjDatum (rootOperatorFamily .E7) (GaloisField 3 1))
      (Pi.single (idx0 .E7) 1) = ((e7Datum (GaloisField 3 1)).rootGroup (Pi.single (idx0 .E7) 1) ⊔
        (e7Datum (GaloisField 3 1)).rootGroup (-Pi.single (idx0 .E7) 1)).map
          (e7Isogeny (GaloisField 3 1)) := by
    rw [Subgroup.map_sup, CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ hγ,
      CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ (IsRoot.neg hγ)]
  have hker' : (e7Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField 3 1))
      (exists_e7Isogeny_ne_one _)
  refine kill_of_cover .E7 (idx0 .E7) witE7 isolatedCheck_E7 (symmetrizer_le_one .E7 rfl _)
    (by decide) (e7Isogeny (GaloisField 3 1)) (e7Isogeny_surjective _) hker' ψ hψ hker
    (R := R) (g := g) ?_ ht ht2
  rw [hRimg, hg, map_conj_map_hom]

theorem kill3At_E7 : Kill3At .E7 0 := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  right
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E7 0 3 1
    Nat.prime_three trivial hadm
  have hR₀ : (e7Datum (GaloisField 3 1)).rootGroup (Pi.single (idx0 .E7) 1) ⊔
      (e7Datum (GaloisField 3 1)).rootGroup (-Pi.single (idx0 .E7) 1) ∈
        fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D :=
    ⟨1, Pi.single (idx0 .E7) 1, Or.inl (hlong (idx0 .E7) trivial), (conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E7 0 3 1
    Nat.prime_three trivial hadm (by decide) (by decide) R hR _ hR₀
  exact kill_E7_aux ψ hψ hker (R := R) (g := g) hg ht ht2

end E7

end CFSG.CGT.PushingUpLit.SolKNA
