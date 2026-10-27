module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank

section Planes

variable {K : Type} [Field K] [Finite K]

theorem card_planes_le :
    Nat.card {P : Submodule K (Fin 2 ⊕ Fin 2 → K) // IsHyperbolicPlane P} ≤
      (Nat.card K ^ 4 - 1) * Nat.card K ^ 3 := by
  classical
  have hpairs := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_hyperbolicPairs
    (K := K) (V := Fin 2 ⊕ Fin 2 → K) (nondegenerate_toBilin'_J (n := 2) (K := K))
  have hform : ∀ p : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 ⊕ Fin 2 → K),
      Matrix.toBilin' (Matrix.J (Fin 2) K) p.2 p.1 = 1 → form p.1 p.2 = 1 := fun p h => by
    rw [toBilin'_J_apply, form_antisymm] at h
    simpa using h
  let f : {p : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 ⊕ Fin 2 → K) //
      Matrix.toBilin' (Matrix.J (Fin 2) K) p.2 p.1 = 1} →
      {P : Submodule K (Fin 2 ⊕ Fin 2 → K) // IsHyperbolicPlane P} := fun p =>
    ⟨Submodule.span K {p.1.1, p.1.2}, p.1.1, p.1.2, hform p.1 p.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨P, u, w, huw, rfl⟩
    refine ⟨⟨(u, w), ?_⟩, rfl⟩
    show Matrix.toBilin' (Matrix.J (Fin 2) K) w u = 1
    rw [toBilin'_J_apply, ← form_antisymm, huw]
  have h1 : Nat.card {P : Submodule K (Fin 2 ⊕ Fin 2 → K) // IsHyperbolicPlane P} ≤
      Nat.card {p : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 ⊕ Fin 2 → K) //
        Matrix.toBilin' (Matrix.J (Fin 2) K) p.2 p.1 = 1} := by
    have : Finite {p : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 ⊕ Fin 2 → K) //
        Matrix.toBilin' (Matrix.J (Fin 2) K) p.2 p.1 = 1} := inferInstance
    exact Nat.card_le_card_of_surjective f hf
  have hV : Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card K ^ 4 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2 ⊕ Fin 2)]
    simp
  have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [hpairs, hV, hd] at h1
  exact h1

end Planes

section Fund

variable {p f : ℕ} [Fact p.Prime]

theorem ncard_fund_psp2_le (hq : 5 ≤ p ^ f) :
    (CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSp
      (CFSG.ClassicalInvolution.Generic.modelUniv .PSp 2 p f Fact.out).D).ncard ≤
      ((p ^ f) ^ 4 - 1) * (p ^ f) ^ 3 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hadm : StatedLieAdmissible .PSp 2 p f :=
    ⟨Fact.out, by omega, le_rfl, fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega⟩
  have hsub : CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSp
      (CFSG.ClassicalInvolution.Generic.modelUniv .PSp 2 p f Fact.out).D ⊆
      (fun P : Submodule (GaloisField p f) (Fin 2 ⊕ Fin 2 → GaloisField p f) => planeGroup P) ''
        {P | IsHyperbolicPlane P} := by
    intro R hR
    obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
    exact ⟨P, hP, rfl⟩
  have hfin : {P : Submodule (GaloisField p f) (Fin 2 ⊕ Fin 2 → GaloisField p f) |
      IsHyperbolicPlane P}.Finite := Set.toFinite _
  calc _ ≤ ((fun P : Submodule (GaloisField p f) (Fin 2 ⊕ Fin 2 → GaloisField p f) =>
          planeGroup P) '' {P | IsHyperbolicPlane P}).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ {P : Submodule (GaloisField p f) (Fin 2 ⊕ Fin 2 → GaloisField p f) |
          IsHyperbolicPlane P}.ncard := Set.ncard_image_le hfin
    _ = Nat.card {P : Submodule (GaloisField p f) (Fin 2 ⊕ Fin 2 → GaloisField p f) //
          IsHyperbolicPlane P} := (Nat.card_coe_set_eq _).symm
    _ ≤ (Nat.card (GaloisField p f) ^ 4 - 1) * Nat.card (GaloisField p f) ^ 3 := card_planes_le
    _ = ((p ^ f) ^ 4 - 1) * (p ^ f) ^ 3 := by rw [hcard]

end Fund

end CFSG.ClassicalInvolution.RouteD.TWZ
