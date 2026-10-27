module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellOffender

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem eq_top_of_rootGrp_le {ℓ : ℙ F (Fin 2 → F)}
    {X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hℓ : rootGrp ℓ ≤ X) (h : ∃ x ∈ X, x • ℓ ≠ ℓ) : X = ⊤ := by
  obtain ⟨x, hx, hxℓ⟩ := h
  have h1 : rootGrp (x • ℓ) ≤ X := by
    rw [rootGrp_smul_eq_map]
    rintro _ ⟨u, hu, rfl⟩
    exact X.mul_mem (X.mul_mem hx (hℓ hu)) (X.inv_mem hx)
  have h2 : rootGrp ℓ ⊔ rootGrp (x • ℓ) = ⊤ := rootGrp_sup_rootGrp (Ne.symm hxℓ)
  exact top_le_iff.mp (h2 ▸ sup_le hℓ h1)

variable [CharP F 2]

theorem exists_rootGrp_eq_map_of_isSylowTwoOf {Γ : Type*} [Group Γ] [Finite Γ] {G T : Subgroup Γ}
    (hT : IsSylowTwoOf T G) (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hα : Function.Surjective α) :
    ∃ ℓ : ℙ F (Fin 2 → F), (T.subgroupOf G).map α = rootGrp ℓ := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf G) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let P : Sylow 2 ↥G := hTp.toSylow hT.2.2
  have hP : ((P : Subgroup ↥G)) = T.subgroupOf G := rfl
  let Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) := Sylow.mapSurjective hα P
  have hQ : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = (T.subgroupOf G).map α := rfl
  have hcardSL : Nat.card (slGamma F) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Nat.card_congr (slGammaEquiv F).toEquiv).symm
  have hQcard : Nat.card Q = Nat.card F := by
    rw [Sylow.card_eq_multiplicity Q, ← hcardSL]
    exact (card_eq_two_pow_factorization_slGamma (k := F)).symm
  obtain ⟨n, -, hn⟩ := card_eq_two_pow (k := F)
  obtain ⟨ℓ, hℓ⟩ := exists_point_eq_rootGrp Nat.prime_two hn
    (P := (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) hQcard
  exact ⟨ℓ, hQ ▸ hℓ⟩

end CFSG.CGT.PushingUpLit.BHS
