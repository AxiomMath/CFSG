module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.GLS.Stage2.Local.P27.FullStmt
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12

section Transport

theorem forall_sylow_dihedral_of_equiv {Q Q' : Type} [Group Q] [Group Q'] [Finite Q'] (ψ : Q ≃* Q')
    (h : ∀ P : Sylow 2 Q, IsDihedral ↥P) : ∀ P' : Sylow 2 Q', IsDihedral ↥P' := by
  intro P'
  have hf : Function.Surjective ψ.symm.toMonoidHom := ψ.symm.surjective
  let P : Sylow 2 Q := P'.mapSurjective hf
  have hP : (P : Subgroup Q) = P'.map ψ.symm.toMonoidHom := Sylow.coe_mapSurjective hf P'
  obtain ⟨m, k, hm, hk, ⟨e⟩⟩ := h P
  have e1 : ↥P' ≃* ↥(P'.map ψ.symm.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ ψ.symm.toMonoidHom ψ.symm.injective
  have e2 : ↥(P'.map ψ.symm.toMonoidHom) ≃* ↥P := MulEquiv.subgroupCongr hP.symm
  exact ⟨m, k, hm, hk, ⟨(e1.trans e2).trans e⟩⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_equiv_of_conj {z x : G} (c : G) (hc : c * z * c⁻¹ = x) :
    Nonempty (↥(centralizer ({z} : Set G)) ≃* ↥(centralizer ({x} : Set G))) := by
  have hmem : ∀ g : G, g ∈ centralizer ({z} : Set G) → c * g * c⁻¹ ∈ centralizer ({x} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hc]
    calc c * g * c⁻¹ * (c * z * c⁻¹) = c * (g * z) * c⁻¹ := by group
      _ = c * (z * g) * c⁻¹ := by rw [hg]
      _ = c * z * c⁻¹ * (c * g * c⁻¹) := by group
  have hmem' : ∀ g : G, g ∈ centralizer ({x} : Set G) → c⁻¹ * g * c ∈ centralizer ({z} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hc] at hg
    have : g * (c * z * c⁻¹) = (c * z * c⁻¹) * g := hg
    calc c⁻¹ * g * c * z = c⁻¹ * (g * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * g) * c := by rw [this]
      _ = z * (c⁻¹ * g * c) := by group
  exact ⟨{ toFun := fun g => ⟨c * g * c⁻¹, hmem g g.2⟩
           invFun := fun g => ⟨c⁻¹ * g * c, hmem' g g.2⟩
           left_inv := fun g => Subtype.ext (by simp [mul_assoc])
           right_inv := fun g => Subtype.ext (by simp [mul_assoc])
           map_mul' := fun g h => Subtype.ext (by simp [mul_assoc]) }⟩

theorem fullG_of_isConj {x y : G} (hxy : IsConj x y) (h : P27.FullG x) : P27.FullG y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  obtain ⟨e⟩ := centralizer_equiv_of_conj c hc
  have hmapO : (oResidual 2 ↥(centralizer ({x} : Set G))).map e.toMonoidHom =
      oResidual 2 ↥(centralizer ({y} : Set G)) :=
    Stage1.Thm6.Prod.map_oResidual e.toMonoidHom e.surjective Nat.prime_two
  let e1 : ↥(O2Of (centralizer ({x} : Set G))) ≃* ↥(oResidual 2 ↥(centralizer ({x} : Set G))) :=
    (Subgroup.equivMapOfInjective _ (centralizer ({x} : Set G)).subtype
      (centralizer ({x} : Set G)).subtype_injective).symm
  let e2 : ↥(oResidual 2 ↥(centralizer ({x} : Set G))) ≃*
      ↥((oResidual 2 ↥(centralizer ({x} : Set G))).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  let e3 : ↥((oResidual 2 ↥(centralizer ({x} : Set G))).map e.toMonoidHom) ≃*
      ↥(oResidual 2 ↥(centralizer ({y} : Set G))) := MulEquiv.subgroupCongr hmapO
  let e4 : ↥(oResidual 2 ↥(centralizer ({y} : Set G))) ≃* ↥(O2Of (centralizer ({y} : Set G))) :=
    Subgroup.equivMapOfInjective _ (centralizer ({y} : Set G)).subtype
      (centralizer ({y} : Set G)).subtype_injective
  exact forall_sylow_dihedral_of_equiv (e1.trans (e2.trans (e3.trans e4))) h

end Transport

section Conj27

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_cen_of_central {z : G} (hcen : IsCentralInvolution z) {u : G} (hu : orderOf u = 2) :
    ∃ g : G, g * u * g⁻¹ ∈ centralizer ({z} : Set G) := by
  obtain ⟨-, S₀, hzS, hSz⟩ := hcen
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hup : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; simp)
  obtain ⟨S₁, hS₁⟩ := hup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₁ S₀
  have hu1 : u ∈ (S₁ : Subgroup G) := hS₁ (Subgroup.mem_zpowers u)
  have h2 : g * u * g⁻¹ ∈ (S₀ : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, hu1, by simp [MulAut.smul_def]⟩
  refine ⟨g, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hSz _ h2

end Conj27

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
