module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type*} [Group G]

theorem conjSubgroup_def (A : Subgroup G) (g : G) :
    conjSubgroup A g = A.map (MulAut.conj g⁻¹).toMonoidHom := rfl

theorem conjSubgroup_inf (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊓ B) g = conjSubgroup A g ⊓ conjSubgroup B g := by
  ext x; simp [mem_conjSubgroup_iff]

theorem conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  simp only [conjSubgroup_def]
  exact Subgroup.map_sup _ _ _

theorem conjSubgroup_le_iff {A B : Subgroup G} {g : G} :
    conjSubgroup A g ≤ conjSubgroup B g ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

theorem conjSubgroup_mono {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjSubgroup A g ≤ conjSubgroup B g :=
  conjSubgroup_le_iff.mpr h

theorem conjSubgroup_eq_self {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    conjSubgroup A g = A := conjSubgroup_eq_iff_mem_normalizer.mpr hg

theorem conjSubgroup_centralizer (A : Subgroup G) (g : G) :
    conjSubgroup (centralizer (A : Set G)) g = centralizer ((conjSubgroup A g : Subgroup G) : Set G) :=
  (CFSG.QuasithinUnique.centralizer_map_equiv (MulAut.conj g⁻¹) A).symm

theorem conjSubgroup_normalizer (A : Subgroup G) (g : G) :
    conjSubgroup (normalizer (A : Set G)) g = normalizer ((conjSubgroup A g : Subgroup G) : Set G) :=
  (CFSG.QuasithinUnique.normalizer_map_equiv (MulAut.conj g⁻¹) A).symm

theorem card_conjSubgroup [Finite G] (A : Subgroup G) (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem relIndex_conjSubgroup (A B : Subgroup G) (g : G) :
    (conjSubgroup A g).relIndex (conjSubgroup B g) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g⁻¹).injective

theorem conjSubgroup_commutator (A B : Subgroup G) (g : G) :
    conjSubgroup ⁅A, B⁆ g = ⁅conjSubgroup A g, conjSubgroup B g⁆ := by
  simp only [conjSubgroup_def]
  exact Subgroup.map_commutator _ _ _

theorem conjSubgroup_pCoreOf (p : ℕ) (A : Subgroup G) (g : G) :
    conjSubgroup (pCoreOf p A) g = pCoreOf p (conjSubgroup A g) :=
  (CFSG.QuasithinUnique.pCoreOf_map_equiv p (MulAut.conj g⁻¹) A).symm

theorem conjSubgroup_top_inv_mem (A : Subgroup G) {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g⁻¹ ∈ normalizer (A : Set G) := inv_mem hg

theorem conjSubgroup_conjSubgroup_inv (A : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup A g) g⁻¹ = A := by
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem conjSubgroup_inv_conjSubgroup (A : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup A g⁻¹) g = A := by
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

end CFSG.QuasithinUnique.C5
