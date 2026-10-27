module

public import CFSG.Dihedral.DihedralFusionStepReplacement

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

inductive DihedralFusionDecomposition
    (S P : Subgroup G) : G → Prop
  | one : DihedralFusionDecomposition S P 1
  | tail {g h : G} {U : Subgroup G} :
      DihedralFusionDecomposition S P g →
      U ≤ S → rightConjugate P g ≤ U →
      ((U = S ∧ h ∈ S) ∨
        (IsKleinFour U ∧ h ∈ Subgroup.normalizer (U : Set G))) →
      DihedralFusionDecomposition S P (g * h)

theorem rightConjugate_eq_of_pointwise
    (P : Subgroup G) {a b : G}
    (hab : ∀ x ∈ P, a⁻¹ * x * a = b⁻¹ * x * b) :
    rightConjugate P a = rightConjugate P b := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, hy, by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        using (hab y hy).symm⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, hy, by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        using hab y hy⟩

theorem dihedralFusionStep_mem_normalizer
    {S U : Subgroup G} {h : G}
    (hstep : (U = S ∧ h ∈ S) ∨
      (IsKleinFour U ∧ h ∈ Subgroup.normalizer (U : Set G))) :
    h ∈ Subgroup.normalizer (U : Set G) := by
  rcases hstep with ⟨rfl, hh⟩ | ⟨_, hh⟩
  · exact Subgroup.le_normalizer hh
  · exact hh

theorem dihedralFusionDecomposition_of_huppert
    [Finite G] (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    {P : Subgroup G} {g : G}
    (hchain : HuppertCentricConjugationDecomposition (S : Subgroup G)
      (HuppertExtremal S) P g) :
    ∃ z : G, DihedralFusionDecomposition (S : Subgroup G) P z ∧
      ∀ x ∈ P, z⁻¹ * x * z = g⁻¹ * x * g := by
  induction hchain with
  | one => exact ⟨1, .one, by intro x _; rfl⟩
  | @tail g h U hprev hUext hUS hcur hh _hcentric ih =>
      obtain ⟨z, hz, hzg⟩ := ih
      have hcurz : rightConjugate P z ≤ U := by
        rw [rightConjugate_eq_of_pointwise P hzg]
        exact hcur
      by_cases hU : IsKleinFour U
      · refine ⟨z * h, .tail hz hUS hcurz (Or.inr ⟨hU, hh⟩), ?_⟩
        intro x hx
        calc
          (z * h)⁻¹ * x * (z * h) = h⁻¹ * (z⁻¹ * x * z) * h := by group
          _ = h⁻¹ * (g⁻¹ * x * g) * h := by rw [hzg x hx]
          _ = (g * h)⁻¹ * x * (g * h) := by group
      · obtain ⟨s, hsS, _hsU, hsh⟩ :=
          dihedral_extremal_normalizer_step_replacement S hm e U hUext hU h hh
        refine ⟨z * s, .tail hz le_rfl (hcurz.trans hUS)
          (Or.inl ⟨rfl, hsS⟩), ?_⟩
        intro x hx
        have hxU : g⁻¹ * x * g ∈ U := hcur
          (Subgroup.mem_map.mpr ⟨x, hx, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
        calc
          (z * s)⁻¹ * x * (z * s) = s⁻¹ * (z⁻¹ * x * z) * s := by group
          _ = s⁻¹ * (g⁻¹ * x * g) * s := by rw [hzg x hx]
          _ = h⁻¹ * (g⁻¹ * x * g) * h := hsh _ hxU
          _ = (g * h)⁻¹ * x * (g * h) := by group

theorem dihedral_fusion_decomposition
    [Finite G] (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (P : Subgroup G) (hPS : P ≤ (S : Subgroup G))
    (g : G) (hg : rightConjugate P g ≤ (S : Subgroup G)) :
    ∃ z : G, DihedralFusionDecomposition (S : Subgroup G) P z ∧
      rightConjugate P z = rightConjugate P g ∧
      ∀ x ∈ P, z⁻¹ * x * z = g⁻¹ * x * g := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzg⟩ := dihedralFusionDecomposition_of_huppert S (by omega) e
    (HuppertExtremal.centric_conjugation_decomposition S hPS hg)
  exact ⟨z, hz, rightConjugate_eq_of_pointwise P hzg, hzg⟩

end CFSG.GorensteinWalter
