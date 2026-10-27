module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.DesarguesianPlanes.LinearCentralizerData

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

@[expose] noncomputable def centerSub : Subgroup G :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range.map
    (linearCentralizerHom φ)

theorem mem_centerSub {x : G} :
    x ∈ centerSub φ ↔
      ∃ a : Fˣ, linearCentralizerHom φ (GeneralLinearGroup.scalar (Fin 2) a) = x := by
  rw [centerSub, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

theorem commute_of_mem_centerSub {x g : G} (hx : x ∈ centerSub φ) (hg : J * g = g * J) :
    x * g = g * x := by
  obtain ⟨a, rfl⟩ := (mem_centerSub φ).mp hx
  obtain ⟨B, rfl⟩ := exists_linearCentralizerHom_eq φ hg
  rw [← map_mul, ← map_mul]
  congr 1
  have h := (Subgroup.mem_center_iff.mp
    (by rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨a, rfl⟩ :
      GeneralLinearGroup.scalar (Fin 2) a ∈ Subgroup.center (GL (Fin 2) F)) B)
  exact h.symm

theorem eq_of_conj_mem_centerSub [Finite G] (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ Subgroup.centralizer {J})
    (hN : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer {J})
    {z : G} (hz : z ∈ centerSub φ) (g : G) (hg : g⁻¹ * z * g ∈ centerSub φ) :
    g⁻¹ * z * g = z := by
  have hcent : ∀ x ∈ centerSub φ, x ∈ Subgroup.centralizer (S : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsJ := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
    exact (commute_of_mem_centerSub φ hx hsJ.symm).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hgn⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer z g (hcent z hz) (hcent _ hg)
  have hnJ := Subgroup.mem_centralizer_singleton_iff.mp (hN hn)
  rw [hgn]
  have hc := commute_of_mem_centerSub φ hz hnJ.symm
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.BrauerLinearThree
